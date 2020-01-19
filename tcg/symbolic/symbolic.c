#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "qemu/bitops.h"

#include "symbolic-struct.h"
#include "symbolic.h"
#include "config.h"

//#define SYMBOLIC_DEBUG
//#define DISABLE_SOLVER

// symbolic temps
Expr* s_temps[TCG_MAX_TEMPS] = {0};

// symbolic memory
#define L1_PAGE_BITS 16
#define L2_PAGE_BITS 16
#define L3_PAGE_BITS 16

typedef struct l3_page_t {
    Expr* entries[1 << L3_PAGE_BITS];
} l3_page_t;

typedef struct l2_page_t {
    l3_page_t* entries[1 << L2_PAGE_BITS];
} l2_page_t;

typedef struct l1_page_t {
    l2_page_t* entries[1 << L1_PAGE_BITS];
} l1_page_t;

// up to 48 bits addressing
typedef struct s_memory_t {
    l1_page_t table;
} s_memory_t;

s_memory_t s_memory = {0};

// path constraints
Expr* path_constraints = NULL;

// Expr allocation pool
Expr* pool           = NULL;
Expr* next_free_expr = NULL;
Expr* last_expr      = NULL; // ToDo: unsafe

// query pool
Expr** queue_query = NULL;
Expr** next_query  = NULL;

TCGContext* internal_tcg_context = NULL;

// from tcg.c
typedef struct TCGHelperInfo {
    void*       func;
    const char* name;
    unsigned    flags;
    unsigned    sizemask;
} TCGHelperInfo;

// from tcg.c
extern GHashTable* helper_table;
extern const char* tcg_find_helper(TCGContext* s, uintptr_t val);
#define str(s) #s
// FLAGS | dh_callflag(ret),
// dh_sizemask(ret, 0) },
#define DEF_HELPER_INFO(HELPER_FUNC)                                           \
    TCGHelperInfo helper_info_##HELPER_FUNC = {.func     = HELPER_FUNC,        \
                                               .name     = str(HELPER_FUNC),   \
                                               .flags    = 0,                  \
                                               .sizemask = 0};

#if 0
TCGOp * op_macro;
#define ADD_VOID_CALL_0(f, op, tcg_ctx)                                        \
    ({                                                                         \
        do {                                                                   \
            TCGOpcode lopc        = INDEX_op_call;                             \
            op_macro              = tcg_op_insert_after(tcg_ctx, op, lopc);    \
            TCGOP_CALLO(op_macro) = 0;                                         \
            op_macro->args[0]     = (uintptr_t)f;                              \
            op_macro->args[1]     = 0;                                         \
            TCGOP_CALLI(op_macro) = 0;                                         \
        } while (0);                                                           \
        op_macro;                                                              \
    })
#endif

#define MARK_TEMP_AS_ALLOCATED(t)                                              \
    do {                                                                       \
        t->temp_allocated = 1;                                                 \
    } while (0)
#define MARK_TEMP_AS_NOT_ALLOCATED(t)                                          \
    do {                                                                       \
        t->temp_allocated = 0;                                                 \
    } while (0)

#ifdef SYMBOLIC_DEBUG
#define debug_printf(...)                                                      \
    do {                                                                       \
        printf(__VA_ARGS__);                                                   \
    } while (0);
#else
#define debug_printf(...)                                                      \
    do {                                                                       \
    } while (0);
#endif

static SymbolicConfig s_config = {0};
static inline void    load_configuration(void)
{
    char* var = getenv("SYMBOLIC_EXEC_START_ADDR");
    if (var) {
        s_config.symbolic_exec_start_addr = (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_start_addr != LONG_MIN &&
               s_config.symbolic_exec_start_addr != LONG_MAX);
    }
    assert(s_config.symbolic_exec_start_addr != 0 &&
           "Need to specify symbolic exec start address.");

    var = getenv("SYMBOLIC_EXEC_STOP_ADDR");
    if (var) {
        s_config.symbolic_exec_stop_addr = (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_stop_addr != LONG_MIN &&
               s_config.symbolic_exec_stop_addr != LONG_MAX);
    }
    assert(s_config.symbolic_exec_stop_addr != 0 &&
           "Need to specify symbolic exec stop address.");

    var = getenv("SYMBOLIC_INJECT_INPUT_MODE");
    if (var) {
        if (strcmp(var, "READ_FD_0") == 0)
            s_config.symbolic_inject_input_mode = READ_FD_0;
        if (strcmp(var, "REG") == 0)
            s_config.symbolic_inject_input_mode = REG;
        if (strcmp(var, "BUFFER") == 0)
            s_config.symbolic_inject_input_mode = BUFFER;
    }
    assert(s_config.symbolic_inject_input_mode != NO_INPUT &&
           "Need to specify symbolic exec injection input mode.");

    s_config.symbolic_exec_reg_name = getenv("SYMBOLIC_EXEC_REG_NAME");

    var = getenv("SYMBOLIC_EXEC_REG_INSTR_ADDR");
    if (var) {
        s_config.symbolic_exec_reg_instr_addr =
            (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_reg_instr_addr != LONG_MIN &&
               s_config.symbolic_exec_reg_instr_addr != LONG_MAX);
        assert(s_config.symbolic_exec_reg_name &&
               "Need to specify symbolic exec register name.");
    } else {
        assert(s_config.symbolic_exec_reg_name == NULL &&
               "Need to specify symbolic exec register address.");
    }
}

void init_symbolic_mode(void)
{
#ifndef DISABLE_SOLVER
    int expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                                  sizeof(Expr) * EXPR_POOL_CAPACITY, 0666);

    assert(expr_pool_shm_id > 0);

    int query_shm_id = shmget(QUERY_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Expr*) * EXPR_POOL_CAPACITY, 0666);
    assert(query_shm_id > 0);

    // printf("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);

    pool = shmat(expr_pool_shm_id, EXPR_POOL_ADDR, 0);
    assert(pool);

    queue_query = shmat(query_shm_id, NULL, 0);
    assert(queue_query);

#else
    pool        = g_malloc0(sizeof(Expr) * EXPR_POOL_CAPACITY);
    queue_query = g_malloc0(sizeof(Expr*) * EXPR_POOL_CAPACITY);
#endif

    // printf("POOL_ADDR=%p\n", pool);

#if 0
    for (size_t i = 0; i < EXPR_POOL_CAPACITY; i++)
        assert(*(queue_query + i) == 0);
#endif

    next_free_expr = pool;
    next_query     = queue_query;

    // configuration
    load_configuration();
}

static inline int count_free_temps(TCGContext* tcg_ctx)
{
    int count = 0;
    for (size_t j = 0; j < BITS_TO_LONGS(TCG_MAX_TEMPS); j++)
        for (size_t i = 0; i < BITS_PER_LONG; i++)
            count += test_bit(i, &tcg_ctx->free_temps[TCG_TYPE_I64].l[j]);
    return count;
}

// FixMe: shitty way to hide the variable...
#define SAVE_TEMPS_COUNT(s)                                                    \
    int temps_initial_count = s->nb_temps - count_free_temps(s);
#define CHECK_TEMPS_COUNT_WITH_DELTA(s, delta)                                 \
    assert(temps_initial_count == s->nb_temps - count_free_temps(s) + delta);
#define CHECK_TEMPS_COUNT(s)                                                   \
    assert(temps_initial_count == s->nb_temps - count_free_temps(s));

// since we are asking for new temps after generating and analyzing TCG,
// tcg_temp_new_internal may returns temps that are in use in the TB
// (but are dead at the end of the TB). To avoid conflicts, we call
// tcg_temp_new_internal until we get a non used temp from the
// previous istructions in the TB.
//
// NOTE: temps must be deallocated after generating instrumentation
//       for one instruction otherwise conflicts may emerge!
static uint8_t         used_temps_idxs[TCG_MAX_TEMPS] = {0};
static inline TCGTemp* new_non_conflicting_temp(TCGType type)
{
    assert(type == TCG_TYPE_I64); // ToDo: validate other types
    TCGTemp* r = NULL;
    TCGTemp* conflicting_temps[TCG_MAX_TEMPS];
    size_t   conflicting_temps_count = 0;
    while (!r) {
        TCGTemp* current = tcg_temp_new_internal(type, false);
        size_t   idx     = temp_idx(current);
        assert(idx < TCG_MAX_TEMPS);
        if (used_temps_idxs[idx] != 0) // temp is in use
        {
            conflicting_temps[conflicting_temps_count++] = current;
        } else {
            r = current;
        }
    }

    // deallocate any temp that is in conflict
    while (conflicting_temps_count > 0) {
        tcg_temp_free_internal(conflicting_temps[conflicting_temps_count - 1]);
        conflicting_temps_count--;
    }

    return r;
}

static inline void mark_insn_as_instrumentation(TCGOp* op)
{
    // we use the last op arg, which is usually unused
    op->args[MAX_OPC_PARAM - 1] = (uint64_t)1;
}

static inline TCGMemOp get_mem_op(uint64_t oi)
{
    return oi >> 32; // ToDo: 32 bit
}

static inline uint32_t get_mem_offset(uint64_t oi)
{
    return oi & 0xFFFFFFFFFFFFFFFF; // ToDo: 32 bit
}

static inline uint64_t make_mem_op_offset(uint32_t op, uint32_t idx)
{
    return (((uint64_t)op) << 32) | idx;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_0(void* f, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = (uintptr_t)f;
    op->args[1]     = 0; // flags
    TCGOP_CALLI(op) = 0; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_1(void* f, TCGTemp* arg, TCGOp* op_in,
                                   TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(arg->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg);
    op->args[1]     = (uintptr_t)f;
    op->args[2]     = 0; // flags
    TCGOP_CALLI(op) = 1; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_2(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = (uintptr_t)f;
    op->args[3]     = 0; // flags
    TCGOP_CALLI(op) = 2; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_3(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = (uintptr_t)f;
    op->args[4]     = 0; // flags
    TCGOP_CALLI(op) = 3; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_4(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGOp* op_in,
                                   TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = (uintptr_t)f;
    op->args[5]     = 0; // flags
    TCGOP_CALLI(op) = 4; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_5(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGTemp* arg4,
                                   TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);
    assert(arg4->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = temp_arg(arg4);
    op->args[5]     = (uintptr_t)f;
    op->args[6]     = 0; // flags
    TCGOP_CALLI(op) = 5; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_6(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGTemp* arg4,
                                   TCGTemp* arg5, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);
    assert(arg4->temp_allocated);
    assert(arg5->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = temp_arg(arg4);
    op->args[5]     = temp_arg(arg5);
    op->args[6]     = (uintptr_t)f;
    op->args[7]     = 0; // flags
    TCGOP_CALLI(op) = 6; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

static inline void check_pool_expr_capacity(void)
{
    assert(next_free_expr >= pool);
    assert(next_free_expr < pool + EXPR_POOL_CAPACITY);
}

static inline Expr* new_expr(void)
{
    // ToDo: use free list
    check_pool_expr_capacity();
    next_free_expr += 1;
    last_expr = next_free_expr - 1;
    return next_free_expr - 1;
}

static inline const char* get_reg_name(TCGContext* tcg_ctx, size_t idx)
{
    TCGTemp* t = &tcg_ctx->temps[idx];
    return t->name;
}

void print_reg(void);
void print_reg(void)
{
    debug_printf("%s is %ssymbolic\n", s_config.symbolic_exec_reg_name,
                 s_temps[12]->opkind == IS_SYMBOLIC ? "" : "not ");
}
DEF_HELPER_INFO(print_reg);

static inline void new_symbolic_expr(void)
{
    Expr* e   = new_expr();
    e->opkind = IS_SYMBOLIC;
    e->op1    = 0; // FixMe: assign id based on the specific symbolic input
    debug_printf("Marking expr%lu as symbolic\n", GET_EXPR_IDX(e));
}

static inline void sync_argo_temp(TCGOp* op, size_t i)
{
    op->life |= SYNC_ARG << i;
}

static inline void mark_dead_arg_temp(TCGOp* op, size_t i)
{
    op->life |= DEAD_ARG << i;
}

// ts <- CONST
static inline void tcg_movi(TCGTemp* ts, uintptr_t const_val,
                            uint8_t is_ts_dead, TCGOp* op_in, TCGOp** op_out,
                            TCGContext* tcg_ctx)
{
    assert(ts->temp_allocated);

    TCGOpcode opc = INDEX_op_movi_i64;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts);
    assert(!is_ts_dead);

    op->args[1] = (uintptr_t)const_val;

    if (op_out)
        *op_out = op;
}

// to <- from
static inline void tcg_mov(TCGTemp* ts_to, TCGTemp* ts_from,
                           uint8_t is_ts_to_dead, uint8_t is_ts_from_dead,
                           TCGOp* op_in, TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_from->temp_allocated);

    TCGOpcode opc = INDEX_op_mov_i64;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    if (op_out)
        *op_out = op;
}

static inline void tcg_cmov(TCGTemp* ts_out, TCGTemp* ts_a, TCGTemp* ts_b,
                            TCGTemp* ts_true, TCGTemp* ts_false, TCGCond cond,
                            uint8_t is_ts_out_dead, uint8_t is_ts_a_dead,
                            uint8_t is_ts_b_dead, uint8_t is_ts_true_dead,
                            uint8_t is_ts_false_dead, TCGOp* op_in,
                            TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_out->temp_allocated);
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_true->temp_allocated);
    assert(ts_false->temp_allocated);

    TCGOpcode opc = INDEX_op_movcond_i64;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    // ret, c1, c2, v1, v2, cond

    op->args[0] = temp_arg(ts_out);
    assert(!is_ts_out_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    op->args[3] = temp_arg(ts_true);
    if (is_ts_true_dead) {
        mark_dead_arg_temp(op, 3);
        tcg_temp_free_internal(ts_true);
    }

    op->args[4] = temp_arg(ts_false);
    if (is_ts_false_dead) {
        mark_dead_arg_temp(op, 4);
        tcg_temp_free_internal(ts_false);
    }

    op->args[5] = cond;

    if (op_out)
        *op_out = op;
}

// c <- a op b
static inline void tcg_binop(TCGTemp* ts_c, TCGTemp* ts_a, TCGTemp* ts_b,
                             uint8_t is_ts_c_dead, uint8_t is_ts_a_dead,
                             uint8_t is_ts_b_dead, OPKIND opkind, TCGOp* op_in,
                             TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_c->temp_allocated);

    TCGOpcode opc;
    switch (opkind) {
        case ADD:
            opc = INDEX_op_add_i64;
            break;
        case SUB:
            opc = INDEX_op_sub_i64;
            break;
        case SHR:
            opc = INDEX_op_shr_i64;
            break;
        case SHL:
            opc = INDEX_op_shl_i64;
            break;
        case AND:
            opc = INDEX_op_and_i64;
            break;
        case OR:
            opc = INDEX_op_or_i64;
            break;
        case XOR:
            opc = INDEX_op_xor_i64;
            break;
        default:
            tcg_abort();
            break;
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_c);
    assert(!is_ts_c_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_b_dead) {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    if (op_out)
        *op_out = op;
}

static inline void tcg_load_n(TCGTemp* ts_from, TCGTemp* ts_to,
                              uintptr_t offset, uint8_t is_ts_from_dead,
                              uint8_t is_ts_to_dead, size_t n_bytes,
                              TCGOp* op_in, TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_from->temp_allocated);
    assert(ts_to->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes) {
        // ToDo: add _i32 address mode
        case 8:
            opc = INDEX_op_ld_i64;
            break;
        case 1:
            opc = INDEX_op_ld8u_i64;
            break;
        default:
            tcg_abort();
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    op->args[2] = offset;

    if (op_out)
        *op_out = op;
}

static inline void tcg_store_n(TCGTemp* ts_to, TCGTemp* ts_val,
                               uintptr_t offset, uint8_t is_ts_to_dead,
                               uint8_t is_ts_val_dead, size_t n_bytes,
                               TCGOp* op_in, TCGOp** op_out,
                               TCGContext* tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_val->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes) {
        case 8:
            opc = INDEX_op_st_i64;
            break;
        case 4:
            opc = INDEX_op_st32_i64;
            break;
        case 2:
            opc = INDEX_op_st16_i64;
            break;
        case 1:
            opc = INDEX_op_st8_i64;
            break;
        default:
            tcg_abort();
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_val);
    if (is_ts_val_dead) {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_val);
    }

    op->args[1] = temp_arg(ts_to);
    if (is_ts_to_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_to);
    }

    op->args[2] = offset;

    if (op_out)
        *op_out = op;
}

// branch to label if a cond b is true
static inline void tcg_brcond(TCGLabel* label, TCGTemp* ts_a, TCGTemp* ts_b,
                              TCGCond cond, uint8_t is_ts_a_dead,
                              uint8_t is_ts_b_dead, TCGOp* op_in,
                              TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);

    label->refs++;
    TCGOpcode opc = INDEX_op_brcond_i64; // ToDo: i32
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_a);
    }

    op->args[1] = temp_arg(ts_b);
    if (is_ts_b_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_b);
    }

    op->args[2] = cond;
    op->args[3] = label_arg(label);

    if (op_out)
        *op_out = op;
}

// branch to label (always)
static inline void tcg_br(TCGLabel* label, TCGOp* op_in, TCGOp** op_out,
                          TCGContext* tcg_ctx)
{
    label->refs++;
    TCGOpcode opc = INDEX_op_br;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]   = label_arg(label);

    if (op_out)
        *op_out = op;
}

// add a goto label (referenced by brcond)
static inline void tcg_set_label(TCGLabel* label, TCGOp* op_in, TCGOp** op_out,
                                 TCGContext* tcg_ctx)
{
    label->present = 1;
    TCGOpcode opc  = INDEX_op_set_label;
    TCGOp*    op   = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]    = label_arg(label);

    if (op_out)
        *op_out = op;
}

static inline void print_something(char* str) { debug_printf("%s\n", str); }

// the string has to be statically allocated, otherwise it will crash!
static inline void tcg_print_const_str(const char* str, TCGOp* op_in,
                                       TCGOp** op, TCGContext* tcg_ctx)
{
    TCGTemp* t_str = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_str, (uintptr_t)str, 0, op_in, NULL, tcg_ctx);
    add_void_call_1(print_something, t_str, op_in, op, tcg_ctx);
    tcg_temp_free_internal(t_str);
}

static inline void init_reg(size_t reg, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(reg < TCG_MAX_TEMPS);
    debug_printf("Setting expr of reg %lu\n", reg);

    TCGTemp* t_last_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_last_expr, (uintptr_t)&last_expr, 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_last_expr, t_last_expr, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGTemp* t_reg_id = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_reg_id, (uintptr_t)reg, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_last_expr, t_reg_id, offsetof(Expr, op1), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_reg_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_reg_size, (uintptr_t)8, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_last_expr, t_reg_size, offsetof(Expr, op2), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_dst, (uintptr_t)&s_temps[reg], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_dst, t_last_expr, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void make_reg_symbolic(const char* reg_name, TCGOp* op,
                                     TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    for (int i = 0; i < TCG_TARGET_NB_REGS; i++) {
        TCGTemp* t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0) {
            debug_printf("Marking %s (id=%d) as symbolic\n", t->name, i);
            add_void_call_0(new_symbolic_expr, op, NULL, tcg_ctx);
            init_reg(i, op, tcg_ctx);
            add_void_call_0(print_reg, op, NULL, tcg_ctx);
        }
    }

    CHECK_TEMPS_COUNT(tcg_ctx);
}

void print_temp(size_t idx);
void print_temp(size_t idx)
{
    if (s_temps[idx]) {
        printf("t[%lu](%s) is ", idx, get_reg_name(internal_tcg_context, idx));
        print_expr(s_temps[idx]);
    }
}

static inline void move_temp_helper(size_t from, size_t to)
{
#if 0
    if (s_temps[to] || s_temps[from]) {
        printf("Move: t[%ld] = t[%ld]\n", to, s_temps[from] ? from : -1);
        if (s_temps[from])
            print_temp(from);
        if (s_temps[to])
            print_temp(to);
    }
#endif
    s_temps[to] = s_temps[from];
}

static inline void move_temp(size_t from, size_t to, TCGOp* op_in,
                             TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp* t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_from, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void clear_temp_helper(uintptr_t temp_idx)
{
#if 0
    if (s_temps[temp_idx])
        printf("Clearing temp %lu\n", temp_idx);
#endif
    s_temps[temp_idx] = 0;
}

static inline void clear_temp(size_t idx, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    assert(idx < TCG_MAX_TEMPS);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t, (uintptr_t)&s_temps[idx], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t, t_zero, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_new_expr(TCGTemp* t_out, TCGOp* op_in,
                                     TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGOp* op;

    add_void_call_0(check_pool_expr_capacity, op_in, &op,
                    tcg_ctx); // ToDo: make inline check
    mark_insn_as_instrumentation(op);

    // assert(next_free_expr);

    TCGTemp* t_next_free_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_next_free_expr_addr, (uintptr_t)&next_free_expr, 0, op_in, NULL,
             tcg_ctx);

    TCGTemp* t_next_free_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_next_free_expr_addr, t_next_free_expr, 0, 0, 0,
               sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_mov(t_out, t_next_free_expr, 0, 0, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(
        op); // required to handle a t_out which already has a reg allocated

    TCGTemp* t_expr_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_expr_size, sizeof(Expr), 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_next_free_expr, t_next_free_expr, t_expr_size, 0, 0, 0, ADD,
              op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_expr_size);

    tcg_store_n(t_next_free_expr_addr, t_next_free_expr, 0, 1, 1, sizeof(void*),
                op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

// When adding instrumentation with branches and when accessing
// the operands contents, TCG may move temp loads (i.e., loading
// content of the temp operand from memory) within the branching
// code (which is not always executed), possibly leading to SIGSEGV.
// To avoid this issue, we insert fake uses for each temp operand
// before any branching code, to make temp loads branchless.
static inline void preserve_op_load(TCGTemp* t, TCGOp* op_in,
                                    TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGTemp* t_dummy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t);
    tcg_mov(t_dummy, t, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t);
    // this is needed since out temp cannot be marked as dead in tcg_mov
    tcg_temp_free_internal(t_dummy);
    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_binop_helper(uintptr_t opkind, uintptr_t t_out_idx,
                                     uintptr_t t_op_a_idx, uintptr_t t_op_b_idx,
                                     uintptr_t t_op_a, uintptr_t t_op_b)
{
    Expr* expr_a = s_temps[t_op_a_idx];
    Expr* expr_b = s_temps[t_op_b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[t_out_idx] = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx, opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_expr   = new_expr();
    binop_expr->opkind = (OPKIND)opkind;

    if (expr_a)
        binop_expr->op1 = expr_a;
    else {
        binop_expr->op1          = (Expr*)(uintptr_t)t_op_a;
        binop_expr->op1_is_const = 1;
    }

    if (expr_b)
        binop_expr->op2 = expr_b;
    else {
        binop_expr->op2          = (Expr*)(uintptr_t)t_op_b;
        binop_expr->op2_is_const = 1;
    }

    s_temps[t_out_idx] = binop_expr;
}

// Binary operation: t_out = t_a opkind t_b
static inline void qemu_binop(OPKIND opkind, TCGTemp* t_op_out, TCGTemp* t_op_a,
                              TCGTemp* t_op_b, TCGOp* op_in,
                              TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // TCGOp *op;

    size_t out = temp_idx(t_op_out);
    size_t a   = temp_idx(t_op_a);
    size_t b   = temp_idx(t_op_b);

    assert(out < TCG_MAX_TEMPS);
    assert(a < TCG_MAX_TEMPS);
    assert(b < TCG_MAX_TEMPS);

    preserve_op_load(t_op_a, op_in, tcg_ctx);
    preserve_op_load(t_op_b, op_in, tcg_ctx);

    // check if both t_a and t_b are concrete
    // if this is the case, then mark dest as concrete

    TCGLabel* label_both_concrete = gen_new_label();

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // tcg_print_const_str("Checking binary op", op_in, &op, tcg_ctx);

    // add_void_call_1(print_expr, t_a, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    TCGTemp* t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[b], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // add_void_call_1(print_expr, t_b, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    // tcg_print_const_str("Checking binary op: DONE", op_in, &op, tcg_ctx);

    TCGTemp* t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel* label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

#if 0
    tcg_print_const_str("Binary op:", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_print_const_str("Binary op: DONE", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[out], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_unop_helper(uintptr_t opkind, uintptr_t t_out_idx,
                                    uintptr_t t_op_a_idx, uintptr_t t_op_a)
{
    Expr* expr_a = s_temps[t_op_a_idx];
    if (expr_a == NULL) {
        s_temps[t_out_idx] = NULL;
        return; // early exit
    }

#if 0
    printf("Unary operation:  %lu = %s %lu\n", t_out_idx, opkind_to_str(opkind), t_op_a_idx);
    print_temp(t_op_a_idx);
#endif

    Expr* unop_expr    = new_expr();
    unop_expr->opkind  = (OPKIND)opkind;
    unop_expr->op1     = expr_a;
    s_temps[t_out_idx] = unop_expr;
}

static inline void qemu_unop(OPKIND opkind, TCGTemp* t_op_out, TCGTemp* t_op_a,
                             TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // TCGOp *op;

    preserve_op_load(t_op_a, op_in, tcg_ctx);

    size_t out = temp_idx(t_op_out);
    size_t a   = temp_idx(t_op_a);

    // check whether t_op_a is concrete

    TCGLabel* label_a_concrete = gen_new_label();
    TCGTemp*  t_a              = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[out], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_l2_page(uintptr_t l1_entry_idx)
{
    assert(l1_entry_idx < 1 << L1_PAGE_BITS);

    debug_printf("Allocating l2 page at idx %lu\n", l1_entry_idx);
    s_memory.table.entries[l1_entry_idx] =
        g_malloc0(sizeof(l2_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l1_entry_idx_addr=%p l2_page_addr=%p\n",
                 &s_memory.table.entries[l1_entry_idx],
                 s_memory.table.entries[l1_entry_idx]);
}

static inline void allocate_l3_page(void** l2_page_idx_addr)
{
    debug_printf("Allocating l3 page at l2_page_idx_addr=%p\n",
                 l2_page_idx_addr);
    *l2_page_idx_addr = g_malloc0(sizeof(l3_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l3_page_addr=%p\n", *l2_page_idx_addr);
}

static inline void print_value(uintptr_t value)
{
    debug_printf("V: %lx\n", value);
}

static inline void print_t_l1_entry_idx_addr(void* l1_entry_addr)
{
    debug_printf("L2 Entry addr: %p\n", l1_entry_addr);
}

static inline void print_t_l3_entry_idx_addr(void* l3_entry_addr)
{
    debug_printf("L3 Entry addr: %p\n", l3_entry_addr);
}

static inline void failure_cross_page_access(void)
{
    printf("A memory access is crossing a L3 page: not yet supported.\n");
    tcg_abort();
}

#define EARLY_EXIT_CONST ((TCGTemp*)1)

static inline void get_expr_addr_for_addr(TCGTemp*  t_addr,
                                          TCGTemp** t_expr_addr,
                                          uintptr_t offset, size_t size,
                                          TCGTemp* early_exit, TCGOp* op_in,
                                          TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp* op;

    TCGTemp* t_addr_with_offset = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_addr_with_offset, offset, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_binop(t_addr_with_offset, t_addr, t_addr_with_offset, 0, 0, 0, ADD,
              op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp* t_l3_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    if (early_exit) {
        TCGTemp* t_null = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_null, (uintptr_t)0, 0, op_in, NULL, tcg_ctx);
        tcg_binop(t_l3_page_idx_addr, t_null, t_null, 0, 1, 0, XOR, op_in, &op,
                  tcg_ctx); // force TCG to allocate the temp into a reg
        // add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL,
        // tcg_ctx);
    }
    *t_expr_addr = t_l3_page_idx_addr;

    // compute index for L1 page

    TCGTemp* t_l1_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l1_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_l1_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_shr_bit, L1_PAGE_BITS + L2_PAGE_BITS, 0, op_in, NULL,
             tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx, t_l1_page_idx, t_l1_shr_bit, 0, 0, 1, SHR, op_in,
              NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp* t_l1_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_page, (uintptr_t)&s_memory, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_l1_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void*) == 8); // 2^3 = 8
    tcg_movi(t_l1_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx, t_l1_page_idx_addr, 0, 0, 0,
              SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx_addr, t_l1_page, 0, 0, 1, ADD,
              op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l1_page);

    TCGTemp* t_l2_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGLabel* label_l2_page_is_allocated = gen_new_label();
    tcg_brcond(label_l2_page_is_allocated, t_l2_page, t_zero, TCG_COND_NE, 0, 0,
               op_in, NULL, tcg_ctx);

    // early_exit?
    TCGLabel* label_early_exit = NULL;
    if (early_exit) {
        label_early_exit = gen_new_label();
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0,
                       op_in, NULL, tcg_ctx);
    }

    // if not, allocate L2 page
    add_void_call_1(allocate_l2_page, t_l1_page_idx, op_in, &op, tcg_ctx);
    // mark since it will preserve regs, marking temps as TS_VAL_MEM
    // however this is done only when the helper is executed
    // and its execution depends on the branch condiion!
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l1_page_idx);

    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 1, 0, sizeof(uintptr_t), op_in,
               &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l2_page_is_allocated, op_in, NULL, tcg_ctx);

    // add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry, op_in, NULL,
    // tcg_ctx);

    // compute index for L2 page
    TCGTemp* t_l2_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l2_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    // FixMe: mask higher bits

    TCGTemp* t_l2_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_shr_bit, L2_PAGE_BITS, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_shr_bit, 0, 0, 1, SHR, op_in,
              NULL, tcg_ctx);

    TCGTemp* t_l2_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_and_bit, 0, 0, 1, AND, op_in,
              NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp* t_l2_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void*) == 8); // 2^3 = 8
    tcg_movi(t_l2_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx, t_l2_page_idx_addr, 0, 1, 0,
              SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx_addr, t_l2_page, 0, 0, 1, ADD,
              op_in, NULL, tcg_ctx);

    TCGTemp* t_l3_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGLabel* label_l3_page_is_allocated = gen_new_label();
    tcg_brcond(label_l3_page_is_allocated, t_l3_page, t_zero, TCG_COND_NE, 0, 0,
               op_in, NULL, tcg_ctx);

    // early_exit?
    if (early_exit) {
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0,
                       op_in, NULL, tcg_ctx);
    }
    tcg_temp_free_internal(t_zero);

    add_void_call_1(allocate_l3_page, t_l2_page_idx_addr, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 1, 0, sizeof(uintptr_t), op_in,
               &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l3_page_is_allocated, op_in, NULL, tcg_ctx);

    // compute index for L3 page

    TCGTemp* t_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l3_page_idx, t_addr_with_offset, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp* t_l3_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l3_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_l3_and_bit, 0, 0, 1, AND, op_in,
              NULL, tcg_ctx);

    // compute the address of the Expr in the page

    assert(sizeof(void*) == 8); // 2^3 = 8
    TCGTemp* t_three = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_three, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_three, 0, 0, 1, SHL, op_in,
              &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    // tcg_movi(t_l3_page_idx_addr, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);
    // tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_l3_page_idx_addr, 0, 0, 0,
    // SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx_addr, t_l3_page, 0, 0, 1, ADD,
              op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    // check that t_l3_page_idx_addr + size is still within the L3 page,
    // otherwise fail FixMe: handle cross page store/loading

    TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_size, size, 0, op_in, NULL, tcg_ctx);
    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_size, 0, 0, 1, ADD, op_in, NULL,
              tcg_ctx);
    TCGTemp* t_max_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_max_l3_page_idx, 1 << L3_PAGE_BITS, 0, op_in, NULL, tcg_ctx);
    TCGLabel* label_no_cross_page_access = gen_new_label();
    tcg_brcond(label_no_cross_page_access, t_l3_page_idx, t_max_l3_page_idx,
               TCG_COND_LT, 1, 1, op_in, NULL, tcg_ctx);
    add_void_call_0(failure_cross_page_access, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_set_label(label_no_cross_page_access, op_in, NULL, tcg_ctx);

    if (early_exit) {
        tcg_set_label(label_early_exit, op_in, NULL, tcg_ctx);
        // add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL,
        // tcg_ctx);
    }

    CHECK_TEMPS_COUNT_WITH_DELTA(
        tcg_ctx,
        -1); // t_expr_addr is allocated here, but freed by the caller!
}

static inline size_t get_mem_op_size(TCGMemOp mem_op)
{
    switch (mem_op & MO_SIZE) {
        case MO_8:
            return 1;
        case MO_16:
            return 2;
        case MO_32:
            return 4;
        case MO_64:
            return 8;
        default:
            tcg_abort();
    }
}

static inline size_t get_mem_op_signextend(TCGMemOp mem_op)
{
    return mem_op & MO_SIGN;
}

static inline void qemu_load_helper(uintptr_t orig_addr,
                                    uintptr_t mem_op_offset, uintptr_t addr_idx,
                                    uintptr_t val_idx)
{
    TCGMemOp  mem_op = get_mem_op(mem_op_offset);
    uintptr_t offset = get_mem_offset(mem_op_offset);

    // assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    uintptr_t addr = orig_addr + offset;

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t  l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t* l3_page     = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    assert(size <= 8);
    Expr*   exprs[8]         = {NULL};
    uint8_t expr_is_not_null = 0;
    for (size_t i = 0; i < size; i++) {
        size_t idx       = (mem_op & MO_BE) ? i : size - i - 1;
        exprs[i]         = l3_page->entries[l3_page_idx + idx];
        expr_is_not_null = expr_is_not_null | (exprs[idx] != 0);
    }

    if (expr_is_not_null == 0) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

#if 0
    printf("Loading %lu bytes: t[%ld] = *0x%p + %lu\n", size, val_idx,
           (void*)orig_addr, offset);
    // printf("Loading %lu bytes from %p at offset %lu\n", size, (void
    // *)orig_addr, offset);
#endif

    Expr* e = NULL;
    for (size_t i = 0; i < size; i++) {
        if (i == 0) {
            if (exprs[i] == NULL) {
                // allocate a new expr for the concrete value
                e                  = new_expr();
                e->opkind          = IS_CONST;
                uint8_t* byte_addr = ((uint8_t*)addr) + i;
                uint8_t  byte      = *byte_addr;
                e->op1             = (Expr*)((uintptr_t)byte);
            } else
                e = exprs[i];
        } else {
            Expr* n_expr   = new_expr();
            n_expr->opkind = CONCAT8;

            n_expr->op1 = e;

            if (exprs[i] == NULL) {
                // fetch the concrete value, embed it in the expr
                uint8_t* byte_addr   = ((uint8_t*)addr) + i;
                uint8_t  byte        = *byte_addr;
                n_expr->op2          = (Expr*)((uintptr_t)byte);
                n_expr->op2_is_const = 1;
            } else {
                n_expr->op2 = exprs[i];
            }

            e = n_expr;
        }
    }

    if (size < 8) {
        Expr*     n_expr = new_expr();
        uintptr_t opkind = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
        n_expr->opkind   = opkind;
        n_expr->op1      = e;
        n_expr->op2      = (Expr*)(8 * size);
        e                = n_expr;
        // printf("Zero extending on load. %lu\n", (8 * size));
    }

    //printf("Load expr:\n");
    //print_expr(e);
    s_temps[val_idx] = e;
}

static inline void qemu_load(TCGTemp* t_addr, TCGTemp* t_val, uintptr_t offset,
                             TCGMemOp mem_op, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(t_val->base_type == TCG_TYPE_TL);
    assert(t_val->base_type == TCG_TYPE_I64); // FixMe: support other types
    assert((mem_op & MO_BE) == 0);            // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    preserve_op_load(t_addr, op_in, tcg_ctx);
    preserve_op_load(t_val, op_in, tcg_ctx);

    TCGOp* op;

    TCGTemp* t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size,
                           EARLY_EXIT_CONST /* FixMe: hack */, op_in, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_end = gen_new_label();

    // early exit
    TCGLabel* label_write_null = gen_new_label();
    tcg_brcond(label_write_null, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0,
               op_in, NULL, tcg_ctx);

    // build expr, if all bytes are concrete goto to label_write_null

    TCGTemp* t_expr_is_null = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_expr_is_null, 0, 0, op_in, NULL, tcg_ctx);

    assert(size <= 8);
    TCGTemp* t_exprs[8] = {NULL};

    for (size_t i = 0; i < size; i++) {
        size_t idx   = (mem_op & MO_BE) ? i : size - i - 1;
        t_exprs[idx] = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_load_n(t_l3_page_idx_addr, t_exprs[idx],
                   sizeof(Expr*) *
                       idx /* Why? Different from the helper but it works...*/,
                   i == size - 1, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
        tcg_binop(t_expr_is_null, t_expr_is_null, t_exprs[idx], 0, 0, 0, OR,
                  op_in, NULL, tcg_ctx);
    }

    tcg_brcond(label_write_null, t_expr_is_null, t_zero, TCG_COND_EQ, 1, 0,
               op_in, NULL, tcg_ctx);

    TCGTemp* t_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        if (i == 0) {
            // if expr is NULL, use the concrete value
            TCGLabel* label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE,
                       0, 0, op_in, NULL, tcg_ctx);

            allocate_new_expr(t_exprs[i], op_in, tcg_ctx);

            TCGTemp* t_mem_value      = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp* t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp* t_mem_value_addr_offset =
                new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL,
                     tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr,
                      t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL,
                      tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t),
                       op_in, NULL, tcg_ctx);

            tcg_store_n(t_exprs[i], t_mem_value, offsetof(Expr, op1), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, IS_CONST, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_opkind, offsetof(Expr, opkind), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);

            t_expr     = t_exprs[i];
            t_exprs[i] = NULL;
        } else {
            TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
            // FixMe: pre-allocate size exprs outside the loop
            allocate_new_expr(t_new_expr, op_in, tcg_ctx);

            TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, CONCAT8, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op2), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            // if expr is NULL, use the concrete value

            TCGLabel* label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE,
                       0, 0, op_in, NULL, tcg_ctx);

            TCGTemp* t_mem_value      = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp* t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp* t_mem_value_addr_offset =
                new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL,
                     tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr,
                      t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL,
                      tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t),
                       op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_mem_value, 0, 0, 1, sizeof(Expr*), op_in,
                        NULL, tcg_ctx);

            TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_one, offsetof(Expr, op1_is_const), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_exprs[i], offsetof(Expr, op1), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
            // mark_insn_as_instrumentation(op);

            t_expr     = t_new_expr;
            t_exprs[i] = NULL;
        }
    }

    // if size is less than sizeof(TCG_TYPE_TL), we may have to
    // zero-extend or sign-extend
    if (size < 8) // FixMe: other archs
    {
        TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp*  t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        uintptr_t opkind   = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
        tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op1), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_extend_bit = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_extend_bit, 8 * size, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_extend_bit, offsetof(Expr, op2), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_one, offsetof(Expr, op2_is_const), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        // mark_insn_as_instrumentation(op);

        t_expr = t_new_expr;
    }

    // add_void_call_1(print_expr, t_expr, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    // write expr to destination temp
    TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op,
             tcg_ctx);
    tcg_store_n(t_to, t_expr, 0, 1, 1, sizeof(void*), op_in, &op, tcg_ctx);
    tcg_br(label_end, op_in, NULL, tcg_ctx);

    // store NULL into destination temp
    tcg_set_label(label_write_null, op_in, NULL, tcg_ctx);
    for (size_t i = 0; i < size; i++)
        if (t_exprs[i])
            tcg_temp_free_internal(t_exprs[i]);
    t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op,
             tcg_ctx);
    tcg_store_n(t_to, t_zero, 0, 1, 1, sizeof(void*), op_in, &op, tcg_ctx);

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_store_helper(uintptr_t orig_addr,
                                     uintptr_t mem_op_offset,
                                     uintptr_t addr_idx, uintptr_t val_idx)
{
    TCGMemOp  mem_op = get_mem_op(mem_op_offset);
    uintptr_t offset = get_mem_offset(mem_op_offset);

    // assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    uintptr_t addr = orig_addr + offset;

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) {
        if (s_temps[val_idx] == NULL) // early exit
            return;

        l2_page                             = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t  l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t* l3_page     = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) {
        if (s_temps[val_idx] == NULL) // early exit
            return;

        l3_page                       = g_malloc0(sizeof(l3_page_t));
        l2_page->entries[l2_page_idx] = l3_page;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    if (s_temps[val_idx] == NULL) {
        for (size_t i = 0; i < size; i++)
            l3_page->entries[l3_page_idx + i] = NULL;
    } else {
#if 0
        printf("Storing %lu bytes: *%p + %lu = t[%ld]\n", size,
               (void*)orig_addr, offset, s_temps[val_idx] ? val_idx : -1);
#endif

#if 0
        if (mem_op & MO_BE)
            printf("Big endian\n");
        else
            printf("Little endian\n");
#endif

        for (size_t i = 0; i < size; i++) {
            Expr* e    = new_expr();
            e->opkind  = EXTRACT8;
            e->op1     = s_temps[val_idx];
            size_t idx = (mem_op & MO_BE) ? size - i - 1 : i;
            e->op2     = (Expr*)idx;
            l3_page->entries[l3_page_idx + i] = e;
            //printf("Storing byte at index %lu\n", i);
            // print_expr(e);
        }
    }
}

static inline void qemu_store(TCGTemp* t_addr, TCGTemp* t_val, uintptr_t offset,
                              TCGMemOp mem_op, TCGOp* op_in,
                              TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to store
    size_t size = get_mem_op_size(mem_op);

    TCGOp __attribute__((unused)) * op;

    // check whether val is concrete
    size_t   val_idx         = temp_idx(t_val);
    TCGTemp* t_val_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_val_expr_addr, (uintptr_t)&s_temps[val_idx], 0, op_in, NULL,
             tcg_ctx);

    TCGTemp* t_val_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_val_expr_addr, t_val_expr, 0, 1, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    // get location where to store expression
    TCGTemp* t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size,
                           t_val_expr, op_in, tcg_ctx);

    // add_void_call_1(print_expr, t_val_expr, op_in, &op, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_end = gen_new_label();
    // early exit
    tcg_brcond(label_end, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0, op_in,
               NULL, tcg_ctx);

    TCGLabel* label_expr_is_not_concrete = gen_new_label();
    tcg_brcond(label_expr_is_not_concrete, t_val_expr, t_zero, TCG_COND_NE, 0,
               1, op_in, NULL, tcg_ctx);

    // write NULL expr for each byte to store
    for (size_t i = 0; i < size; i++) {
        // set Expr
        tcg_store_n(t_l3_page_idx_addr, t_val_expr, sizeof(Expr*) * i, 0, 0,
                    sizeof(void*), op_in, NULL, tcg_ctx);
    }

    tcg_br(label_end, op_in, NULL, tcg_ctx);

    tcg_set_label(label_expr_is_not_concrete, op_in, NULL, tcg_ctx);

    // write EXT8(expr, index) for each byte to store
    for (size_t i = 0; i < size; i++) {
        // build EXTRACT expr
        TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        // FixMe: pre-allocate size exprs outside the loop
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_opkind, EXTRACT8, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_val_expr, offsetof(Expr, op1), 0,
                    i == size - 1, sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_index = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_index, size - i - 1, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_index, offsetof(Expr, op2), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        // mark_insn_as_instrumentation(op);

        // set Expr
        size_t idx = (mem_op & MO_BE) ? i : size - i - 1;
        tcg_store_n(t_l3_page_idx_addr, t_new_expr, sizeof(Expr*) * idx,
                    i == size - 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);
    }

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void extend(TCGTemp* t_op_to, TCGTemp* t_op_from,
                          EXTENDKIND extkind, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t to   = temp_idx(t_op_to);
    size_t from = temp_idx(t_op_from);

#if 0
    TCGOp* op;
    tcg_print_const_str("Zero-extending", op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);
#endif

    // check whether t_op_from is concrete
    TCGTemp* t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(
        t_out, t_from, 0, 0, op_in, NULL,
        tcg_ctx); // this is needed since we need to always overide t_to expr

    TCGLabel* label_op_is_const = gen_new_label();
    tcg_brcond(label_op_is_const, t_from, t_zero, TCG_COND_EQ, 0, 1, op_in,
               NULL, tcg_ctx);

    // create a ZEXT 32 expr

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    tcg_store_n(t_out, t_from, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t),
                op_in, NULL, tcg_ctx);

    uint8_t   opkind;
    uintptr_t opkind_const_param;
    switch (extkind) {
        case ZEXT_8:
            opkind             = ZEXT;
            opkind_const_param = 8;
            break;
        case ZEXT_16:
            opkind             = ZEXT;
            opkind_const_param = 16;
            break;
        case ZEXT_32:
            opkind             = ZEXT;
            opkind_const_param = 32;
            break;
        case SEXT_8:
            opkind             = SEXT;
            opkind_const_param = 8;
            break;
        case SEXT_16:
            opkind             = SEXT;
            opkind_const_param = 16;
            break;
        case SEXT_32:
            opkind             = SEXT;
            opkind_const_param = 32;
            break;
        default:
            tcg_abort();
    }

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    TCGTemp* t_const_param = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_const_param, opkind_const_param, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_const_param, offsetof(Expr, op2), 0, 1, sizeof(Expr*),
                op_in, NULL, tcg_ctx);

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    // add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    tcg_set_label(label_op_is_const, op_in, NULL, tcg_ctx);

    // overide t_op_to expr
    TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void mark_temp_as_in_use(TCGTemp* t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 1;
}

static inline void mark_temp_as_free(TCGTemp* t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 0;
}

static inline OPKIND get_opkind(TCGOpcode opc)
{
    switch (opc) {
        case INDEX_op_add_i64:;
            return ADD;
        case INDEX_op_sub_i64:
            return SUB;
        case INDEX_op_mul_i64:
            return MUL;
        case INDEX_op_div_i64:
            return DIV;
        case INDEX_op_divu_i64:
            return DIVU;
        case INDEX_op_rem_i64:
            return REM;
        case INDEX_op_remu_i64:
            return REMU;
        case INDEX_op_and_i64:
            return AND;
        case INDEX_op_or_i64:
            return OR;
        case INDEX_op_xor_i64:
            return XOR;
        case INDEX_op_shl_i64:
            return SHL;
        case INDEX_op_shr_i64:
            return SHR;
        case INDEX_op_sar_i64:
            return SAR;
        case INDEX_op_rotl_i64:
            return ROTL;
        case INDEX_op_rotr_i64:
            return ROTR;
        case INDEX_op_ctz_i64:
            return CTZ;
        default:
            tcg_abort();
    }
}

static inline OPKIND get_opkind_from_cond(TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();

        case TCG_COND_EQ:
            return EQ;
        case TCG_COND_NE:
            return NE;

        case TCG_COND_LT:
            return LT;
        case TCG_COND_LE:
            return LE;
        case TCG_COND_GE:
            return GE;
        case TCG_COND_GT:
            return GT;

        case TCG_COND_LTU:
            return LTU;
        case TCG_COND_LEU:
            return LEU;
        case TCG_COND_GEU:
            return GEU;
        case TCG_COND_GTU:
            return GTU;

        default:
            tcg_abort();
    }
}

static inline OPKIND get_opkind_from_neg_cond(TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();

        case TCG_COND_EQ:
            return NE;
        case TCG_COND_NE:
            return EQ;

        case TCG_COND_LT:
            return GE;
        case TCG_COND_LE:
            return GT;
        case TCG_COND_GE:
            return LT;
        case TCG_COND_GT:
            return LE;

        case TCG_COND_LTU:
            return GEU;
        case TCG_COND_LEU:
            return GTU;
        case TCG_COND_GEU:
            return LTU;
        case TCG_COND_GTU:
            return LEU;

        default:
            tcg_abort();
    }
}

static inline void print_pi(void)
{
    if (!path_constraints)
        printf("\nPath constraints: true\n\n");
    else {
        printf("\nPath constraints:\n");
        print_expr(path_constraints);
        printf("\n");
    }
}

static TCGCond check_branch_cond_helper(uintptr_t a, uintptr_t b, TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();
        //
        case TCG_COND_EQ:
            if (a == b)
                return TCG_COND_EQ;
            else
                return TCG_COND_NE;
        case TCG_COND_NE:
            if (a != b)
                return TCG_COND_NE;
            else
                return TCG_COND_EQ;
        //
        case TCG_COND_LTU:
            if (a < b)
                return TCG_COND_LTU;
            else
                return TCG_COND_GEU;
        case TCG_COND_LEU:
            if (a <= b)
                return TCG_COND_LEU;
            else
                return TCG_COND_GTU;
        case TCG_COND_GEU:
            if (a > b)
                return TCG_COND_GTU;
            else
                return TCG_COND_LEU;
        case TCG_COND_GTU:
            if (a >= b)
                return TCG_COND_GEU;
            else
                return TCG_COND_LTU;
        //
        default:
            tcg_abort();
    }
}

static void setcond_helper(uintptr_t a, uintptr_t b, uintptr_t cond,
                           uintptr_t out_idx, uintptr_t a_idx, uintptr_t b_idx)
{
    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_idx] = NULL;
        return; // early exit
    }

    Expr* setcond_expr   = new_expr();
    setcond_expr->opkind = get_opkind_from_cond(cond);

    if (expr_a)
        setcond_expr->op1 = expr_a;
    else {
        setcond_expr->op1          = (Expr*)(uintptr_t)a;
        setcond_expr->op1_is_const = 1;
    }

    if (expr_b)
        setcond_expr->op2 = expr_b;
    else {
        setcond_expr->op2          = (Expr*)(uintptr_t)b;
        setcond_expr->op2_is_const = 1;
    }

    s_temps[out_idx] = setcond_expr;
}

static void branch_helper(uintptr_t a, uintptr_t b, uintptr_t cond,
                          uintptr_t a_idx, uintptr_t b_idx, uintptr_t pc)
{
    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL)
        return; // early exit

#if 0
    printf("Branch at %lx: %lu %s %lu\n", pc, a_idx, opkind_to_str(get_opkind_from_cond(cond)), b_idx);
    print_temp(a_idx);
    print_temp(b_idx);
#endif

    Expr* branch_expr = new_expr();

    TCGCond sat_cond    = check_branch_cond_helper(a, b, cond);
    branch_expr->opkind = get_opkind_from_cond(sat_cond);

    if (expr_a)
        branch_expr->op1 = expr_a;
    else {
        branch_expr->op1          = (Expr*)(uintptr_t)a;
        branch_expr->op1_is_const = 1;
    }

    if (expr_b)
        branch_expr->op2 = expr_b;
    else {
        branch_expr->op2          = (Expr*)(uintptr_t)b;
        branch_expr->op2_is_const = 1;
    }

    Expr* old_pi = NULL;
    if (path_constraints == NULL) {
        path_constraints = branch_expr;
    } else {
        old_pi              = path_constraints;
        Expr* new_pi_expr   = new_expr();
        new_pi_expr->opkind = AND;
        new_pi_expr->op1    = branch_expr;
        new_pi_expr->op2    = old_pi;
        path_constraints    = new_pi_expr;
    }
#ifdef SYMBOLIC_DEBUG
    printf("Branch at %lx\n", pc);
    print_pi();
#endif

    // Invert branch and submit query

    Expr* branch_neg_expr   = new_expr();
    branch_neg_expr->opkind = get_opkind_from_neg_cond(sat_cond);

    if (expr_a)
        branch_neg_expr->op1 = expr_a;
    else {
        branch_neg_expr->op1          = (Expr*)(uintptr_t)a;
        branch_neg_expr->op1_is_const = 1;
    }

    if (expr_b)
        branch_neg_expr->op2 = expr_b;
    else {
        branch_neg_expr->op2          = (Expr*)(uintptr_t)b;
        branch_neg_expr->op2_is_const = 1;
    }

    Expr* query = branch_neg_expr;
    if (old_pi) {
        query         = new_expr();
        query->opkind = AND;
        query->op1    = branch_neg_expr;
        query->op2    = old_pi;
    }
    assert(*next_query == 0);

#if 0
    return;
#endif

    *next_query = query;
    assert(*next_query != 0);
    next_query++;
    assert(*next_query == 0);
    assert(next_query < queue_query + EXPR_POOL_CAPACITY);
    // printf("Query submitted to solver\n");
}

static inline void branch(TCGTemp* t_op_a, TCGTemp* t_op_b, TCGCond cond,
                          TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // check if both t_op_a and t_op_b are concrete
    // if this is true, skip any further work

    size_t op_a_idx = temp_idx(t_op_a);
    size_t op_b_idx = temp_idx(t_op_b);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[op_b_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);
    tcg_temp_free_internal(t_a_or_b);

#if 0
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // one of them is symbolic, build the expression

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    // set expr opkind
    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    OPKIND   opkind   = get_opkind_from_cond(cond);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    OPKIND   opkind_neg   = get_opkind_from_neg_cond(cond);
    TCGTemp* t_opkind_neg = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind_neg, opkind_neg, 0, op_in, NULL, tcg_ctx);
    TCGTemp* t_opkind_actual = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_cmov(t_opkind_actual, t_op_a, t_op_b, t_opkind, t_opkind_neg, cond, 0,
             0, 0, 1, 1, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);
    tcg_store_n(t_out, t_opkind_actual, offsetof(Expr, opkind), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_a);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel* label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in,
               NULL, tcg_ctx);
    tcg_temp_free_internal(t_zero);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_one);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_b);

#if 0
    tcg_print_const_str("Branch cond expr", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_print_const_str("Branch cond DONE", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // build the new expr for path_constraints: t_out AND path_constraints

    TCGTemp* t_new_pi_expr = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(
        t_new_pi_expr, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, AND, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    TCGTemp* t_pi_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_pi_addr, (uintptr_t)&path_constraints, 0, op_in, NULL, tcg_ctx);

    tcg_store_n(t_new_pi_expr, t_out, offsetof(Expr, op1), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_out);

    TCGTemp* t_old_pi_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_pi_addr, t_old_pi_expr, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_old_pi_expr, offsetof(Expr, op2), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_old_pi_expr);

    tcg_store_n(t_pi_addr, t_new_pi_expr, 0, 1, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_new_pi_expr);
    tcg_temp_free_internal(t_pi_addr);

#ifdef SYMBOLIC_DEBUG
    TCGOp* op;
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline TCGTemp* tcg_find_temp_arch_reg(TCGContext* tcg_ctx,
                                              const char* reg_name)
{
    for (int i = 0; i < TCG_TARGET_NB_REGS; i++) {
        TCGTemp* t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0)
            return t;
    }
    tcg_abort();
}

// ToDo: support other archs/platforms
#define SYSCALL_NR_READ 0
#define FD_STDIN        0
static uintptr_t   symbolic_input_next_id = 0;
static inline void qemu_syscall_helper(uintptr_t syscall_no,
                                       uintptr_t syscall_arg0,
                                       uintptr_t syscall_arg1,
                                       uintptr_t syscall_arg2)
{
    if (syscall_no != SYSCALL_NR_READ)
        return;
    if (syscall_arg0 != FD_STDIN)
        return;

    uintptr_t addr = syscall_arg1;
    uintptr_t size = syscall_arg2;
    printf("Marking as symbolic %lu bytes at 0x%lx during read from stdin\n",
           size, addr);

    // expression for the entire input
    Expr* e_input   = new_expr();
    e_input->opkind = IS_SYMBOLIC;
    e_input->op1    = (Expr*)symbolic_input_next_id++; // ID
    e_input->op2    = (Expr*)size;                     // number of bytes

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) {
        l2_page                             = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t  l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t* l3_page     = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) {
        l3_page                       = g_malloc0(sizeof(l3_page_t));
        l2_page->entries[l2_page_idx] = l3_page;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    for (size_t i = 0; i < size; i++) {
        Expr* e                                        = new_expr();
        e->opkind                                      = EXTRACT8;
        e->op1                                         = e_input;
        e->op2                                         = (Expr*)i;
        l3_page->entries[l3_page_idx + (size - i - 1)] = e;
    }
}

#if 0
static inline void qemu_movcond_store_helper(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, TCGTemp* t_op_true,
                                TCGTemp* t_op_false, TCGCond cond, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{

}
#endif

static inline void qemu_movcond(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, TCGTemp* t_op_true,
                                TCGTemp* t_op_false, TCGCond cond, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // tcg_print_const_str("Doing a movcond", op_in, NULL, tcg_ctx);

    branch(t_op_a, t_op_b, cond, op_in, tcg_ctx);

    size_t op_out_idx   = temp_idx(t_op_out);
    size_t op_true_idx  = temp_idx(t_op_true);
    size_t op_false_idx = temp_idx(t_op_false);

    TCGTemp* t_true = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_true, (uintptr_t)&s_temps[op_true_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_true, t_true, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_false = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_false, (uintptr_t)&s_temps[op_false_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_load_n(t_false, t_false, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_cmov(t_out, t_op_a, t_op_b, t_true, t_false, cond, 0, 0, 0, 1, 1, op_in,
             NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    TCGTemp* t_out_addr = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_out_addr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_addr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline EXTENDKIND get_extend_kind(TCGOpcode opkind)
{
    switch (opkind) {
        case INDEX_op_ext8u_i64:
            return ZEXT_8;
        case INDEX_op_ext8s_i64:
            return SEXT_8;

        case INDEX_op_ext16u_i64:
            return ZEXT_16;
        case INDEX_op_ext16s_i64:
            return SEXT_16;

        case INDEX_op_ext32u_i64:
        case INDEX_op_extu_i32_i64:
            return ZEXT_32;
        case INDEX_op_ext32s_i64:
            return SEXT_32;

        default:
            tcg_abort();
    }
}

static void register_helpers(void)
{
    g_hash_table_insert(helper_table, (gpointer)print_reg,
                        (gpointer)&helper_info_print_reg);
}

#include "symbolic-i386.c"

static int instrument = 0;
static int first_load = 0;
int        parse_translation_block(TranslationBlock* tb, uintptr_t tb_pc,
                                   uint8_t* tb_code, TCGContext* tcg_ctx)
{
    internal_tcg_context  = tcg_ctx;
    int force_flush_cache = 0;

    register_helpers();

    TCGOp __attribute__((unused)) * op;
    uintptr_t pc = 0;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        switch (op->opc) {

            case INDEX_op_insn_start:
                pc = op->args[0];
                if (instrument == 0 &&
                    pc == s_config.symbolic_exec_start_addr) {
                    // ToDo: we could start instrumenting when we inject
                    //       for the first time a symbolic data?
                    instrument        = 1;
                    force_flush_cache = 1;
                } else if (instrument == 1 &&
                           pc == s_config.symbolic_exec_stop_addr) {
                    instrument        = 0;
                    *next_query       = FINAL_QUERY;
                    force_flush_cache = 1;
                }

                if (instrument) {
                    debug_printf("Instrumenting %lx\n", op->args[0]);
                    if (pc == s_config.symbolic_exec_reg_instr_addr)
                        make_reg_symbolic(s_config.symbolic_exec_reg_name, op,
                                          tcg_ctx);
                }
                break;

            case INDEX_op_set_label:
                break;

            // moving a constant into a temp does not create symbolic exprs
            case INDEX_op_movi_i64:
            case INDEX_op_movi_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                if (instrument) {
                    TCGTemp* t = arg_temp(op->args[0]);
#if 1
                    clear_temp(temp_idx(t), op, tcg_ctx);
#else
                    TCGTemp* t_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_idx, (uintptr_t)temp_idx(t), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_idx);
#endif
                }
                break;

            // we always move exprs between temps, avoiding any check on the
            // source ToDo: branchless but more expensive?
            case INDEX_op_mov_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* from = arg_temp(op->args[1]);
                    TCGTemp* to   = arg_temp(op->args[0]);
#if 1
                    move_temp(temp_idx(from), temp_idx(to), op, tcg_ctx);
#else
                    TCGTemp* t_to_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_to_idx, (uintptr_t)temp_idx(to), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_from_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_from_idx, (uintptr_t)temp_idx(from), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_2(move_temp_helper, t_from_idx, t_to_idx, op,
                                    NULL, tcg_ctx);
                    tcg_temp_free_internal(t_to_idx);
                    tcg_temp_free_internal(t_from_idx);
#endif
                }
                break;

            case INDEX_op_add_i64:
            case INDEX_op_sub_i64:
            case INDEX_op_mul_i64:
            case INDEX_op_div_i64:
            case INDEX_op_divu_i64:
            case INDEX_op_rem_i64:
            case INDEX_op_remu_i64:
            case INDEX_op_and_i64:
            case INDEX_op_or_i64:
            case INDEX_op_xor_i64:
            case INDEX_op_shl_i64:
            case INDEX_op_shr_i64:
            case INDEX_op_sar_i64:
            case INDEX_op_rotl_i64:
            case INDEX_op_rotr_i64:
            case INDEX_op_ctz_i64:;

                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    OPKIND   bin_opkind = get_opkind(op->opc);
                    TCGTemp* t_out      = arg_temp(op->args[0]);
                    TCGTemp* t_a        = arg_temp(op->args[1]);
                    TCGTemp* t_b        = arg_temp(op->args[2]);
#if 1
                    qemu_binop(bin_opkind, t_out, t_a, t_b, op, tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)bin_opkind, 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_out_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_out_idx, (uintptr_t)temp_idx(t_out), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_b_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_b_idx, (uintptr_t)temp_idx(t_b), 0, op, NULL,
                             tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(qemu_binop_helper, t_opkind, t_out_idx,
                                    t_a_idx, t_b_idx, t_a, t_b, op, NULL,
                                    tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_out_idx);
                    tcg_temp_free_internal(t_a_idx);
                    tcg_temp_free_internal(t_b_idx);
#endif
                }
                break;

            case INDEX_op_discard:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                if (instrument) {
                    TCGTemp* t = arg_temp(op->args[0]);
#if 1
                    clear_temp(temp_idx(t), op, tcg_ctx);
#else
                    TCGTemp* t_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_idx, (uintptr_t)temp_idx(t), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_idx);
#endif
                }
                break;

            case INDEX_op_qemu_ld_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_val = arg_temp(op->args[0]);
                    TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 0
                    TCGMemOp  mem_op = get_memop(op->args[2]);
                    uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                    qemu_load(t_ptr, t_val, offset, mem_op, op,
                              tcg_ctx); // bugged
#else
                    MARK_TEMP_AS_ALLOCATED(t_ptr);
                    TCGTemp* t_mem_op = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_mem_op,
                             make_mem_op_offset(get_memop(op->args[2]),
                                                get_mmuidx(op->args[2])),
                             0, op, NULL, tcg_ctx);
                    TCGTemp* t_ptr_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_val_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_4(qemu_load_helper, t_ptr, t_mem_op,
                                    t_ptr_idx, t_val_idx, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                    tcg_temp_free_internal(t_mem_op);
                    tcg_temp_free_internal(t_ptr_idx);
                    tcg_temp_free_internal(t_val_idx);
#endif

                    first_load = 1;
                }
                break;

            case INDEX_op_qemu_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_val = arg_temp(op->args[0]);
                    TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 1
                    TCGMemOp  mem_op = get_memop(op->args[2]);
                    uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                    qemu_store(t_ptr, t_val, offset, mem_op, op, tcg_ctx);
#else
                    MARK_TEMP_AS_ALLOCATED(t_ptr);
                    TCGTemp* t_mem_op = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_mem_op,
                             make_mem_op_offset(get_memop(op->args[2]),
                                                get_mmuidx(op->args[2])),
                             0, op, NULL, tcg_ctx);
                    TCGTemp* t_ptr_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_val_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_4(qemu_store_helper, t_ptr, t_mem_op,
                                    t_ptr_idx, t_val_idx, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                    tcg_temp_free_internal(t_mem_op);
                    tcg_temp_free_internal(t_ptr_idx);
                    tcg_temp_free_internal(t_val_idx);
#endif
                }
                break;

            case INDEX_op_ld_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument && 0) {
                    uintptr_t offset = (uintptr_t)op->args[2];
                    if (is_xmm_offset(offset)) {
                        // printf("load to xmm data (offset=%lu)\n", offset);
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_mem_op, make_mem_op_offset(MO_LEQ, offset),
                                 0, op, NULL, tcg_ctx);
                        TCGTemp* t_ptr_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op,
                                 NULL, tcg_ctx);
                        TCGTemp* t_val_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op,
                                 NULL, tcg_ctx);
                        add_void_call_4(qemu_load_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                        tcg_temp_free_internal(t_mem_op);
                        tcg_temp_free_internal(t_ptr_idx);
                        tcg_temp_free_internal(t_val_idx);
                    }
                }
                break;

            case INDEX_op_st32_i64:
            case INDEX_op_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    uintptr_t offset = (uintptr_t)op->args[2];
                    if (is_xmm_offset(offset)) {
                        // printf("store to xmm data (offset=%lu)\n", offset);
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        if (op->opc == INDEX_op_st_i64) {
                            tcg_movi(t_mem_op,
                                     make_mem_op_offset(MO_LEQ, offset), 0, op,
                                     NULL, tcg_ctx);
                        } else {
                            tcg_movi(t_mem_op,
                                     make_mem_op_offset(MO_LEUL, offset), 0, op,
                                     NULL, tcg_ctx);
                        }
                        TCGTemp* t_ptr_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op,
                                 NULL, tcg_ctx);
                        TCGTemp* t_val_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op,
                                 NULL, tcg_ctx);
                        add_void_call_4(qemu_store_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                        tcg_temp_free_internal(t_mem_op);
                        tcg_temp_free_internal(t_ptr_idx);
                        tcg_temp_free_internal(t_val_idx);
                    }
                }
                break;

            case INDEX_op_setcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
                    TCGTemp* t_b   = arg_temp(op->args[2]);
                    TCGCond  cond  = op->args[3];
#if 0
                    // ToDo
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_b_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_b_idx, (uintptr_t)temp_idx(t_b), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_out_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_out_idx, (uintptr_t)temp_idx(t_out), 0, op, NULL,
                             tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(setcond_helper, t_a, t_b, t_cond, t_out_idx,
                                    t_a_idx, t_b_idx, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_a_idx);
                    tcg_temp_free_internal(t_b_idx);
                    tcg_temp_free_internal(t_out_idx);
#endif
                }
                break;

            case INDEX_op_brcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_a  = arg_temp(op->args[0]);
                    TCGTemp* t_b  = arg_temp(op->args[1]);
                    TCGCond  cond = op->args[2];
#if 0
                    branch(t_a, t_b, cond, op, tcg_ctx);
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_b_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_b_idx, (uintptr_t)temp_idx(t_b), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(branch_helper, t_a, t_b, t_cond, t_a_idx,
                                    t_b_idx, t_pc, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_a_idx);
                    tcg_temp_free_internal(t_b_idx);
                    tcg_temp_free_internal(t_pc);
#endif
                }
                break;

            case INDEX_op_ext8u_i64:
            case INDEX_op_ext8s_i64:
            case INDEX_op_ext16u_i64:
            case INDEX_op_ext16s_i64:
            case INDEX_op_ext32u_i64:
            case INDEX_op_ext32s_i64:
            case INDEX_op_extu_i32_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_to   = arg_temp(op->args[0]);
                    TCGTemp* t_from = arg_temp(op->args[1]);
                    extend(t_to, t_from, get_extend_kind(op->opc), op, tcg_ctx);
                }
                break;

            case INDEX_op_goto_ptr:
            case INDEX_op_goto_tb:
            case INDEX_op_exit_tb:
            case INDEX_op_brcond_i32: // skip when emulating 64 bit?
                break;

            case INDEX_op_call:
                for (size_t i = 0; i < TCGOP_CALLO(op); i++)
                    mark_temp_as_in_use(arg_temp(op->args[i]));
                for (size_t i = 0; i < TCGOP_CALLI(op); i++)
                    mark_temp_as_in_use(
                        arg_temp(op->args[TCGOP_CALLO(op) + i]));
                if (instrument) {
                    const char* helper_name = tcg_find_helper(
                        tcg_ctx, op->args[TCGOP_CALLI(op) + TCGOP_CALLO(op)]);
                    if (strcmp(helper_name, "syscall") == 0) {
#if 0
                        printf("Syscall\n");
                        // ToDo: inline instrumentation
#else
                        // ToDo: support other archs/platforms
                        // ToDo: reg temps could be located once for all in the
                        // init phase... ToDo: rax should be an immediate, we
                        // should check it and
                        //       only instrument the syscalls that we care for
                        TCGTemp* t_syscall_no =
                            tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        TCGTemp* t_syscall_arg0 =
                            tcg_find_temp_arch_reg(tcg_ctx, "rdi");
                        TCGTemp* t_syscall_arg1 =
                            tcg_find_temp_arch_reg(tcg_ctx, "rsi");
                        TCGTemp* t_syscall_arg2 =
                            tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                        MARK_TEMP_AS_ALLOCATED(t_syscall_no);
                        MARK_TEMP_AS_ALLOCATED(t_syscall_arg0);
                        MARK_TEMP_AS_ALLOCATED(t_syscall_arg1);
                        MARK_TEMP_AS_ALLOCATED(t_syscall_arg2);
                        // ToDo: should mark bytes after the call
                        add_void_call_4(qemu_syscall_helper, t_syscall_no,
                                        t_syscall_arg0, t_syscall_arg1,
                                        t_syscall_arg2, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_syscall_no);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_syscall_arg0);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_syscall_arg1);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_syscall_arg2);
#endif
                    } else if (strcmp(helper_name, "cc_compute_all") == 0) {

                        // if you allocate it after MARK_TEMP_AS_ALLOCATED(...)
                        // it mark as not allocated the temps "..."
                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);

                        TCGTemp* t_ret = arg_temp(op->args[0]);

                        TCGTemp* t_dst = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_dst);

                        TCGTemp* t_src1 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src1);

                        TCGTemp* t_src2 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_src2);

                        TCGTemp* t_ccop = arg_temp(op->args[4]); // cc_op
                        MARK_TEMP_AS_ALLOCATED(t_ccop);

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_ret));
                        v          = PACK_1(v, temp_idx(t_dst));
                        v          = PACK_2(v, temp_idx(t_src1));
                        v          = PACK_3(v, temp_idx(t_src2));

                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_5(qemu_cc_compute_all, t_packed_idx,
                                        t_dst, t_src1, t_src2, t_ccop, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_ccop);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src1);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src2);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "cc_compute_c") == 0) {

                        // if you allocate it after MARK_TEMP_AS_ALLOCATED(...)
                        // it mark as not allocated the temps "..."
                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);

                        TCGTemp* t_ret = arg_temp(op->args[0]);

                        TCGTemp* t_dst = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_dst);

                        TCGTemp* t_src1 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src1);

                        TCGTemp* t_src2 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_src2);

                        TCGTemp* t_ccop = arg_temp(op->args[4]); // cc_op
                        MARK_TEMP_AS_ALLOCATED(t_ccop);

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_ret));
                        v          = PACK_1(v, temp_idx(t_dst));
                        v          = PACK_2(v, temp_idx(t_src1));
                        v          = PACK_3(v, temp_idx(t_src2));

                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_5(qemu_cc_compute_c, t_packed_idx, t_dst,
                                        t_src1, t_src2, t_ccop, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_ccop);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src1);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src2);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "rclq") == 0) {

                        TCGTemp* t_out = arg_temp(op->args[0]);

                        TCGTemp* t_env = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);

                        TCGTemp* t_0 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_0);

                        TCGTemp* t_1 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_1);

                        TCGTemp* t_ccsrc =
                            tcg_find_temp_arch_reg(tcg_ctx, "cc_src");

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_out));
                        v          = PACK_1(v, temp_idx(t_0));
                        v          = PACK_2(v, temp_idx(t_1));
                        v          = PACK_3(v, temp_idx(t_ccsrc));

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_4(qemu_rcl, t_packed_idx, t_env, t_0, t_1,
                                        op, NULL, tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_0);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_1);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "pxor_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)XOR, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_op_bytewise, t_opkind,
                                        t_dst_addr, t_src_addr, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else if (strcmp(helper_name, "por_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)OR, 0, op, NULL, tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_op_bytewise, t_opkind,
                                        t_dst_addr, t_src_addr, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else if (strcmp(helper_name, "psubb_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)SUB, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_op_bytewise, t_opkind,
                                        t_dst_addr, t_src_addr, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else if (strcmp(helper_name, "pcmpeqb_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)CMPB, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_op_bytewise, t_opkind,
                                        t_dst_addr, t_src_addr, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else if (strcmp(helper_name, "pmovmskb_xmm") == 0) {

                        TCGTemp* t_dst_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_dst_idx,
                                 (uintptr_t)temp_idx(arg_temp(op->args[0])), 0,
                                 op, NULL, tcg_ctx);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_2(qemu_xmm_pmovmskb, t_dst_idx,
                                        t_src_addr, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_dst_idx);

                    } else if (strcmp(helper_name, "pslldq_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)SHL, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_shift, t_opkind, t_dst_addr,
                                        t_src_addr, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else if (strcmp(helper_name, "psrldq_xmm") == 0) {

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)SHR, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_shift, t_opkind, t_dst_addr,
                                        t_src_addr, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);

                    } else {

                        const char* helper_whitelist[] = {
                            "lookup_tb_ptr", "rechecking_single_step"};

                        int helper_is_whitelisted = 0;
                        for (size_t i = 0;
                             i < sizeof(helper_whitelist) / sizeof(char*);
                             i++) {
                            if (strcmp(helper_whitelist[i], helper_name) == 0)
                                helper_is_whitelisted = 1;
                        }

                        if (!helper_is_whitelisted)
                            printf("Helper %s is not instrumented\n",
                                   helper_name);
                    }
                }
                break;

            case INDEX_op_movcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out   = arg_temp(op->args[0]);
                    TCGTemp* t_a     = arg_temp(op->args[1]);
                    TCGTemp* t_b     = arg_temp(op->args[2]);
                    TCGTemp* t_true  = arg_temp(op->args[3]);
                    TCGTemp* t_false = arg_temp(op->args[4]);
                    TCGCond  cond    = op->args[5];
                    qemu_movcond(t_out, t_a, t_b, t_true, t_false, cond, op,
                                 tcg_ctx);
                }
                break;

            case INDEX_op_neg_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
#if 1
                    qemu_unop(NEG, t_out, t_a, op, tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)NEG, 0, op, NULL, tcg_ctx);
                    TCGTemp* t_out_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_out_idx, (uintptr_t)temp_idx(t_out), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    add_void_call_4(qemu_unop_helper, t_opkind, t_out_idx,
                                    t_a_idx, t_a, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_out_idx);
                    tcg_temp_free_internal(t_a_idx);
#endif
                }
                break;
#if 0
            // ToDo
            case INDEX_op_extract_i64:
            case INDEX_op_deposit_i64:
            case INDEX_op_setcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                // mark_temp_as_in_use(arg_temp(op->args[1]));
                // mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    TCGTemp* t = arg_temp(op->args[0]);
#if 0
                    clear_temp(temp_idx(t), op, tcg_ctx);
#else
                    TCGTemp* t_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_idx, (uintptr_t)temp_idx(t), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_idx);
#endif
                }
                break;
#endif

            case INDEX_op_ld_i32:
                break; // ToDo: not interesting only when at 64 bit

            default:
                if (instrument) {
                    const TCGOpDef* def __attribute__((unused)) =
                        &tcg_op_defs[op->opc];
                    debug_printf("Unhandled TCG instruction: %s\n", def->name);
                }
        }

        // mark as free any temp that was dead at this instruction
        unsigned life = op->life;
        life /= DEAD_ARG;
        if (life) {
            for (int i = 0; life; ++i, life >>= 1)
                if (life & 1)
                    mark_temp_as_free(arg_temp(op->args[i]));
        }
    }

    return force_flush_cache;
}