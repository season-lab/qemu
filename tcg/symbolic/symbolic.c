#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "qemu/bitops.h"

#include "symbolic-struct.h"
#include "symbolic.h"
#include "config.h"

//#define SYMBOLIC_DEBUG
//#define DISABLE_SOLVER

#define QUEUE_OP_MAX_SIZE 128
size_t        op_to_add_size               = 0;
TCGOp*        op_to_add[QUEUE_OP_MAX_SIZE] = {0};
extern TCGOp* tcg_op_alloc(TCGOpcode opc);
extern TCGOp* tcg_op_insert_before_op(TCGContext* s, TCGOp* op, TCGOp* new_op);

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
Query* queue_query = NULL;
Query* next_query  = NULL;

TCGContext* internal_tcg_context = NULL;

// from tcg.c
typedef struct TCGHelperInfo {
    void*       func;
    const char* name;
    unsigned    flags;
    unsigned    sizemask;
} TCGHelperInfo;

// Pattern:
//      movq    0xBASE(, %REG, 8), %REG
//      jmpq    *%rax
//
typedef struct {
    TCGTemp*  index;
    TCGTemp*  addr;
    TCGTemp*  mov;
    uint8_t   scale_is_addr_size;
    uintptr_t displacement;
    uint8_t   has_done_load;
    uint8_t   need_to_free_addr;
} JumpTableFinder;

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
        else if (strcmp(var, "REG") == 0)
            s_config.symbolic_inject_input_mode = REG;
        else if (strcmp(var, "BUFFER") == 0)
            s_config.symbolic_inject_input_mode = BUFFER;
        else if (strcmp(var, "FROM_FILE") == 0) {
            s_config.symbolic_inject_input_mode = FROM_FILE;
            s_config.inputfile = getenv("SYMBOLIC_TESTCASE_NAME");
            assert(s_config.inputfile && "Neet to specify testcase path.");
        }
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

static InstrumentationMode instrumentation_mode = INSTRUMENT_BEFORE;
static inline void         set_instrumentation_mode(InstrumentationMode mode)
{
    instrumentation_mode = mode;
}

void init_symbolic_mode(void)
{
#ifndef DISABLE_SOLVER
    int expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                                  sizeof(Expr) * EXPR_POOL_CAPACITY, 0666);

    assert(expr_pool_shm_id > 0);

    int query_shm_id = shmget(QUERY_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Query) * EXPR_QUERY_CAPACITY, 0666);
    assert(query_shm_id > 0);

    // printf("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);

    pool = shmat(expr_pool_shm_id, EXPR_POOL_ADDR, 0);
    assert(pool);

    queue_query = shmat(query_shm_id, NULL, 0);
    assert(queue_query);

#else
    pool        = g_malloc0(sizeof(Expr) * EXPR_POOL_CAPACITY);
    queue_query = g_malloc0(sizeof(Query) * EXPR_QUERY_CAPACITY);

    printf("TRACER in NO SOLVER mode\n");
#endif

    // printf("POOL_ADDR=%p\n", pool);

#if 0
    for (size_t i = 0; i < EXPR_POOL_CAPACITY; i++)
        assert(*(queue_query + i) == 0);
#endif

    next_free_expr = pool;
    next_query     = queue_query;

#ifndef DISABLE_SOLVER
    struct timespec polling_time;
    polling_time.tv_sec  = 0;
    polling_time.tv_nsec = 10;
    while (next_query[0].query != (void*)SHM_READY) {
        nanosleep(&polling_time, NULL);
    }
#endif
    next_query++;

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
    TCGOpcode opc = INDEX_op_call;
    TCGOp*    op  = instrumentation_mode == INSTRUMENT_BEFORE
                    ? tcg_op_insert_before(tcg_ctx, op_in, opc)
                    : tcg_op_alloc(opc);
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

    if (instrumentation_mode == INSTRUMENT_AFTER) {
        op_to_add[op_to_add_size++] = op;
    }
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
    TCGOp*    op  = instrumentation_mode == INSTRUMENT_BEFORE
                    ? tcg_op_insert_before(tcg_ctx, op_in, opc)
                    : tcg_op_alloc(opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    if (op_out)
        *op_out = op;

    if (instrumentation_mode == INSTRUMENT_AFTER) {
        op_to_add[op_to_add_size++] = op;
    }
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

static inline void print_something(char* str) { printf("%s\n", str); }
DEF_HELPER_INFO(print_something);

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

static inline void move_temp_size_helper(size_t from, size_t to, size_t size)
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

    Expr* from_expr = s_temps[from];
    if (from_expr && size < sizeof(uintptr_t)) {
        Expr* e   = new_expr();
        e->opkind = EXTRACT;
        e->op1    = from_expr;
        SET_EXPR_CONST_OP(e->op2, e->op2_is_const, (size * 8) - 1);
        SET_EXPR_CONST_OP(e->op3, e->op3_is_const, 0);
        from_expr = e;
    }

    s_temps[to] = from_expr;
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

static inline void move_temp(size_t from, size_t to, size_t size, TCGOp* op_in,
                             TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp* t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    if (size != 0 && size < sizeof(uintptr_t)) {

        TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

        TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

        tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

        TCGLabel* label_a_concrete = gen_new_label();
        tcg_brcond(label_a_concrete, t_from, t_zero, TCG_COND_EQ, 0, 0, op_in,
                   NULL, tcg_ctx);

        allocate_new_expr(
            t_out, op_in,
            tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

        TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_opkind, EXTRACT, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_from, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t),
                    op_in, NULL, tcg_ctx);

        TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

        TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_size, (size * 8) - 1, 0, op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_size, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t),
                    op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 0,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_zero, offsetof(Expr, op3), 0, 1, sizeof(uintptr_t),
                    op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_one, offsetof(Expr, op3_is_const), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

        TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_to, t_out, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);

    } else {
        TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_to, t_from, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);
    }

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

static inline void qemu_binop_helper(uintptr_t opkind, uintptr_t packed_idx,
                                     uintptr_t a, uintptr_t b)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t b_idx   = UNPACK_2(packed_idx);
    uintptr_t size   = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_idx] = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_expr   = new_expr();
    binop_expr->opkind = (OPKIND)opkind;

    if (expr_a)
        binop_expr->op1 = expr_a;
    else {
        binop_expr->op1          = (Expr*)(uintptr_t)a;
        binop_expr->op1_is_const = 1;
    }

    if (expr_b)
        binop_expr->op2 = expr_b;
    else {
        binop_expr->op2          = (Expr*)(uintptr_t)b;
        binop_expr->op2_is_const = 1;
    }

    if (size != 0 && size < sizeof(uintptr_t)) {
        binop_expr->op3          = (Expr*)(uintptr_t)size;
        binop_expr->op3_is_const = 1;
    }

    s_temps[out_idx] = binop_expr;
}

// Binary operation: t_out = t_a opkind t_b
static inline void qemu_binop(OPKIND opkind, TCGTemp* t_op_out, TCGTemp* t_op_a,
                              TCGTemp* t_op_b, size_t size, TCGOp* op_in,
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

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    if (size != 0 && size < sizeof(uintptr_t)) {

        TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_size, size, 0, op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_size, offsetof(Expr, op3), 0, 1, sizeof(uintptr_t),
                    op_in, NULL, tcg_ctx);

        tcg_store_n(t_out, t_one, offsetof(Expr, op3_is_const), 0, 0,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);
    }

    // if t_a is concrete, then store its concrete value into t_out expr

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

    Expr* unop_expr    = new_expr();
    unop_expr->opkind  = (OPKIND)opkind;
    unop_expr->op1     = expr_a;
    s_temps[t_out_idx] = unop_expr;

    if (opkind == NOT) {
        print_expr(unop_expr);
    }
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

static inline void qemu_pc_write_helper(uintptr_t value)
{
    printf("Jumping to %lx\n", value);
}

static inline void qemu_pc_write(TCGTemp* t_op_a, TCGOp* op_in,
                                 TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t a = temp_idx(t_op_a);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr(t_out, op_in, tcg_ctx);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, SYMBOLIC_PC, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    TCGOp* op;
    tcg_print_const_str("\nSymbolic PC\n", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_out);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_jump_table(TCGTemp* t_addr, TCGOp* op_in,
                                   TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t a = temp_idx(t_addr);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    TCGOp* op;
    tcg_print_const_str("\nSymbolic jump table\n", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr(t_out, op_in, tcg_ctx);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, SYMBOLIC_JUMP_TABLE_ACCESS, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_store_n(t_out, t_addr, offsetof(Expr, op2), 0, 0, sizeof(uintptr_t),
                op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    // add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    tcg_temp_free_internal(t_out);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

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
    size_t    size = get_mem_op_size(mem_op);
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
    if (orig_addr > 0x61f490 && orig_addr < 0x61f490 + 256) {
        printf("Loading %lu bytes: t[%ld] = *(0x%p + %lu)\n", size, val_idx,
               (void*)orig_addr, offset);
    }
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

#if 0
    // 
    if (orig_addr > 0x61f490 && orig_addr < 0x61f490 + 256) {
          printf("Load expr:\n");
        print_expr(e);
    }
#endif

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
        if (orig_addr > 0x61f490 && orig_addr < 0x61f490 + 256) {
            printf("Storing %lu bytes: *%p + %lu = t[%ld]\n", size,
                   (void*)orig_addr, offset, s_temps[val_idx] ? val_idx : -1);
        }
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
            // printf("Storing byte at index %lu\n", i);
#if 0
            if (orig_addr > 0x61f490 && orig_addr < 0x61f490 + 256) {
                print_expr(e);
            }
#endif
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

static inline void qemu_extend_helper(uintptr_t packed_idx)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t extkind = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

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

    Expr* e   = new_expr();
    e->opkind = opkind;
    e->op1    = s_temps[a_idx];
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, opkind_const_param);
    s_temps[out_idx] = e;
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
        case INDEX_op_sub_i32:
        case INDEX_op_sub_i64:
            return SUB;
        case INDEX_op_mul_i32:
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
        case INDEX_op_sar_i32:
        case INDEX_op_sar_i64:
            return SAR;
        case INDEX_op_rotl_i64:
            return ROTL;
        case INDEX_op_rotr_i64:
            return ROTR;
        case INDEX_op_ctz_i64:
            return CTZ;
        case INDEX_op_neg_i64:
            return NEG;
        case INDEX_op_not_i64:
            return NOT;
        case INDEX_op_muls2_i64:
        case INDEX_op_muls2_i32:
            return MUL;
        case INDEX_op_mulu2_i64:
        case INDEX_op_mulu2_i32:
            return MULU;
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
        case TCG_COND_LT:
            if (((intptr_t)a) < ((intptr_t)b))
                return TCG_COND_LT;
            else
                return TCG_COND_GE;
        case TCG_COND_LE:
            if (((intptr_t)a) <= ((intptr_t)b))
                return TCG_COND_LE;
            else
                return TCG_COND_GT;
        case TCG_COND_GE:
            if (((intptr_t)a) >= ((intptr_t)b))
                return TCG_COND_GE;
            else
                return TCG_COND_LT;
        case TCG_COND_GT:
            if (((intptr_t)a) > ((intptr_t)b))
                return TCG_COND_GT;
            else
                return TCG_COND_LE;
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
        case TCG_COND_GTU:
            if (a > b)
                return TCG_COND_GTU;
            else
                return TCG_COND_LEU;
        case TCG_COND_GEU:
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
                          uintptr_t packed_idx, uintptr_t pc)
{
    size_t a_idx = UNPACK_0(packed_idx);
    size_t b_idx = UNPACK_1(packed_idx);
    size_t size  = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL)
        return; // early exit

#if 0
    printf("Branch at %lx: %lu %s %lu\n", pc, a_idx, opkind_to_str(get_opkind_from_cond(cond)), b_idx);
    print_temp(a_idx);
    print_temp(b_idx);
#endif

    Expr*   branch_expr = new_expr();
    TCGCond sat_cond    = check_branch_cond_helper(a, b, cond);
    branch_expr->opkind = get_opkind_from_cond(sat_cond);
    SET_EXPR_OP(branch_expr->op1, branch_expr->op1_is_const, expr_a, a);
    SET_EXPR_OP(branch_expr->op2, branch_expr->op2_is_const, expr_b, b);

    branch_expr->op3 = (Expr*)size;

    next_query[0].query   = branch_expr;
    next_query[0].address = pc;
    assert(next_query[0].query != 0);
    next_query++;
    assert(next_query[0].query == 0);
    assert(next_query < queue_query + EXPR_QUERY_CAPACITY);

    // printf("Submitted a query\n");
    // uintptr_t query_id = next_query - queue_query;
    // if (query_id > 0 && query_id % 1000 == 0)
    //    printf("Submitted %ld queries\n", query_id);

    // printf("Branch at %lx\n", pc);
    // print_expr(branch_expr);
#if 0
    if (pc == 0x4132c3) {
        exit(0);
    }
#endif
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

#define FD_STDIN       0
#define MAX_INPUT_SIZE 4096
static Expr* input_exprs[MAX_INPUT_SIZE] = {0};
#define MAX_FP          128
#define FP_UNINTIALIZED 0
#define FP_CLOSED       1
#define FP_ZERO_OFFSET  2
// fp >= 0: offset in the inputfile
static intptr_t input_fp[MAX_FP] = {0};

static inline void read_from_input(intptr_t offset, uintptr_t addr, size_t size)
{
    assert(offset >= 0 && "Invalid offset");
    // printf("Offset=%ld size=%ld\n", offset, size);
    assert((offset + size) < MAX_INPUT_SIZE && "Offset is too large");

    printf(
        "Reading %lu bytes from input at 0x%lx. Storing them at addr 0x%lx\n",
        size, offset, addr);

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
        Expr* e_byte = input_exprs[offset + i];
        if (e_byte == NULL) {
            e_byte                  = new_expr();
            e_byte->opkind          = IS_SYMBOLIC;
            e_byte->op1             = (Expr*)(offset + i); // ID
            e_byte->op2             = (Expr*)1;            // number of bytes
            input_exprs[offset + i] = e_byte;
        }
        l3_page->entries[l3_page_idx + i] = e_byte;
    }
}

void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                         uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                         uintptr_t ret_val)
{
    int       fp;
    SyscallNo nr = (SyscallNo)syscall_no;
    switch (nr) {
        case SYS_OPEN:
        case SYS_OPENAT:
            fp = ((int)ret_val);
            if (s_config.symbolic_inject_input_mode == FROM_FILE && fp >= 0) {
                const char* fname = nr == SYS_OPEN ? (const char*)syscall_arg0
                                                   : (const char*)syscall_arg1;
                // printf("Opening file: %s vs %s\n", fname,
                // s_config.inputfile);
                if (strcmp(fname, s_config.inputfile) == 0) {
                    input_fp[fp] = FP_ZERO_OFFSET; // offset 0
                    // printf("Opening input file: %s\n", fname);
                }
            }
            break;
        //
        case SYS_CLOSE:
            fp           = syscall_arg0;
            input_fp[fp] = FP_CLOSED;
            break;
        //
        case SYS_SEEK:
            fp = syscall_arg0;
            if (s_config.symbolic_inject_input_mode == READ_FD_0 &&
                fp == FD_STDIN && input_fp[fp] != FP_CLOSED) {
                off_t offset = syscall_arg1;
                int   whence = syscall_arg2;
                switch (whence) {
                    case SEEK_CUR:
                        if (input_fp[fp] == FP_UNINTIALIZED) {
                            input_fp[fp] = offset + FP_ZERO_OFFSET;
                        } else {
                            assert(input_fp[fp] >= FP_ZERO_OFFSET);
                            input_fp[fp] += offset;
                        }
                        break;
                    case SEEK_SET:
                        input_fp[fp] = offset + FP_ZERO_OFFSET;
                        break;
                    default:
                        tcg_abort();
                }
            } else if (s_config.symbolic_inject_input_mode == FROM_FILE &&
                       input_fp[fp] >= FP_ZERO_OFFSET) {
                off_t offset = syscall_arg1;
                int   whence = syscall_arg2;
                switch (whence) {
                    case SEEK_CUR:
                        input_fp[fp] += offset;
                        break;
                    case SEEK_SET:
                        input_fp[fp] = offset + FP_ZERO_OFFSET;
                        break;
                    default:
                        tcg_abort();
                }
            }
            break;
        //
        case SYS_READ:
            fp = syscall_arg0;
            if (s_config.symbolic_inject_input_mode == READ_FD_0 &&
                fp == FD_STDIN) {

                if (input_fp[fp] == FP_CLOSED) {
                    printf("Reading from stdin but fp has been previosly "
                           "closed. What do we need to do?");
                    tcg_abort();
                } else if (input_fp[fp] == FP_UNINTIALIZED) {
                    // first read from stdin, set offset to zero
                    input_fp[fp] = FP_ZERO_OFFSET;
                }
                read_from_input(input_fp[fp] - FP_ZERO_OFFSET, syscall_arg1,
                                ret_val);
                input_fp[fp] += ret_val;

            } else if (s_config.symbolic_inject_input_mode == FROM_FILE &&
                       input_fp[fp] >= FP_ZERO_OFFSET) {
                read_from_input(input_fp[fp] - FP_ZERO_OFFSET, syscall_arg1,
                                ret_val);
                input_fp[fp] += ret_val;
            }
            break;

        default:
            tcg_abort();
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
    // branch(t_op_a, t_op_b, cond, op_in, tcg_ctx);

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

static inline void qemu_deposit_helper(uintptr_t packed_idx, uintptr_t a,
                                       uintptr_t b, uintptr_t poslen)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t b_idx   = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL && s_temps[b_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

    Expr* e   = new_expr();
    e->opkind = DEPOSIT;
    SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[a_idx], a);
    SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[b_idx], b);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, poslen);
    s_temps[out_idx] = e;
}

static inline void qemu_deposit(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, uintptr_t pos, uintptr_t len,
                                TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t op_out_idx = temp_idx(t_op_out);
    size_t op_a_idx   = temp_idx(t_op_a);
    size_t op_b_idx   = temp_idx(t_op_b);

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

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, DEPOSIT, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    uint64_t poslen = 0;
    poslen          = PACK_0(poslen, pos);
    poslen          = PACK_1(poslen, len);

    TCGTemp* t_poslen = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_poslen, poslen, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_poslen, offsetof(Expr, op3), 0, 1, sizeof(uint64_t),
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

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_extract_helper(uintptr_t packed_idx, uintptr_t a)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t pos     = UNPACK_2(packed_idx);
    uintptr_t len     = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

    Expr* e   = new_expr();
    e->opkind = QZEXTRACT;
    SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[a_idx], a);
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, pos);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, len);
    s_temps[out_idx] = e;
}

static inline void qemu_extract(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                uintptr_t pos, uintptr_t len, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t op_out_idx = temp_idx(t_op_out);
    size_t op_a_idx   = temp_idx(t_op_a);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, QZEXTRACT, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uint64_t), op_in,
                NULL, tcg_ctx);

    TCGTemp* t_pos = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_pos, pos, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_pos, offsetof(Expr, op2), 0, 1, sizeof(uint64_t),
                op_in, NULL, tcg_ctx);

    TCGTemp* t_len = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_len, len, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_len, offsetof(Expr, op3), 0, 1, sizeof(uint64_t),
                op_in, NULL, tcg_ctx);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline OPKIND get_high_opkind(OPKIND opkind)
{
    switch (opkind) {
        case MUL:
            return MUL_HIGH;
        case MULU:
            return MULU_HIGH;

        default:
            tcg_abort();
    }
}

static inline void qemu_binop_low_high_helper(OPKIND    opkind,
                                              uintptr_t packed_idx, uintptr_t a,
                                              uintptr_t b)
{
    uintptr_t out_high_idx = UNPACK_0(packed_idx);
    uintptr_t out_low_idx  = UNPACK_1(packed_idx);
    uintptr_t a_idx        = UNPACK_2(packed_idx);
    uintptr_t b_idx        = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_high_idx] = NULL;
        s_temps[out_low_idx]  = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_low_expr   = new_expr();
    binop_low_expr->opkind = (OPKIND)opkind;

    if (expr_a) {
        binop_low_expr->op1 = expr_a;
    } else {
        binop_low_expr->op1          = (Expr*)(uintptr_t)a;
        binop_low_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_low_expr->op2 = expr_b;
    } else {
        binop_low_expr->op2          = (Expr*)(uintptr_t)b;
        binop_low_expr->op2_is_const = 1;
    }

    s_temps[out_low_idx] = binop_low_expr;

    Expr* binop_high_expr   = new_expr();
    binop_high_expr->opkind = get_high_opkind(opkind);

    if (expr_a) {
        binop_high_expr->op1 = expr_a;
    } else {
        binop_high_expr->op1          = (Expr*)(uintptr_t)a;
        binop_high_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_high_expr->op2 = expr_b;
    } else {
        binop_high_expr->op2          = (Expr*)(uintptr_t)b;
        binop_high_expr->op2_is_const = 1;
    }

    s_temps[out_high_idx] = binop_high_expr;
}

static inline void qemu_binop_half_helper(OPKIND opkind, uintptr_t packed_idx,
                                          uintptr_t a, uintptr_t b)
{
    uintptr_t out_high_idx = UNPACK_0(packed_idx);
    uintptr_t out_low_idx  = UNPACK_1(packed_idx);
    uintptr_t a_idx        = UNPACK_2(packed_idx);
    uintptr_t b_idx        = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_high_idx] = NULL;
        s_temps[out_low_idx]  = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_low_expr   = new_expr();
    binop_low_expr->opkind = (OPKIND)opkind;

    if (expr_a) {
        binop_low_expr->op1 = expr_a;
    } else {
        binop_low_expr->op1          = (Expr*)(uintptr_t)a;
        binop_low_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_low_expr->op2 = expr_b;
    } else {
        binop_low_expr->op2          = (Expr*)(uintptr_t)b;
        binop_low_expr->op2_is_const = 1;
    }

    binop_low_expr->op3 = (Expr*)4; // ToDo

    s_temps[out_low_idx] = binop_low_expr;

    Expr* binop_high_expr   = new_expr();
    binop_high_expr->opkind = get_high_opkind(opkind);

    if (expr_a) {
        binop_high_expr->op1 = expr_a;
    } else {
        binop_high_expr->op1          = (Expr*)(uintptr_t)a;
        binop_high_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_high_expr->op2 = expr_b;
    } else {
        binop_high_expr->op2          = (Expr*)(uintptr_t)b;
        binop_high_expr->op2_is_const = 1;
    }

    binop_high_expr->op3 = (Expr*)(-4); // ToDo

    s_temps[out_high_idx] = binop_high_expr;
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
    g_hash_table_insert(helper_table, (gpointer)print_something,
                        (gpointer)&helper_info_print_something);
}

typedef struct {
    uint8_t   is_alive;
    uint8_t   is_const;
    uintptr_t const_value;
} TCGTempStaticState;

#include "symbolic-i386.c"

static inline void qemu_memmove(uintptr_t src, uintptr_t dst,
                                uintptr_t packed_idx, uintptr_t size)
{
    Expr** src_exprs = get_expr_addr((uintptr_t)src, size, 0);
    Expr** dst_exprs = get_expr_addr((uintptr_t)dst, size, 0);

    // printf("Memmove from=%lx to=%lx size=%lu\n", src, dst, size);

    if (src_exprs == NULL && dst_exprs == NULL) {
        return;
    }

    if (src_exprs == NULL) {
        for (size_t i = 0; i < size; i++) {
            dst_exprs[i] = NULL;
        }
        return;
    }

    if (dst_exprs == NULL) {
        dst_exprs = get_expr_addr((uintptr_t)dst, size, 1);
    }

#if 0
    printf("[+] Memmove from=%lx to=%lx size=%lu\n", src, dst, size);
#endif
    for (size_t i = 0; i < size; i++) {
        dst_exprs[i] = src_exprs[i];
        // print_expr(dst_exprs[i]);
    }
}

static int instrument = 0;
int        parse_translation_block(TranslationBlock* tb, uintptr_t tb_pc,
                                   uint8_t* tb_code, TCGContext* tcg_ctx)
{
    internal_tcg_context  = tcg_ctx;
    int force_flush_cache = 0;

    register_helpers();

    JumpTableFinder jump_table_finder_curr_instr = {0};
    JumpTableFinder jump_table_finder_prev_instr = {0};

    TCGTempStaticState temp_static_state[TCG_MAX_TEMPS] = {0};

#if 0
    int ops_to_skip = -1;
    if (instrument) {
        ops_to_skip = detect_memmove_xmm(tcg_ctx);
    }
#endif

    TCGOp* op;
    TCGOp* next_op;
    TCGOp* prev_op         = NULL;
    int    hit_first_instr = 0;

    uintptr_t pc = 0;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
#if 0
        for (size_t idx = 0; idx < op_to_add_size; idx++) {
            tcg_op_insert_before_op(tcg_ctx, op, op_to_add[idx]);
            op_to_add[idx] = NULL;
        }
        op_to_add_size = 0;
#endif

        next_op = QTAILQ_NEXT(op, link);

#if 0
        if (ops_to_skip > 0) {
            instrument = 0;
            ops_to_skip--;
        }
#endif

        // skip TB prologue
        if (op->opc != INDEX_op_insn_start && !hit_first_instr) {
            continue;
        }

        switch (op->opc) {

            case INDEX_op_insn_start:
                hit_first_instr = 1;
                pc              = op->args[0];

                jump_table_finder_prev_instr = jump_table_finder_curr_instr;
                memset(&jump_table_finder_curr_instr, 0,
                       sizeof(JumpTableFinder));

                if (instrument == 0 &&
                    pc == s_config.symbolic_exec_start_addr) {
                    // ToDo: we could start instrumenting when we inject
                    //       for the first time a symbolic data?
                    instrument        = 1;
                    force_flush_cache = 1;
                } else if (instrument == 1 &&
                           pc == s_config.symbolic_exec_stop_addr) {
                    instrument          = 0;
                    next_query[0].query = FINAL_QUERY;
                    printf("Number of queries: %lu\n",
                           (next_query - queue_query) - 1);
                    printf("Number of expressions: %lu\n",
                           GET_EXPR_IDX(next_free_expr) - 1);
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
                    // static analysis
                    temp_static_state[temp_idx(t)].is_alive    = 1;
                    temp_static_state[temp_idx(t)].is_const    = 1;
                    temp_static_state[temp_idx(t)].const_value = op->args[1];
                }
                break;

            // we always move exprs between temps, avoiding any check on the
            // source ToDo: branchless but more expensive?
            case INDEX_op_mov_i64:
            case INDEX_op_mov_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* from = arg_temp(op->args[1]);
                    TCGTemp* to   = arg_temp(op->args[0]);
                    size_t   size = op->opc == INDEX_op_mov_i64 ? 0 : 4;
#if 1
                    move_temp(temp_idx(from), temp_idx(to), size, op, tcg_ctx);
#else
                    TCGTemp* t_to_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_to_idx, (uintptr_t)temp_idx(to), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_from_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_from_idx, (uintptr_t)temp_idx(from), 0, op, NULL,
                             tcg_ctx);
                    if (size == sizeof(uintptr_t)) {
                        add_void_call_2(move_temp_helper, t_from_idx, t_to_idx,
                                        op, NULL, tcg_ctx);
                    } else {
                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)size, 0, op, NULL, tcg_ctx);
                        add_void_call_3(move_temp_helper, t_from_idx, t_to_idx,
                                        t_size, op, NULL, tcg_ctx);
                        tcg_temp_free_internal(t_size);
                    }
                    tcg_temp_free_internal(t_to_idx);
                    tcg_temp_free_internal(t_from_idx);
#endif
                    // jump table finder
                    if (jump_table_finder_curr_instr.displacement > 0 &&
                        jump_table_finder_curr_instr.scale_is_addr_size &&
                        jump_table_finder_curr_instr.index &&
                        jump_table_finder_curr_instr.has_done_load &&
                        jump_table_finder_curr_instr.addr &&
                        jump_table_finder_curr_instr.mov == from) {

                        jump_table_finder_curr_instr.mov = to;
                        assert(to != from);
                        assert(jump_table_finder_curr_instr.addr != to);
                        assert(jump_table_finder_curr_instr.addr != from);
                    }
                }
                break;

            case INDEX_op_add_i64:
            case INDEX_op_sub_i32:
            case INDEX_op_sub_i64:
            case INDEX_op_mul_i64:
            case INDEX_op_mul_i32:
            case INDEX_op_div_i64:
            case INDEX_op_divu_i64:
            case INDEX_op_rem_i64:
            case INDEX_op_remu_i64:
            case INDEX_op_and_i64:
            case INDEX_op_or_i64:
            case INDEX_op_xor_i64:
            case INDEX_op_shl_i64:
            case INDEX_op_shr_i64:
            case INDEX_op_sar_i32:
            case INDEX_op_sar_i64:
            case INDEX_op_rotl_i64:
            case INDEX_op_rotr_i64:
            case INDEX_op_ctz_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    OPKIND   bin_opkind = get_opkind(op->opc);
                    TCGTemp* t_out      = arg_temp(op->args[0]);
                    TCGTemp* t_a        = arg_temp(op->args[1]);
                    TCGTemp* t_b        = arg_temp(op->args[2]);

                    size_t size;
                    if (t_a->type == TCG_TYPE_I32) {
                        size = 4;
                    } else {
                        size = 0;
                        assert(t_a->type == TCG_TYPE_I64);
                    }
#if 1
                    qemu_binop(bin_opkind, t_out, t_a, t_b, size, op, tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)bin_opkind, 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v = PACK_0(v, temp_idx(t_out));
                    v = PACK_1(v, temp_idx(t_a));
                    v = PACK_2(v, temp_idx(t_b));
                    v = PACK_3(v, size);

                    TCGTemp* t_packed_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_helper, t_opkind, t_packed_idx,
                                    t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                    // jump table finder
                    if (op->opc == INDEX_op_shl_i64 &&
                        t_a->name && // native register
                        !temp_static_state[temp_idx(t_a)].is_const &&
                        temp_static_state[temp_idx(t_b)].is_alive &&
                        temp_static_state[temp_idx(t_b)].is_const &&
                        temp_static_state[temp_idx(t_b)].const_value == 3) {

                        jump_table_finder_curr_instr.index              = t_a;
                        jump_table_finder_curr_instr.scale_is_addr_size = 1;
                    }
                    if (op->opc == INDEX_op_add_i64 &&
                        temp_static_state[temp_idx(t_b)].is_alive &&
                        temp_static_state[temp_idx(t_b)].is_const &&
                        temp_static_state[temp_idx(t_b)].const_value > 0x1000) {

                        jump_table_finder_curr_instr.displacement =
                            temp_static_state[temp_idx(t_b)].const_value;
                        jump_table_finder_curr_instr.addr = t_out;
                    }
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

                    if (next_op->opc == INDEX_op_st_i64 &&
                        get_mem_op_size(get_memop(op->args[2])) == 8 &&
                        is_xmm_offset(next_op->args[2])) {

                        TCGTemp* t_src = arg_temp(op->args[1]);

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_src));

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)8, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_dst, (uintptr_t)next_op->args[2], 0, op,
                                 NULL, tcg_ctx);

                        TCGTemp* t_env = arg_temp(next_op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);
                        tcg_binop(t_dst, t_dst, t_env, 0, 0, 0, ADD, op, NULL,
                                  tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                        MARK_TEMP_AS_ALLOCATED(t_src);
                        add_void_call_4(qemu_memmove, t_src, t_dst,
                                        t_packed_idx, t_size, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src);
                        tcg_temp_free_internal(t_dst);
                        tcg_temp_free_internal(t_packed_idx);
                        tcg_temp_free_internal(t_size);

                    } else {
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 0
                        TCGMemOp  mem_op = get_memop(op->args[2]);
                        uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                        qemu_load(t_ptr, t_val, offset, mem_op, op,
                                tcg_ctx); // bugged
#else
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_mem_op,
                                 make_mem_op_offset(get_memop(op->args[2]),
                                                    get_mmuidx(op->args[2])),
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
#endif
                        // jump table finder
                        if (jump_table_finder_curr_instr.displacement > 0 &&
                            jump_table_finder_curr_instr.scale_is_addr_size &&
                            jump_table_finder_curr_instr.index &&
                            t_ptr == jump_table_finder_curr_instr.addr) {

                            jump_table_finder_curr_instr.has_done_load = 1;
                            jump_table_finder_curr_instr.mov           = t_val;
                            TCGTemp* t_addr =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            MARK_TEMP_AS_ALLOCATED(t_ptr);
                            tcg_mov(t_addr, t_ptr, 0, 0, op, NULL, tcg_ctx);
                            MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                            assert(t_addr != t_val);

                            move_temp(temp_idx(t_ptr), temp_idx(t_addr),
                                      sizeof(uintptr_t), op, tcg_ctx);

                            jump_table_finder_curr_instr.addr = t_addr;
                            jump_table_finder_curr_instr.need_to_free_addr = 1;
                            // printf("Jump table finder: load\n");
                        }
                    }
                }
                break;

            case INDEX_op_qemu_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {

                    if (prev_op && prev_op->opc == INDEX_op_ld_i64 &&
                        get_mem_op_size(get_memop(op->args[2])) == 8 &&
                        is_xmm_offset(prev_op->args[2])) {

                        TCGTemp* t_dst = arg_temp(op->args[1]);

                        uint64_t v = 0;
                        v          = PACK_0(v, 0); // src_idx
                        v          = PACK_1(v, temp_idx(t_dst));

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)8, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_src = new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_src, (uintptr_t)prev_op->args[2], 0, op,
                                 NULL, tcg_ctx);

                        TCGTemp* t_env = arg_temp(prev_op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);
                        tcg_binop(t_src, t_src, t_env, 0, 0, 0, ADD, op, NULL,
                                  tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                        MARK_TEMP_AS_ALLOCATED(t_dst);
                        add_void_call_4(qemu_memmove, t_src, t_dst,
                                        t_packed_idx, t_size, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        tcg_temp_free_internal(t_src);
                        tcg_temp_free_internal(t_packed_idx);
                        tcg_temp_free_internal(t_size);

                    } else {
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 0
                        TCGMemOp  mem_op = get_memop(op->args[2]);
                        uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                        qemu_store(t_ptr, t_val, offset, mem_op, op, tcg_ctx);
#else
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_mem_op,
                                 make_mem_op_offset(get_memop(op->args[2]),
                                                    get_mmuidx(op->args[2])),
                                 0, op, NULL, tcg_ctx);
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
#endif
                    }
                }
                break;

            case INDEX_op_ld_i64:
            case INDEX_op_ld32s_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    uintptr_t offset = (uintptr_t)op->args[2];
                    if (op->opc == INDEX_op_ld32s_i64 &&
                        is_xmm_offset(offset)) {
                        tcg_abort();
                    }
#if 0
                    if (is_xmm_offset(offset)) {

                        printf("load to xmm data (offset=%lu)\n", offset);
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
#endif
                }
                break;

            case INDEX_op_st32_i64:
            case INDEX_op_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    uintptr_t offset = (uintptr_t)op->args[2];
                    if (is_eip_offset(offset)) {

                        TCGTemp* t_value = arg_temp(op->args[0]);
                        qemu_pc_write(t_value, op, tcg_ctx);
#if 0
                        MARK_TEMP_AS_ALLOCATED(t_value);
                        add_void_call_1(qemu_pc_write_helper, t_value, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_value);
#endif

                        if (jump_table_finder_prev_instr.scale_is_addr_size &&
                            jump_table_finder_prev_instr.displacement &&
                            jump_table_finder_prev_instr.addr &&
                            jump_table_finder_prev_instr.index &&
                            jump_table_finder_prev_instr.has_done_load &&
                            jump_table_finder_prev_instr.mov == t_value) {

                            printf("\nJump Table at %lx?\n", pc);
                            qemu_jump_table(jump_table_finder_prev_instr.addr,
                                            op, tcg_ctx);

                            if (jump_table_finder_prev_instr
                                    .need_to_free_addr) {
                                tcg_temp_free_internal(
                                    jump_table_finder_prev_instr.addr);
                                clear_temp(
                                    temp_idx(jump_table_finder_prev_instr.addr),
                                    op, tcg_ctx);
                            }
                        }

                    } else if (is_xmm_offset(offset)) {
                        if (op->opc == INDEX_op_st_i32) {
                            printf("store to xmm data (offset=%lu)\n", offset);
                            tcg_abort();
                        }
#if 0
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
#endif
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

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_a));
                    v          = PACK_1(v, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_5(branch_helper, t_a, t_b, t_cond,
                                    t_packed_idx, t_pc, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_packed_idx);
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
#if 1
                    extend(t_to, t_from, get_extend_kind(op->opc), op, tcg_ctx);
#else

                    uint64_t opkind = get_extend_kind(op->opc);

                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_to));
                    v1          = PACK_1(v1, temp_idx(t_from));
                    v1          = PACK_2(v1, opkind);

                    TCGTemp* t_packed = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    add_void_call_1(qemu_extend_helper, t_packed, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_packed);
#endif
                }
                break;

            case INDEX_op_goto_ptr:
            case INDEX_op_goto_tb:
            case INDEX_op_exit_tb:
                break;

            case INDEX_op_call:
#if 1
                for (size_t i = 0; i < TCGOP_CALLO(op); i++)
                    mark_temp_as_in_use(arg_temp(op->args[i]));
                for (size_t i = 0; i < TCGOP_CALLI(op); i++)
                    mark_temp_as_in_use(
                        arg_temp(op->args[TCGOP_CALLO(op) + i]));
#endif
                if (instrument) {

                    const char* helper_name = tcg_find_helper(
                        tcg_ctx, op->args[TCGOP_CALLI(op) + TCGOP_CALLO(op)]);

                    if (strcmp(helper_name, "syscall") == 0) {

                        // we directly instrment the syscall handler for x86
                        // see syscall.c in linux-user

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

                    } else if (strcmp(helper_name, "divq_EAX") == 0 ||
                               strcmp(helper_name, "idivq_EAX") == 0) {

                        TCGTemp* t_rax = tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                        TCGTemp* t_0   = arg_temp(op->args[1]);

                        uint64_t mode; // 0: div, 1: idiv
                        switch (helper_name[0]) {
                            case 'd':
                                mode = 0;
                                break;
                            case 'i':
                                mode = 1;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_rax));
                        v          = PACK_1(v, temp_idx(t_rdx));
                        v          = PACK_2(v, temp_idx(t_0));
                        v          = PACK_3(v, mode);

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_rax);
                        MARK_TEMP_AS_ALLOCATED(t_rdx);
                        MARK_TEMP_AS_ALLOCATED(t_0);

                        add_void_call_4(qemu_divq_EAX, t_packed_idx, t_rax,
                                        t_rdx, t_0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_rax);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_rdx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_0);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "pxor_xmm") == 0 ||
                               strcmp(helper_name, "por_xmm") == 0 ||
                               strcmp(helper_name, "paddb_xmm") == 0 ||
                               strcmp(helper_name, "paddw_xmm") == 0 ||
                               strcmp(helper_name, "paddl_xmm") == 0 ||
                               strcmp(helper_name, "paddq_xmm") == 0 ||
                               strcmp(helper_name, "psubb_xmm") == 0 ||
                               strcmp(helper_name, "psubw_xmm") == 0 ||
                               strcmp(helper_name, "psubl_xmm") == 0 ||
                               strcmp(helper_name, "psubq_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqb_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqw_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeql_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqq_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtb_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtw_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtl_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtq_xmm") == 0 ||
                               strcmp(helper_name, "pminub_xmm") == 0) {

                        OPKIND    opkind;
                        uintptr_t slice;
                        switch (helper_name[1]) {
                            case 'x':
                                opkind = XOR;
                                slice  = 1;
                                break;
                            case 'o':
                                opkind = OR;
                                slice  = 1;
                                break;
                            case 'a':
                                opkind = SUB;
                                slice  = suffix_to_slice(helper_name[4], 0);
                                break;
                            case 's':
                                opkind = SUB;
                                slice  = suffix_to_slice(helper_name[4], 0);
                                break;
                            case 'c':
                                if (helper_name[5] == 'q') {
                                    opkind = CMP_EQ;
                                } else if (helper_name[4] == 'g' &&
                                           helper_name[5] == 't') {
                                    opkind = CMP_GT;
                                } else {
                                    tcg_abort();
                                }
                                slice = suffix_to_slice(helper_name[6], 0);
                                break;
                            case 'm':
                                opkind = MIN;
                                slice  = suffix_to_slice(helper_name[5], 0);
                                break;
                            default:
                                tcg_abort();
                        }

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)opkind, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);

                        uint64_t v = slice;
                        v          = v | (pc << 8);

                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, v, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_op, t_opkind, t_dst_addr,
                                        t_src_addr, t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);
                        tcg_temp_free_internal(t_slice);

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

                    } else if (strcmp(helper_name, "psllb_xmm") == 0 ||
                               strcmp(helper_name, "psllw_xmm") == 0 ||
                               strcmp(helper_name, "pslld_xmm") == 0 ||
                               strcmp(helper_name, "psllq_xmm") == 0 ||
                               strcmp(helper_name, "pslldq_xmm") == 0 ||
                               strcmp(helper_name, "psrlb_xmm") == 0 ||
                               strcmp(helper_name, "psrlw_xmm") == 0 ||
                               strcmp(helper_name, "psrld_xmm") == 0 ||
                               strcmp(helper_name, "psrlq_xmm") == 0 ||
                               strcmp(helper_name, "psrldq_xmm") == 0) {

                        OPKIND    opkind;
                        uintptr_t slice;
                        switch (helper_name[2]) {
                            case 'l':
                                opkind = SHL;
                                slice  = suffix_to_slice(helper_name[4],
                                                        helper_name[5]);
                                break;
                            case 'r':
                                opkind = SHR;
                                slice  = suffix_to_slice(helper_name[4],
                                                        helper_name[5]);
                                break;
                            default:
                                tcg_abort();
                        }

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)opkind, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, slice, 0, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_op, t_opkind, t_dst_addr,
                                        t_src_addr, t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);
                        tcg_temp_free_internal(t_slice);

                    } else if (strcmp(helper_name, "pshufd_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);
                        TCGTemp* t_order =
                            arg_temp(op->args[2]); // this is an immediate

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_pshufd, t_dst_addr, t_src_addr,
                                        t_order, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);

                    } else if (strcmp(helper_name, "movl_mm_T0_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src =
                            arg_temp(op->args[1]); // this is 32 bit

                        TCGTemp* t_src_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_src_idx, (uintptr_t)temp_idx(t_src), 0, op,
                                 NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        add_void_call_2(qemu_xmm_movl_mm_T0, t_dst_addr,
                                        t_src_idx, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        tcg_temp_free_internal(t_src_idx);

                    } else if (strcmp(helper_name, "punpcklbw_xmm") == 0 ||
                               strcmp(helper_name, "punpcklwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckldq_xmm") == 0 ||
                               strcmp(helper_name, "punpcklqdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhbw_xmm") == 0 ||
                               strcmp(helper_name, "punpckhwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckhdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhqdq_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);

                        uint8_t slice;
                        switch (helper_name[7]) {
                            case 'b':
                                slice = 1;
                                break;
                            case 'w':
                                slice = 2;
                                break;
                            case 'd':
                                slice = 4;
                                break;
                            case 'q':
                                slice = 8;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint8_t lowbytes;
                        if (helper_name[6] == 'l') {
                            lowbytes = 1;
                        } else if (helper_name[6] == 'h') {
                            lowbytes = 0;
                        } else {
                            tcg_abort();
                        }

                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, (uintptr_t)slice, 0, op, NULL,
                                 tcg_ctx);

                        TCGTemp* t_lowbytes =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_lowbytes, lowbytes, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_punpck, t_dst_addr, t_src_addr,
                                        t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_slice);
                        tcg_temp_free_internal(t_lowbytes);

                    } else if (strcmp(helper_name, "fxsave") == 0) {

                        TCGTemp* t_env = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);

                        MARK_TEMP_AS_ALLOCATED(t_env);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_2(qemu_fxsave, t_env, t_ptr, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                    } else if (strcmp(helper_name, "fxrstor") == 0) {

                        TCGTemp* t_env = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);

                        MARK_TEMP_AS_ALLOCATED(t_env);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_2(qemu_fxrstor, t_env, t_ptr, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

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

                        if (!helper_is_whitelisted) {
                            printf("Helper %s is not instrumented\n",
                                   helper_name);
                        }
                    }
                }
                break;

            case INDEX_op_movcond_i64:
            case INDEX_op_movcond_i32:
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

                    size_t size = op->opc == INDEX_op_movcond_i64 ? 0 : 4;
#if 0
                    // ToDo
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_a));
                    v          = PACK_1(v, temp_idx(t_b));
                    v          = PACK_2(v, size);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_5(branch_helper, t_a, t_b, t_cond,
                                    t_packed_idx, t_pc, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_packed_idx);
                    tcg_temp_free_internal(t_pc);

                    qemu_movcond(t_out, t_a, t_b, t_true, t_false, cond, op,
                                 tcg_ctx);
#endif
                }
                break;

            case INDEX_op_neg_i64:
            case INDEX_op_not_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
#if 0
                    qemu_unop(get_opkind(op->opc), t_out, t_a, op, tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)get_opkind(op->opc), 0, op,
                             NULL, tcg_ctx);
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

            case INDEX_op_deposit_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    TCGTemp*  t_out = arg_temp(op->args[0]);
                    TCGTemp*  t_a   = arg_temp(op->args[1]);
                    TCGTemp*  t_b   = arg_temp(op->args[2]);
                    uintptr_t pos   = (uintptr_t)op->args[3];
                    uintptr_t len   = (uintptr_t)op->args[4];
                    // printf("Deposit pos=%lu len=%lu\n", pos, len);
#if 0 // Bugged?
                    qemu_deposit(t_out, t_a, t_b, pos, len, op, tcg_ctx);
#else
                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_out));
                    v1          = PACK_1(v1, temp_idx(t_a));
                    v1          = PACK_2(v1, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    uint64_t v2 = 0;
                    v2          = PACK_0(v2, pos);
                    v2          = PACK_1(v2, len);

                    TCGTemp* t_poslen = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_poslen, (uintptr_t)v2, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_deposit_helper, t_packed_idx, t_a, t_b,
                                    t_poslen, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_packed_idx);
                    tcg_temp_free_internal(t_poslen);
#endif
                }
                break;

            case INDEX_op_extract_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
#if 1
                    uintptr_t pos = (uintptr_t)op->args[2];
                    uintptr_t len = (uintptr_t)op->args[3];
                    qemu_extract(t_out, t_a, pos, len, op, tcg_ctx);
#else
                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_out));
                    v1          = PACK_1(v1, temp_idx(t_a));
                    v1          = PACK_2(v1, op->args[2]);
                    v1          = PACK_3(v1, op->args[3]);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    add_void_call_2(qemu_extract_helper, t_packed_idx, t_a, op,
                                    NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            case INDEX_op_muls2_i64:
            case INDEX_op_mulu2_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out_low  = arg_temp(op->args[0]);
                    TCGTemp* t_out_high = arg_temp(op->args[1]);
                    TCGTemp* t_a        = arg_temp(op->args[2]);
                    TCGTemp* t_b        = arg_temp(op->args[3]);
#if 0
                    // ToDo
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, get_opkind(op->opc), 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_out_high));
                    v          = PACK_1(v, temp_idx(t_out_low));
                    v          = PACK_2(v, temp_idx(t_a));
                    v          = PACK_3(v, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_low_high_helper, t_opkind,
                                    t_packed_idx, t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            case INDEX_op_muls2_i32:
            case INDEX_op_mulu2_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out_low  = arg_temp(op->args[0]);
                    TCGTemp* t_out_high = arg_temp(op->args[1]);
                    TCGTemp* t_a        = arg_temp(op->args[2]);
                    TCGTemp* t_b        = arg_temp(op->args[3]);
#if 0
                    // ToDo
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, get_opkind(op->opc), 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_out_high));
                    v          = PACK_1(v, temp_idx(t_out_low));
                    v          = PACK_2(v, temp_idx(t_a));
                    v          = PACK_3(v, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_half_helper, t_opkind,
                                    t_packed_idx, t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            default:
                if (instrument) {
                    const TCGOpDef* def __attribute__((unused)) =
                        &tcg_op_defs[op->opc];
                    printf("Unhandled TCG instruction: %s\n", def->name);
                    tcg_abort();
                }
        }

        // mark as free any temp that was dead at this instruction
        unsigned life = op->life;
        life /= DEAD_ARG;
        if (life) {
            for (int i = 0; life; ++i, life >>= 1) {
                if (life & 1) {
                    mark_temp_as_free(arg_temp(op->args[i]));
                    temp_static_state[temp_idx(arg_temp(op->args[i]))]
                        .is_alive = 0;
                }
            }
        }

#if 0
        if (ops_to_skip == 0 && instrument == 0) {
            instrument = 1;
            instrument_memmove_xmm(op, tcg_ctx);
        }
#endif
        prev_op = op;
    }

    return force_flush_cache;
}