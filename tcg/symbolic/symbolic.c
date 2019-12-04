#include <stdio.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "symbolic.h"

typedef enum OPKIND
{
    ADD,
    SUB,
    MUL,
    DIV,
    DIVU,
    REM,
    REMU,
    AND,
    OR,
    XOR,
    SHL,
    SHR,
    SAR,
    ROTL,
    ROTR
} OPKIND;

typedef struct Expr
{
    //struct Expr *next_free; // eq to zero when in use or when not yet allocated
    struct Expr *op1;
    struct Expr *op2;
    uint8_t opkind;
    uint8_t op1_is_const;
    uint8_t op2_is_const;
    uint8_t is_symbolic_input;
} Expr;

// symbolic temps
Expr *stemps[TCG_MAX_TEMPS] = {0};

// symbolic memory
#define L1_PAGE_BITS 16
#define L2_PAGE_BITS 16
#define L3_PAGE_BITS 16

typedef struct l3_page_t
{
    Expr *entries[1 << L3_PAGE_BITS];
} l3_page_t;

typedef struct l2_page_t
{
    l3_page_t *entries[1 << L2_PAGE_BITS];
} l2_page_t;

typedef struct l1_page_t
{
    l2_page_t *entries[1 << L1_PAGE_BITS];
} l1_page_t;

// up to 48 bits addressing
typedef struct s_memory_t
{
    l1_page_t table;
} s_memory_t;

s_memory_t s_memory = {0};

// Expr allocation pool
#define EXPR_POOL_CAPACITY (256 * 1024)
Expr pool[EXPR_POOL_CAPACITY] = {0};
Expr *next_free_expr = &pool[0];
Expr *last_expr = NULL; // ToDo: unsafe

#if 0
TCGOp * op_macro;
#define ADD_VOID_CALL_0(f, op, tcg_ctx) ({do { \
    TCGOpcode lopc = INDEX_op_call; \
    op_macro = tcg_op_insert_after(tcg_ctx, op, lopc); \
    TCGOP_CALLO(op_macro) = 0; \
    op_macro->args[0] = (uintptr_t) f; \
    op_macro->args[1] = 0; \
    TCGOP_CALLI(op_macro) = 0; \
} while (0); op_macro; })
#endif

#define MARK_TEMP_AS_ALLOCATED(t) do { t->temp_allocated = 1; } while(0)
#define MARK_TEMP_AS_NOT_ALLOCATED(t) do { t->temp_allocated = 0; } while(0)

// since we are asking for new temps after generating and analyzing TCG,
// tcg_temp_new_internal may returns temps that are in use in the TB
// (but are dead at the end of the TB). To avoid conflicts, we call
// tcg_temp_new_internal until we get a non used temp from the
// previous istructions in the TB.
//
// NOTE: temps must be deallocated after generating instrumentation
//       for one instruction otherwise conflicts may emerge!
static uint8_t used_temps_idxs[TCG_MAX_TEMPS] = {0};
static inline TCGTemp *new_non_conflicting_temp(TCGType type)
{

    TCGTemp *r = NULL;
    TCGTemp *conflicting_temps[TCG_MAX_TEMPS];
    size_t conflicting_temps_count = 0;
    while (!r)
    {
        TCGTemp *current = tcg_temp_new_internal(type, false);
        size_t idx = temp_idx(current);
        if (used_temps_idxs[idx] != 0) // temp is in use
        {
            conflicting_temps[conflicting_temps_count++] = current;
        }
        else
        {
            r = current;
        }
    }

    // deallocate any temp that is in conflict
    while (conflicting_temps_count > 0)
    {
        tcg_temp_free_internal(conflicting_temps[conflicting_temps_count - 1]);
        conflicting_temps_count--;
    }

    return r;
}

static inline void mark_insn_as_instrumentation(TCGOp *op)
{
    // we use the last op arg, which is usually unused
    op->args[MAX_OPC_PARAM - 1] = (uint64_t)1;
}

static inline void add_void_call_0(void *f, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = (uintptr_t)f;
    op->args[1] = 0;     // flags
    TCGOP_CALLI(op) = 0; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

static inline void add_void_call_1(void *f, TCGTemp *arg, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(arg->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg);
    op->args[1] = (uintptr_t)f;
    op->args[2] = 0;     // flags
    TCGOP_CALLI(op) = 1; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

static inline void add_void_call_2(void *f, TCGTemp *arg0, TCGTemp *arg1, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg0);
    op->args[1] = temp_arg(arg1);
    op->args[2] = (uintptr_t)f;
    op->args[3] = 0;     // flags
    TCGOP_CALLI(op) = 2; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

static inline void check_pool_expr_capacity(void)
{
    assert(next_free_expr >= pool);
    assert(next_free_expr < pool + EXPR_POOL_CAPACITY);
}

#define GET_EXPR_IDX(e) ((((uintptr_t)e) - ((uintptr_t)&pool)) / sizeof(Expr))

static inline Expr *new_expr(void)
{
    // ToDo: use free list
    check_pool_expr_capacity();
    next_free_expr += 1;
    last_expr = next_free_expr - 1;
    return next_free_expr - 1;
}

static inline void print_reg(void)
{
    size_t r = 12; // RDI
    //printf("RDI is at %p\n", &stemps[r]);
    printf("RDI is %ssymbolic\n", stemps[r]->is_symbolic_input ? "" : "not ");
}

static inline void new_symbolic_expr(void)
{
    Expr *e = new_expr();
    e->is_symbolic_input = 1;
    printf("Marking expr%lu as symbolic\n", GET_EXPR_IDX(e));
}

static inline void sync_argo_temp(TCGOp *op, size_t i)
{
    op->life |= SYNC_ARG << i;
}

static inline void mark_dead_arg_temp(TCGOp *op, size_t i)
{
    op->life |= DEAD_ARG << i;
}

// ts <- CONST
static inline void tcg_movi(TCGTemp *ts, uintptr_t const_val,
                            uint8_t is_ts_dead, uint8_t is_const_val_dead,
                            TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts->temp_allocated);

    TCGOpcode opc = INDEX_op_movi_i64;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts);
    assert(!is_ts_dead);

    op->args[1] = (uintptr_t)const_val;
    if (is_const_val_dead)
        mark_dead_arg_temp(op, 1);

    if (op_out)
        *op_out = op;
}

// to <- from
static inline void tcg_mov(TCGTemp *ts_to, TCGTemp *ts_from,
                           uint8_t is_ts_to_dead, uint8_t is_ts_from_dead,
                           TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_from->temp_allocated);

    TCGOpcode opc = INDEX_op_mov_i64;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead)
        mark_dead_arg_temp(op, 1);

    if (op_out)
        *op_out = op;
}

// c <- a op b
static inline void tcg_binop(TCGTemp *ts_c, TCGTemp *ts_a, TCGTemp *ts_b,
                             uint8_t is_ts_c_dead, uint8_t is_ts_a_dead, uint8_t is_ts_b_dead,
                             OPKIND opkind, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_c->temp_allocated);

    TCGOpcode opc;
    switch (opkind)
    {
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
    default:
        tcg_abort();
        break;
    }

    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_c);
    assert(!is_ts_c_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead)
        mark_dead_arg_temp(op, 1);

    op->args[2] = temp_arg(ts_b);
    if (is_ts_b_dead)
        mark_dead_arg_temp(op, 2);

    if (op_out)
        *op_out = op;
}

static inline void tcg_load_n(TCGTemp *ts_from, TCGTemp *ts_to, uintptr_t offset,
                              uint8_t is_ts_from_dead, uint8_t is_ts_to_dead, uint8_t is_offset_dead,
                              size_t n_bytes, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_from->temp_allocated);
    assert(ts_to->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes)
    {
    // ToDo: add _i32 address mode
    case 8:
        opc = INDEX_op_ld_i64;
        break;
    default:
        tcg_abort();
    }

    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead)
        mark_dead_arg_temp(op, 1);

    op->args[2] = offset;
    if (is_offset_dead)
        mark_dead_arg_temp(op, 2);

    if (op_out)
        *op_out = op;
}

static inline void tcg_store_n(TCGTemp *ts_to, TCGTemp *ts_val, uintptr_t offset,
                                uint8_t is_ts_to_dead, uint8_t is_ts_val_dead, uint8_t is_offset_dead,
                                size_t n_bytes, TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_val->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes)
    {
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

    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_val);
    if (is_ts_val_dead)
        mark_dead_arg_temp(op, 0);

    op->args[1] = temp_arg(ts_to);
    if (is_ts_to_dead)
        mark_dead_arg_temp(op, 1);

    op->args[2] = offset;
    if (is_offset_dead)
        mark_dead_arg_temp(op, 2);

    if (op_out)
        *op_out = op;
}

// branch to label if a cond b is true
static inline void tcg_brcond(TCGLabel *label, TCGTemp *ts_a, TCGTemp *ts_b, TCGCond cond,
                              uint8_t is_ts_a_dead, uint8_t is_ts_b_dead,
                              TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);

    label->refs++;
    TCGOpcode opc = INDEX_op_brcond_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_a);
    if (is_ts_a_dead)
        mark_dead_arg_temp(op, 0);

    op->args[1] = temp_arg(ts_b);
    if (is_ts_b_dead)
        mark_dead_arg_temp(op, 1);

    op->args[2] = cond;
    op->args[3] = label_arg(label);

    if (op_out)
        *op_out = op;
}

// add a goto label (referenced by brcond)
static inline void tcg_set_label(TCGLabel *label,
                                TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    label->present = 1;
    TCGOpcode opc = INDEX_op_set_label;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label);

    if (op_out)
        *op_out = op;
}

static inline void init_reg(size_t reg, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(reg < TCG_MAX_TEMPS);
    printf("Setting expr of reg %lu\n", reg);

    TCGTemp *t_last_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_last_expr, (uintptr_t)&last_expr, 0, 1, op_in, NULL, tcg_ctx);
    tcg_load_n(t_last_expr, t_last_expr, 0, 0, 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_dst, (uintptr_t)&stemps[reg], 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t_dst, t_last_expr, 0, 1, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_dst);
    tcg_temp_free_internal(t_last_expr);
}

static inline void make_reg_symbolic(const char *reg_name, TCGOp *op, TCGContext *tcg_ctx)
{
    for (int i = 0; i < TCG_TARGET_NB_REGS; i++)
    {
        TCGTemp *t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0)
        {
            printf("Marking %s (id=%d) as symbolic\n", t->name, i);
            add_void_call_0(new_symbolic_expr, op, NULL, tcg_ctx);
            init_reg(i, op, tcg_ctx);
            add_void_call_0(print_reg, op, NULL, tcg_ctx);
        }
    }
}

static inline void move_temp(size_t from, size_t to, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp *t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&stemps[from], 0, 1, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&stemps[to], 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_from, 0, 1, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_from);
    tcg_temp_free_internal(t_to);
}

static inline void clear_temp(size_t idx, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(idx < TCG_MAX_TEMPS);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp *t = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t, (uintptr_t)&stemps[idx], 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t, t_zero, 0, 1, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_zero);
    tcg_temp_free_internal(t);
}

static inline void test_expr(void)
{
    Expr *e = next_free_expr - 1;
    printf("Testing expr\n");
    assert(e->is_symbolic_input == 0);
    printf("Done\n");
}

static inline void allocate_new_expr(TCGTemp *t_out, TCGOp *op_in, TCGContext *tcg_ctx)
{
    add_void_call_0(check_pool_expr_capacity, op_in, NULL, tcg_ctx); // ToDo: make inline check

    TCGTemp *t_next_free_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_next_free_expr_addr, (uintptr_t)&next_free_expr, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp *t_next_free_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_next_free_expr_addr, t_next_free_expr, 0, 0, 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_mov(t_out, t_next_free_expr, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_expr_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_expr_size, sizeof(Expr), 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_next_free_expr, t_next_free_expr, t_expr_size, 0, 0, 0, ADD, op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_expr_size);

    tcg_store_n(t_next_free_expr_addr, t_next_free_expr, 0, 0, 0, 0, sizeof(void *), op_in, NULL, tcg_ctx);

    TCGOp * helper;
    add_void_call_0(check_pool_expr_capacity, op_in, &helper, tcg_ctx); // ToDo: make inline check
    mark_insn_as_instrumentation(helper);

    tcg_temp_free_internal(t_next_free_expr);
    tcg_temp_free_internal(t_next_free_expr_addr);
}

// When adding instrumentation with branches and when accessing
// the operands contents, TCG may move temp loads (i.e., loading
// content of the temp operand from memory) within the branching
// code (which is not always executed), possibly leading to SIGSEGV.
// To avoid this issue, we insert fake uses for each temp operand
// before any branching code, to make temp loads branchless.
static inline void preserve_op_load(TCGTemp *t, TCGOp *op_in, TCGContext *tcg_ctx)
{
    TCGTemp *t_dummy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t);
    tcg_mov(t_dummy, t, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t);
    tcg_temp_free_internal(t_dummy);
}

// Binary operation: t_out = t_a opkind t_b
static inline void binary_op(OPKIND opkind, TCGTemp *t_op_out, TCGTemp *t_op_a, TCGTemp *t_op_b, TCGOp *op_in, TCGContext *tcg_ctx)
{
    size_t out = temp_idx(t_op_out);
    size_t a = temp_idx(t_op_a);
    size_t b = temp_idx(t_op_b);

    assert(out < TCG_MAX_TEMPS);
    assert(a < TCG_MAX_TEMPS);
    assert(b < TCG_MAX_TEMPS);

    preserve_op_load(t_op_a, op_in, tcg_ctx);
    preserve_op_load(t_op_b, op_in, tcg_ctx);

    // check if both t_a and t_b are concrete
    // if this is the case, then skip any further work

    TCGLabel *label_both_concrete = gen_new_label();

    TCGTemp *t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&stemps[a], 0, 1, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&stemps[b], 0, 1, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_a_and_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_and_b, t_a, t_b, 0, 0, 0, AND, op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, 1, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    tcg_brcond(label_both_concrete, t_a_and_b, t_zero, TCG_COND_EQ, 1, 0, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_a_and_b);

    // allocate expr for t_out
    TCGTemp *t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(t_out, op_in, tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, 1, op_in, NULL, tcg_ctx);

    TCGLabel *label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0, 0, 1, op_in, NULL, tcg_ctx);
    TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, 1, 1, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel *label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 0, 0, 1, op_in, NULL, tcg_ctx);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp *t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&stemps[out], 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_a);
    tcg_temp_free_internal(t_b);
    tcg_temp_free_internal(t_out);
    tcg_temp_free_internal(t_out_expr);
    tcg_temp_free_internal(t_zero);
    tcg_temp_free_internal(t_one);
}

static inline void allocate_l2_page(uintptr_t l1_entry_idx)
{
    assert(l1_entry_idx < 1 << L1_PAGE_BITS);

    printf("Allocating l2 page at idx %lu\n", l1_entry_idx);
    s_memory.table.entries[l1_entry_idx] = g_malloc0(sizeof(l2_page_t)); // FixMe: get mmap lock
    printf("Done: l1_entry_idx_addr=%p l2_page_addr=%p\n", &s_memory.table.entries[l1_entry_idx], s_memory.table.entries[l1_entry_idx]);
}

static inline void allocate_l3_page(void ** l2_page_idx_addr)
{
    printf("Allocating l3 page at l2_page_idx_addr=%p\n", l2_page_idx_addr);
    *l2_page_idx_addr = g_malloc0(sizeof(l3_page_t)); // FixMe: get mmap lock
    printf("Done: l3_page_addr=%p\n", *l2_page_idx_addr);
}

static inline void print_t_l1_entry_idx_addr(void *l1_entry_addr)
{
    printf("L2 Entry addr: %p\n", l1_entry_addr);
}

static inline void qemu_load(TCGTemp *t_addr, TCGTemp *t_val, uintptr_t offset, TCGOp *op_in, TCGContext *tcg_ctx)
{
    TCGOp * op;

    preserve_op_load(t_addr, op_in, tcg_ctx);
    preserve_op_load(t_val, op_in, tcg_ctx);

    // compute index for L1 page

    TCGTemp *t_l1_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_mov(t_l1_page_idx, t_addr, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp *t_l1_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_shr_bit, L1_PAGE_BITS + L2_PAGE_BITS, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx, t_l1_page_idx, t_l1_shr_bit, 0, 0, 1, SHR, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l1_shr_bit);

    // check whether L2 page is allocated for that index

    TCGTemp *t_l1_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_page, (uintptr_t)&s_memory, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp *t_l1_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void *) == 8); // 2^3 = 8
    tcg_movi(t_l1_page_idx_addr, (uintptr_t)3, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx, t_l1_page_idx_addr, 0, 0, 0, SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx_addr, t_l1_page, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l1_page);

    TCGTemp *t_l2_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGLabel *label_l2_page_is_allocated = gen_new_label();
    tcg_brcond(label_l2_page_is_allocated, t_l2_page, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    // if not, allocate L2 page
    add_void_call_1(allocate_l2_page, t_l1_page_idx, op_in, &op, tcg_ctx);
    // mark since it will preserve regs, marking temps as TS_VAL_MEM
    // however this is done only when the helper is executed
    // and its execution depends on the branch condiion!
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l1_page_idx);

    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 1, 0, 1, sizeof(uintptr_t), op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l1_page_idx_addr);

    tcg_set_label(label_l2_page_is_allocated, op_in, NULL, tcg_ctx);

    //add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry, op_in, NULL, tcg_ctx);

    // compute index for L2 page
    TCGTemp *t_l2_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_mov(t_l2_page_idx, t_addr, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp *t_l2_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_shr_bit, L2_PAGE_BITS, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_shr_bit, 0, 0, 1, SHR, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l2_shr_bit);

    TCGTemp *t_l2_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_and_bit, 0xFFFF, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_and_bit, 0, 0, 1, AND, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l2_and_bit);

    // check whether L2 page is allocated for that index

    TCGTemp *t_l2_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void *) == 8); // 2^3 = 8
    tcg_movi(t_l2_page_idx_addr, (uintptr_t)3, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx, t_l2_page_idx_addr, 0, 1, 0, SHL, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l2_page_idx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx_addr, t_l2_page, 0, 0, 0, ADD, op_in, NULL, tcg_ctx);

    //add_void_call_1(print_t_l1_entry_idx_addr, t_l2_page, op_in, NULL, tcg_ctx);

    TCGTemp *t_l3_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGLabel *label_l3_page_is_allocated = gen_new_label();
    tcg_brcond(label_l3_page_is_allocated, t_l3_page, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    add_void_call_1(allocate_l3_page, t_l2_page_idx_addr, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 1, 0, 1, sizeof(uintptr_t), op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l2_page_idx_addr);

    tcg_set_label(label_l3_page_is_allocated, op_in, NULL, tcg_ctx);

    // compute index for L3 page

    TCGTemp *t_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_mov(t_l3_page_idx, t_addr, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp *t_l3_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l3_and_bit, 0xFFFF, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_l3_and_bit, 0, 0, 1, AND, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l3_and_bit);

    // compute the address of the Expr in the page

    TCGTemp *t_l3_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void *) == 8); // 2^3 = 8
    tcg_movi(t_l3_page_idx_addr, (uintptr_t)3, 0, 1, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_l3_page_idx_addr, 0, 1, 0, SHL, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l3_page_idx);

    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx_addr, t_l3_page, 0, 0, 0, ADD, op_in, NULL, tcg_ctx);

    // check whether there is an Expr at that address

    TCGTemp *t_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l3_page_idx_addr, t_expr, 0, 1, 0, 1, sizeof(uintptr_t), op_in, &op, tcg_ctx);
    tcg_temp_free_internal(t_l3_page_idx_addr);

    TCGLabel *label_op_is_const = gen_new_label();
    tcg_brcond(label_op_is_const, t_expr, t_zero, TCG_COND_EQ, 0, 0, op_in, NULL, tcg_ctx);

    // there is an expression, assign it to the t_dst
    TCGTemp *t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&stemps[temp_idx(t_val)], 0, 1, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_expr, 0, 1, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_to);

    tcg_set_label(label_op_is_const, op_in, NULL, tcg_ctx);

    // clean up
    tcg_temp_free_internal(t_zero);
}

static inline void mark_temp_as_in_use(TCGTemp *t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 1;
}

static inline void mark_temp_as_free(TCGTemp *t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 0;
}

void parse_translation_block(TranslationBlock *tb, uintptr_t pc, uint8_t *tb_code, TCGContext *tcg_ctx)
{

    if (pc < 0x40054d || pc > 0x400578) // boundary of foo function
        return;

    int instrument = 0;

    TCGOp *op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        switch (op->opc)
        {

        case INDEX_op_insn_start:
            if (pc < 0x40054d || pc > 0x400578)
                instrument = 0;
            else
                instrument = 1;

            printf("Instrumenting %lx\n", op->args[0]);
            if (op->args[0] == 0x40054d)
                make_reg_symbolic("rdi", op, tcg_ctx);
            break;

        case INDEX_op_set_label:
            break;

        // moving a constant into a temp does not create symbolic exprs
        case INDEX_op_movi_i64:
        case INDEX_op_movi_i32:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            break;

        // we always move exprs between temps, avoiding any check on the source
        // ToDo: branchless but more expensive?
        case INDEX_op_mov_i64:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            if (instrument)
            {
                TCGTemp *from = arg_temp(op->args[1]);
                TCGTemp *to = arg_temp(op->args[0]);
                move_temp(temp_idx(from), temp_idx(to), op, tcg_ctx);
            }
            break;

        case INDEX_op_add_i64:;
            OPKIND bin_opkind = ADD;
        case INDEX_op_sub_i64:
            bin_opkind = SUB;
        case INDEX_op_mul_i64:
            bin_opkind = MUL;
        case INDEX_op_div_i64:
            bin_opkind = DIV;
        case INDEX_op_divu_i64:
            bin_opkind = DIVU;
        case INDEX_op_rem_i64:
            bin_opkind = REM;
        case INDEX_op_remu_i64:
            bin_opkind = REMU;
        case INDEX_op_and_i64:
            bin_opkind = AND;
        case INDEX_op_or_i64:
            bin_opkind = OR;
        case INDEX_op_xor_i64:
            bin_opkind = XOR;
        case INDEX_op_shl_i64:
            bin_opkind = SHL;
        case INDEX_op_shr_i64:
            bin_opkind = SHR;
        case INDEX_op_sar_i64:
            bin_opkind = SAR;
        case INDEX_op_rotl_i64:
            bin_opkind = ROTL;
        case INDEX_op_rotr_i64:
            bin_opkind = ROTR;

            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            mark_temp_as_in_use(arg_temp(op->args[2]));
            if (instrument)
            {
                TCGTemp *t_out = arg_temp(op->args[0]);
                TCGTemp *t_a = arg_temp(op->args[1]);
                TCGTemp *t_b = arg_temp(op->args[2]);
                binary_op(bin_opkind, t_out, t_a, t_b, op, tcg_ctx);
            }
            break;

        case INDEX_op_discard:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            if (instrument && 0)
            {
                TCGTemp *t = arg_temp(op->args[0]);
                clear_temp(temp_idx(t), op, tcg_ctx);
            }
            break;

        case INDEX_op_qemu_st_i64:
            if (instrument)
            {
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                TCGTemp *t_val = arg_temp(op->args[0]);
                TCGTemp *t_ptr = arg_temp(op->args[1]);
                uintptr_t offset = (uintptr_t)op->args[3];
                qemu_load(t_ptr, t_val, offset, op, tcg_ctx);
            }
            break;

        default:;
            const TCGOpDef *def = &tcg_op_defs[op->opc];
            printf("Unhandled TCG instruction: %s\n", def->name);
        }

        // mark as free any temp that was dead at this instruction
        unsigned life = op->life;
        life /= DEAD_ARG;
        if (life)
        {
            for (int i = 0; life; ++i, life >>= 1)
                if (life & 1)
                    mark_temp_as_free(arg_temp(op->args[i]));
        }
    }
}