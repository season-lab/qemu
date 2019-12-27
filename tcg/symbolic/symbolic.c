#include <stdio.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "symbolic.h"
#include "qemu/bitops.h"

#include "config.h"

//#define SYMBOLIC_DEBUG

typedef enum OPKIND
{
    RESERVED,
    // op1 is used to store the value or id
    IS_CONST, // constants could also be embedded within an operand
    IS_SYMBOLIC,
    // unary
    NEG,
    // binary
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
    ROTR,
    //
    EQ,
    NE,
    // signed
    LT,
    LE,
    GE,
    GT,
    // unsigned
    LTU,
    LEU,
    GEU,
    GTU,
    // binary
    ZEXT, // ZEXT(arg0, n): zero-extend arg0 from the n-1 msb bits
    SEXT, // SEXT(arg0, n): sign-extend arg0 from the n-1 msb bits
    // binary
    CONCAT8,  // CONCAT8(arg0, arg1): concat one byte (arg1) to arg0
    EXTRACT8, // EXTRACT8(arg0, i): extract i-th byte from arg0
    // ternary
    DEPOSIT,  // DEPOSIT(arg0, arg1, arg2, pos, len):
              //    arg0 = (arg1 & ~MASK(pos, len)) | ((arg2 << pos) & MASK(pos, len))
              // where: MASK(pos, len) build a mask of bits, where len bits are set to
              // one starting at position 8 (going towards msb).
              // e.g., MASK(8, 4) = 0x0f00
    EXTRACT,  // EXTRACT(arg0, arg1, pos, len):
              //    arg0 = (arg1 << (N_BITS-(pos+len))) >> (N_BITS-len)
              // e.g., EXTRACT(arg0, arg1, 8, 4):
              //  when N_BITS=32 then arg0 = (arg1 << 20) >> 28
    SEXTRACT, // same as EXTRACT but using arithmetic shift
} OPKIND;

typedef enum EXTENDKIND
{
    ZEXT_8,
    ZEXT_16,
    ZEXT_32,
    //
    SEXT_8,
    SEXT_16,
    SEXT_32,
} EXTENDKIND;

typedef struct Expr
{
    struct Expr *op1;
    struct Expr *op2;
    struct Expr *op3;
    uint8_t opkind;
    uint8_t op1_is_const;
    uint8_t op2_is_const;
    uint8_t op3_is_const;
} Expr;

// symbolic temps
Expr *s_temps[TCG_MAX_TEMPS] = {0};

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

// path constraints
Expr *path_constraints = NULL;

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

#define MARK_TEMP_AS_ALLOCATED(t) \
    do                            \
    {                             \
        t->temp_allocated = 1;    \
    } while (0)
#define MARK_TEMP_AS_NOT_ALLOCATED(t) \
    do                                \
    {                                 \
        t->temp_allocated = 0;        \
    } while (0)

#ifdef SYMBOLIC_DEBUG
#define debug_printf(...)    \
    do                       \
    {                        \
        printf(__VA_ARGS__); \
    } while (0);
#else
#define debug_printf(...) \
    do                    \
    {                     \
    } while (0);
#endif

static inline int count_free_temps(TCGContext *tcg_ctx)
{
    int count = 0;
    for (size_t j = 0; j < BITS_TO_LONGS(TCG_MAX_TEMPS); j++)
        for (size_t i = 0; i < BITS_PER_LONG; i++)
            count += test_bit(i, &tcg_ctx->free_temps[TCG_TYPE_I64].l[j]);
    return count;
}

// FixMe: shitty way to hide the variable...
#define SAVE_TEMPS_COUNT(s) int temps_initial_count = s->nb_temps - count_free_temps(s);
#define CHECK_TEMPS_COUNT_WITH_DELTA(s, delta) assert(temps_initial_count == s->nb_temps - count_free_temps(s) + delta);
#define CHECK_TEMPS_COUNT(s) assert(temps_initial_count == s->nb_temps - count_free_temps(s));

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
    assert(type == TCG_TYPE_I64); // ToDo: validate other types
    TCGTemp *r = NULL;
    TCGTemp *conflicting_temps[TCG_MAX_TEMPS];
    size_t conflicting_temps_count = 0;
    while (!r)
    {
        TCGTemp *current = tcg_temp_new_internal(type, false);
        size_t idx = temp_idx(current);
        assert(idx < TCG_MAX_TEMPS);
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

// see tcg_gen_callN in tgc.c
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

// see tcg_gen_callN in tgc.c
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

// see tcg_gen_callN in tgc.c
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

// see tcg_gen_callN in tgc.c
static inline void add_void_call_4(void *f,
                                   TCGTemp *arg0, TCGTemp *arg1,
                                   TCGTemp *arg2, TCGTemp *arg3,
                                   TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg0);
    op->args[1] = temp_arg(arg1);
    op->args[2] = temp_arg(arg2);
    op->args[3] = temp_arg(arg3);
    op->args[4] = (uintptr_t)f;
    op->args[5] = 0;     // flags
    TCGOP_CALLI(op) = 4; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_6(void *f,
                                   TCGTemp *arg0, TCGTemp *arg1,
                                   TCGTemp *arg2, TCGTemp *arg3,
                                   TCGTemp *arg4, TCGTemp *arg5,
                                   TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);
    assert(arg4->temp_allocated);
    assert(arg5->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg0);
    op->args[1] = temp_arg(arg1);
    op->args[2] = temp_arg(arg2);
    op->args[3] = temp_arg(arg3);
    op->args[4] = temp_arg(arg4);
    op->args[5] = temp_arg(arg5);
    op->args[6] = (uintptr_t)f;
    op->args[7] = 0;     // flags
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
    //printf("RDI is at %p\n", &stemps[r]);
    debug_printf("RDI is %ssymbolic\n", s_temps[12]->opkind == IS_SYMBOLIC ? "" : "not ");
}

static inline void new_symbolic_expr(void)
{
    Expr *e = new_expr();
    e->opkind = IS_SYMBOLIC;
    e->op1 = 0; // FixMe: assign id based on the specific symbolic input
    debug_printf("Marking expr%lu as symbolic\n", GET_EXPR_IDX(e));
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
                            uint8_t is_ts_dead,
                            TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts->temp_allocated);

    TCGOpcode opc = INDEX_op_movi_i64;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts);
    assert(!is_ts_dead);

    op->args[1] = (uintptr_t)const_val;

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
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    if (op_out)
        *op_out = op;
}

static inline void tcg_cmov(TCGTemp *ts_out,
                            TCGTemp *ts_a, TCGTemp *ts_b,
                            TCGTemp *ts_true, TCGTemp *ts_false, TCGCond cond,
                            uint8_t is_ts_out_dead, uint8_t is_ts_a_dead, uint8_t is_ts_b_dead,
                            uint8_t is_ts_true_dead, uint8_t is_ts_false_dead,
                            TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    assert(ts_out->temp_allocated);
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_true->temp_allocated);
    assert(ts_false->temp_allocated);

    TCGOpcode opc = INDEX_op_movcond_i64;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    // ret, c1, c2, v1, v2, cond

    op->args[0] = temp_arg(ts_out);
    assert(!is_ts_out_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead)
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_a_dead)
    {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    op->args[3] = temp_arg(ts_true);
    if (is_ts_true_dead)
    {
        mark_dead_arg_temp(op, 3);
        tcg_temp_free_internal(ts_true);
    }

    op->args[4] = temp_arg(ts_false);
    if (is_ts_false_dead)
    {
        mark_dead_arg_temp(op, 4);
        tcg_temp_free_internal(ts_false);
    }

    op->args[5] = cond;

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

    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_c);
    assert(!is_ts_c_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead)
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_b_dead)
    {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    if (op_out)
        *op_out = op;
}

static inline void tcg_load_n(TCGTemp *ts_from, TCGTemp *ts_to, uintptr_t offset,
                              uint8_t is_ts_from_dead, uint8_t is_ts_to_dead,
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
    case 1:
        opc = INDEX_op_ld8u_i64;
        break;
    default:
        tcg_abort();
    }

    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead)
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    op->args[2] = offset;

    if (op_out)
        *op_out = op;
}

static inline void tcg_store_n(TCGTemp *ts_to, TCGTemp *ts_val, uintptr_t offset,
                               uint8_t is_ts_to_dead, uint8_t is_ts_val_dead,
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
    {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_val);
    }

    op->args[1] = temp_arg(ts_to);
    if (is_ts_to_dead)
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_to);
    }

    op->args[2] = offset;

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
    {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_a);
    }

    op->args[1] = temp_arg(ts_b);
    if (is_ts_b_dead)
    {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_b);
    }

    op->args[2] = cond;
    op->args[3] = label_arg(label);

    if (op_out)
        *op_out = op;
}

// branch to label (always)
static inline void tcg_br(TCGLabel *label,
                          TCGOp *op_in, TCGOp **op_out, TCGContext *tcg_ctx)
{
    label->refs++;
    TCGOpcode opc = INDEX_op_br;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label);

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

static inline void print_something(char *str)
{
    debug_printf("%s\n", str);
}

// the string has to be statically allocated, otherwise it will crash!
static inline void tcg_print_const_str(const char *str, TCGOp *op_in, TCGOp **op, TCGContext *tcg_ctx)
{
    TCGTemp *t_str = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_str, (uintptr_t)str, 0, op_in, NULL, tcg_ctx);
    add_void_call_1(print_something, t_str, op_in, op, tcg_ctx);
    tcg_temp_free_internal(t_str);
}

static inline void init_reg(size_t reg, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(reg < TCG_MAX_TEMPS);
    debug_printf("Setting expr of reg %lu\n", reg);

    TCGTemp *t_last_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_last_expr, (uintptr_t)&last_expr, 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_last_expr, t_last_expr, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_dst, (uintptr_t)&s_temps[reg], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_dst, t_last_expr, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void make_reg_symbolic(const char *reg_name, TCGOp *op, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    for (int i = 0; i < TCG_TARGET_NB_REGS; i++)
    {
        TCGTemp *t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0)
        {
            debug_printf("Marking %s (id=%d) as symbolic\n", t->name, i);
            add_void_call_0(new_symbolic_expr, op, NULL, tcg_ctx);
            init_reg(i, op, tcg_ctx);
            add_void_call_0(print_reg, op, NULL, tcg_ctx);
        }
    }

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void move_temp(size_t from, size_t to, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp *t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_from, 0, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void clear_temp(size_t idx, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    assert(idx < TCG_MAX_TEMPS);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t, (uintptr_t)&s_temps[idx], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t, t_zero, 0, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_new_expr(TCGTemp *t_out, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGOp *op;

    add_void_call_0(check_pool_expr_capacity, op_in, &op, tcg_ctx); // ToDo: make inline check
    mark_insn_as_instrumentation(op);

    TCGTemp *t_next_free_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_next_free_expr_addr, (uintptr_t)&next_free_expr, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_next_free_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_next_free_expr_addr, t_next_free_expr, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_mov(t_out, t_next_free_expr, 0, 0, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op); // required to handle a t_out which already has a reg allocated

    TCGTemp *t_expr_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_expr_size, sizeof(Expr), 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_next_free_expr, t_next_free_expr, t_expr_size, 0, 0, 0, ADD, op_in, NULL, tcg_ctx);

    tcg_temp_free_internal(t_expr_size);

    tcg_store_n(t_next_free_expr_addr, t_next_free_expr, 0, 1, 1, sizeof(void *), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline const char *opkind_to_str(uint8_t opkind)
{
    switch (opkind)
    {
    case ADD:
        return "+";
    case SUB:
        return "-";

    case AND:
        return "&";
    case OR:
        return "|";

    case EQ:
        return "==";
    case NE:
        return "!=";

    case LT:
        return "<";
    case LE:
        return "<=";
    case GE:
        return ">=";
    case GT:
        return ">";

    case LTU:
        return "<u";
    case LEU:
        return "<=u";
    case GEU:
        return ">=u";
    case GTU:
        return ">u";

    case ZEXT:
        return "ZERO-EXTEND";
    case SEXT:
        return "SIGN-EXTEND";

    case EXTRACT8:
        return "EXTRACT";
    case CONCAT8:
        return "CONCAT";

    default:
        printf("\nstr(opkind=%u) is unknown\n", opkind);
        tcg_abort();
    }
}

#define MAX_PRINT_CHECK 1024
static uint8_t printed[MAX_PRINT_CHECK];

static inline void print_expr_internal(Expr *expr, uint8_t reset)
{
    if (reset)
        for (size_t i = 0; i < MAX_PRINT_CHECK; i++)
            printed[i] = 0;

    printf("expr:");
    //printf(" addr=%p", expr);
    printf(" id=%lu", GET_EXPR_IDX(expr));
    if (expr)
    {
        printf(" is_symbolic_input=%u", expr->opkind == IS_SYMBOLIC);
        printf(" op1_is_const=%u", expr->op1_is_const);
        printf(" op2_is_const=%u", expr->op2_is_const);
        if (expr->opkind == IS_SYMBOLIC)
            printf(" INPUT_%lu\n", (uintptr_t)expr->op1);
        else if (expr->opkind == IS_CONST)
            printf(" 0x%lu\n", (uintptr_t)expr->op1);
        else
        {

            if (expr->op1_is_const || expr->op1 == NULL)
                printf(" 0x%lx", (uintptr_t)expr->op1);
            else
                printf(" E_%lu", GET_EXPR_IDX(expr->op1));

            printf(" %s", opkind_to_str(expr->opkind));

            if (expr->op2_is_const || expr->opkind == EXTRACT8 || expr->op2 == NULL)
                printf(" 0x%lx", (uintptr_t)expr->op2);
            else
                printf(" E_%lu", GET_EXPR_IDX(expr->op2));
            printf("\n");

            // FixMe: this makes a mess

            if (!expr->op1_is_const && expr->op1 != NULL)
            {
                assert(GET_EXPR_IDX(expr->op1) < MAX_PRINT_CHECK);
                if (!printed[GET_EXPR_IDX(expr->op1)])
                {
                    printf("E_%lu:: ", GET_EXPR_IDX(expr->op1));
                    print_expr_internal(expr->op1, 0);
                    printed[GET_EXPR_IDX(expr->op1)] = 1;
                }
                if (expr->op1 == NULL)
                    assert(expr->op2);
            }

            if (!expr->op2_is_const && expr->opkind != EXTRACT8 && expr->op2 != NULL)
            {
                assert(GET_EXPR_IDX(expr->op2) < MAX_PRINT_CHECK);
                if (!printed[GET_EXPR_IDX(expr->op2)])
                {
                    printf("E_%lu:: ", GET_EXPR_IDX(expr->op2));
                    print_expr_internal(expr->op2, 0);
                    printed[GET_EXPR_IDX(expr->op2)] = 1;
                }
                if (expr->op2 == NULL)
                    assert(expr->op1);
            }
        }
    }
    else
    {
        printf("\n");
    }
}

static inline void print_expr(Expr *expr)
{
    printf("\n");
    print_expr_internal(expr, 1);
}

// When adding instrumentation with branches and when accessing
// the operands contents, TCG may move temp loads (i.e., loading
// content of the temp operand from memory) within the branching
// code (which is not always executed), possibly leading to SIGSEGV.
// To avoid this issue, we insert fake uses for each temp operand
// before any branching code, to make temp loads branchless.
static inline void preserve_op_load(TCGTemp *t, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGTemp *t_dummy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t);
    tcg_mov(t_dummy, t, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t);
    // this is needed since out temp cannot be marked as dead in tcg_mov
    tcg_temp_free_internal(t_dummy);
    CHECK_TEMPS_COUNT(tcg_ctx);
}

// Binary operation: t_out = t_a opkind t_b
static inline void binary_op(OPKIND opkind, TCGTemp *t_op_out, TCGTemp *t_op_a, TCGTemp *t_op_b, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    //TCGOp *op;

    size_t out = temp_idx(t_op_out);
    size_t a = temp_idx(t_op_a);
    size_t b = temp_idx(t_op_b);

    assert(out < TCG_MAX_TEMPS);
    assert(a < TCG_MAX_TEMPS);
    assert(b < TCG_MAX_TEMPS);

    preserve_op_load(t_op_a, op_in, tcg_ctx);
    preserve_op_load(t_op_b, op_in, tcg_ctx);

    // check if both t_a and t_b are concrete
    // if this is the case, then mark dest as concrete

    TCGLabel *label_both_concrete = gen_new_label();

    TCGTemp *t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    //tcg_print_const_str("Checking binary op", op_in, &op, tcg_ctx);

    //add_void_call_1(print_expr, t_a, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    TCGTemp *t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[b], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    //add_void_call_1(print_expr, t_b, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    //tcg_print_const_str("Checking binary op: DONE", op_in, &op, tcg_ctx);

    TCGTemp *t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp *t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL, tcg_ctx); // force TCG to allocate the temp into a reg

    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in, NULL, tcg_ctx);

    allocate_new_expr(t_out, op_in, tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel *label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel *label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

#if 0
    tcg_print_const_str("Binary op:", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_print_const_str("Binary op: DONE", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    //add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp *t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[out], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_l2_page(uintptr_t l1_entry_idx)
{
    assert(l1_entry_idx < 1 << L1_PAGE_BITS);

    debug_printf("Allocating l2 page at idx %lu\n", l1_entry_idx);
    s_memory.table.entries[l1_entry_idx] = g_malloc0(sizeof(l2_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l1_entry_idx_addr=%p l2_page_addr=%p\n", &s_memory.table.entries[l1_entry_idx], s_memory.table.entries[l1_entry_idx]);
}

static inline void allocate_l3_page(void **l2_page_idx_addr)
{
    debug_printf("Allocating l3 page at l2_page_idx_addr=%p\n", l2_page_idx_addr);
    *l2_page_idx_addr = g_malloc0(sizeof(l3_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l3_page_addr=%p\n", *l2_page_idx_addr);
}

static inline void print_value(uintptr_t value)
{
    debug_printf("V: %lx\n", value);
}

static inline void print_t_l1_entry_idx_addr(void *l1_entry_addr)
{
    debug_printf("L2 Entry addr: %p\n", l1_entry_addr);
}

static inline void print_t_l3_entry_idx_addr(void *l3_entry_addr)
{
    debug_printf("L3 Entry addr: %p\n", l3_entry_addr);
}

static inline void failure_cross_page_access(void)
{
    printf("A memory access is crossing a L3 page: not yet supported.\n");
    tcg_abort();
}

#define EARLY_EXIT_CONST ((TCGTemp *)1)

static inline void get_expr_addr_for_addr(TCGTemp *t_addr, TCGTemp **t_expr_addr, uintptr_t offset, size_t size, TCGTemp *early_exit, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp *op;

    TCGTemp *t_addr_with_offset = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_addr_with_offset, offset, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_binop(t_addr_with_offset, t_addr, t_addr_with_offset, 0, 0, 0, ADD, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp *t_l3_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    if (early_exit)
    {
        TCGTemp *t_null = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_null, (uintptr_t)0, 0, op_in, NULL, tcg_ctx);
        tcg_binop(t_l3_page_idx_addr, t_null, t_null, 0, 1, 0, XOR, op_in, &op, tcg_ctx); // force TCG to allocate the temp into a reg
        //add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL, tcg_ctx);
    }
    *t_expr_addr = t_l3_page_idx_addr;

    // compute index for L1 page

    TCGTemp *t_l1_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l1_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_l1_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_shr_bit, L1_PAGE_BITS + L2_PAGE_BITS, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx, t_l1_page_idx, t_l1_shr_bit, 0, 0, 1, SHR, op_in, NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp *t_l1_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_page, (uintptr_t)&s_memory, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_l1_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void *) == 8); // 2^3 = 8
    tcg_movi(t_l1_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx, t_l1_page_idx_addr, 0, 0, 0, SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx_addr, t_l1_page, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l1_page);

    TCGTemp *t_l2_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGLabel *label_l2_page_is_allocated = gen_new_label();
    tcg_brcond(label_l2_page_is_allocated, t_l2_page, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    // early_exit?
    TCGLabel *label_early_exit = NULL;
    if (early_exit)
    {
        label_early_exit = gen_new_label();
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0, op_in, NULL, tcg_ctx);
    }

    // if not, allocate L2 page
    add_void_call_1(allocate_l2_page, t_l1_page_idx, op_in, &op, tcg_ctx);
    // mark since it will preserve regs, marking temps as TS_VAL_MEM
    // however this is done only when the helper is executed
    // and its execution depends on the branch condiion!
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l1_page_idx);

    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 1, 0, sizeof(uintptr_t), op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l2_page_is_allocated, op_in, NULL, tcg_ctx);

    //add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry, op_in, NULL, tcg_ctx);

    // compute index for L2 page
    TCGTemp *t_l2_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l2_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    // FixMe: mask higher bits

    TCGTemp *t_l2_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_shr_bit, L2_PAGE_BITS, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_shr_bit, 0, 0, 1, SHR, op_in, NULL, tcg_ctx);

    TCGTemp *t_l2_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_and_bit, 0, 0, 1, AND, op_in, NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp *t_l2_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void *) == 8); // 2^3 = 8
    tcg_movi(t_l2_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx, t_l2_page_idx_addr, 0, 1, 0, SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx_addr, t_l2_page, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);

    TCGTemp *t_l3_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGLabel *label_l3_page_is_allocated = gen_new_label();
    tcg_brcond(label_l3_page_is_allocated, t_l3_page, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    // early_exit?
    if (early_exit)
    {
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0, op_in, NULL, tcg_ctx);
    }
    tcg_temp_free_internal(t_zero);

    add_void_call_1(allocate_l3_page, t_l2_page_idx_addr, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 1, 0, sizeof(uintptr_t), op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l3_page_is_allocated, op_in, NULL, tcg_ctx);

    // compute index for L3 page

    TCGTemp *t_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l3_page_idx, t_addr_with_offset, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp *t_l3_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l3_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_l3_and_bit, 0, 0, 1, AND, op_in, NULL, tcg_ctx);

    // compute the address of the Expr in the page

    assert(sizeof(void *) == 8); // 2^3 = 8
    TCGTemp *t_three = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_three, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_three, 0, 0, 1, SHL, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    //tcg_movi(t_l3_page_idx_addr, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);
    //tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_l3_page_idx_addr, 0, 0, 0, SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx_addr, t_l3_page, 0, 0, 1, ADD, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    // check that t_l3_page_idx_addr + size is still within the L3 page, otherwise fail
    // FixMe: handle cross page store/loading

    TCGTemp *t_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_size, size, 0, op_in, NULL, tcg_ctx);
    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_size, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);
    TCGTemp *t_max_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_max_l3_page_idx, 1 << L3_PAGE_BITS, 0, op_in, NULL, tcg_ctx);
    TCGLabel *label_no_cross_page_access = gen_new_label();
    tcg_brcond(label_no_cross_page_access, t_l3_page_idx, t_max_l3_page_idx, TCG_COND_LT, 1, 1, op_in, NULL, tcg_ctx);
    add_void_call_0(failure_cross_page_access, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_set_label(label_no_cross_page_access, op_in, NULL, tcg_ctx);

    if (early_exit)
    {
        tcg_set_label(label_early_exit, op_in, NULL, tcg_ctx);
        //add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL, tcg_ctx);
    }

    CHECK_TEMPS_COUNT_WITH_DELTA(tcg_ctx, -1); // t_expr_addr is allocated here, but freed by the caller!
}

static inline size_t get_mem_op_size(TCGMemOp mem_op)
{
    switch (mem_op & MO_SIZE)
    {
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

static inline void qemu_load_helper (
    uintptr_t orig_addr,
    uintptr_t mem_op_uidx,
    uintptr_t addr_idx,
    uintptr_t val_idx)
{
    TCGMemOp mem_op = get_memop(mem_op_uidx);
    uintptr_t offset = (uintptr_t)get_mmuidx(mem_op_uidx);

    assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    //printf("Loading %lu bytes from %p at offset %lu\n", size, (void *)orig_addr, offset);

    uintptr_t addr = orig_addr + offset;

    uintptr_t l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t *l2_page = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t *l3_page = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    assert(size <= 8);
    Expr *exprs[8] = {NULL};
    uint8_t expr_is_not_null = 0;
    for (size_t i = 0; i < size; i++)
    {
        exprs[i] = l3_page->entries[l3_page_idx + i];
        expr_is_not_null = expr_is_not_null | (exprs[i] != 0);
    }

    if (expr_is_not_null == 0) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    Expr *e = NULL;
    for (size_t i = 0; i < size; i++)
    {
        if (i == 0)
        {
            if (exprs[i] == NULL)
            {
                // allocate a new expr for the concrete value
                e = new_expr();
                e->opkind = IS_CONST;
                uint8_t *byte_addr = ((uint8_t *)addr) + i;
                uint8_t byte = *byte_addr;
                e->op1 = (Expr *)((uintptr_t)byte);
            }
            else
                e = exprs[i];
        }
        else
        {
            Expr *n_expr = new_expr();
            n_expr->opkind = CONCAT8;

            if (exprs[i] == NULL)
            {
                // fetch the concrete value, embed it in the expr
                uint8_t *byte_addr = ((uint8_t *)addr) + i;
                uint8_t byte = *byte_addr;
                n_expr->op1 = (Expr *)((uintptr_t)byte);
                n_expr->op1_is_const = 1;
            }
            else
            {
                e->op1 = exprs[i];
            }

            n_expr->op2 = e;

            e = n_expr;
        }
    }

    s_temps[val_idx] = e;
}

static inline void qemu_load(TCGTemp *t_addr, TCGTemp *t_val, uintptr_t offset, TCGMemOp mem_op, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(t_val->base_type == TCG_TYPE_TL);
    assert(t_val->base_type == TCG_TYPE_I64); // FixMe: support other types
    assert((mem_op & MO_BE) == 0);            // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    preserve_op_load(t_addr, op_in, tcg_ctx);
    preserve_op_load(t_val, op_in, tcg_ctx);

    TCGOp *op;

    TCGTemp *t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size, EARLY_EXIT_CONST /* FixMe: hack */, op_in, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel *label_end = gen_new_label();

    // early exit
    TCGLabel *label_write_null = gen_new_label();
    tcg_brcond(label_write_null, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0, op_in, NULL, tcg_ctx);

    // build expr, if all bytes are concrete goto to label_write_null

    TCGTemp *t_expr_is_null = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_expr_is_null, 0, 0, op_in, NULL, tcg_ctx);

    assert(size <= 8);
    TCGTemp *t_exprs[8] = {NULL};

    for (size_t i = 0; i < size; i++)
    {
        t_exprs[i] = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_load_n(t_l3_page_idx_addr, t_exprs[i], sizeof(Expr *) * i,
                   i == size - 1, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
        tcg_binop(t_expr_is_null, t_expr_is_null, t_exprs[i], 0, 0, 0, OR, op_in, NULL, tcg_ctx);
    }

    tcg_brcond(label_write_null, t_expr_is_null, t_zero, TCG_COND_EQ, 1, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_expr = NULL;
    for (size_t i = 0; i < size; i++)
    {
        if (i == 0)
        {
            // if expr is NULL, use the concrete value
            TCGLabel *label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

            allocate_new_expr(t_exprs[i], op_in, tcg_ctx);

            TCGTemp *t_mem_value = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp *t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp *t_mem_value_addr_offset = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL, tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr, t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_store_n(t_exprs[i], t_mem_value, offsetof(Expr, op1), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

            TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, IS_CONST, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);

            t_expr = t_exprs[i];
            t_exprs[i] = NULL;
        }
        else
        {
            TCGTemp *t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
            // FixMe: pre-allocate size exprs outside the loop
            allocate_new_expr(t_new_expr, op_in, tcg_ctx);

            TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, CONCAT8, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op1), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

            // if expr is NULL, use the concrete value

            TCGLabel *label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

            TCGTemp *t_mem_value = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp *t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp *t_mem_value_addr_offset = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL, tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr, t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL, tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t), op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_mem_value, 0, 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

            TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_one, offsetof(Expr, op1_is_const), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_exprs[i], offsetof(Expr, op2), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

            //add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
            //mark_insn_as_instrumentation(op);

            t_expr = t_new_expr;
            t_exprs[i] = NULL;
        }
    }

    // if size is less than sizeof(TCG_TYPE_TL), we may have to
    // zero-extend or sign-extend
    if (size < 8) // FixMe: other archs
    {
        TCGTemp *t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        uintptr_t opkind = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
        tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op1), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

        TCGTemp *t_extend_bit = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_extend_bit, 8 * size, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_extend_bit, offsetof(Expr, op2), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

        TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_one, offsetof(Expr, op2_is_const), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

        //add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        //mark_insn_as_instrumentation(op);

        t_expr = t_new_expr;
    }

    //add_void_call_1(print_expr, t_expr, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    // write expr to destination temp
    TCGTemp *t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op, tcg_ctx);
    tcg_store_n(t_to, t_expr, 0, 1, 1, sizeof(void *), op_in, &op, tcg_ctx);
    tcg_br(label_end, op_in, NULL, tcg_ctx);

    // store NULL into destination temp
    tcg_set_label(label_write_null, op_in, NULL, tcg_ctx);
    for (size_t i = 0; i < size; i++)
        if (t_exprs[i])
            tcg_temp_free_internal(t_exprs[i]);
    t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op, tcg_ctx);
    tcg_store_n(t_to, t_zero, 0, 1, 1, sizeof(void *), op_in, &op, tcg_ctx);

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_store_helper (
    uintptr_t orig_addr,
    uintptr_t mem_op_uidx,
    uintptr_t addr_idx,
    uintptr_t val_idx)
{
    TCGMemOp mem_op = get_memop(mem_op_uidx);
    uintptr_t offset = (uintptr_t)get_mmuidx(mem_op_uidx);

    assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    //printf("Loading %lu bytes from %p at offset %lu\n", size, (void *)orig_addr, offset);

    uintptr_t addr = orig_addr + offset;

    uintptr_t l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t *l2_page = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL)
    {
        if (s_temps[val_idx] == NULL)  // early exit
            return;

        l2_page = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t *l3_page = l2_page->entries[l2_page_idx];
    if (l3_page == NULL)
    {
        if (s_temps[val_idx] == NULL)  // early exit
            return;

        l3_page = g_malloc0(sizeof(l3_page_t));
        l2_page->entries[l2_page_idx] = l3_page;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    if (s_temps[val_idx] == NULL)
    {
        for (size_t i = 0; i < size; i++)
            l3_page->entries[l3_page_idx + i] = NULL;
    }
    else
    {
        for (size_t i = 0; i < size; i++)
        {
            Expr *e = new_expr();
            e->opkind = EXTRACT8;
            e->op1 = s_temps[val_idx];
            e->op2 = (Expr *) i;
            l3_page->entries[l3_page_idx + i] = e;
        }
    }
}

static inline void qemu_store(TCGTemp *t_addr, TCGTemp *t_val, uintptr_t offset, TCGMemOp mem_op, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to store
    size_t size = get_mem_op_size(mem_op);

    TCGOp __attribute__((unused))  *op;

    // check whether val is concrete
    size_t val_idx = temp_idx(t_val);
    TCGTemp *t_val_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_val_expr_addr, (uintptr_t)&s_temps[val_idx], 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_val_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_val_expr_addr, t_val_expr, 0, 1, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    // get location where to store expression
    TCGTemp *t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size, t_val_expr, op_in, tcg_ctx);

    //add_void_call_1(print_expr, t_val_expr, op_in, &op, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel *label_end = gen_new_label();
    // early exit
    tcg_brcond(label_end, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel *label_expr_is_not_concrete = gen_new_label();
    tcg_brcond(label_expr_is_not_concrete, t_val_expr, t_zero, TCG_COND_NE, 0, 1, op_in, NULL, tcg_ctx);

    // write NULL expr for each byte to store
    for (size_t i = 0; i < size; i++)
    {
        // set Expr
        tcg_store_n(t_l3_page_idx_addr, t_val_expr, sizeof(Expr *) * i,
                    0, 0,
                    sizeof(void *), op_in, NULL, tcg_ctx);
    }

    tcg_br(label_end, op_in, NULL, tcg_ctx);

    tcg_set_label(label_expr_is_not_concrete, op_in, NULL, tcg_ctx);

    // write EXT8(expr, index) for each byte to store
    for (size_t i = 0; i < size; i++)
    {
        // build EXTRACT expr
        TCGTemp *t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        // FixMe: pre-allocate size exprs outside the loop
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_opkind, EXTRACT8, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_val_expr, offsetof(Expr, op1), 0, i == size - 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

        TCGTemp *t_index = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_index, i, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_index, offsetof(Expr, op2), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

        //add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        //mark_insn_as_instrumentation(op);

        // set Expr
        tcg_store_n(t_l3_page_idx_addr, t_new_expr, sizeof(Expr *) * i,
                    i == size - 1, 1,
                    sizeof(void *), op_in, NULL, tcg_ctx);
    }

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void extend(TCGTemp *t_op_to, TCGTemp *t_op_from, EXTENDKIND extkind, TCGOp *op_in, TCGContext *tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t to = temp_idx(t_op_to);
    size_t from = temp_idx(t_op_from);

    // check whether t_op_from is concrete
    TCGTemp *t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp *t_out = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_out, t_from, 0, 0, op_in, NULL, tcg_ctx); // this is needed since we need to always overide t_to expr

    TCGLabel *label_op_is_const = gen_new_label();
    tcg_brcond(label_op_is_const, t_from, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL, tcg_ctx);

    // create a ZEXT 32 expr

    //TCGOp *op;
    //tcg_print_const_str("Zero-extending", op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    allocate_new_expr(t_out, op_in, tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    tcg_store_n(t_out, t_from, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    uint8_t opkind;
    uintptr_t opkind_const_param;
    switch (extkind)
    {
    case ZEXT_8:
        opkind = ZEXT;
        opkind_const_param = 8;
        break;
    case ZEXT_16:
        opkind = ZEXT;
        opkind_const_param = 16;
        break;
    case ZEXT_32:
        opkind = ZEXT;
        opkind_const_param = 32;
        break;
    case SEXT_8:
        opkind = SEXT;
        opkind_const_param = 8;
        break;
    case SEXT_16:
        opkind = SEXT;
        opkind_const_param = 16;
        break;
    case SEXT_32:
        opkind = SEXT;
        opkind_const_param = 32;
        break;
    default:
        tcg_abort();
    }

    TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_const_param = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_const_param, opkind_const_param, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_const_param, offsetof(Expr, op2), 0, 1, sizeof(Expr *), op_in, NULL, tcg_ctx);

    TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    //add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);

    tcg_set_label(label_op_is_const, op_in, NULL, tcg_ctx);

    // overide t_op_to expr
    TCGTemp *t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
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

static inline OPKIND get_opkind(TCGOpcode opc)
{
    switch (opc)
    {
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
    default:
        tcg_abort();
    }
}

static inline OPKIND get_opkind_from_cond(TCGCond cond)
{
    switch (cond)
    {
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
    switch (cond)
    {
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
    else
    {
        printf("\nPath constraints:\n");
        print_expr(path_constraints);
        printf("\n");
    }
}

static inline void branch(TCGTemp *t_op_a, TCGTemp *t_op_b, TCGCond cond, TCGOp *op_in, TCGContext *tcg_ctx)
{
    // check if both t_op_a and t_op_b are concrete
    // if this is true, skip any further work

    size_t op_a_idx = temp_idx(t_op_a);
    size_t op_b_idx = temp_idx(t_op_b);

    TCGTemp *t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[op_b_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp *t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel *label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_a_or_b);

#if 0
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // one of them is symbolic, build the expression

    // allocate expr for t_out
    TCGTemp *t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(t_out, op_in, tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    // set expr opkind
    TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    OPKIND opkind = get_opkind_from_cond(cond);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    OPKIND opkind_neg = get_opkind_from_neg_cond(cond);
    TCGTemp *t_opkind_neg = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind_neg, opkind_neg, 0, op_in, NULL, tcg_ctx);
    TCGTemp *t_opkind_actual = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_cmov(t_opkind_actual, t_op_a, t_op_b, t_opkind, t_opkind_neg, cond, 0, 0, 0, 1, 1, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);
    tcg_store_n(t_out, t_opkind_actual, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel *label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0, sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_a);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel *label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_zero);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_one);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
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

    TCGTemp *t_new_pi_expr = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(t_new_pi_expr, op_in, tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, AND, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    TCGTemp *t_pi_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_pi_addr, (uintptr_t)&path_constraints, 0, op_in, NULL, tcg_ctx);

    tcg_store_n(t_new_pi_expr, t_out, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_out);

    TCGTemp *t_old_pi_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_pi_addr, t_old_pi_expr, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_old_pi_expr, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_old_pi_expr);

    tcg_store_n(t_pi_addr, t_new_pi_expr, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_new_pi_expr);
    tcg_temp_free_internal(t_pi_addr);

#ifdef SYMBOLIC_DEBUG
    TCGOp *op;
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);
}

static inline EXTENDKIND get_extend_kind(TCGOpcode opkind)
{
    switch (opkind)
    {
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

static int instrument = 0;
static int first_load = 0;
void parse_translation_block(TranslationBlock *tb, uintptr_t pc, uint8_t *tb_code, TCGContext *tcg_ctx)
{
    //if (pc < 0x40054d || pc > 0x400577) // boundary of foo function
    //    return;

    TCGOp __attribute__((unused)) *op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        switch (op->opc)
        {

        case INDEX_op_insn_start:
            if (instrument == 0 && pc == START)
                instrument = 1;
            else if (instrument == 1 && pc == STOP)
                instrument = 0;

            if (instrument)
            {
                debug_printf("Instrumenting %lx\n", op->args[0]);
                if (op->args[0] == REG_AT)
                    make_reg_symbolic(REG, op, tcg_ctx);
            }
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
        case INDEX_op_rotr_i64:;

            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            mark_temp_as_in_use(arg_temp(op->args[2]));
            if (instrument)
            {
                OPKIND bin_opkind = get_opkind(op->opc);
                TCGTemp *t_out = arg_temp(op->args[0]);
                TCGTemp *t_a = arg_temp(op->args[1]);
                TCGTemp *t_b = arg_temp(op->args[2]);
                binary_op(bin_opkind, t_out, t_a, t_b, op, tcg_ctx);
            }
            break;

        case INDEX_op_discard:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            if (instrument)
            {
                TCGTemp *t = arg_temp(op->args[0]);
                clear_temp(temp_idx(t), op, tcg_ctx);
            }
            break;

        case INDEX_op_qemu_ld_i64:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            if (instrument)
            {
                TCGTemp *t_val = arg_temp(op->args[0]);
                TCGTemp *t_ptr = arg_temp(op->args[1]);
#if 1
                TCGMemOp mem_op = get_memop(op->args[2]);
                uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                qemu_load(t_ptr, t_val, offset, mem_op, op, tcg_ctx);
#else
                MARK_TEMP_AS_ALLOCATED(t_ptr);
                TCGTemp *t_mem_op = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_mem_op, (uintptr_t)op->args[2], 0, op, NULL, tcg_ctx);
                TCGTemp *t_ptr_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op, NULL, tcg_ctx);
                TCGTemp *t_val_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op, NULL, tcg_ctx);
                add_void_call_4(qemu_load_helper,
                                t_ptr, t_mem_op, t_ptr_idx, t_val_idx,
                                op, NULL, tcg_ctx);
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
            if (instrument)
            {
                TCGTemp *t_val = arg_temp(op->args[0]);
                TCGTemp *t_ptr = arg_temp(op->args[1]);
#if 1
                TCGMemOp mem_op = get_memop(op->args[2]);
                uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                qemu_store(t_ptr, t_val, offset, mem_op, op, tcg_ctx);
#else
                MARK_TEMP_AS_ALLOCATED(t_ptr);
                TCGTemp *t_mem_op = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_mem_op, (uintptr_t)op->args[2], 0, op, NULL, tcg_ctx);
                TCGTemp *t_ptr_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op, NULL, tcg_ctx);
                TCGTemp *t_val_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op, NULL, tcg_ctx);
                add_void_call_4(qemu_store_helper,
                                t_ptr, t_mem_op, t_ptr_idx, t_val_idx,
                                op, NULL, tcg_ctx);
                MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                tcg_temp_free_internal(t_mem_op);
                tcg_temp_free_internal(t_ptr_idx);
                tcg_temp_free_internal(t_val_idx);
#endif
            }
            break;

        case INDEX_op_ld_i32:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            break;

        case INDEX_op_st_i64:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            break;

        case INDEX_op_brcond_i64:
            mark_temp_as_in_use(arg_temp(op->args[0]));
            mark_temp_as_in_use(arg_temp(op->args[1]));
            if (instrument)
            {
                TCGTemp *t_a = arg_temp(op->args[0]);
                TCGTemp *t_b = arg_temp(op->args[1]);
                TCGCond cond = op->args[2];
                branch(t_a, t_b, cond, op, tcg_ctx);
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
            if (instrument)
            {
                TCGTemp *t_to = arg_temp(op->args[0]);
                TCGTemp *t_from = arg_temp(op->args[1]);
                extend(t_to, t_from, get_extend_kind(op->opc), op, tcg_ctx);
            }
            break;

        case INDEX_op_goto_ptr:
        case INDEX_op_goto_tb:
        case INDEX_op_exit_tb:
        case INDEX_op_brcond_i32: // skip when emulating 64 bit
            break;

        default:
            if (instrument)
            {
                const TCGOpDef *def __attribute__((unused)) = &tcg_op_defs[op->opc];
                debug_printf("Unhandled TCG instruction: %s\n", def->name);
            }
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