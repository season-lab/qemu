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

typedef struct l3_page_t {
    Expr * entries[1 << L3_PAGE_BITS];
} l3_page_t;

typedef struct l2_page_t {
    l3_page_t * entries[1 << L2_PAGE_BITS];
} l2_page_t;

typedef struct l1_page_t {
    l2_page_t * entries[1 << L1_PAGE_BITS];
} l1_page_t;

// up to 48 bits addressing
typedef struct s_memory_t {
    l1_page_t table;
} s_memory_t;

s_memory_t s_memory = { 0 };

// Expr allocation pool
#define EXPR_POOL_CAPACITY (256 * 1024)
Expr pool[EXPR_POOL_CAPACITY] = {0};
Expr *next_free_expr = &pool[0];
Expr *last_expr = NULL; // ToDo: unsafe

#if 0
int counter = 0;
void helper_pcounter(void);
void helper_pcounter(void)
{
    printf("Counter: %x\n", counter);
}
#endif

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
    op->args[MAX_OPC_PARAM - 1] = (uint64_t) 1;
}

static inline void add_void_call_0(void *f, TCGOp *op_in, TCGContext *tcg_ctx)
{
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = (uintptr_t)f;
    op->args[1] = 0;        // flags
    TCGOP_CALLI(op) = 0;    // input args
    TCGOP_CALLO(op) = 0;    // ret args

    //mark_insn_as_instrumentation(op);
}

static inline void add_void_call_1(void *f, TCGTemp * arg, TCGOp *op_in, TCGContext *tcg_ctx, uint8_t mark_as_instrumentation)
{
    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg);
    op->args[1] = (uintptr_t)f;
    op->args[2] = 0;        // flags
    TCGOP_CALLI(op) = 1;    // input args
    TCGOP_CALLO(op) = 0;    // ret args

    if (mark_as_instrumentation)
        mark_insn_as_instrumentation(op);
}

static inline void add_void_call_2(void *f, TCGTemp * arg0, TCGTemp * arg1, TCGOp *op_in, TCGContext *tcg_ctx)
{
    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(arg0);
    op->args[1] = temp_arg(arg1);
    op->args[2] = (uintptr_t)f;
    op->args[3] = 0;        // flags
    TCGOP_CALLI(op) = 2;    // input args
    TCGOP_CALLO(op) = 0;    // ret args

    mark_insn_as_instrumentation(op);
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

static inline void load_addr(void *addr, TCGTemp **t, TCGOp *op_in, TCGContext *tcg_ctx)
{
    TCGTemp *ptr = new_non_conflicting_temp(TCG_TYPE_PTR);
    TCGOpcode opc = INDEX_op_movi_i64;
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(ptr);
    op->args[1] = (uintptr_t)addr;
    *t = ptr;
}

static inline void load_n_from_addr(TCGTemp *ptr, TCGTemp *val, uintptr_t offset, size_t n_bytes, TCGOp *op_in, TCGContext *tcg_ctx)
{
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
    op->args[0] = temp_arg(val);
    op->args[1] = temp_arg(ptr);
    op->args[2] = offset;
}

static inline void load_from_addr(TCGTemp *ptr, TCGTemp *val, TCGOp *op_in, TCGContext *tcg_ctx) // ToDo: add offset arg
{
    load_n_from_addr(ptr, val, 0, sizeof(uintptr_t), op_in, tcg_ctx);
}

static inline void store_to_addr_n(TCGTemp *ptr, TCGTemp *val, uintptr_t offset, size_t n, TCGOp *op_in, TCGContext *tcg_ctx)
{
    TCGOpcode opc;
    switch (n)
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
    op->args[0] = temp_arg(val);
    op->args[1] = temp_arg(ptr);
    op->args[2] = offset;
}

static inline void store_to_addr(TCGTemp *ptr, TCGTemp *val, uintptr_t offset, TCGOp *op_in, TCGContext *tcg_ctx)
{
    // FixMe: what if val is only 32bit?
    store_to_addr_n(ptr, val, offset, sizeof(void *), op_in, tcg_ctx);
}

static inline void init_reg(size_t reg, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(reg < TCG_MAX_TEMPS);
    printf("Setting expr of reg %lu\n", reg);
    TCGTemp *t_dst;
    TCGTemp *t_last_expr;
    load_addr(&last_expr, &t_last_expr, op_in, tcg_ctx);
    load_from_addr(t_last_expr, t_last_expr, op_in, tcg_ctx);
    load_addr(&stemps[reg], &t_dst, op_in, tcg_ctx);
    store_to_addr(t_dst, t_last_expr, 0, op_in, tcg_ctx);
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
            add_void_call_0(new_symbolic_expr, op, tcg_ctx);
            init_reg(i, op, tcg_ctx);
            add_void_call_0(print_reg, op, tcg_ctx);
        }
    }
}

static inline void move_temp(size_t from, size_t to, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp *t_to;
    TCGTemp *t_from;
    load_addr(&stemps[from], &t_from, op_in, tcg_ctx);
    load_from_addr(t_from, t_from, op_in, tcg_ctx);
    load_addr(&stemps[to], &t_to, op_in, tcg_ctx);
    store_to_addr(t_to, t_from, 0, op_in, tcg_ctx);
    tcg_temp_free_internal(t_to);
    tcg_temp_free_internal(t_from);
}

static inline void clear_temp(size_t idx, TCGOp *op_in, TCGContext *tcg_ctx)
{
    assert(idx < TCG_MAX_TEMPS);

    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    TCGOpcode opc = INDEX_op_movi_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_zero);
    op->args[1] = (uintptr_t)0;

    TCGTemp *t;
    load_addr(&stemps[idx], &t, op_in, tcg_ctx);
    store_to_addr(t, t_zero, 0, op_in, tcg_ctx);

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
    add_void_call_0(check_pool_expr_capacity, op_in, tcg_ctx); // ToDo: make inline check

    TCGTemp *t_next_free_expr_addr;
    load_addr(&next_free_expr, &t_next_free_expr_addr, op_in, tcg_ctx);

    TCGTemp *t_next_free_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    load_from_addr(t_next_free_expr_addr, t_next_free_expr, op_in, tcg_ctx);

    TCGOpcode opc = INDEX_op_mov_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_out);
    op->args[1] = temp_arg(t_next_free_expr);

    //add_void_call_0(test_expr, op_in, tcg_ctx); // ToDo: make inline check

    TCGTemp *t_expr_size = new_non_conflicting_temp(TCG_TYPE_I64);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_expr_size);
    op->args[1] = (uintptr_t)sizeof(Expr);

    opc = INDEX_op_add_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_next_free_expr);
    op->args[1] = temp_arg(t_next_free_expr);
    op->args[2] = temp_arg(t_expr_size);

    tcg_temp_free_internal(t_expr_size);

    store_to_addr(t_next_free_expr_addr, t_next_free_expr, 0, op_in, tcg_ctx);

    //add_void_call_0(check_pool_expr_capacity, op_in, tcg_ctx); // ToDo: make inline check

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
    TCGOpcode opc = INDEX_op_mov_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_dummy);
    op->args[1] = temp_arg(t);
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

    TCGTemp *t_a;
    load_addr(&stemps[a], &t_a, op_in, tcg_ctx);
    load_from_addr(t_a, t_a, op_in, tcg_ctx);

    TCGTemp *t_b;
    load_addr(&stemps[b], &t_b, op_in, tcg_ctx);
    load_from_addr(t_b, t_b, op_in, tcg_ctx);

    TCGTemp *t_a_and_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    TCGOpcode opc = INDEX_op_and_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_a_and_b);
    op->args[1] = temp_arg(t_a);
    op->args[2] = temp_arg(t_b);

    // ToDo: make this smarter
    TCGTemp *t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_zero);
    op->args[1] = (uintptr_t)0;

    label_both_concrete->refs++;
    opc = INDEX_op_brcond_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_a_and_b);
    op->args[1] = temp_arg(t_zero);
    op->args[2] = TCG_COND_EQ;
    op->args[3] = label_arg(label_both_concrete);

    tcg_temp_free_internal(t_a_and_b);

    // allocate expr for t_out
    TCGTemp *t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(t_out, op_in, tcg_ctx);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp *t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_one);
    op->args[1] = (uintptr_t)1;

    TCGLabel *label_ta_not_concrete = gen_new_label();

    label_ta_not_concrete->refs++;
    opc = INDEX_op_brcond_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_a);
    op->args[1] = temp_arg(t_zero);
    op->args[2] = TCG_COND_NE;
    op->args[3] = label_arg(label_ta_not_concrete);

    opc = INDEX_op_mov_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_a);
    op->args[1] = temp_arg(t_op_a);

    store_to_addr_n(t_out, t_one, offsetof(Expr, op1_is_const), 1, op_in, tcg_ctx);

    TCGTemp *t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_one);
    op->args[1] = (uintptr_t)opkind;

    store_to_addr_n(t_out, t_opkind, offsetof(Expr, opkind), 1, op_in, tcg_ctx);

    label_ta_not_concrete->present = 1;
    opc = INDEX_op_set_label;
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label_ta_not_concrete);

    store_to_addr(t_out, t_a, offsetof(Expr, op1), op_in, tcg_ctx);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel *label_tb_not_concrete = gen_new_label();

    label_tb_not_concrete->refs++;
    opc = INDEX_op_brcond_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_a);
    op->args[1] = temp_arg(t_zero);
    op->args[2] = TCG_COND_NE;
    op->args[3] = label_arg(label_tb_not_concrete);

    opc = INDEX_op_mov_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_b);
    op->args[1] = temp_arg(t_op_b);

    store_to_addr_n(t_out, t_one, offsetof(Expr, op2_is_const), 1, op_in, tcg_ctx);

    label_tb_not_concrete->present = 1;
    opc = INDEX_op_set_label;
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label_tb_not_concrete);

    store_to_addr(t_out, t_b, offsetof(Expr, op2), op_in, tcg_ctx);

    // assign expr to t_out
    TCGTemp *t_out_expr;
    load_addr(&stemps[out], &t_out_expr, op_in, tcg_ctx);
    store_to_addr(t_out_expr, t_out, 0, op_in, tcg_ctx);

    label_both_concrete->present = 1;
    opc = INDEX_op_set_label;
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label_both_concrete);

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

static inline void allocate_l3_page(uintptr_t l1_entry_idx, uintptr_t l2_entry_idx)
{
    assert(l1_entry_idx < 1 << L1_PAGE_BITS);
    assert(s_memory.table.entries[l1_entry_idx]);
    assert(l2_entry_idx < 1 << L2_PAGE_BITS);

    printf("Allocating l3 page at idx %lu\n", l2_entry_idx);
    s_memory.table.entries[l1_entry_idx]->entries[l2_entry_idx] = g_malloc0(sizeof(l3_page_t)); // FixMe: get mmap lock
    printf("Done: l3_page_addr=%p\n", s_memory.table.entries[l1_entry_idx]->entries[l2_entry_idx]);
}

static inline void print_t_l1_entry_idx_addr(void * l1_entry_addr)
{
    printf("L1 Entry addr: %p\n", l1_entry_addr);
}

static inline void preserve_temp(TCGOp *op, size_t i)
{
    op->life |= SYNC_ARG << i;
}


static inline void qemu_load(TCGTemp *t_orig_ptr, TCGTemp *t_orig_val, uintptr_t offset, TCGOp *op_in, TCGContext *tcg_ctx)
{
    preserve_op_load(t_orig_ptr, op_in, tcg_ctx);
    preserve_op_load(t_orig_val, op_in, tcg_ctx);

    // compute index for L1 table

    TCGTemp * t_l1_entry_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    TCGOpcode opc = INDEX_op_mov_i64; // ToDo: i32
    TCGOp *op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry_idx);
    op->args[1] = temp_arg(t_orig_ptr);

    TCGTemp * t_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_shr_bit);
    op->args[1] = (uintptr_t) L1_PAGE_BITS + L2_PAGE_BITS;

    TCGTemp * t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_zero);
    op->args[1] = (uintptr_t) 0;

    opc = INDEX_op_shr_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry_idx);
    op->args[1] = temp_arg(t_l1_entry_idx);
    op->args[2] = temp_arg(t_shr_bit);

    // check whether L2 page is allocated for that index

    TCGLabel *label_l2_page_is_allocated = gen_new_label();

    TCGTemp * t_s_memory = new_non_conflicting_temp(TCG_TYPE_PTR);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_s_memory);
    op->args[1] = (uintptr_t) &s_memory;

    TCGTemp * t_l1_entry_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    opc = INDEX_op_movi_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry_idx_addr);
    assert(sizeof(l2_page_t *) == 8);
    op->args[1] = (uintptr_t) 3;

    opc = INDEX_op_shl_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry_idx_addr);
    op->args[1] = temp_arg(t_l1_entry_idx);
    op->args[2] = temp_arg(t_l1_entry_idx_addr);

    opc = INDEX_op_add_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry_idx_addr);
    op->args[1] = temp_arg(t_l1_entry_idx_addr);
    op->args[2] = temp_arg(t_s_memory);

    //add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry_idx_addr, op_in, tcg_ctx);

    TCGTemp * t_l1_entry = new_non_conflicting_temp(TCG_TYPE_PTR);
    load_n_from_addr(t_l1_entry_idx_addr, t_l1_entry, 0, 8, op_in, tcg_ctx);

    label_l2_page_is_allocated->refs++;
    opc = INDEX_op_brcond_i64; // ToDo: i32
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = temp_arg(t_l1_entry);
    op->args[1] = temp_arg(t_zero);
    op->args[2] = TCG_COND_NE;
    op->args[3] = label_arg(label_l2_page_is_allocated);

    // if not, allocate L2 page
    add_void_call_1(allocate_l2_page, t_l1_entry_idx, op_in, tcg_ctx, 1);

    label_l2_page_is_allocated->present = 1;
    opc = INDEX_op_set_label;
    op = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0] = label_arg(label_l2_page_is_allocated);

    add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry_idx_addr, op_in, tcg_ctx, 0);
#if 0
    add_void_call_2(allocate_l3_page, t_l1_entry, t_l1_entry, op_in, tcg_ctx);
#endif

    tcg_temp_free_internal(t_s_memory);
    tcg_temp_free_internal(t_zero);
    tcg_temp_free_internal(t_l1_entry_idx_addr);
    tcg_temp_free_internal(t_shr_bit);
    tcg_temp_free_internal(t_l1_entry_idx);
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
            if (instrument && 0)
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
                TCGTemp * t_val = arg_temp(op->args[0]);
                TCGTemp * t_ptr = arg_temp(op->args[1]);
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