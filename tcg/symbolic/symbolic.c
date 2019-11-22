#include <stdio.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "symbolic.h"

typedef struct Expr
{
    struct Expr *next_free; // eq to zero when in use or when not yet allocated
    struct Expr *op1;
    struct Expr *op2;
    unsigned char opkind;
    unsigned char op1_is_const;
    unsigned char op2_is_const;
    unsigned char is_symbolic_input;
} Expr;

// symbolic state
Expr *sregs[TCG_TARGET_NB_REGS] = {0};

// Expr allocation pool
#define EXPR_POOL_CAPACITY (256 * 1024)
Expr pool[EXPR_POOL_CAPACITY] = {0};
Expr *next_free_expr = NULL;
unsigned int expr_allocated = 0;

#if 1
int counter = 0;
void helper_pcounter(void);
void helper_pcounter(void)
{
    printf("Counter: %x\n", counter);
}
#endif

static inline Expr *new_expr(void)
{
    // ToDo: use free list
    assert(expr_allocated < EXPR_POOL_CAPACITY);
    expr_allocated += 1;
    return &pool[expr_allocated - 1];
}

static inline Expr *new_symbolic_expr(void)
{
    Expr *e = new_expr();
    e->is_symbolic_input = 1;
    return e;
}

static inline void make_reg_symbolic(const char *reg_name, TCGContext *tcg_ctx)
{
    for (int i = 0; i < TCG_TARGET_NB_REGS; i++)
    {
        TCGTemp *t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0)
        {
            printf("Making symbolic: %s\n", t->name);
            sregs[i] = new_symbolic_expr();
        }
    }
}

static int done = 0;

void parse_translation_block(TranslationBlock *tb, uintptr_t pc, uint8_t *tb_code, TCGContext *tcg_ctx)
{
    //if (pc < 0x40054d || pc > 0x400578)
    //    return;
#if 0
    if (pc == 0x40054d)
        make_reg_symbolic("rdi", tcg_ctx);
#endif
    TCGOp *op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
#if 0
        switch(op->opc) {

            case INDEX_op_insn_start:
                printf("Instrumenting %lx\n", op->args[0]);
                break;

            default:
                /* ToDo */;
        }
#endif
#if 1
        if (done) return;
        if (op->opc != INDEX_op_insn_start || op->args[0] != 0x40054d) continue;
        printf("Instrumenting BB\n");
        done = 1;
#if 0
        TCGLabel *l = gen_new_label();
        TCGTemp * tt0 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        TCGTemp * tt1 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        TCGTemp * tt2 = tcg_temp_new_internal(TCG_TYPE_I64, false);
        //tcg_gen_br(l);
        tcg_gen_mov_i64(temp_tcgv_i64(tt2), tcg_const_i64((uintptr_t) &counter));
        tcg_gen_ld_i32(temp_tcgv_i32(tt0), temp_tcgv_ptr(tt2), 0);
        tcg_gen_mov_i32(temp_tcgv_i32(tt1), tcg_const_i32(0x2));
        tcg_gen_brcond_i32(TCG_COND_NE, temp_tcgv_i32(tt0), temp_tcgv_i32(tt1), l);
        gen_set_label(l);
#endif

#if 1
        TCGTemp * ptr2 = tcg_temp_new_internal(TCG_TYPE_PTR, false);
        TCGOpcode lopc = INDEX_op_movi_i64;
        TCGOp *lop = tcg_op_insert_after(tcg_ctx, op, lopc);
        lop->args[0] = temp_arg(ptr2);
        lop->args[1] = (uintptr_t) &counter;

        TCGTemp * ptr = tcg_temp_new_internal(TCG_TYPE_PTR, false);
        lopc = INDEX_op_movi_i64;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(ptr);
        lop->args[1] = (uintptr_t) &counter;

        TCGTemp * t4 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        lopc = INDEX_op_ld_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t4);
        lop->args[1] = temp_arg(ptr2);
        lop->args[2] = 0;

        TCGTemp * t3 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        lopc = INDEX_op_movi_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t3);
        lop->args[1] = 0x0;
#endif
#if 1
        TCGLabel *l = gen_new_label();

        l->refs++;
        lopc = INDEX_op_brcond_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t4);
        lop->args[1] = temp_arg(t3);
        lop->args[2] = TCG_COND_NE;
        lop->args[3] = label_arg(l);
#else
        TCGLabel *l = gen_new_label();
        l->refs++;
        lopc = INDEX_op_br;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = label_arg(l);
#endif



        TCGTemp * t1 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        lopc = INDEX_op_ld_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t1);
        lop->args[1] = temp_arg(ptr);
        lop->args[2] = 0;

        TCGTemp * t2 = tcg_temp_new_internal(TCG_TYPE_I32, false);
        lopc = INDEX_op_movi_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t2);
        lop->args[1] = 0xDEAD;

        lopc = INDEX_op_add_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t1);
        lop->args[1] = temp_arg(t1);
        lop->args[2] = temp_arg(t2);

        lopc = INDEX_op_st_i32;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = temp_arg(t1);
        lop->args[1] = temp_arg(ptr);
        lop->args[2] = 0;

        lopc = INDEX_op_call;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        TCGOP_CALLO(lop) = 0;
        lop->args[0] = (uintptr_t) helper_pcounter;
        lop->args[1] = 0; // flags
        TCGOP_CALLI(lop) = 0;
#if 1
        l->present = 1;
        lopc = INDEX_op_set_label;
        lop = tcg_op_insert_after(tcg_ctx, lop, lopc);
        lop->args[0] = label_arg(l);
#endif

        printf("Instrumenting BB done\n");
        break;
#endif
    }
}