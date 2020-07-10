#include "../../target/i386/cpu.h"

#define XMM_BYTES 16

static inline size_t get_op_width(CCOp op)
{
    switch (op) {
        case CC_OP_ADDB:
        case CC_OP_MULB:
        case CC_OP_SUBB:
        case CC_OP_LOGICB:
        case CC_OP_INCB:
        case CC_OP_DECB:
        case CC_OP_SHLB:
        case CC_OP_SARB:
        case CC_OP_BMILGB:
            return 1;
        case CC_OP_ADDW:
        case CC_OP_MULW:
        case CC_OP_SUBW:
        case CC_OP_LOGICW:
        case CC_OP_INCW:
        case CC_OP_DECW:
        case CC_OP_SHLW:
        case CC_OP_SARW:
        case CC_OP_BMILGW:
            return 2;
        case CC_OP_ADDL:
        case CC_OP_MULL:
        case CC_OP_SUBL:
        case CC_OP_LOGICL:
        case CC_OP_INCL:
        case CC_OP_DECL:
        case CC_OP_SHLL:
        case CC_OP_SARL:
        case CC_OP_BMILGL:
            return 4;
        case CC_OP_ADDQ:
        case CC_OP_MULQ:
        case CC_OP_SUBQ:
        case CC_OP_LOGICQ:
        case CC_OP_INCQ:
        case CC_OP_DECQ:
        case CC_OP_SHLQ:
        case CC_OP_SARQ:
        case CC_OP_BMILGQ:
            return 8;

        default:
            printf("Unknown width cc_op=%u\n", op);
            tcg_abort();
    }
}

// flag == 0: all
// flag == 1: carry flag
static inline OPKIND get_eflags_opkind(uintptr_t cc_op, uint8_t flag)
{
    switch (cc_op) {
        case CC_OP_ADCB:
            return flag == 0 ? EFLAGS_ALL_ADCB : EFLAGS_C_ADCB;
        case CC_OP_ADCW:
            return flag == 0 ? EFLAGS_ALL_ADCW : EFLAGS_C_ADCW;
        case CC_OP_ADCL:
            return flag == 0 ? EFLAGS_ALL_ADCL : EFLAGS_C_ADCL;
        case CC_OP_ADCQ:
            return flag == 0 ? EFLAGS_ALL_ADCQ : EFLAGS_C_ADCQ;
        //
        case CC_OP_ADCX:
            return EFLAGS_ALL_ADCX;
        case CC_OP_ADOX:
            return EFLAGS_ALL_ADOX;
        case CC_OP_ADCOX:
            return EFLAGS_ALL_ADCOX;
        //
        case CC_OP_SBBB:
            return flag == 0 ? EFLAGS_ALL_SBBB : EFLAGS_C_SBBB;
        case CC_OP_SBBW:
            return flag == 0 ? EFLAGS_ALL_SBBW : EFLAGS_C_SBBW;
        case CC_OP_SBBL:
            return flag == 0 ? EFLAGS_ALL_SBBL : EFLAGS_C_SBBL;
        case CC_OP_SBBQ:
            return flag == 0 ? EFLAGS_ALL_SBBQ : EFLAGS_C_SBBQ;

        default:
            printf("No OPKIND for cc_op=%lu\n", cc_op);
            tcg_abort();
    }
}

static void qemu_cc_compute_all(uint64_t packed_idx, uintptr_t dst,
                                uintptr_t src1, uintptr_t src2, uintptr_t cc_op)
{
    uintptr_t ret_idx  = UNPACK_0(packed_idx);
    uintptr_t dst_idx  = UNPACK_1(packed_idx);
    uintptr_t src1_idx = UNPACK_2(packed_idx);
    uintptr_t src2_idx = UNPACK_3(packed_idx);

    switch (cc_op) {
        case CC_OP_EFLAGS:
            // src1
            s_temps[ret_idx] = s_temps[src1_idx];
            break;
        case CC_OP_CLR:
            // CC_Z | CC_P;
            s_temps[ret_idx] = NULL;
            break;
        case CC_OP_POPCNT:
            // src1 ? 0 : CC_Z;
            if (s_temps[src1_idx]) {
                Expr* e   = new_expr();
                e->opkind = ITE_NE_ZERO;
                e->op1    = s_temps[src1_idx];
                SET_EXPR_CONST_OP(e->op2, e->op2_is_const, 0);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, CC_Z);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_MULB:
        case CC_OP_MULW:
        case CC_OP_MULL:
        case CC_OP_MULQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_MUL;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_ADDB:
        case CC_OP_ADDW:
        case CC_OP_ADDL:
        case CC_OP_ADDQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_ADD;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_ADCB:
        case CC_OP_ADCW:
        case CC_OP_ADCL:
        case CC_OP_ADCQ:
            if (s_temps[src1_idx] || s_temps[src2_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = get_eflags_opkind(cc_op, 0);
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[src2_idx], src2);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SUBB:
        case CC_OP_SUBW:
        case CC_OP_SUBL:
        case CC_OP_SUBQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_SUB;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SBBB:
        case CC_OP_SBBW:
        case CC_OP_SBBL:
        case CC_OP_SBBQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = get_eflags_opkind(cc_op, 0);
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[src2_idx], src2);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_LOGICB:
        case CC_OP_LOGICW:
        case CC_OP_LOGICL:
        case CC_OP_LOGICQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_LOGIC;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_INCB:
        case CC_OP_INCW:
        case CC_OP_INCL:
        case CC_OP_INCQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_INC;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_DECB:
        case CC_OP_DECW:
        case CC_OP_DECL:
        case CC_OP_DECQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_DEC;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SHLB:
        case CC_OP_SHLW:
        case CC_OP_SHLL:
        case CC_OP_SHLQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_SHL;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SARB:
        case CC_OP_SARW:
        case CC_OP_SARL:
        case CC_OP_SARQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_SAR;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_BMILGB:
        case CC_OP_BMILGW:
        case CC_OP_BMILGL:
        case CC_OP_BMILGQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_ALL_BMILG;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_ADCX:
        case CC_OP_ADOX:
        case CC_OP_ADCOX:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = get_eflags_opkind(cc_op, 0);
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[src2_idx], src2);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        default:
            printf("Helper cc_compute_all with unhandled cc_op=%lu\n", cc_op);
    }
}

static void qemu_cc_compute_c(uint64_t packed_idx, uintptr_t dst,
                              uintptr_t src1, uintptr_t src2, uintptr_t cc_op)
{
    uintptr_t ret_idx  = UNPACK_0(packed_idx);
    uintptr_t dst_idx  = UNPACK_1(packed_idx);
    uintptr_t src1_idx = UNPACK_2(packed_idx);
    uintptr_t src2_idx = UNPACK_3(packed_idx);

    switch (cc_op) {
        case CC_OP_LOGICB:
        case CC_OP_LOGICW:
        case CC_OP_LOGICL:
        case CC_OP_LOGICQ:
        case CC_OP_CLR:
        case CC_OP_POPCNT:
            // carry is always zero
            s_temps[ret_idx] = NULL;
            break;

        case CC_OP_EFLAGS:
        case CC_OP_SARB:
        case CC_OP_SARW:
        case CC_OP_SARL:
        case CC_OP_SARQ:
        case CC_OP_ADOX:
            // src1 & 1;
            if (s_temps[src1_idx]) {
                Expr* e   = new_expr();
                e->opkind = AND;
                e->op1    = s_temps[src1_idx];
                SET_EXPR_CONST_OP(e->op2, e->op2_is_const, 1);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_INCB:
        case CC_OP_INCW:
        case CC_OP_INCL:
        case CC_OP_INCQ:
        case CC_OP_DECB:
        case CC_OP_DECW:
        case CC_OP_DECL:
        case CC_OP_DECQ:
            // src1
            s_temps[ret_idx] = s_temps[src1_idx];
            break;

        case CC_OP_MULB:
        case CC_OP_MULW:
        case CC_OP_MULL:
        case CC_OP_MULQ:
            // src1 != 0;
            if (s_temps[src1_idx]) {
                Expr* e   = new_expr();
                e->opkind = NE;
                e->op1    = s_temps[src1_idx];
                SET_EXPR_CONST_OP(e->op2, e->op2_is_const, 0);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_ADCX:
        case CC_OP_ADCOX:
            // dst
            s_temps[ret_idx] = s_temps[dst_idx];
            break;

        case CC_OP_ADDB:
        case CC_OP_ADDW:
        case CC_OP_ADDL:
        case CC_OP_ADDQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_C_ADD;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_ADCB:
        case CC_OP_ADCW:
        case CC_OP_ADCL:
        case CC_OP_ADCQ:
            if (s_temps[src1_idx] || s_temps[src2_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = get_eflags_opkind(cc_op, 1);
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[src2_idx], src2);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SUBB:
        case CC_OP_SUBW:
        case CC_OP_SUBL:
        case CC_OP_SUBQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_C_SUB;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SBBB:
        case CC_OP_SBBW:
        case CC_OP_SBBL:
        case CC_OP_SBBQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = get_eflags_opkind(cc_op, 1);
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[src2_idx], src2);
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_SHLB:
        case CC_OP_SHLW:
        case CC_OP_SHLL:
        case CC_OP_SHLQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_C_SHL;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        case CC_OP_BMILGB:
        case CC_OP_BMILGW:
        case CC_OP_BMILGL:
        case CC_OP_BMILGQ:
            if (s_temps[src1_idx] || s_temps[dst_idx]) {
                Expr* e   = new_expr();
                e->opkind = EFLAGS_C_BMILG;
                SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[dst_idx], dst);
                SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[src1_idx], src1);
                SET_EXPR_CONST_OP(e->op3, e->op3_is_const, get_op_width(cc_op));
                s_temps[ret_idx] = e;
            } else {
                s_temps[ret_idx] = NULL;
            }
            break;

        default:
            printf("Helper cc_compute_c with unhandled cc_op=%lu\n", cc_op);
    }
}

static inline Expr* build_concat_expr(Expr** exprs, void* addr, size_t size,
                                      int reversed)
{
    Expr* dst_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        size_t idx = i; // reversed ? i : (size - i - 1);
        if (i == 0) {
            dst_expr = exprs[idx];
            if (dst_expr == NULL) {
                dst_expr           = new_expr();
                dst_expr->opkind   = IS_CONST;
                uint8_t* byte_addr = ((uint8_t*)addr) + idx;
                uint8_t  byte      = *byte_addr;
                dst_expr->op1      = (Expr*)((uintptr_t)byte);
            }
        } else {
            Expr* n_expr   = new_expr();
            n_expr->opkind = CONCAT8L;
            if (exprs[idx] == NULL) {
                // fetch the concrete value, embed it in the expr
                uint8_t* byte_addr   = ((uint8_t*)addr) + idx;
                uint8_t  byte        = *byte_addr;
                n_expr->op1          = (Expr*)((uintptr_t)byte);
                n_expr->op1_is_const = 1;
            } else {
                n_expr->op1 = exprs[idx];
            }
            n_expr->op2 = dst_expr;

            dst_expr = n_expr;
        }
    }

    // print_expr(dst_expr);
    return dst_expr;
}

void symbolic_clear_mem(uintptr_t addr, uintptr_t size)
{
    size_t overflow_n_bytes = 0;
    Expr** exprs = get_expr_addr((uintptr_t)addr, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        size -= overflow_n_bytes;
        symbolic_clear_mem(addr + size, overflow_n_bytes);
    }

    if (exprs == NULL) {
        return;
    }

    for (size_t i = 0; i < size; i++) {
        exprs[i] = NULL;
    }
}

static inline void qemu_memmove(uintptr_t src, uintptr_t dst, uintptr_t size)
{
    size_t overflow_n_bytes = 0;
    // printf("A overflow_n_bytes: %lu\n", overflow_n_bytes);
    Expr** src_exprs =
        get_expr_addr((uintptr_t)src, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        if (overflow_n_bytes >= size) {
            printf("B overflow_n_bytes: %lu size=%lu\n", overflow_n_bytes,
                   size);
        }
        assert(overflow_n_bytes < size);
        size -= overflow_n_bytes;
        assert(size);
        qemu_memmove(src + size, dst + size, overflow_n_bytes);
    }
    overflow_n_bytes = 0;
    Expr** dst_exprs =
        get_expr_addr((uintptr_t)dst, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        if (overflow_n_bytes >= size) {
            printf("B overflow_n_bytes: %lu size=%lu\n", overflow_n_bytes,
                   size);
        }
        assert(overflow_n_bytes < size);
        size -= overflow_n_bytes;
        assert(size);
        qemu_memmove(src + size, dst + size, overflow_n_bytes);
    }

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
        size_t overflow_n_bytes;
        dst_exprs = get_expr_addr((uintptr_t)dst, size, 1, &overflow_n_bytes);
    }

#if 0
    printf("[+] Memmove from=%lx to=%lx size=%lu\n", src, dst, size);
#endif
    for (size_t i = 0; i < size; i++) {
        dst_exprs[i] = src_exprs[i];
        // print_expr(dst_exprs[i]);

#if DEBUG_EXPR_CONSISTENCY
        if (src_exprs[i]) {
            // printf("MEMMOVE: index=%lu src=%lx dst=%lx val=%p\n", i, src + i, dst + i, src_exprs[i]);
            add_consistency_check_addr(src_exprs[i], src + i, 1, SYMBOLIC_LOAD);
        }
#endif
    }
}

static inline void qemu_memset(Expr* value, uintptr_t dst, uintptr_t size)
{
    size_t overflow_n_bytes = 0;
    Expr** dst_exprs =
        get_expr_addr((uintptr_t)dst, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        if (overflow_n_bytes >= size) {
            printf("B overflow_n_bytes: %lu size=%lu\n", overflow_n_bytes,
                   size);
        }
        assert(overflow_n_bytes < size);
        size -= overflow_n_bytes;
        assert(size);
        qemu_memset(value, dst + size, overflow_n_bytes);
    }

    if (value == NULL && dst_exprs == NULL) {
        // printf("memset concrete\n");
        return;
    }

    // print_expr(value);
    if (value == NULL) {
        for (size_t i = 0; i < size; i++) {
            // print_expr(dst_exprs[i]);
            dst_exprs[i] = NULL;
        }
        return;
    }

    if (dst_exprs == NULL) {
        size_t overflow_n_bytes;
        dst_exprs = get_expr_addr((uintptr_t)dst, size, 1, &overflow_n_bytes);
    }

#if 0
    printf("[+] Memset to=%lx size=%lu\n", dst, size);
#endif
    for (size_t i = 0; i < size; i++) {
        dst_exprs[i] = value;
    }
}

static inline size_t suffix_to_slice(char suffix, char suffix2)
{
    if (suffix == 'b') {
        return 1;
    } else if (suffix == 'w') {
        return 2;
    } else if (suffix == 'l') {
        return 4;
    } else if (suffix == 'q') {
        return 8;
    } else if (suffix == 'd' && suffix2 == 'q') {
        return 16;
    } else if (suffix == 'd' && suffix2 != 'q') {
        return 8;
    } else {
        tcg_abort();
    }
}

static void qemu_xmm_op_internal(uintptr_t opkind, uint8_t* dst_addr,
                                 uint8_t* src_addr, uintptr_t packed_slice_pc,
                                 size_t n_bytes)
{
    uintptr_t slice = packed_slice_pc & 0xFF;
    assert(slice <= 16 && slice > 0);

    size_t overflow_n_bytes = 0;
    // printf("A overflow_n_bytes: %lu\n", overflow_n_bytes);
    Expr** dst_expr_addr =
        get_expr_addr((uintptr_t)dst_addr, n_bytes, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        // printf("B overflow_n_bytes: %lu\n", overflow_n_bytes);
        assert(overflow_n_bytes < n_bytes);
        n_bytes -= overflow_n_bytes;
        assert(n_bytes);
        qemu_xmm_op_internal(opkind, dst_addr + n_bytes, src_addr + n_bytes,
                             packed_slice_pc, overflow_n_bytes);
    }
    overflow_n_bytes = 0;
    Expr** src_expr_addr =
        get_expr_addr((uintptr_t)src_addr, n_bytes, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        assert(overflow_n_bytes < n_bytes);
        n_bytes -= overflow_n_bytes;
        assert(n_bytes);
        qemu_xmm_op_internal(opkind, dst_addr + n_bytes, src_addr + n_bytes,
                             packed_slice_pc, overflow_n_bytes);
    }

    if (dst_expr_addr == NULL && src_expr_addr == NULL) {
        // printf("qemu_xmm_op_bytewise: both regs are concrete\n");
        return;
    }

    if ((opkind == XOR || opkind == SUB || opkind == EQ) &&
        dst_addr == src_addr) {
        // xmm reg will be concrete
        for (size_t i = 0; i < n_bytes; i++) {
            dst_expr_addr[i] = NULL;
        }
        return;
    }

    for (size_t i = 0; i < n_bytes; i += slice) {

        uint8_t src_is_not_null = 0;
        uint8_t dst_is_not_null = 0;
        for (size_t k = 0; k < slice && !src_is_not_null && !dst_is_not_null;
             k++) {
            if (src_expr_addr) {
                if (opkind == SHL || opkind == SHR || opkind == SAR) {
                    src_is_not_null |= src_expr_addr[0] != NULL;
                } else {
                    src_is_not_null |= src_expr_addr[i + k] != NULL;
                }
            }
            if (dst_expr_addr) {
                dst_is_not_null |= dst_expr_addr[i + k] != NULL;
            }
        }
        if (!src_is_not_null && !dst_is_not_null) {
            // no need to clear dst since it is already fully concrete
            continue;
        }

#if 0
        uintptr_t pc = packed_slice_pc >> 8;
        printf("[+] qemu_xmm_op: pc=%lx opkind=%s src_addr=%p dst_addr=%p slice=%lu count=%ld\n",
            pc, opkind_to_str(opkind), src_addr, dst_addr, slice, i);
#endif

        Expr* e   = new_expr();
        e->opkind = opkind;

        if (src_expr_addr == NULL) {
            src_expr_addr =
                get_expr_addr((uintptr_t)src_addr, n_bytes, 1, NULL);
        }
        if (dst_expr_addr == NULL) {
            dst_expr_addr =
                get_expr_addr((uintptr_t)dst_addr, n_bytes, 1, NULL);
        }

        Expr* src_slice;
        Expr* dst_slice;
        if (slice > 1) {
            // ToDo: optimize when one of the two is fully concrete
            if (opkind == SHL || opkind == SHR || opkind == SAR) {
                src_slice =
                    build_concat_expr(&src_expr_addr[i], &src_addr[i], 1, 0);

                if (slice == 16) {
                    Expr* src2 = new_expr();
                    src2->opkind = SHL;
                    src2->op1 = src_slice;
                    SET_EXPR_CONST_OP(src2->op2, src2->op2_is_const, 3);
                    src_slice = src2;
                }

            } else {
                src_slice =
                    build_concat_expr(&src_expr_addr[i], &src_addr[i], slice, 0);
            }

            dst_slice =
                build_concat_expr(&dst_expr_addr[i], &dst_addr[i], slice, 0);

#if DEBUG_EXPR_CONSISTENCY
            // printf("XMM_OP_A1:\n");
            add_consistency_check_addr(dst_slice, ((uintptr_t)dst_addr) + i, slice, opkind);
            // printf("XMM_OP_B1:\n");
            if (opkind == SHL || opkind == SHR || opkind == SAR) {
                if (slice == 16) {
                    add_consistency_check_addr(src_slice->op1, ((uintptr_t)src_addr), 1, opkind);
                } else {
                    add_consistency_check_addr(src_slice, ((uintptr_t)src_addr), 1, opkind);
                }
            } else {
                add_consistency_check_addr(src_slice, ((uintptr_t)src_addr) + i, slice, opkind);
            }
#endif

            e->op1 = dst_slice;
            e->op2 = src_slice;

        } else {
            SET_EXPR_OP(e->op1, e->op1_is_const, dst_expr_addr[i], dst_addr[i]);

            if (opkind == SHL || opkind == SHR || opkind == SAR) {
                SET_EXPR_OP(e->op2, e->op2_is_const, src_expr_addr[0], src_addr[0]);
            } else {
                SET_EXPR_OP(e->op2, e->op2_is_const, src_expr_addr[i], src_addr[i]);
            }

#if DEBUG_EXPR_CONSISTENCY
            if (dst_expr_addr[i]) {
                // printf("XMM_OP_A2: addr=%p\n", dst_addr + i);
                add_consistency_check(dst_expr_addr[i], dst_addr[i], slice, opkind);
            }
            if (src_expr_addr[i]) {
                // printf("XMM_OP_B2:\n");
                if (opkind == SHL || opkind == SHR || opkind == SAR) {
                    add_consistency_check(src_expr_addr[0], src_addr[0], 1, opkind);
                } else {
                    add_consistency_check(src_expr_addr[i], src_addr[i], slice, opkind);
                }
            }
#endif
        }

        SET_EXPR_CONST_OP(e->op3, e->op3_is_const, slice);

#if 0
        print_expr(e);
#endif

        if (slice > 1) {
            for (size_t k = 0; k < slice; k++) {
                Expr* e_byte   = new_expr();
                e_byte->opkind = EXTRACT8;
                e_byte->op1    = e;
                SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const, k);
                dst_expr_addr[i + k] = e_byte;
            }
        } else {
            dst_expr_addr[i] = e;
        }
    }

}

static void qemu_xmm_op(uintptr_t opkind, uint8_t* dst_addr, uint8_t* src_addr,
                        uintptr_t packed_slice_pc)
{
    qemu_xmm_op_internal(opkind, dst_addr, src_addr, packed_slice_pc,
                         XMM_BYTES);
}

#if 0
static void qemu_xmm_shift(uintptr_t opkind, uint64_t* dst_addr,
                           uint64_t* src_addr)
{
    Expr** dst_expr_addr = get_expr_addr((uintptr_t)dst_addr, XMM_BYTES);
    Expr** src_expr_addr = get_expr_addr((uintptr_t)src_addr, XMM_BYTES);
    if (dst_expr_addr == NULL && src_expr_addr == NULL) {
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0; i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    int dst_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && dst_is_not_null == 0; i++) {
        dst_is_not_null |= dst_expr_addr[i] != NULL;
    }

    if (src_is_not_null == 0 && dst_is_not_null == 0) {
        // no need to clear dst since it is already fully concrete
        return;
    }

#if 0
    printf("qemu_xmm_shift: opkind=%s src_addr=%p dst_addr=%p\n",
           opkind_to_str(opkind), src_addr, dst_addr);
#endif

    Expr* src_expr = NULL;
    if (src_is_not_null) {
        src_expr = build_concat_expr(src_expr_addr, src_addr, XMM_BYTES, 0);
    }

    Expr* dst_expr = build_concat_expr(dst_expr_addr, dst_addr, XMM_BYTES, 0);

    Expr* e   = new_expr();
    e->opkind = opkind;
    e->op1 = dst_expr; // we need a CONCAT expr when is fully concrete because
                       // it's a 128 bit const
    // src is 128 bit but its max value is 16
    SET_EXPR_OP(e->op2, e->op2_is_const, src_expr, *src_addr);

    for (size_t i = 0; i < XMM_BYTES; i++) {
        Expr* e_byte   = new_expr();
        e_byte->opkind = EXTRACT8;
        e_byte->op1    = e;
        SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const, i);
        dst_expr_addr[i] = e_byte;
    }
}
#endif

static inline int is_xmm_offset(uintptr_t offset)
{
    if (offset >= offsetof(CPUX86State, xmm_regs) &&
        offset < offsetof(CPUX86State, opmask_regs))
        return 1;
    return 0;
}

static inline int is_eip_offset(uintptr_t offset)
{
    if (offset == offsetof(CPUX86State, eip)) {
        return 1;
    }
    return 0;
}

static void qemu_xmm_pmovmskb(uintptr_t dst_idx, uint64_t* src_addr,
                              size_t n_bytes)
{
    Expr** src_expr_addr =
        get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0, NULL);
    if (src_expr_addr == NULL) {
        s_temps[dst_idx] = NULL;
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0; i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    if (src_is_not_null == 0) {
        s_temps[dst_idx] = NULL;
        return;
    }
#if 0
    printf("Helper qemu_xmm_pmovmskb: symbolic op\n");
#endif
    Expr* src_expr   = build_concat_expr(src_expr_addr, src_addr, XMM_BYTES, 0);
    Expr* e          = new_expr();
    e->opkind        = PMOVMSKB;
    e->op1           = src_expr;
    s_temps[dst_idx] = e;
#if 0
    printf("qemu_xmm_pmovmskb: symbolic xmm reg\n");
    print_expr(e);
    printf("XMM_A: %lx\n", *src_addr);
    printf("XMM_B: %lx\n", *(src_addr+1));
#endif

#if DEBUG_EXPR_CONSISTENCY
    Expr* src_expr_a = build_concat_expr(src_expr_addr, src_addr, 8, 0);
    // print_expr(src_expr_a);
    add_consistency_check_addr(src_expr_a, (uintptr_t)src_addr, 8, PMOVMSKB);
    Expr* src_expr_b = build_concat_expr(src_expr_addr + 8, (void*)(((uintptr_t)src_addr) + 8), 8, 0);
    // print_expr(src_expr_b);
    add_consistency_check_addr(src_expr_b, ((uintptr_t)src_addr) + 8, 8, PMOVMSKB);
#endif
}

static void qemu_xmm_mov_mm_T0(uint64_t* dst_addr, uintptr_t src_idx, size_t size)
{
    Expr** dst_expr_addr =
        get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0, NULL);
    if (s_temps[src_idx] == NULL) {
        if (dst_expr_addr == NULL) {
            return;
        }
        for (size_t i = 0; i < XMM_BYTES; i++) {
            dst_expr_addr[i] = NULL;
        }
        return;
    }
#if 0
    printf("Helper qemu_xmm_movl_mm_T0: symbolic op\n");
#endif
    for (size_t i = 0; i < size; i++) {
        Expr* e_byte   = new_expr();
        e_byte->opkind = EXTRACT8;
        e_byte->op1    = s_temps[src_idx];
        SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const,
                          i); // ToDo: check endianess!!!
        dst_expr_addr[i] = e_byte;
    }
    for (size_t i = size; i < XMM_BYTES; i++) {
        dst_expr_addr[i] = NULL;
    }
}

static void qemu_xmm_pshuf(uint64_t* dst_addr, uint64_t* src_addr,
                           uintptr_t order, uintptr_t size)
{
    Expr** dst_expr_addr =
        get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0, NULL);
    Expr** src_expr_addr =
        get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0, NULL);

    if (src_expr_addr == NULL) {
        if (dst_expr_addr != NULL) {
            for (size_t i = 0; i < XMM_BYTES; i++) {
                dst_expr_addr[i] = NULL;
            }
        }
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0; i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    if (!src_is_not_null) {
        if (dst_expr_addr != NULL) {
            for (size_t i = 0; i < XMM_BYTES; i++) {
                dst_expr_addr[i] = NULL;
            }
        }
        return;
    }
#if 0
    printf("Helper qemu_xmm_pshuf: symbolic op\n");
#endif
    uint8_t count = 0;
    for (size_t i = 0; i < XMM_BYTES; i += size) {
        // ToDo: check endianness
        uint8_t src_pos = ((order >> (2 * count++)) & 3) * size;
        for (size_t k = 0; k < size; k++) {
            dst_expr_addr[i + k] = src_expr_addr[src_pos + k];
        }
    }
}

static void qemu_xmm_punpck(uint64_t* dst_addr, uint64_t* src_addr,
                            uintptr_t slice, uint8_t lowbytes)
{
    Expr** dst_expr_addr =
        get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0, NULL);
    Expr** src_expr_addr =
        get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0, NULL);

    if (src_expr_addr == NULL && dst_expr_addr == NULL) {
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0 && src_expr_addr;
         i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    int dst_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && dst_is_not_null == 0 && dst_expr_addr;
         i++) {
        dst_is_not_null |= dst_expr_addr[i] != NULL;
    }

    if (!src_is_not_null && !dst_is_not_null) {
        return;
    }
#if 0
    printf("Helper qemu_xmm_punpck: symbolic op\n");
#endif
    Expr* dst_exprs[XMM_BYTES];
    for (size_t i = 0; i < XMM_BYTES; i++) {
        dst_exprs[i] = dst_expr_addr[i];
    }

    size_t base_index;
    if (lowbytes) {
        base_index = 0;
    } else {
        base_index = XMM_BYTES / 2;
    }

    uint8_t count = 0;
    for (size_t i = 0; i < XMM_BYTES; i += (2 * slice)) {
        for (size_t k = 0; k < slice; k++) {
            dst_expr_addr[i + k] = dst_exprs[base_index + (count * slice) + k];
        }
        for (size_t k = 0; k < slice; k++) {
            dst_expr_addr[i + slice + k] =
                src_expr_addr[base_index + (count * slice) + k];
        }
        count++;
    }
}

static void qemu_xmm_pack(uint64_t* dst_addr, uint64_t* src_addr,
                          uintptr_t packed_info)
{
    Expr** dst_expr_addr =
        get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0, NULL);
    Expr** src_expr_addr =
        get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0, NULL);

    if (src_expr_addr == NULL && dst_expr_addr == NULL) {
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0 && src_expr_addr;
         i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    int dst_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && dst_is_not_null == 0 && dst_expr_addr;
         i++) {
        dst_is_not_null |= dst_expr_addr[i] != NULL;
    }

    if (!src_is_not_null && !dst_is_not_null) {
        return;
    }

    uint8_t unpacked_size = UNPACK_0(packed_info);
    uint8_t packed_size   = UNPACK_1(packed_info);
    uint8_t opkind =
        UNPACK_2(packed_info) ? SIGNED_SATURATION : UNSIGNED_SATURATION;

#if 0
    printf("Helper qemu_xmm_pack: symbolic op\n");
#endif

    // make a copy of dest exprs
    Expr* dst_exprs[XMM_BYTES];
    for (size_t i = 0; i < XMM_BYTES; i++) {
        dst_exprs[i] = dst_expr_addr[i];
    }

    // ToDo: check endianness
    for (size_t i = 0; i < XMM_BYTES / 2; i += packed_size) {
        unsigned offset        = ((i / packed_size) * unpacked_size);
        Expr*    bytes_to_pack = build_concat_expr(
            dst_exprs + offset, dst_addr + offset, unpacked_size, 0);
        for (size_t k = 0; k < packed_size; k++) {
            Expr* e   = new_expr();
            e->opkind = opkind;
            e->op1    = bytes_to_pack;
            SET_EXPR_CONST_OP(e->op2, e->op2_is_const, packed_size);
            SET_EXPR_CONST_OP(e->op3, e->op3_is_const, k);
            dst_expr_addr[i + k] = e;
        }
    }

    for (size_t i = 0; i < (XMM_BYTES / 2); i += packed_size) {
        unsigned offset        = ((i / packed_size) * unpacked_size);
        Expr*    bytes_to_pack = build_concat_expr(
            src_expr_addr + offset, src_addr + offset, unpacked_size, 0);
        for (size_t k = 0; k < packed_size; k++) {
            Expr* e   = new_expr();
            e->opkind = opkind;
            e->op1    = bytes_to_pack;
            SET_EXPR_CONST_OP(e->op2, e->op2_is_const, packed_size);
            SET_EXPR_CONST_OP(e->op3, e->op3_is_const, k);
            dst_expr_addr[(XMM_BYTES / 2) + i + k] = e;
        }
    }
}

static inline void atomic_fetch_op(uint64_t packed_info, uintptr_t a_ptr,
                                   uintptr_t b_val)
{
    uintptr_t t_out_idx         = UNPACK_0(packed_info);
    uintptr_t t_a_idx           = UNPACK_1(packed_info);
    uintptr_t t_b_idx           = UNPACK_2(packed_info);
    uintptr_t size_order_opkind = UNPACK_3(packed_info);

    uintptr_t opkind = size_order_opkind & 0xFF;
    uintptr_t order  = (size_order_opkind >> 8) & 0xF;
    uintptr_t size   = size_order_opkind >> 12;

#if 0
    for (size_t i = 0; i < size; i++) {
        if (a_ptr + i >= 0x4004000028 && a_ptr + i <= 0x4004000028 + 8) {
            tcg_abort();
        }
    }
#endif

    if (s_temps[t_a_idx]) {
        // ToDo: memory slice
        load_concretization(s_temps[t_a_idx], a_ptr);
    }

    Expr** a_exprs = get_expr_addr(a_ptr, size, 0, NULL);

    if (a_exprs == NULL && s_temps[t_b_idx] == NULL) {
        s_temps[t_out_idx] = NULL;
        return;
    }

    int a_is_not_null = 0;
    if (a_exprs) {
        for (size_t i = 0; i < size && a_is_not_null == 0; i++) {
            a_is_not_null |= a_exprs[i] != NULL;
        }
    }

    if (!a_is_not_null && s_temps[t_b_idx] == NULL) {
        s_temps[t_out_idx] = NULL;
        return;
    }

    Expr*     e_a   = NULL;
    uintptr_t a_val = 0;
    if (a_exprs == NULL || !a_is_not_null) {
        switch (size) {
            case 1:
                a_val = *((uint8_t*)a_ptr);
                break;
            case 2:
                a_val = *((uint16_t*)a_ptr);
                break;
            case 4:
                a_val = *((uint32_t*)a_ptr);
                break;
            case 8:
                a_val = *((uint64_t*)a_ptr);
                break;
            default:
                tcg_abort();
        }
    } else {
        e_a = build_concat_expr(a_exprs, (void*)a_ptr, size, 0);
    }
#if 0
    printf("atomic_fetch_op: expr_a=%p expr_b=%p\n", a_exprs, s_temps[t_b_idx]);
#endif
    Expr* e   = new_expr();
    e->opkind = opkind;
    SET_EXPR_OP(e->op1, e->op1_is_const, e_a, a_val);
    SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[t_b_idx], b_val);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, size);

    if (order == 0) {
        s_temps[t_out_idx] = e_a;
    } else {
        s_temps[t_out_idx] = e;
    }

    if (a_exprs == NULL) {
        a_exprs = get_expr_addr(a_ptr, size, 1, NULL);
    }
    for (size_t i = 0; i < size; i++) {
        Expr* e_byte   = new_expr();
        e_byte->opkind = EXTRACT8;
        e_byte->op1    = e;
        SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const, i);
        a_exprs[i] = e_byte;
#if 0
        if (a_ptr + i >= 0x4004000028 && a_ptr + i <= 0x4004000028 + 8) {
            tcg_abort();
        }
#endif
    }
}

static void cmpxchg_handler(uint64_t packed_info, uintptr_t a_ptr,
                            uintptr_t b_val, uintptr_t pc, uintptr_t addr_to)
{
    uintptr_t t_out_idx    = UNPACK_0(packed_info);
    uintptr_t t_a_idx      = UNPACK_1(packed_info);
    uintptr_t t_b_idx      = UNPACK_2(packed_info);
    uintptr_t t_c_idx_size = UNPACK_3(packed_info);

    uintptr_t size    = t_c_idx_size & 0xF;
    uintptr_t t_c_idx = t_c_idx_size >> 4;

    if (s_temps[t_a_idx]) {
        // ToDo: memory slice
        load_concretization(s_temps[t_a_idx], a_ptr);
    }

    Expr** a_exprs = get_expr_addr(a_ptr, size, 0, NULL);
    Expr*  expr_b  = s_temps[t_b_idx];
    Expr*  expr_c  = s_temps[t_c_idx];

    int a_is_not_null = 0;
    if (a_exprs) {
        for (size_t i = 0; i < size && a_is_not_null == 0; i++) {
            a_is_not_null |= a_exprs[i] != NULL;
        }
    }

    if ((a_exprs == NULL || !a_is_not_null) && expr_b == NULL &&
        expr_c == NULL) {
        s_temps[t_out_idx] = NULL;
        return;
    }

    uintptr_t a_val;
    switch (size) {
        case 1:
            a_val = *((uint8_t*)a_ptr);
            break;
        case 2:
            a_val = *((uint16_t*)a_ptr);
            break;
        case 4:
            a_val = *((uint32_t*)a_ptr);
            break;
        case 8:
            a_val = *((uint64_t*)a_ptr);
            break;
        default:
            tcg_abort();
    }

    Expr* expr_a = NULL;
    if (a_exprs != NULL && a_is_not_null) {
        expr_a = build_concat_expr(a_exprs, (void*)a_ptr, size, 0);
    }

    if ((a_exprs != NULL && a_is_not_null) || expr_b != NULL) {
#if 0
        printf("cmpxchg: a_exprs=%p a_is_not_null=%d expr_b=%p\n", 
            a_exprs, a_is_not_null, expr_b);
#endif
        branch_helper_internal(a_val, b_val, TCG_COND_EQ, expr_a, expr_b, 
                                size == 8 ? 0 : size, pc, addr_to);
    }

#if DEBUG_EXPR_CONSISTENCY
    if (expr_a) {
        // printf("CHECK EXPR_A:\n");
        // print_expr(expr_a);
        add_consistency_check(expr_a, a_val, size, CMP_EQ);
    }
    if (expr_b) {
        // printf("CHECK EXPR_B:\n");
        // print_expr(expr_b);
        add_consistency_check(expr_b, b_val, size, CMP_EQ);
    }
#endif

    if (a_val == b_val) {
        if (expr_c == NULL) {
            // clear out memory
            if (a_exprs) {
                for (size_t i = 0; i < size; i++) {
                    a_exprs[i] = NULL;
                }
            }
        } else {
            // write memory
            if (a_exprs == NULL) {
                a_exprs = get_expr_addr(a_ptr, size, 1, NULL);
            }
            for (size_t i = 0; i < size; i++) {
                Expr* e_byte   = new_expr();
                e_byte->opkind = EXTRACT8;
                e_byte->op1    = expr_c;
                SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const, i);
                a_exprs[i] = e_byte;
            }

#if 0
            if (a_ptr == 0x4004000028) {
                printf("\nWriting at %lx pc=%lx:\n", a_ptr, pc);
                print_expr(expr_c);
            }
#endif
        }
    } else {
        s_temps[t_b_idx] = expr_a;
    }
}

static void xchg_handler(uint64_t packed_info, uintptr_t a_ptr)
{
    uintptr_t t_out_idx = UNPACK_0(packed_info);
    uintptr_t t_a_idx   = UNPACK_1(packed_info);
    uintptr_t t_b_idx   = UNPACK_2(packed_info);
    uintptr_t size      = UNPACK_3(packed_info);

    if (s_temps[t_a_idx]) {
        // ToDo: memory slice
        load_concretization(s_temps[t_a_idx], a_ptr);
    }

    Expr** a_exprs = get_expr_addr(a_ptr, size, 0, NULL);
    Expr*  expr_b  = s_temps[t_b_idx];

    int a_is_not_null = 0;
    if (a_exprs) {
        for (size_t i = 0; i < size && a_is_not_null == 0; i++) {
            a_is_not_null |= a_exprs[i] != NULL;
        }
    }

    if ((a_exprs == NULL || !a_is_not_null) && expr_b == NULL) {
        s_temps[t_out_idx] = NULL;
        return;
    }

    Expr* expr_a = NULL;
    if (a_exprs != NULL && a_is_not_null) {
        expr_a = build_concat_expr(a_exprs, (void*)a_ptr, size, 0);
    }
    s_temps[t_out_idx] = expr_a;

    if (s_temps[t_b_idx] != NULL) {
        if (a_exprs == NULL) {
            a_exprs = get_expr_addr(a_ptr, size, 1, NULL);
        }
        for (size_t i = 0; i < size; i++) {
            Expr* e_byte   = new_expr();
            e_byte->opkind = EXTRACT8;
            e_byte->op1    = s_temps[t_b_idx];
            SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const, i);
            a_exprs[i] = e_byte;
        }
    } else {
        if (a_exprs != NULL && a_is_not_null) {
            for (size_t i = 0; i < size; i++) {
                a_exprs[i] = NULL;
            }
        }
    }
}

#define XO(X) offsetof(X86XSaveArea, X)

static void qemu_fxsave(CPUX86State* env, uintptr_t ptr)
{
    int          i, nb_xmm_regs;
    target_ulong addr;

    if (env->hflags & HF_CS64_MASK) {
        nb_xmm_regs = 16;
    } else {
        nb_xmm_regs = 8;
    }

    // printf("FXSAVE at [%lx, %lx] %lu\n", ptr, ptr+512, 16 * XMM_BYTES + XO(legacy.xmm_regs) - XO(legacy.fcw));

    // clear_mem(ptr, 512);
    clear_mem(ptr + XO(legacy.fcw), XO(legacy.xmm_regs) - XO(legacy.fcw));

    addr = ptr + XO(legacy.xmm_regs);
    for (i = 0; i < nb_xmm_regs; i++) {
        qemu_memmove((uintptr_t)&(env->xmm_regs[i]), addr, XMM_BYTES);
        addr += XMM_BYTES;
    }
}

static void qemu_fxrstor(CPUX86State* env, uintptr_t ptr)
{
    int          i, nb_xmm_regs;
    target_ulong addr;

    if (env->hflags & HF_CS64_MASK) {
        nb_xmm_regs = 16;
    } else {
        nb_xmm_regs = 8;
    }

    addr = ptr + XO(legacy.xmm_regs);
    for (i = 0; i < nb_xmm_regs; i++) {
        qemu_memmove(addr, (uintptr_t)&(env->xmm_regs[i]), XMM_BYTES);
        addr += XMM_BYTES;
    }
}

static void qemu_rcl(uint64_t packed_idx, CPUX86State* env, uintptr_t t_0,
                     uintptr_t t_1)
{
    uintptr_t t_out_idx = UNPACK_0(packed_idx);
    uintptr_t t_0_idx   = UNPACK_1(packed_idx);
    uintptr_t t_1_idx   = UNPACK_2(packed_idx);
    uintptr_t t_src_idx = UNPACK_3(packed_idx);

    if (s_temps[t_0_idx] == NULL && s_temps[t_1_idx] == NULL) {
        s_temps[t_out_idx] = NULL;
        s_temps[t_src_idx] = NULL;
        // printf("Helper qemu_rcl: concrete op\n");
    } else {
        // printf("Helper qemu_rcl: symbolic op\n");

        Expr* e   = new_expr();
        e->opkind = RCL;
        SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[t_0_idx], t_0);
        SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[t_1_idx], t_1);
        SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[t_src_idx], env->cc_src);
        s_temps[t_out_idx] = e;

        e         = new_expr();
        e->opkind = EFLAGS_ALL_RCL;
        SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[t_0_idx], t_0);
        SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[t_1_idx], t_1);
        SET_EXPR_OP(e->op3, e->op3_is_const, s_temps[t_src_idx], env->cc_src);
        s_temps[t_src_idx] = e;
    }

    // print_expr(e);
}

static void qemu_divq_EAX(uint64_t packed_idx, uintptr_t rax, uintptr_t rdx,
                          uintptr_t t0)
{
    uintptr_t t_rax_idx = UNPACK_0(packed_idx);
    uintptr_t t_rdx_idx = UNPACK_1(packed_idx);
    uintptr_t t_0_idx   = UNPACK_2(packed_idx);
    uintptr_t mode      = UNPACK_3(packed_idx) & 1; // 0: div, 1: idiv
    assert(mode == 0 || mode == 1);

#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[t_rax_idx]) {
        add_consistency_check(s_temps[t_rax_idx], rax, 8, mode == 0 ? DIVU : DIV);
    }
    if (s_temps[t_rdx_idx]) {
        add_consistency_check(s_temps[t_rdx_idx], rdx, 8, mode == 0 ? DIVU : DIV);
    }
    if (s_temps[t_0_idx]) {
        add_consistency_check(s_temps[t_0_idx], t0, 8, mode == 0 ? DIVU : DIV);
    }
#endif

    if (s_temps[t_rax_idx] == NULL && s_temps[t_rdx_idx] == NULL &&
        s_temps[t_0_idx] == NULL) {
        s_temps[t_rax_idx] = NULL;
        s_temps[t_rdx_idx] = NULL;
    } else {

        // print_expr(s_temps[t_rdx_idx]);
        // print_expr(s_temps[t_rax_idx]);

        Expr* rdxrax   = new_expr();
        rdxrax->opkind = CONCAT;
        SET_EXPR_OP(rdxrax->op1, rdxrax->op1_is_const, s_temps[t_rdx_idx], rdx);
        SET_EXPR_OP(rdxrax->op2, rdxrax->op2_is_const, s_temps[t_rax_idx], rax);

        Expr* d   = new_expr();
        d->opkind = mode == 0 ? DIVU : DIV;
        d->op1    = rdxrax;
        SET_EXPR_OP(d->op2, d->op2_is_const, s_temps[t_0_idx], t0);

        Expr* d2   = new_expr();
        d2->opkind = EXTRACT;
        d2->op1    = d;
        SET_EXPR_CONST_OP(d2->op2, d2->op2_is_const, 63);
        SET_EXPR_CONST_OP(d2->op3, d2->op3_is_const, 0);
        s_temps[t_rax_idx] = d2;

        // print_expr(d2);

        Expr* r   = new_expr();
        r->opkind = mode == 0 ? REMU : REM;
        r->op1    = rdxrax;
        SET_EXPR_OP(r->op2, r->op2_is_const, s_temps[t_0_idx], t0);

        Expr* r2   = new_expr();
        r2->opkind = EXTRACT;
        r2->op1    = r;
        SET_EXPR_CONST_OP(r2->op2, r2->op2_is_const, 63);
        SET_EXPR_CONST_OP(r2->op3, r2->op3_is_const, 0);
        s_temps[t_rdx_idx] = r2;
    }

    // print_expr(e);
}

static void qemu_divl_EAX(uint64_t packed_idx, uintptr_t rax, uintptr_t rdx,
                          uintptr_t t0)
{
    uintptr_t t_rax_idx = UNPACK_0(packed_idx);
    uintptr_t t_rdx_idx = UNPACK_1(packed_idx);
    uintptr_t t_0_idx   = UNPACK_2(packed_idx);
    uintptr_t mode      = UNPACK_3(packed_idx) & 1; // 0: div, 1: idiv
    assert(mode == 0 || mode == 1);

#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[t_rax_idx]) {
        add_consistency_check(s_temps[t_rax_idx], rax, 8, mode == 0 ? DIVU : DIV);
    }
    if (s_temps[t_rdx_idx]) {
        add_consistency_check(s_temps[t_rdx_idx], rdx, 8, mode == 0 ? DIVU : DIV);
    }
    if (s_temps[t_0_idx]) {
        add_consistency_check(s_temps[t_0_idx], t0, 8, mode == 0 ? DIVU : DIV);
    }
#endif

    if (s_temps[t_rax_idx] == NULL && s_temps[t_rdx_idx] == NULL &&
        s_temps[t_0_idx] == NULL) {
        s_temps[t_rax_idx] = NULL;
        s_temps[t_rdx_idx] = NULL;
    } else {
#if 0
        print_expr(s_temps[t_rdx_idx]);
        print_expr(s_temps[t_rax_idx]);
#endif
        Expr* edx   = new_expr();
        edx->opkind = EXTRACT;
        SET_EXPR_OP(edx->op1, edx->op1_is_const, s_temps[t_rdx_idx], rdx);
        SET_EXPR_CONST_OP(edx->op2, edx->op2_is_const, 31);
        SET_EXPR_CONST_OP(edx->op3, edx->op3_is_const, 0);

        Expr* eax   = new_expr();
        eax->opkind = EXTRACT;
        SET_EXPR_OP(eax->op1, eax->op1_is_const, s_temps[t_rax_idx], rax);
        SET_EXPR_CONST_OP(eax->op2, eax->op2_is_const, 31);
        SET_EXPR_CONST_OP(eax->op3, eax->op3_is_const, 0);

        Expr* t_0   = new_expr();
        t_0->opkind = EXTRACT;
        SET_EXPR_OP(t_0->op1, t_0->op1_is_const, s_temps[t_0_idx], t0);
        SET_EXPR_CONST_OP(t_0->op2, t_0->op2_is_const, 31);
        SET_EXPR_CONST_OP(t_0->op3, t_0->op3_is_const, 0);

        Expr* edxeax   = new_expr();
        edxeax->opkind = CONCAT;
        edxeax->op1    = edx;
        edxeax->op2    = eax;

        Expr* d   = new_expr();
        d->opkind = mode == 0 ? DIVU : DIV;
        d->op1    = edxeax;
        d->op2    = t_0;

        Expr* d2   = new_expr();
        d2->opkind = EXTRACT;
        d2->op1    = d;
        SET_EXPR_CONST_OP(d2->op2, d2->op2_is_const, 31);
        SET_EXPR_CONST_OP(d2->op3, d2->op3_is_const, 0);
        s_temps[t_rax_idx] = d2;

        Expr* r   = new_expr();
        r->opkind = mode == 0 ? REMU : REM;
        r->op1    = edxeax;
        r->op2    = t_0;

        Expr* r2   = new_expr();
        r2->opkind = EXTRACT;
        r2->op1    = r;
        SET_EXPR_CONST_OP(r2->op2, r2->op2_is_const, 31);
        SET_EXPR_CONST_OP(r2->op3, r2->op3_is_const, 0);
        s_temps[t_rdx_idx] = r2;
    }

    // print_expr(e);
}

static void qemu_divw_AX(uint64_t packed_idx, uintptr_t rax, uintptr_t rdx,
                          uintptr_t t0)
{
    uintptr_t t_rax_idx = UNPACK_0(packed_idx);
    uintptr_t t_rdx_idx = UNPACK_1(packed_idx);
    uintptr_t t_0_idx   = UNPACK_2(packed_idx);
    uintptr_t mode      = UNPACK_3(packed_idx) & 1; // 0: div, 1: idiv
    assert(mode == 0 || mode == 1);

    if (s_temps[t_rax_idx] == NULL && s_temps[t_rdx_idx] == NULL &&
        s_temps[t_0_idx] == NULL) {
        s_temps[t_rax_idx] = NULL;
        s_temps[t_rdx_idx] = NULL;
    } else {
#if 0
        print_expr(s_temps[t_rdx_idx]);
        print_expr(s_temps[t_rax_idx]);
#endif
        Expr* edx   = new_expr();
        edx->opkind = EXTRACT;
        SET_EXPR_OP(edx->op1, edx->op1_is_const, s_temps[t_rdx_idx], rdx);
        SET_EXPR_CONST_OP(edx->op2, edx->op2_is_const, 15);
        SET_EXPR_CONST_OP(edx->op3, edx->op3_is_const, 0);

        Expr* eax   = new_expr();
        eax->opkind = EXTRACT;
        SET_EXPR_OP(eax->op1, eax->op1_is_const, s_temps[t_rax_idx], rax);
        SET_EXPR_CONST_OP(eax->op2, eax->op2_is_const, 15);
        SET_EXPR_CONST_OP(eax->op3, eax->op3_is_const, 0);

        Expr* t_0   = new_expr();
        t_0->opkind = EXTRACT;
        SET_EXPR_OP(t_0->op1, t_0->op1_is_const, s_temps[t_0_idx], t0);
        SET_EXPR_CONST_OP(t_0->op2, t_0->op2_is_const, 15);
        SET_EXPR_CONST_OP(t_0->op3, t_0->op3_is_const, 0);

        Expr* edxeax   = new_expr();
        edxeax->opkind = CONCAT;
        edxeax->op1    = edx;
        edxeax->op2    = eax;

        Expr* d   = new_expr();
        d->opkind = mode == 0 ? DIVU : DIV;
        d->op1    = edxeax;
        d->op2    = t_0;

        Expr* d2   = new_expr();
        d2->opkind = EXTRACT;
        d2->op1    = d;
        SET_EXPR_CONST_OP(d2->op2, d2->op2_is_const, 15);
        SET_EXPR_CONST_OP(d2->op3, d2->op3_is_const, 0);
        s_temps[t_rax_idx] = d2;

        Expr* r   = new_expr();
        r->opkind = mode == 0 ? REMU : REM;
        r->op1    = edxeax;
        r->op2    = t_0;

        Expr* r2   = new_expr();
        r2->opkind = EXTRACT;
        r2->op1    = r;
        SET_EXPR_CONST_OP(r2->op2, r2->op2_is_const, 15);
        SET_EXPR_CONST_OP(r2->op3, r2->op3_is_const, 0);

        s_temps[t_rdx_idx] = r2;
    }

    // print_expr(e);
}

static void qemu_divb_AL(uint64_t packed_idx, uintptr_t rax, uintptr_t rdx,
                          uintptr_t t0)
{
    uintptr_t t_rax_idx = UNPACK_0(packed_idx);
    uintptr_t t_0_idx   = UNPACK_1(packed_idx);
    uintptr_t mode      = UNPACK_2(packed_idx); // 0: div, 1: idiv
    assert(mode == 0 || mode == 1);

    if (s_temps[t_rax_idx] == NULL && s_temps[t_0_idx] == NULL) {
        s_temps[t_rax_idx] = NULL;
    } else {
#if 0
        print_expr(s_temps[t_rax_idx]);
#endif

        Expr* eax   = new_expr();
        eax->opkind = EXTRACT;
        SET_EXPR_OP(eax->op1, eax->op1_is_const, s_temps[t_rax_idx], rax);
        SET_EXPR_CONST_OP(eax->op2, eax->op2_is_const, 15);
        SET_EXPR_CONST_OP(eax->op3, eax->op3_is_const, 0);

        Expr* t_0   = new_expr();
        t_0->opkind = EXTRACT;
        SET_EXPR_OP(t_0->op1, t_0->op1_is_const, s_temps[t_0_idx], t0);
        SET_EXPR_CONST_OP(t_0->op2, t_0->op2_is_const, 7);
        SET_EXPR_CONST_OP(t_0->op3, t_0->op3_is_const, 0);

        Expr* d   = new_expr();
        d->opkind = mode == 0 ? DIVU : DIV;
        d->op1    = eax;
        d->op2    = t_0;

        Expr* d2   = new_expr();
        d2->opkind = EXTRACT;
        d2->op1    = d;
        SET_EXPR_CONST_OP(d2->op2, d2->op2_is_const, 7);
        SET_EXPR_CONST_OP(d2->op3, d2->op3_is_const, 0);

        Expr* r   = new_expr();
        r->opkind = mode == 0 ? REMU : REM;
        r->op1    = eax;
        r->op2    = t_0;

        Expr* r2   = new_expr();
        r2->opkind = EXTRACT;
        r2->op1    = r;
        SET_EXPR_CONST_OP(r2->op2, r2->op2_is_const, 7);
        SET_EXPR_CONST_OP(r2->op3, r2->op3_is_const, 0);

        Expr* r2d2   = new_expr();
        r2d2->opkind = CONCAT;
        r2d2->op1    = r2;
        r2d2->op2    = d2;

        s_temps[t_rax_idx] = r2d2;
    }

    // print_expr(e);
}

#if 0
static inline void xmm_memmove(uint8_t* src, uint8_t* dst, uintptr_t size,
                               uintptr_t rdx_idx)
{
    src = src - size;
    dst = dst - size;

    assert(src != dst);

    if (s_temps[rdx_idx]) {
        Expr* e   = new_expr();
        e->opkind = SUB;
        e->op1    = s_temps[rdx_idx];
        SET_EXPR_CONST_OP(e->op2, e->op2_is_const, size);
        s_temps[rdx_idx] = e;
    }

    Expr** src_exprs = get_expr_addr((uintptr_t)src, size, 0);
    Expr** dst_exprs = get_expr_addr((uintptr_t)dst, size, 0);

    // printf("Memmove\n");
    for (size_t i = 0; i < size; i++) {
        dst_exprs[i] = src_exprs[i];
        // print_expr(dst_exprs[i]);
    }
}

static inline void instrument_memmove_xmm(TCGOp* op, TCGContext* tcg_ctx)
{
    TCGTemp* t_rsi  = tcg_find_temp_arch_reg(tcg_ctx, "rsi");
    TCGTemp* t_rdi  = tcg_find_temp_arch_reg(tcg_ctx, "rdi");
    TCGTemp* t_rdx  = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
    TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_size, (uintptr_t)0x40, 0, op, NULL, tcg_ctx);
    TCGTemp* t_rdx_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_rdx_idx, (uintptr_t)temp_idx(t_rdx), 0, op, NULL, tcg_ctx);
    MARK_TEMP_AS_ALLOCATED(t_rsi);
    MARK_TEMP_AS_ALLOCATED(t_rdi);
    add_void_call_4(xmm_memmove, t_rsi, t_rdi, t_size, t_rdx_idx, op, NULL,
                    tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_rsi);
    MARK_TEMP_AS_NOT_ALLOCATED(t_rdi);
    tcg_temp_free_internal(t_size);
    tcg_temp_free_internal(t_rdx);
}

#define TEST_OPCODE(pattern, opc, index, failure)                              \
    if (pattern[index] == opc) {                                               \
        index += 1;                                                            \
    } else {                                                                   \
        failure = 1;                                                           \
    }

static inline int detect_memmove_xmm(TCGContext* tcg_ctx)
{
    /*
        0x4000d2e67f:  0f 10 06                 movups   (%rsi), %xmm0
        0x4000d2e682:  0f 10 4e 10              movups   0x10(%rsi), %xmm1
        0x4000d2e686:  0f 10 56 20              movups   0x20(%rsi), %xmm2
        0x4000d2e68a:  0f 10 5e 30              movups   0x30(%rsi), %xmm3
        0x4000d2e68e:  48 83 c6 40              addq     $0x40, %rsi
        0x4000d2e692:  48 83 ea 40              subq     $0x40, %rdx
        0x4000d2e696:  0f 29 07                 movaps   %xmm0, (%rdi)
        0x4000d2e699:  0f 29 4f 10              movaps   %xmm1, 0x10(%rdi)
        0x4000d2e69d:  0f 29 57 20              movaps   %xmm2, 0x20(%rdi)
        0x4000d2e6a1:  0f 29 5f 30              movaps   %xmm3, 0x30(%rdi)
        0x4000d2e6a5:  48 83 c7 40              addq     $0x40, %rdi
        0x4000d2e6a9:  48 83 fa 40              cmpq     $0x40, %rdx
        0x4000d2e6ad:  77 d0                    ja       0x4000d2e67f
    */

    TCGOpcode pattern[] = {
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_qemu_ld_i64, INDEX_op_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_mov_i64,     INDEX_op_discard,
        INDEX_op_discard, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_sub_i64,
        INDEX_op_mov_i64,     INDEX_op_mov_i64,
        INDEX_op_mov_i64, /* NEXT */
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64,
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_ld_i64,      INDEX_op_qemu_st_i64, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_add_i64,
        INDEX_op_mov_i64,     INDEX_op_discard, /* NEXT */
        INDEX_op_movi_i64,    INDEX_op_mov_i64,
        INDEX_op_sub_i64, /* NEXT */
    };

    uint8_t start       = 0;
    size_t  index       = 0;
    size_t  pattern_len = sizeof(pattern) / sizeof(TCGOpcode);
    TCGOp*  op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        uint8_t failure = 0;
        switch (op->opc) {
            case INDEX_op_insn_start:
                start = 1;
                break;
            default:
                if (start && index < pattern_len) {
#if 0
                    printf("Current=%s expected=%s\n",
                           tcg_op_defs[op->opc].name,
                           tcg_op_defs[pattern[index]].name);
#endif
                    TEST_OPCODE(pattern, op->opc, index, failure);
                }
        }
        if (start && failure) {
            // printf("Pattern not found\n");
            break;
        }
    }

    if (index == pattern_len) {
        return pattern_len;
    }

    // printf("Pattern not found (index=%lu)\n", index);
    return -1;
}
#endif