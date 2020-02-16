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
            return 0;
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
        case CC_OP_ADCX:
            return EFLAGS_ALL_ADCX;
        case CC_OP_ADOX:
            return EFLAGS_ALL_ADOX;
        case CC_OP_ADCOX:
            return EFLAGS_ALL_ADCOX;

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

static Expr** get_expr_addr(uintptr_t addr, size_t size, uint8_t allocate)
{
    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) {
        if (!allocate) {
            return NULL;
        }
        l2_page                             = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size < 1 << L3_PAGE_BITS); // ToDo: cross page access

    l3_page_t* l3_page = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) {
        if (!allocate) {
            return NULL;
        }
        l3_page                       = g_malloc0(sizeof(l3_page_t));
        l2_page->entries[l2_page_idx] = l3_page;
    }

    return &l3_page->entries[l3_page_idx];
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
            n_expr->opkind = CONCAT8;
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

static void qemu_xmm_op(uintptr_t opkind, uint8_t* dst_addr, uint8_t* src_addr,
                        uintptr_t packed_slice_pc)
{
    uintptr_t slice = packed_slice_pc & 0xFF;
    assert(slice <= 16);

    Expr** dst_expr_addr = get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0);
    Expr** src_expr_addr = get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0);
    if (dst_expr_addr == NULL && src_expr_addr == NULL) {
        // printf("qemu_xmm_op_bytewise: both regs are concrete\n");
        return;
    }

    if ((opkind == XOR || opkind == SUB || opkind == EQ) &&
        dst_addr == src_addr) {
        // xmm reg will be concrete
        for (size_t i = 0; i < XMM_BYTES; i++) {
            dst_expr_addr[i] = NULL;
        }
        return;
    }

    for (size_t i = 0; i < XMM_BYTES; i += slice) {

        uint8_t src_is_not_null = 0;
        uint8_t dst_is_not_null = 0;
        assert(src_expr_addr && dst_expr_addr);
        for (size_t k = 0; k < slice && !src_is_not_null && !dst_is_not_null;
             k++) {
            src_is_not_null |= src_expr_addr[i + k] != NULL;
            dst_is_not_null |= dst_expr_addr[i + k] != NULL;
        }
        if (!src_is_not_null && !dst_is_not_null) {
            // no need to clear dst since it is already fully concrete
            continue;
        }

#if 0
        // uintptr_t pc = packed_slice_pc >> 8;
        printf("[+] qemu_xmm_op: pc=%lx opkind=%s src_addr=%p dst_addr=%p slice=%lu count=%ld\n",
            pc, opkind_to_str(opkind), src_addr, dst_addr, slice, i);
#endif

        Expr* e   = new_expr();
        e->opkind = opkind;

        Expr* src_slice;
        Expr* dst_slice;
        if (slice > 1) {
            // ToDo: optimize when one of the two is fully concrete
            src_slice =
                build_concat_expr(&src_expr_addr[i], &src_addr[i], slice, 0);
            dst_slice =
                build_concat_expr(&dst_expr_addr[i], &dst_addr[i], slice, 0);

            e->op1    = dst_slice;
            e->op2    = src_slice;
        } else {
            SET_EXPR_OP(e->op1, e->op1_is_const, src_expr_addr[i], src_addr[i]);
            SET_EXPR_OP(e->op2, e->op2_is_const, dst_expr_addr[i], dst_addr[i]);
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

static void qemu_xmm_pmovmskb(uintptr_t dst_idx, uint64_t* src_addr)
{
    Expr** src_expr_addr = get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0);
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

    // printf("qemu_xmm_pmovmskb: symbolic xmm reg\n");
    // print_expr(e);
}

static void qemu_xmm_movl_mm_T0(uint64_t* dst_addr, uintptr_t src_idx)
{
    Expr** dst_expr_addr = get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0);
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
    // src is 32 bit
    for (size_t i = 0; i < sizeof(uint32_t); i++) {
        Expr* e_byte   = new_expr();
        e_byte->opkind = EXTRACT8;
        e_byte->op1    = s_temps[src_idx];
        SET_EXPR_CONST_OP(e_byte->op2, e_byte->op2_is_const,
                          i); // ToDo: check endianess!!!
        dst_expr_addr[i] = e_byte;
    }
    for (size_t i = sizeof(uint32_t); i < XMM_BYTES; i++) {
        dst_expr_addr[i] = NULL;
    }
}

static void qemu_xmm_pshufd(uint64_t* dst_addr, uint64_t* src_addr,
                            uintptr_t order)
{
    Expr** dst_expr_addr = get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0);
    Expr** src_expr_addr = get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0);

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
    printf("Helper qemu_xmm_pshufd: symbolic op\n");
#endif
    uint8_t count = 0;
    for (size_t i = 0; i < XMM_BYTES; i += sizeof(uint32_t)) {
        // ToDo: check endianness
        uint8_t src_pos = ((order >> (2 * count++)) & 3) * 4;
        for (size_t k = 0; k < sizeof(uint32_t); k++) {
            dst_expr_addr[i + k] = src_expr_addr[src_pos + k];
        }
    }
}

static void qemu_xmm_punpck(uint64_t* dst_addr, uint64_t* src_addr,
                            uintptr_t slice, uint8_t lowbytes)
{
    Expr** dst_expr_addr = get_expr_addr((uintptr_t)dst_addr, XMM_BYTES, 0);
    Expr** src_expr_addr = get_expr_addr((uintptr_t)src_addr, XMM_BYTES, 0);

    if (src_expr_addr == NULL && dst_expr_addr == NULL) {
        return;
    }

    int src_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && src_is_not_null == 0 && src_expr_addr; i++) {
        src_is_not_null |= src_expr_addr[i] != NULL;
    }

    int dst_is_not_null = 0;
    for (size_t i = 0; i < XMM_BYTES && dst_is_not_null == 0 && dst_expr_addr; i++) {
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

#define XO(X) offsetof(X86XSaveArea, X)

static Expr* xmm_save_state[XMM_BYTES * 16];

static void qemu_fxsave(CPUX86State* env, uintptr_t ptr)
{
    int          i, nb_xmm_regs;
    target_ulong addr;

    if (env->hflags & HF_CS64_MASK) {
        nb_xmm_regs = 16;
    } else {
        nb_xmm_regs = 8;
    }

    // addr = ptr + XO(legacy.xmm_regs);
    addr = 0;

    for (i = 0; i < nb_xmm_regs; i++) {
        Expr** src_expr_addr =
            get_expr_addr((uintptr_t) & (env->xmm_regs[i]), XMM_BYTES, 0);

#if 0
        printf("FXSAVE: xmm at %p\n", & (env->xmm_regs[i]));
#endif
        for (size_t k = 0; k < XMM_BYTES; k++) {
            if (src_expr_addr == NULL) {
                xmm_save_state[addr + k] = NULL;
            } else {
                xmm_save_state[addr + k] = src_expr_addr[k];
                //print_expr(src_expr_addr[k]);
            }
        }

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

    // addr = ptr + XO(legacy.xmm_regs);
    addr = 0;

    for (i = 0; i < nb_xmm_regs; i++) {

        Expr** dst_expr_addr =
            get_expr_addr((uintptr_t) & (env->xmm_regs[i]), XMM_BYTES, 0);
#if 0
        printf("FXRSTOR: xmm at %p\n", & (env->xmm_regs[i]));
#endif
        for (size_t k = 0; k < XMM_BYTES; k++) {
            if (dst_expr_addr) {
                dst_expr_addr[k] = xmm_save_state[addr + k];
                //print_expr(dst_expr_addr[k]);
            } else {
                assert(xmm_save_state[addr + k] == NULL);
            }
        }

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
    uintptr_t mode      = UNPACK_3(packed_idx); // 0: div, 1: idiv
    assert(mode == 0 || mode == 1);

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
        SET_EXPR_CONST_OP(d2->op2, d2->op2_is_const, 31);
        SET_EXPR_CONST_OP(d2->op3, d2->op3_is_const, 0);
        s_temps[t_rax_idx] = d2;

        // print_expr(d2);

        Expr* r   = new_expr();
        r->opkind = mode == 0 ? REMU : REM;
        d->op1    = rdxrax;
        SET_EXPR_OP(r->op2, r->op2_is_const, s_temps[t_0_idx], t0);

        Expr* r2   = new_expr();
        r2->opkind = EXTRACT;
        r2->op1    = r;
        SET_EXPR_CONST_OP(r2->op2, r2->op2_is_const, 31);
        SET_EXPR_CONST_OP(r2->op3, r2->op3_is_const, 0);
        s_temps[t_rdx_idx] = r2;
    }

    // print_expr(e);
}

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

#if 0
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