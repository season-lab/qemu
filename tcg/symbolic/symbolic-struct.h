#ifndef SYMBOLIC_STRUCT_H
#define SYMBOLIC_STRUCT_H

#include <stdlib.h>
#include <assert.h>

// same as tcg_abort()
#ifndef ABORT
#define ABORT()                                                                \
    do {                                                                       \
        fprintf(stderr, "%s:%d: tcg fatal error\n", __FILE__, __LINE__);       \
        abort();                                                               \
    } while (0)
#endif

#define EXPR_POOL_CAPACITY  (1024 * 1024 * 8)
#define EXPR_QUERY_CAPACITY (256 * 1024)
#define EXPR_POOL_SHM_KEY   (0xDEADBEEF + 2)
#define EXPR_POOL_ADDR      ((const void*)0x7f05c8cc7000)
#define QUERY_SHM_KEY       0xCAFECAFE
#define FINAL_QUERY         ((void*)0xDEAD)
#define SHM_READY           (0xDEADBEEF)
#define MEM_BARRIER()       asm volatile("" ::: "memory")

#define PACK_0(p, v) (p | (v & 0xFFFF))
#define PACK_1(p, v) (p | ((v & 0xFFFF) << 16))
#define PACK_2(p, v) (p | ((v & 0xFFFF) << 32))
#define PACK_3(p, v) (p | ((v & 0xFFFF) << 48))

#define UNPACK_0(p) (p & 0xFFFF)
#define UNPACK_1(p) ((p >> 16) & 0xFFFF)
#define UNPACK_2(p) ((p >> 32) & 0xFFFF)
#define UNPACK_3(p) ((p >> 48) & 0xFFFF)

#define DEPOSIT_MASK(pos, len) (((((uintptr_t)1LU) << len) - 1) << pos)

typedef enum OPKIND {
    RESERVED,
    //
    IS_CONST, // constants could also be embedded within an operand
    IS_SYMBOLIC,
    // unary
    NEG,
    NOT,
    // binary
    ADD,
    SUB, // 6
    MUL,
    MULU,
    DIV,
    DIVU, // 10
    REM,
    REMU,
    AND, // 13
    OR,
    XOR, // 15
    SHL,
    SHR,
    SAR,
    SAL,
    ROTL,
    ROTR,
    //
    EQ, // 22
    NE,
    // signed
    LT, // 24
    LE,
    GE,
    GT,
    // unsigned
    LTU, // 28
    LEU,
    GEU,
    GTU,
    // binary
    ZEXT, // ZEXT(arg0, n): zero-extend arg0 from the n-1 msb bits
    SEXT, // SEXT(arg0, n): sign-extend arg0 from the n-1 msb bits
    // binary
    CONCAT,   // 34
    CONCAT8,  // CONCAT8(arg0, arg1): concat one byte (arg1) to arg0
    EXTRACT8, // EXTRACT8(arg0, i): extract i-th byte from arg0
    EXTRACT,
    // ternary
    DEPOSIT, // DEPOSIT(arg0, arg1, arg2, pos, len):
             //    arg0 = (arg1 & ~MASK(pos, len)) | ((arg2 << pos) & MASK(pos,
             //    len))
             // where: MASK(pos, len) build a mask of bits, where len bits are
             // set to one starting at position 8 (going towards msb). e.g.,
             // MASK(8, 4) = 0x0f00
    QZEXTRACT, // EXTRACT(arg0, arg1, pos, len):
               //    arg0 = (arg1 << (N_BITS-(pos+len))) >> (N_BITS-len)
               // e.g., EXTRACT(arg0, arg1, 8, 4):
               //  when N_BITS=32 then arg0 = (arg1 << 20) >> 28
    QSEXTRACT, // same as EXTRACT but using arithmetic shift
    QZEXTRACT2,
    //
    CTZ, // count trailing zeros (x86: BSF, TZCNT)
    RCL,
    //
    ITE, // 42
    ITE_EQ_ZERO,
    ITE_NE_ZERO,
    OR_3,
    XOR_3,
    // XMM
    PMOVMSKB, // 47
    CMP_EQ,
    CMP_GT,
    CMP_GE,
    CMP_LE,
    CMP_LT,
    MIN,
    // double binop
    MUL_HIGH, // 56
    MULU_HIGH,
    //
    EFLAGS_ALL_ADD,
    EFLAGS_ALL_ADCB,
    EFLAGS_ALL_ADCW,
    EFLAGS_ALL_ADCL,
    EFLAGS_ALL_ADCQ,
    EFLAGS_ALL_SUB,
    EFLAGS_ALL_MUL,
    EFLAGS_ALL_SBBB,
    EFLAGS_ALL_SBBW,
    EFLAGS_ALL_SBBL,
    EFLAGS_ALL_SBBQ,
    EFLAGS_ALL_LOGIC,
    EFLAGS_ALL_INC,
    EFLAGS_ALL_DEC,
    EFLAGS_ALL_SHL,
    EFLAGS_ALL_SAR,
    EFLAGS_ALL_BMILG,
    EFLAGS_ALL_ADCX,
    EFLAGS_ALL_ADOX,
    EFLAGS_ALL_ADCOX,
    EFLAGS_ALL_RCL,
    //
    EFLAGS_C_ADD,
    EFLAGS_C_ADCB,
    EFLAGS_C_ADCW,
    EFLAGS_C_ADCL,
    EFLAGS_C_ADCQ,
    EFLAGS_C_SUB,
    EFLAGS_C_MUL,
    EFLAGS_C_SBBB,
    EFLAGS_C_SBBW,
    EFLAGS_C_SBBL,
    EFLAGS_C_SBBQ,
    EFLAGS_C_LOGIC,
    EFLAGS_C_SHL,
    EFLAGS_C_BMILG,
    //
    SYMBOLIC_PC,
    SYMBOLIC_JUMP_TABLE_ACCESS,
    MEMORY_SLICE,
    MEMORY_SLICE_ACCESS,
    SYMBOLIC_LOAD,
    SYMBOLIC_STORE,
} OPKIND;

typedef enum EXTENDKIND {
    ZEXT_8,
    ZEXT_16,
    ZEXT_32,
    //
    SEXT_8,
    SEXT_16,
    SEXT_32,
} EXTENDKIND;

typedef struct Expr {
    struct Expr* op1;
    struct Expr* op2;
    struct Expr* op3;
    uint8_t      opkind;
    uint8_t      op1_is_const;
    uint8_t      op2_is_const;
    uint8_t      op3_is_const;
} Expr;

typedef struct Query {
    Expr*     query;
    uintptr_t address;
    uint8_t   arg0;
    uint8_t   arg1;
    uint8_t   arg2;
    uint8_t   arg3;
} Query;

extern Expr* pool;
#define GET_EXPR_IDX(e)  (((Expr*)e) - ((Expr*)pool))
#define GET_QUERY_IDX(q) ((((Query*)q) - ((Query*)query_queue)) - 1)

static inline const char* opkind_to_str(uint8_t opkind)
{
    switch (opkind) {
        case IS_SYMBOLIC:
            return "symbolic_data";
        case NOT:
            return "~";
        case NEG:
            return "-";
        case ADD:
            return "+";
        case SUB:
            return "-";
        case MUL:
            return "*";
        case DIV:
            return "/";
        case DIVU:
            return "/u";
        case REM:
            return "\%";
        case REMU:
            return "\%u";
        case AND:
            return "&";
        case OR:
            return "|";
        case XOR: // 13
            return "^";
        case SHR: // 14
            return "l>>";
        case SHL: // 15
            return "l<<";
        case SAL:
            return "a<<";
        case SAR:
            return "a>>";
        case ROTL:
            return "rotl";
        case ROTR:
            return "rotr";

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

        case CONCAT:
            return "..";

        case EXTRACT8:
            return "EXTRACT8";
        case EXTRACT:
            return "EXTRACT";
        case CONCAT8:
            return "CONCAT8";

        case CTZ:
            return "CTZ";
        case RCL:
            return "RCL";

        case DEPOSIT:
            return "DEPOSIT";
        case QZEXTRACT2:
            return "QZEXTRACT2";

        case ITE:
            return "ITE";
        case ITE_EQ_ZERO:
            return "ITE_EQ_ZERO";
        case ITE_NE_ZERO:
            return "ITE_NE_ZERO";
        case OR_3:
            return "OR_3";
        case XOR_3:
            return "XOR_3";

        case CMP_EQ:
            return "CMPB";
        case PMOVMSKB:
            return "PMOVMSKB";

        case MUL_HIGH:
            return "MUL_HIGH";
        case MULU_HIGH:
            return "MULU_HIGH";

        case EFLAGS_ALL_ADD:
        case EFLAGS_ALL_ADCB:
        case EFLAGS_ALL_ADCW:
        case EFLAGS_ALL_ADCL:
        case EFLAGS_ALL_ADCQ:
        case EFLAGS_ALL_SUB:
        case EFLAGS_ALL_MUL:
        case EFLAGS_ALL_SBBB:
        case EFLAGS_ALL_SBBW:
        case EFLAGS_ALL_SBBL:
        case EFLAGS_ALL_SBBQ:
        case EFLAGS_ALL_LOGIC:
        case EFLAGS_ALL_INC:
        case EFLAGS_ALL_DEC:
        case EFLAGS_ALL_SHL:
        case EFLAGS_ALL_SAR:
        case EFLAGS_ALL_BMILG:
        case EFLAGS_ALL_ADCX:
        case EFLAGS_ALL_ADOX:
        case EFLAGS_ALL_ADCOX:
            return "EFLAGS_ALL_OP";
        case EFLAGS_ALL_RCL:
            return "EFLAGS_ALL_RCL";

        case EFLAGS_C_ADD:
            return "EFLAGS_C_ADD";
        case EFLAGS_C_ADCB:
            return "EFLAGS_C_ADCB";
        case EFLAGS_C_ADCW:
            return "EFLAGS_C_ADCW";
        case EFLAGS_C_ADCL:
            return "EFLAGS_C_ADCL";
        case EFLAGS_C_ADCQ:
            return "EFLAGS_C_ADCQ";
        case EFLAGS_C_SUB:
            return "EFLAGS_C_SUB";
        case EFLAGS_C_MUL:
            return "EFLAGS_C_MUL";
        case EFLAGS_C_SBBB:
            return "EFLAGS_C_SBBB";
        case EFLAGS_C_SBBW:
            return "EFLAGS_C_SBBW";
        case EFLAGS_C_SBBL:
            return "EFLAGS_C_SBBL";
        case EFLAGS_C_SBBQ:
            return "EFLAGS_C_SBBQ";
        case EFLAGS_C_LOGIC:
            return "EFLAGS_C_LOGIC";
        case EFLAGS_C_SHL:
            return "EFLAGS_C_SHL";

        case SYMBOLIC_JUMP_TABLE_ACCESS:
            return "SYMBOLIC_JUMP_TABLE_ACCESS";
        case SYMBOLIC_PC:
            return "SYMBOLIC_PC";
        case MEMORY_SLICE:
            return "MEMORY_SLICE";

        default:
            printf("\nstr(opkind=%u) is unknown\n", opkind);
            ABORT();
    }
}

#define MAX_PRINT_CHECK (1024 * 1024)
uint8_t            printed[MAX_PRINT_CHECK];
static inline void print_expr_internal(Expr* expr, uint8_t reset)
{
    if (reset)
        for (size_t i = 0; i < MAX_PRINT_CHECK; i++)
            printed[i] = 0;

    printf("expr:");
    if (expr == NULL) {
        printf(" NULL\n");
        return;
    }

    assert(expr->op1_is_const == 0 || expr->op1_is_const == 1);
    assert(expr->op2_is_const == 0 || expr->op2_is_const == 1);
    assert(expr->op3_is_const == 0 || expr->op3_is_const == 1);

    // printf(" addr=%p", expr);
    printf(" id=%lu", GET_EXPR_IDX(expr));
    if (expr) {
        printf(" is_symbolic_input=%u", expr->opkind == IS_SYMBOLIC);
        printf(" op1_is_const=%u", expr->op1_is_const);
        printf(" op2_is_const=%u", expr->op2_is_const);
        if (expr->opkind == IS_SYMBOLIC)
            printf(" INPUT_%lu\n", (uintptr_t)expr->op1);
        else if (expr->opkind == IS_CONST)
            printf(" 0x%lu\n", (uintptr_t)expr->op1);
        else {

            if (expr->op1_is_const || expr->op1 == NULL)
                printf(" 0x%lx", (uintptr_t)expr->op1);
            else
                printf(" E_%lu", GET_EXPR_IDX(expr->op1));

            printf(" %s", opkind_to_str(expr->opkind));

            if (expr->opkind != NEG && expr->opkind != PMOVMSKB) {
                if (expr->op2_is_const || expr->opkind == EXTRACT8 ||
                    expr->opkind == ZEXT || expr->opkind == SEXT ||
                    expr->op2 == NULL)
                    printf(" 0x%lx", (uintptr_t)expr->op2);
                else
                    printf(" E_%lu", GET_EXPR_IDX(expr->op2));
            }

            if (expr->opkind == EFLAGS_C_ADCQ || expr->op3_is_const) {
                if (expr->op3_is_const)
                    printf(" 0x%lx", (uintptr_t)expr->op3);
                else
                    printf(" E_%lu", GET_EXPR_IDX(expr->op3));
            }
            printf("\n");

            // FixMe: this makes a mess

            assert(expr != expr->op1);
            assert(expr != expr->op2);

            if (!expr->op1_is_const && expr->op1 != NULL) {
                assert(GET_EXPR_IDX(expr->op1) < MAX_PRINT_CHECK);
                if (!printed[GET_EXPR_IDX(expr->op1)]) {
                    printf("E_%lu:: ", GET_EXPR_IDX(expr->op1));
                    print_expr_internal(expr->op1, 0);
                    printed[GET_EXPR_IDX(expr->op1)] = 1;
                }
                if (expr->op1 == NULL)
                    assert(expr->op2);
            }

            if (!expr->op2_is_const && expr->opkind != EXTRACT8 &&
                expr->opkind != ZEXT && expr->opkind != SEXT &&
                expr->op2 != NULL) {
                assert(GET_EXPR_IDX(expr->op2) < MAX_PRINT_CHECK);
                if (!printed[GET_EXPR_IDX(expr->op2)]) {
                    printf("E_%lu:: ", GET_EXPR_IDX(expr->op2));
                    print_expr_internal(expr->op2, 0);
                    printed[GET_EXPR_IDX(expr->op2)] = 1;
                }
                if (expr->op2 == NULL)
                    assert(expr->op1);
            }

            if (expr->opkind == EFLAGS_C_ADCQ && !expr->op3_is_const) {
                assert(GET_EXPR_IDX(expr->op3) < MAX_PRINT_CHECK);
                if (!printed[GET_EXPR_IDX(expr->op3)]) {
                    printf("E_%lu:: ", GET_EXPR_IDX(expr->op3));
                    print_expr_internal(expr->op3, 0);
                    printed[GET_EXPR_IDX(expr->op3)] = 1;
                }
            }
        }
    } else {
        printf("\n");
    }
}

static inline void print_expr(Expr* expr)
{
    printf("\n");
    print_expr_internal(expr, 1);
}

#define EXPR_CONST_OP(c_arg) ((Expr*)(uintptr_t)c_arg)

#define SET_EXPR_CONST_OP(op, op_is_const, c_arg)                              \
    do {                                                                       \
        op          = EXPR_CONST_OP(c_arg);                                    \
        op_is_const = 1;                                                       \
    } while (0);

#define SET_EXPR_OP(op, op_is_const, s_arg, c_arg)                             \
    do {                                                                       \
        if (s_arg) {                                                           \
            op = s_arg;                                                        \
        } else {                                                               \
            SET_EXPR_CONST_OP(op, op_is_const, c_arg);                         \
        }                                                                      \
    } while (0);

#define CONST(op) ((uintptr_t)op)

#define MAX_INPUT_SIZE 4096

#endif // SYMBOLIC_STRUCT_H