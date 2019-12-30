#ifndef SYMBOLIC_STRUCT_H
#define SYMBOLIC_STRUCT_H

#include <stdlib.h>
#include <assert.h>

// same as tcg_abort()
#ifndef ABORT
#define ABORT() \
do {\
    fprintf(stderr, "%s:%d: tcg fatal error\n", __FILE__, __LINE__);\
    abort();\
} while (0)
#endif

#define EXPR_POOL_CAPACITY  (256 * 1024)
#define EXPR_POOL_SHM_KEY   (0xDEADBEEF + 2)
#define EXPR_POOL_ADDR      ((const void *)0x7f05c8cc7000)
#define QUERY_SHM_KEY       0xCAFECAFE
#define FINAL_QUERY         ((void *)0xDEAD)
#define MEM_BARRIER() asm volatile("" ::: "memory")

typedef enum OPKIND
{
    RESERVED,
    //
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
    AND, // 11
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

void print_expr_internal(Expr *expr, uint8_t reset);
void print_expr(Expr *expr);
const char *opkind_to_str(uint8_t opkind);

extern Expr *pool;
#define GET_EXPR_IDX(e) ((((uintptr_t)e) - ((uintptr_t)pool)) / sizeof(Expr))

inline const char *opkind_to_str(uint8_t opkind)
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
        ABORT();
    }
}

#define MAX_PRINT_CHECK 1024
uint8_t printed[MAX_PRINT_CHECK];
inline void print_expr_internal(Expr *expr, uint8_t reset)
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

inline void print_expr(Expr *expr)
{
    printf("\n");
    print_expr_internal(expr, 1);
}

#endif // SYMBOLIC_STRUCT_H