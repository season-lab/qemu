#ifndef SYMBOLIC_STRUCT_H
#define SYMBOLIC_STRUCT_H

#define EXPR_POOL_CAPACITY (256 * 1024)
#define EXPR_POOL_SHM_KEY   0xDEADBEEF
#define QUERY_SHM_KEY       0xCAFECAFE

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

#endif // SYMBOLIC_STRUCT_H