#ifndef TCG_SYMBOLIC
#define TCG_SYMBOLIC

#include "tcg-op.h"
#include "exec/tb-context.h"
#include "qemu/osdep.h"
#include "qemu/error-report.h"
#include "cpu.h"
#include "tcg/tcg.h"
#include "tcg/tcg-op.h"
#include "exec/exec-all.h"
#include "exec/gen-icount.h"
#include "exec/log.h"
#include "exec/translator.h"

#include "syscall_nr.h"

#define TCG_INSTRUMENTATION

typedef enum RESTORE_LOC { TO_REG, TO_MEM, TO_CONST } RESTORE_LOC;

typedef struct temp_to_restore_t {
    TCGTemp*        ts;
    RESTORE_LOC     where;
    TCGReg          reg;
    intptr_t        mem_offset;
    tcg_target_long const_val;
} temp_to_restore_t;

// FixMe: refactor this
#define DEFINE_TEMPS_TO_RECOVER(temps_to_restore_var, temp_to_restores_count)  \
    temp_to_restore_t temps_to_restore_var[TCG_MAX_TEMPS];                     \
    size_t            temp_to_restores_count = 0;

inline uint8_t is_instrumentation(const TCGOp* op)
{
    return op->args[MAX_OPC_PARAM - 1] == 1;
}

inline void add_temp_reg_to_restore(TCGTemp* ts, TCGReg reg,
                                    temp_to_restore_t* temps_to_restore,
                                    size_t*            temps_to_restore_count)
{
    size_t i = *temps_to_restore_count;
    (*temps_to_restore_count)++;
    assert(*temps_to_restore_count < TCG_MAX_TEMPS);
    assert(ts->val_type == TEMP_VAL_REG);
    temps_to_restore[i].ts               = ts;
    temps_to_restore[i].ts->mem_coherent = 0;
    temps_to_restore[i].reg              = reg;
    temps_to_restore[i].where            = TO_REG;
}

// from tcg.c
void tcg_reg_free(TCGContext* s, TCGReg reg, TCGRegSet allocated_regs);
void temp_load(TCGContext*, TCGTemp*, TCGRegSet, TCGRegSet, TCGRegSet);

static inline void
add_temp_const_to_restore(TCGTemp* ts, tcg_target_long const_val,
                          temp_to_restore_t* temps_to_restore,
                          size_t*            temps_to_restore_count)
{
    size_t i = *temps_to_restore_count;
    (*temps_to_restore_count)++;
    assert(*temps_to_restore_count < TCG_MAX_TEMPS);
    assert(ts->val_type == TEMP_VAL_CONST);
    temps_to_restore[i].ts        = ts;
    temps_to_restore[i].where     = TO_CONST;
    temps_to_restore[i].const_val = const_val;

    // it does not make sense to mark it as not mem coherent... right?
    // temps_to_restore[i].ts->mem_coherent = 0;
}

static inline void add_temp_mem_to_restore(TCGTemp* ts, TCGReg reg,
                                           intptr_t           mem_offset,
                                           temp_to_restore_t* temps_to_restore,
                                           size_t* temps_to_restore_count)
{
    size_t i = *temps_to_restore_count;
    (*temps_to_restore_count)++;
    assert(*temps_to_restore_count < TCG_MAX_TEMPS);
    assert(ts->val_type == TEMP_VAL_MEM);
    temps_to_restore[i].ts         = ts;
    temps_to_restore[i].reg        = reg;
    temps_to_restore[i].mem_offset = mem_offset;
    temps_to_restore[i].where      = TO_MEM;

    // it does not make sense to mark it as not mem coherent... right?
    // temps_to_restore[i].ts->mem_coherent = 0;
}

static inline void restore_temp_to_reg(size_t i, TCGRegSet allocated_regs,
                                       TCGContext*        s,
                                       temp_to_restore_t* temps_to_restore,
                                       size_t* temps_to_restore_count)
{
    tcg_debug_assert(!temps_to_restore[i].ts->fixed_reg);
    tcg_reg_free(s, temps_to_restore[i].reg, allocated_regs);
    tcg_regset_reset_reg(allocated_regs, temps_to_restore[i].reg);
    TCGRegSet arg_set = 0;
    tcg_regset_set_reg(arg_set, temps_to_restore[i].reg);
    temp_load(s, temps_to_restore[i].ts, arg_set, allocated_regs, 0);
    temps_to_restore[i].ts->mem_coherent = 0;
}

void init_symbolic_mode(void);
int  parse_translation_block(TranslationBlock* tb, uintptr_t pc,
                             uint8_t* tb_code, TCGContext* tcg_ctx);

void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                         uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                         uintptr_t ret_val);

typedef enum {
    INSTRUMENT_BEFORE,
    INSTRUMENT_AFTER,
} InstrumentationMode;

#endif // TCG_SYMBOLIC