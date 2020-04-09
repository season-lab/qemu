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
    return op->args[MAX_OPC_PARAM - 1] > 0;
}

inline void set_conditional_instrumentation_label(TCGOp* op, unsigned label_id)
{
    // increase by one the label since it may be zero
    op->args[MAX_OPC_PARAM - 1] = (uint64_t)label_id + 1;
}

inline uint8_t get_conditional_instrumentation_label(const TCGOp* op)
{
    return op->args[MAX_OPC_PARAM - 1] - 1;
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

static inline int load_temp_to_reg(TCGContext* ctx,
                                    TCGTemp* ts,
                                    TCGReg reg,
                                    TCGRegSet allocated_regs)
{
    if (ctx->reg_to_temp[reg] != NULL && ctx->reg_to_temp[reg] != ts) {
        printf("Reg %u is used by temp %lu\n", reg,
            temp_idx(ctx->reg_to_temp[reg]) - ctx->nb_globals);
        return 1;
    }
    tcg_regset_reset_reg(allocated_regs, reg);
    TCGRegSet arg_set = 0;
    tcg_regset_set_reg(arg_set, reg);
    ts->val_type = TEMP_VAL_MEM; // force to reload from memory!
    temp_load(ctx, ts, arg_set, allocated_regs, 0);
    ts->mem_coherent = 0;
    assert(ts->val_type == TEMP_VAL_REG);
    return 0;
}

void init_symbolic_mode(void);
int  parse_translation_block(TranslationBlock* tb, uintptr_t pc,
                             uint8_t* tb_code, TCGContext* tcg_ctx);

typedef enum {
    INSTRUMENT_BEFORE,
    INSTRUMENT_AFTER,
} InstrumentationMode;

typedef struct {
    TCGTemp* ts;
    TCGReg   reg;
    unsigned label_id;
} ConditionalTempSync;

extern TCGOp* symb_current_gen_op;
extern int symb_restore_pass;
extern ConditionalTempSync conditional_temp_syncs[TCG_MAX_TEMPS];

#endif // TCG_SYMBOLIC