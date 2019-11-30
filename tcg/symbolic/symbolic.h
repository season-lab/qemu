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

#if 0
void helper_pcounter(void);

static inline void gen_helper_pcounter(void)
{
  tcg_gen_callN(helper_pcounter, NULL, 0, NULL);
}
#endif

#define TCG_INSTRUMENTATION

typedef enum RESTORE_LOC
{
    TO_REG,
    TO_MEM
} RESTORE_POINT;

typedef struct temp_to_restore_t
{
    TCGTemp * ts;
    RESTORE_POINT where;
    TCGReg reg;
    intptr_t mem_offset;
} temp_to_restore_t;

void parse_translation_block(TranslationBlock * tb, uintptr_t pc, uint8_t * tb_code, TCGContext * tcg_ctx);

#endif // TCG_SYMBOLIC