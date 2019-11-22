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

void parse_translation_block(TranslationBlock * tb, uintptr_t pc, uint8_t * tb_code, TCGContext * tcg_ctx);

#endif // TCG_SYMBOLIC