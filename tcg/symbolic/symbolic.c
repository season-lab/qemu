#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>
#include <pthread.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "qemu/bitops.h"

#include "symbolic-struct.h"
#include "symbolic.h"
#include "config.h"
#include "symbolic-instrumentation.h"

//#define SYMBOLIC_DEBUG
//#define DISABLE_SOLVER
#define SYMBOLIC_COSTANT_ACCESS 1
#define SYMBOLIC_INPUT_ACCESS   1
#define JUMP_TABLE_FINDER       0
#define SYMBOLIC_PC_FINDER      0
#define DEBUG_EXPR_CONSISTENCY  0
#define LINEARIZATION           0
#define VISIT_LINEARIZATION     1
#define VISIT_LINEARIZATION_TR  (1024 * 6)

#define printf(...) fprintf(stderr, __VA_ARGS__)

#define QUEUE_OP_MAX_SIZE 128
size_t        op_to_add_size               = 0;
TCGOp*        op_to_add[QUEUE_OP_MAX_SIZE] = {0};
extern TCGOp* tcg_op_alloc(TCGOpcode opc);
extern TCGOp* tcg_op_insert_before_op(TCGContext* s, TCGOp* op, TCGOp* new_op);

uintptr_t symbolic_pc;

TCGOp*              symb_current_gen_op                   = NULL;
int                 symb_restore_pass                     = 0;
ConditionalTempSync conditional_temp_syncs[TCG_MAX_TEMPS] = {0};
uint64_t symbolic_start_code = 0;
uint64_t symbolic_end_code = 0;

// symbolic temps
Expr* s_temps[TCG_MAX_TEMPS] = {0};

// symbolic memory
#define L1_PAGE_BITS 16
#define L2_PAGE_BITS 16
#define L3_PAGE_BITS 16

typedef struct l3_page_t {
    Expr* entries[1 << L3_PAGE_BITS];
} l3_page_t;

typedef struct l2_page_t {
    l3_page_t* entries[1 << L2_PAGE_BITS];
} l2_page_t;

typedef struct l1_page_t {
    l2_page_t* entries[1 << L1_PAGE_BITS];
} l1_page_t;

// up to 48 bits addressing
typedef struct s_memory_t {
    l1_page_t table;
} s_memory_t;

s_memory_t s_memory = {0};

static uint8_t  virgin_bitmap[BRANCH_BITMAP_SIZE] = {0};
static uint8_t* bitmap                            = NULL;
static uint16_t prev_loc                          = 0;

#if VISIT_LINEARIZATION
static uint16_t visit_map[BRANCH_BITMAP_SIZE]     = {0};
static uint8_t tb_is_symbolic                     = 0;
#endif

static uintptr_t current_tb_pc = 0;

GHashTable* coverage_log_bb_ht = NULL;
GHashTable* coverage_log_edges_ht = NULL;

// path constraints
Expr* path_constraints = NULL;

#if 0
// const base cache
static GHashTable* const_base_ht = NULL;
#endif

// Expr allocation pool
Expr* pool           = NULL;
Expr* next_free_expr = NULL;
Expr* last_expr      = NULL; // ToDo: unsafe

// query pool
Query* query_queue = NULL;
Query* next_query  = NULL;

static size_t page_size            = 0;
pthread_t     main_thread          = 0;

typedef struct {
    uint8_t shared_counter;
    off_t  offset;
} FileDescriptorStatus;

static int symbolic_mode = 0;

#define FD_STDIN 0
static Expr* input_exprs[MAX_INPUT_SIZE] = {0};
#define MAX_FP 128
static FileDescriptorStatus* input_fp[MAX_FP] = {0};

#if SYMBOLIC_INPUT_ACCESS
static uintptr_t input_start_addr = 0;
static uintptr_t input_end_addr = 0;
static uintptr_t input_offset = 0;
static uintptr_t input_is_constant = 0;
#endif

// from tcg.c
typedef struct TCGHelperInfo {
    void*       func;
    const char* name;
    unsigned    flags;
    unsigned    sizemask;
} TCGHelperInfo;

// Pattern:
//      movq    0xBASE(, %REG, 8), %REG
//      jmpq    *%rax
//
typedef struct {
    TCGTemp*  index;
    TCGTemp*  addr;
    TCGTemp*  mov;
    uint8_t   scale_is_addr_size;
    uintptr_t displacement;
    uint8_t   has_done_load;
    uint8_t   need_to_free_addr;
} JumpTableFinder;

// from tcg.c
extern GHashTable* helper_table;
extern const char* tcg_find_helper(TCGContext* s, uintptr_t val);
#define str(s) #s
// FLAGS | dh_callflag(ret),
// dh_sizemask(ret, 0) },
#define DEF_HELPER_INFO(HELPER_FUNC)                                           \
    TCGHelperInfo helper_info_##HELPER_FUNC = {.func     = HELPER_FUNC,        \
                                               .name     = str(HELPER_FUNC),   \
                                               .flags    = 0,                  \
                                               .sizemask = 0};

#if 0
TCGOp * op_macro;
#define ADD_VOID_CALL_0(f, op, tcg_ctx)                                        \
    ({                                                                         \
        do {                                                                   \
            TCGOpcode lopc        = INDEX_op_call;                             \
            op_macro              = tcg_op_insert_after(tcg_ctx, op, lopc);    \
            TCGOP_CALLO(op_macro) = 0;                                         \
            op_macro->args[0]     = (uintptr_t)f;                              \
            op_macro->args[1]     = 0;                                         \
            TCGOP_CALLI(op_macro) = 0;                                         \
        } while (0);                                                           \
        op_macro;                                                              \
    })
#endif

#define MARK_TEMP_AS_ALLOCATED(t)                                              \
    do {                                                                       \
        t->temp_allocated = 1;                                                 \
    } while (0)
#define MARK_TEMP_AS_NOT_ALLOCATED(t)                                          \
    do {                                                                       \
        t->temp_allocated = 0;                                                 \
    } while (0)

#ifdef SYMBOLIC_DEBUG
#define debug_printf(...)                                                      \
    do {                                                                       \
        printf(__VA_ARGS__);                                                   \
    } while (0);
#else
#define debug_printf(...)                                                      \
    do {                                                                       \
    } while (0);
#endif

static inline TCGTemp* tcg_find_temp_arch_reg(TCGContext* tcg_ctx,
                                              const char* reg_name)
{
    for (int i = 0; i < TCG_TARGET_NB_REGS; i++) {
        TCGTemp* t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0)
            return t;
    }
    tcg_abort();
}

typedef enum {
    UNKNOWN,
    MALLOC,
    REALLOC,
    CALLOC,
    FREE,
    STRCMP,
    STRNCMP,
    PRINTF,
    FPRINTF,
    STRLEN,
    STRNLEN,
    MEMCHR,
    MEMCMP,
    MEMMOVE,
    MEMSET,
    MEMCPY,
    STRCPY,
    STRNCPY,
    FPUTC,
} LIB_MODEL;

typedef struct {
    char* image;
    LIB_MODEL model;
    uintptr_t offset;
} PltInfo;

static GSList* plt_info = NULL;
static GHashTable* plt_addrs = NULL;
inline static void parse_plt_info(char* path) 
{
    FILE* fp = fopen(path, "r");
    if (fp == NULL)
        return;

    size_t len = 128;
    char* buffer = g_malloc0(len);
    ssize_t read;
    while ((read = getline(&buffer, &len, fp)) != -1) {
        // printf("line: %s\n", buffer);
        PltInfo* plt = g_malloc0(sizeof(PltInfo));
        char* token = strtok(buffer, ",");
        if (!token) continue;
        char* s = g_malloc0(strlen(token) + 1);
        plt->image = strcpy(s, token);
        token = strtok(NULL, ",");
        if (!token) {
            free(plt);
            continue;
        }
        if (strcmp(token, "malloc") == 0) {
            plt->model = MALLOC;
        } else if (strcmp(token, "calloc") == 0) {
            plt->model = CALLOC;
        } else if (strcmp(token, "realloc") == 0) {
            plt->model = REALLOC;
        } else if (strcmp(token, "free") == 0) {
            plt->model = FREE;
        } else if (strcmp(token, "strcmp") == 0) {
            plt->model = STRCMP;
        } else if (strcmp(token, "strncmp") == 0) {
            plt->model = STRNCMP;
        } else if (strcmp(token, "strcpy") == 0) {
            plt->model = STRCPY;
        } else if (strcmp(token, "strncpy") == 0) {
            plt->model = STRNCPY;
        } else if (strcmp(token, "strlen") == 0) {
            plt->model = STRLEN;
        } else if (strcmp(token, "strnlen") == 0) {
            plt->model = STRNLEN;
        }  else if (strcmp(token, "memchr") == 0) {
            plt->model = MEMCHR;
        } else if (strcmp(token, "memcmp") == 0) {
            plt->model = MEMCMP;
        } else if (strcmp(token, "memmove") == 0 ||
                    strcmp(token, "__memmove_chk") == 0) {
            plt->model = MEMMOVE;
        } else if (strcmp(token, "memcpy") == 0 ||
                    strcmp(token, "__memcpy_chk") == 0) {
            plt->model = MEMCPY;
        } else if (strcmp(token, "memset") == 0 ||
                    strcmp(token, "__memset_chk") == 0) {
            plt->model = MEMSET;
        } else if (strcmp(token, "printf") == 0) {
            plt->model = PRINTF;
        } else if (strcmp(token, "fprintf") == 0
                    || strcmp(token, "vfprintf") == 0
                    || strcmp(token, "__printf_chk") == 0
                    ) {
            plt->model = FPRINTF;
        } else if (strcmp(token, "fputc") == 0) {
            plt->model = FPUTC;
        }
        token = strtok(NULL, ",");
        if (!token || plt->model == 0) {
            free(plt);
            continue;
        }
        plt->offset = strtoull(token, NULL, 16);
        plt_info = g_slist_append(plt_info, plt);
    }
    free(buffer);

#if 0
    GSList* el = plt_info;
    while (el) {
        PltInfo* plt = el->data;
        printf("PLT: image=%s model=%u offset=%lx\n",
            plt->image, plt->model, plt->offset);
        el = g_slist_next(el);
    }
#endif

    fclose(fp);
}

void load_image(char* name, uintptr_t addr)
{
    if (plt_info) {
        if (plt_addrs == NULL) {
            plt_addrs = g_hash_table_new(NULL, NULL);
        }
    } else {
        return;
    }

    // printf("Loading image %s at %lx\n", name, addr);
    GSList* el = plt_info;
    while (el) {
        PltInfo* plt = el->data;
        if (strcmp(plt->image, name) == 0) {
#if 0
            printf("PLT: image=%s model=%u addr=%lx\n",
                        plt->image, plt->model, (addr + plt->offset));
#endif
            g_hash_table_insert(plt_addrs, (gpointer)(addr + plt->offset), (gpointer) plt->model);
        }
        el = g_slist_next(el);
    }
#if 0
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, plt_addrs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        printf("PLT: model=%p addr=%p\n", value, key);
    }
#endif
}

int mode = 0;

static SymbolicConfig s_config = {0};
static inline void    load_configuration(void)
{
    char* var = getenv("COVERAGE_TRACER_LOG");
    if (var) {
        s_config.coverage_tracer_log_bb = var;
    }

    var = getenv("COVERAGE_TRACER_LOG_EDGES");
    if (var) {
        s_config.coverage_tracer_log_edges = var;
    }

    var = getenv("COVERAGE_TRACER_FILTER_LIB");
    if (var) {
        s_config.coverage_tracer_filter_lib = (int)strtoll(var, NULL, 16);
    }

    var = getenv("COVERAGE_TRACER");
    if (var) {
        s_config.coverage_tracer = var;
        bitmap = g_malloc0(sizeof(uint8_t) * BRANCH_BITMAP_SIZE);
        return;
    }

    var = getenv("EXPR_POOL_SHM_KEY");
    if (var) {
        s_config.expr_pool_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(s_config.expr_pool_shm_key != ULLONG_MAX);
    }
    assert(s_config.expr_pool_shm_key != 0 && "Missing EXPR_POOL_SHM_KEY");

    var = getenv("QUERY_SHM_KEY");
    if (var) {
        s_config.query_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(s_config.query_shm_key != ULLONG_MAX);
    }
    assert(s_config.query_shm_key != 0 && "Missing QUERY_SHM_KEY");

#if BRANCH_COVERAGE == FUZZOLIC
    var = getenv("BITMAP_SHM_KEY");
    if (var) {
        s_config.bitmap_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(s_config.bitmap_shm_key != ULLONG_MAX);
    }
    assert(s_config.bitmap_shm_key != 0 && "Missing BITMAP_SHM_KEY");
#endif

    var = getenv("SYMBOLIC_EXEC_START_ADDR");
    if (var) {
        s_config.symbolic_exec_start_addr = (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_start_addr != LONG_MIN &&
               s_config.symbolic_exec_start_addr != LONG_MAX);
    }
#if 0
    assert(s_config.symbolic_exec_start_addr != 0 &&
           "Need to specify symbolic exec start address.");
#endif
    var = getenv("SYMBOLIC_EXEC_STOP_ADDR");
    if (var) {
        s_config.symbolic_exec_stop_addr = (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_stop_addr != LONG_MIN &&
               s_config.symbolic_exec_stop_addr != LONG_MAX);
    }
#if 0
    assert(s_config.symbolic_exec_stop_addr != 0 &&
           "Need to specify symbolic exec stop address.");
#endif
    var = getenv("SYMBOLIC_INJECT_INPUT_MODE");
    if (var) {
        if (strcmp(var, "READ_FD_0") == 0)
            s_config.symbolic_inject_input_mode = READ_FD_0;
        else if (strcmp(var, "REG") == 0)
            s_config.symbolic_inject_input_mode = REG;
        else if (strcmp(var, "BUFFER") == 0)
            s_config.symbolic_inject_input_mode = BUFFER;
        else if (strcmp(var, "FROM_FILE") == 0) {
            s_config.symbolic_inject_input_mode = FROM_FILE;
            s_config.inputfile = getenv("SYMBOLIC_TESTCASE_NAME");
            assert(s_config.inputfile && "Neet to specify testcase path.");
        }
    }
    assert(s_config.symbolic_inject_input_mode != NO_INPUT &&
           "Need to specify symbolic exec injection input mode.");

    s_config.symbolic_exec_reg_name = getenv("SYMBOLIC_EXEC_REG_NAME");

    var = getenv("SYMBOLIC_EXEC_REG_INSTR_ADDR");
    if (var) {
        s_config.symbolic_exec_reg_instr_addr =
            (uintptr_t)strtoll(var, NULL, 16);
        assert(s_config.symbolic_exec_reg_instr_addr != LONG_MIN &&
               s_config.symbolic_exec_reg_instr_addr != LONG_MAX);
        assert(s_config.symbolic_exec_reg_name &&
               "Need to specify symbolic exec register name.");
    } else {
        assert(s_config.symbolic_exec_reg_name == NULL &&
               "Need to specify symbolic exec register address.");
    }

    var = getenv("SYMBOLIC_EXEC_PLT_STUB_MALLOC");
    if (var) {
        s_config.plt_stub_malloc = (uintptr_t)strtoll(var, NULL, 16);
    }

    var = getenv("SYMBOLIC_EXEC_PLT_STUB_REALLOC");
    if (var) {
        s_config.plt_stub_realloc = (uintptr_t)strtoll(var, NULL, 16);
    }

    var = getenv("SYMBOLIC_EXEC_PLT_STUB_FREE");
    if (var) {
        s_config.plt_stub_free = (uintptr_t)strtoll(var, NULL, 16);
    }

    var = getenv("SYMBOLIC_EXEC_PLT_STUB_PRINTF");
    if (var) {
        s_config.plt_stub_printf = (uintptr_t)strtoll(var, NULL, 16);
    }

    var = getenv("DEBUG_FUZZ_EXPR");
    if (var) {
        s_config.debug_fuzz_expr = 1;
    }

    var = getenv("DEBUG_FUZZ_EXPR_IDX");
    if (var) {
        s_config.debug_fuzz_expr_idx = strtoull(var, NULL, 10);
        printf("DEBUG_FUZZ_EXPR_IDX = %lu\n", s_config.debug_fuzz_expr_idx);
    }

    var = getenv("DEBUG_FUZZ_EXPR_VALUE");
    if (var) {
        s_config.debug_fuzz_expr_value = strtoull(var, NULL, 10);
    }

    var = getenv("PLT_INFO_FILE");
    if (var) {
        parse_plt_info(var);
    }
}

static InstrumentationMode instrumentation_mode = INSTRUMENT_BEFORE;
static inline void         set_instrumentation_mode(InstrumentationMode mode)
{
    instrumentation_mode = mode;
}

static inline void load_coverage_bitmap(const char* path, uint8_t* data,
                                        size_t size)
{
    printf("[TRACER] Loading bitmap: %s\n", path);
    FILE* fp = fopen(path, "r");
    if (!fp) {
        printf("[TRACER] Bitmap %s does not exist. Initializing it.\n", path);
        return;
    }
    int r = fread(data, 1, size, fp);
    if (r != size) {
        printf("[TRACER] Invalid bitmap %s. Resetting it.\n", path);
        memset(data, 0, size);
    }
    fclose(fp);
}

static inline void load_coverage_log(const char*  path,
                                     GHashTable** coverage_log)
{
    *coverage_log = g_hash_table_new(NULL, NULL);
    printf("[TRACER] Loading coverage log: %s\n", path);
    FILE* fp = fopen(path, "r");
    if (!fp) {
        printf("[TRACER] Log %s does not exist. Initializing it.\n", path);
        return;
    }
    ssize_t res;
    char*   line = NULL;
    size_t  len  = 0;
    while ((res = getline(&line, &len, fp)) != -1) {
        uint64_t address = strtoll(line, NULL, 16);
        g_hash_table_add(*coverage_log, (gpointer)address);
    }
    fclose(fp);
}

static inline void save_coverage_bitmap(const char* path, uint8_t* data,
                                        size_t size)
{
    printf("[TRACER] Saving bitmap: %s\n", path);
    FILE* fp = fopen(path, "w");
    int   r  = fwrite(data, 1, size, fp);
    if (r != size) {
        printf("[TRACER] Failed to save bitmap: %s\n", path);
    }
    fclose(fp);
}

static inline void save_coverage_log(const char*  path,
                                     GHashTable** coverage_log)
{
    printf("[TRACER] Saving coverage log: %s\n", path);
    FILE* fp = fopen(path, "w");

    char           line[16];
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, *coverage_log);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        int size = snprintf(line, sizeof(line), "%p\n", key);
        assert(size < sizeof(line));
        fwrite(line, 1, size, fp);
    }
    g_hash_table_destroy(*coverage_log);
    *coverage_log = NULL;
    fclose(fp);
}

void init_symbolic_mode(void)
{
    // configuration
    load_configuration();

    if (s_config.coverage_tracer) {
        load_coverage_bitmap(s_config.coverage_tracer, bitmap,
                             BRANCH_BITMAP_SIZE);
        if (s_config.coverage_tracer_log_bb) {
            load_coverage_log(s_config.coverage_tracer_log_bb, &coverage_log_bb_ht);
        }
        if (s_config.coverage_tracer_log_edges) {
            load_coverage_log(s_config.coverage_tracer_log_edges, &coverage_log_edges_ht);
        }
        main_thread = pthread_self();
        return;
    }

#ifndef DISABLE_SOLVER

    struct timespec polling_time;
    polling_time.tv_sec  = 0;
    polling_time.tv_nsec = 50;

    int expr_pool_shm_id;
    do {
        // printf("[TRACER] Waiting for shared memory #1 (key=%lu)...\n", s_config.expr_pool_shm_key);
        expr_pool_shm_id = shmget(s_config.expr_pool_shm_key, // IPC_PRIVATE,
                                  sizeof(Expr) * EXPR_POOL_CAPACITY, 0666 | IPC_CREAT);
        if (expr_pool_shm_id >= 0) {
            break;
        }
        nanosleep(&polling_time, NULL);
    } while (1);
    assert(expr_pool_shm_id >= 0);

    int query_shm_id;
    do {
        // printf("[TRACER] Waiting for shared memory #2...\n");
        query_shm_id = shmget(s_config.query_shm_key, // IPC_PRIVATE,
                              sizeof(Query) * EXPR_QUERY_CAPACITY, 0666 | IPC_CREAT);
        if (query_shm_id >= 0) {
            break;
        }
        nanosleep(&polling_time, NULL);
    } while (1);
    assert(query_shm_id >= 0);

#if BRANCH_COVERAGE == FUZZOLIC
    int bitmap_shm_id;
    do {
        // printf("[TRACER] Waiting for shared memory #3...\n");
        bitmap_shm_id = shmget(s_config.bitmap_shm_key, // IPC_PRIVATE,
                               sizeof(uint8_t) * BRANCH_BITMAP_SIZE, 0666 | IPC_CREAT);
        if (bitmap_shm_id >= 0) {
            break;
        }
        nanosleep(&polling_time, NULL);
    } while (1);
    assert(bitmap_shm_id > 0);
#endif

    pool = shmat(expr_pool_shm_id, EXPR_POOL_ADDR, 0);
    assert(pool);

    query_queue = shmat(query_shm_id, NULL, 0);
    assert(query_queue);
#if BRANCH_COVERAGE == FUZZOLIC
    bitmap = shmat(bitmap_shm_id, NULL, 0);
    assert(bitmap);
#endif

#else
    pool        = g_malloc0(sizeof(Expr) * EXPR_POOL_CAPACITY);
    query_queue = g_malloc0(sizeof(Query) * EXPR_QUERY_CAPACITY);
    bitmap      = g_malloc0(sizeof(uint8_t) * BRANCH_BITMAP_SIZE);

    printf("\nTRACER in NO SOLVER mode\n");
#endif

    // printf("POOL_ADDR=%p\n", pool);

#if 0
    for (size_t i = 0; i < EXPR_POOL_CAPACITY; i++)
        assert(*(queue_query + i) == 0);
#endif

    next_free_expr = pool;
    next_query     = query_queue;

#ifndef DISABLE_SOLVER
    while (next_query[0].query != (void*)SHM_READY) {
        nanosleep(&polling_time, NULL);
    }
#endif

    MEM_BARRIER();

    next_query++;

    page_size = sysconf(_SC_PAGESIZE);
#if 0
    const_base_ht = g_hash_table_new(NULL, NULL);
#endif

    if (s_config.symbolic_inject_input_mode == READ_FD_0) {
        input_fp[FD_STDIN]         = malloc(sizeof(FileDescriptorStatus));
        input_fp[FD_STDIN]->offset = 0;
        input_fp[FD_STDIN]->shared_counter = 1;
    }

    main_thread = pthread_self();
}

static inline int count_free_temps(TCGContext* tcg_ctx)
{
    int count = 0;
    for (size_t j = 0; j < BITS_TO_LONGS(TCG_MAX_TEMPS); j++)
        for (size_t i = 0; i < BITS_PER_LONG; i++)
            count += test_bit(i, &tcg_ctx->free_temps[TCG_TYPE_I64].l[j]);
    return count;
}

// FixMe: shitty way to hide the variable...
#define SAVE_TEMPS_COUNT(s)                                                    \
    int temps_initial_count = s->nb_temps - count_free_temps(s);
#define CHECK_TEMPS_COUNT_WITH_DELTA(s, delta)                                 \
    assert(temps_initial_count == s->nb_temps - count_free_temps(s) + delta);
#define CHECK_TEMPS_COUNT(s)                                                   \
    assert(temps_initial_count == s->nb_temps - count_free_temps(s));

// since we are asking for new temps after generating and analyzing TCG,
// tcg_temp_new_internal may returns temps that are in use in the TB
// (but are dead at the end of the TB). To avoid conflicts, we call
// tcg_temp_new_internal until we get a non used temp from the
// previous istructions in the TB.
//
// NOTE: temps must be deallocated after generating instrumentation
//       for one instruction otherwise conflicts may emerge!
static uint8_t         used_temps_idxs[TCG_MAX_TEMPS] = {0};
static inline TCGTemp* new_non_conflicting_temp(TCGType type)
{
    assert(type == TCG_TYPE_I64); // ToDo: validate other types
    TCGTemp* r = NULL;
    TCGTemp* conflicting_temps[TCG_MAX_TEMPS];
    size_t   conflicting_temps_count = 0;
    while (!r) {
        TCGTemp* current = tcg_temp_new_internal(type, false);
        size_t   idx     = temp_idx(current);
        assert(idx < TCG_MAX_TEMPS);
        if (used_temps_idxs[idx] != 0) // temp is in use
        {
            conflicting_temps[conflicting_temps_count++] = current;
        } else {
            r = current;
        }
    }

    // deallocate any temp that is in conflict
    while (conflicting_temps_count > 0) {
        tcg_temp_free_internal(conflicting_temps[conflicting_temps_count - 1]);
        conflicting_temps_count--;
    }

    return r;
}

static inline void mark_insn_as_instrumentation(TCGOp* op)
{
    // we use the last op arg, which is usually unused
    // op->args[MAX_OPC_PARAM - 1] = (uint64_t)1;
}

static inline TCGMemOp get_mem_op(uint64_t oi)
{
    return oi >> 32; // ToDo: 32 bit
}

static inline uint32_t get_mem_offset(uint64_t oi)
{
    return oi & 0xFFFFFFFFFFFFFFFF; // ToDo: 32 bit
}

static inline uint64_t make_mem_op_offset(uint32_t op, uint32_t idx)
{
    return (((uint64_t)op) << 32) | idx;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_0(void* f, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = (uintptr_t)f;
    op->args[1]     = 0; // flags
    TCGOP_CALLI(op) = 0; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_1(void* f, TCGTemp* arg, TCGOp* op_in,
                                   TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(arg->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg);
    op->args[1]     = (uintptr_t)f;
    op->args[2]     = 0; // flags
    TCGOP_CALLI(op) = 1; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_2(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = (uintptr_t)f;
    op->args[3]     = 0; // flags
    TCGOP_CALLI(op) = 2; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_3(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = (uintptr_t)f;
    op->args[4]     = 0; // flags
    TCGOP_CALLI(op) = 3; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_4(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGOp* op_in,
                                   TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = (uintptr_t)f;
    op->args[5]     = 0; // flags
    TCGOP_CALLI(op) = 4; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_5(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGTemp* arg4,
                                   TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);
    assert(arg4->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc = INDEX_op_call;
    TCGOp*    op  = instrumentation_mode == INSTRUMENT_BEFORE
                    ? tcg_op_insert_before(tcg_ctx, op_in, opc)
                    : tcg_op_alloc(opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = temp_arg(arg4);
    op->args[5]     = (uintptr_t)f;
    op->args[6]     = 0; // flags
    TCGOP_CALLI(op) = 5; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;

    if (instrumentation_mode == INSTRUMENT_AFTER) {
        op_to_add[op_to_add_size++] = op;
    }
}

// see tcg_gen_callN in tgc.c
static inline void add_void_call_6(void* f, TCGTemp* arg0, TCGTemp* arg1,
                                   TCGTemp* arg2, TCGTemp* arg3, TCGTemp* arg4,
                                   TCGTemp* arg5, TCGOp* op_in, TCGOp** op_out,
                                   TCGContext* tcg_ctx)
{
    assert(arg0->temp_allocated);
    assert(arg1->temp_allocated);
    assert(arg2->temp_allocated);
    assert(arg3->temp_allocated);
    assert(arg4->temp_allocated);
    assert(arg5->temp_allocated);

    // FixMe: check 32 bit, check other archs
    TCGOpcode opc   = INDEX_op_call;
    TCGOp*    op    = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]     = temp_arg(arg0);
    op->args[1]     = temp_arg(arg1);
    op->args[2]     = temp_arg(arg2);
    op->args[3]     = temp_arg(arg3);
    op->args[4]     = temp_arg(arg4);
    op->args[5]     = temp_arg(arg5);
    op->args[6]     = (uintptr_t)f;
    op->args[7]     = 0; // flags
    TCGOP_CALLI(op) = 6; // input args
    TCGOP_CALLO(op) = 0; // ret args

    if (op_out)
        *op_out = op;
}

static inline void check_pool_expr_capacity(void)
{
    assert(next_free_expr >= pool);
    assert(next_free_expr < pool + EXPR_POOL_CAPACITY);
}

static inline Expr* new_expr(void)
{
    // ToDo: use free list
    check_pool_expr_capacity();
    next_free_expr += 1;
    last_expr = next_free_expr - 1;
    return last_expr;
}

static inline const char* get_reg_name(TCGContext* tcg_ctx, size_t idx)
{
    TCGTemp* t = &tcg_ctx->temps[idx];
    return t->name;
}

void print_reg(void);
void print_reg(void)
{
    debug_printf("%s is %ssymbolic\n", s_config.symbolic_exec_reg_name,
                 s_temps[12]->opkind == IS_SYMBOLIC ? "" : "not ");
}
DEF_HELPER_INFO(print_reg);

static inline void new_symbolic_expr(void)
{
    Expr* e   = new_expr();
    e->opkind = IS_SYMBOLIC;
    e->op1    = 0; // FixMe: assign id based on the specific symbolic input
    debug_printf("Marking expr%lu as symbolic\n", GET_EXPR_IDX(e));
}

static inline void sync_argo_temp(TCGOp* op, size_t i)
{
    op->life |= SYNC_ARG << i;
}

static inline void mark_dead_arg_temp(TCGOp* op, size_t i)
{
    op->life |= DEAD_ARG << i;
}

// ts <- CONST
static inline void tcg_movi(TCGTemp* ts, uintptr_t const_val,
                            uint8_t is_ts_dead, TCGOp* op_in, TCGOp** op_out,
                            TCGContext* tcg_ctx)
{
    assert(ts->temp_allocated);

    TCGOpcode opc = INDEX_op_movi_i64;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts);
    assert(!is_ts_dead);

    op->args[1] = (uintptr_t)const_val;

    if (op_out)
        *op_out = op;
}

// to <- from
static inline void tcg_mov(TCGTemp* ts_to, TCGTemp* ts_from,
                           uint8_t is_ts_to_dead, uint8_t is_ts_from_dead,
                           TCGOp* op_in, TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_from->temp_allocated);

    TCGOpcode opc = INDEX_op_mov_i64;
    TCGOp*    op  = instrumentation_mode == INSTRUMENT_BEFORE
                    ? tcg_op_insert_before(tcg_ctx, op_in, opc)
                    : tcg_op_alloc(opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    if (op_out)
        *op_out = op;

    if (instrumentation_mode == INSTRUMENT_AFTER) {
        op_to_add[op_to_add_size++] = op;
    }
}

static inline void tcg_cmov(TCGTemp* ts_out, TCGTemp* ts_a, TCGTemp* ts_b,
                            TCGTemp* ts_true, TCGTemp* ts_false, TCGCond cond,
                            uint8_t is_ts_out_dead, uint8_t is_ts_a_dead,
                            uint8_t is_ts_b_dead, uint8_t is_ts_true_dead,
                            uint8_t is_ts_false_dead, TCGOp* op_in,
                            TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_out->temp_allocated);
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_true->temp_allocated);
    assert(ts_false->temp_allocated);

    TCGOpcode opc = INDEX_op_movcond_i64;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    // ret, c1, c2, v1, v2, cond

    op->args[0] = temp_arg(ts_out);
    assert(!is_ts_out_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    op->args[3] = temp_arg(ts_true);
    if (is_ts_true_dead) {
        mark_dead_arg_temp(op, 3);
        tcg_temp_free_internal(ts_true);
    }

    op->args[4] = temp_arg(ts_false);
    if (is_ts_false_dead) {
        mark_dead_arg_temp(op, 4);
        tcg_temp_free_internal(ts_false);
    }

    op->args[5] = cond;

    if (op_out)
        *op_out = op;
}

// c <- a op b
static inline void tcg_binop(TCGTemp* ts_c, TCGTemp* ts_a, TCGTemp* ts_b,
                             uint8_t is_ts_c_dead, uint8_t is_ts_a_dead,
                             uint8_t is_ts_b_dead, OPKIND opkind, TCGOp* op_in,
                             TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);
    assert(ts_c->temp_allocated);

    TCGOpcode opc;
    switch (opkind) {
        case ADD:
            opc = INDEX_op_add_i64;
            break;
        case SUB:
            opc = INDEX_op_sub_i64;
            break;
        case SHR:
            opc = INDEX_op_shr_i64;
            break;
        case SHL:
            opc = INDEX_op_shl_i64;
            break;
        case AND:
            opc = INDEX_op_and_i64;
            break;
        case OR:
            opc = INDEX_op_or_i64;
            break;
        case XOR:
            opc = INDEX_op_xor_i64;
            break;
        default:
            tcg_abort();
            break;
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_c);
    assert(!is_ts_c_dead);

    op->args[1] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_a);
    }

    op->args[2] = temp_arg(ts_b);
    if (is_ts_b_dead) {
        mark_dead_arg_temp(op, 2);
        tcg_temp_free_internal(ts_b);
    }

    if (op_out)
        *op_out = op;
}

static inline void tcg_load_n(TCGTemp* ts_from, TCGTemp* ts_to,
                              uintptr_t offset, uint8_t is_ts_from_dead,
                              uint8_t is_ts_to_dead, size_t n_bytes,
                              TCGOp* op_in, TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_from->temp_allocated);
    assert(ts_to->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes) {
        // ToDo: add _i32 address mode
        case 8:
            opc = INDEX_op_ld_i64;
            break;
        case 1:
            opc = INDEX_op_ld8u_i64;
            break;
        default:
            tcg_abort();
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_to);
    assert(!is_ts_to_dead);

    op->args[1] = temp_arg(ts_from);
    if (is_ts_from_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_from);
    }

    op->args[2] = offset;

    if (op_out)
        *op_out = op;
}

static inline void tcg_store_n(TCGTemp* ts_to, TCGTemp* ts_val,
                               uintptr_t offset, uint8_t is_ts_to_dead,
                               uint8_t is_ts_val_dead, size_t n_bytes,
                               TCGOp* op_in, TCGOp** op_out,
                               TCGContext* tcg_ctx)
{
    assert(ts_to->temp_allocated);
    assert(ts_val->temp_allocated);

    TCGOpcode opc;
    switch (n_bytes) {
        case 8:
            opc = INDEX_op_st_i64;
            break;
        case 4:
            opc = INDEX_op_st32_i64;
            break;
        case 2:
            opc = INDEX_op_st16_i64;
            break;
        case 1:
            opc = INDEX_op_st8_i64;
            break;
        default:
            tcg_abort();
    }

    TCGOp* op = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_val);
    if (is_ts_val_dead) {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_val);
    }

    op->args[1] = temp_arg(ts_to);
    if (is_ts_to_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_to);
    }

    op->args[2] = offset;

    if (op_out)
        *op_out = op;
}

// branch to label if a cond b is true
static inline void tcg_brcond(TCGLabel* label, TCGTemp* ts_a, TCGTemp* ts_b,
                              TCGCond cond, uint8_t is_ts_a_dead,
                              uint8_t is_ts_b_dead, TCGOp* op_in,
                              TCGOp** op_out, TCGContext* tcg_ctx)
{
    assert(ts_a->temp_allocated);
    assert(ts_b->temp_allocated);

    label->refs++;
    TCGOpcode opc = INDEX_op_brcond_i64; // ToDo: i32
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);

    op->args[0] = temp_arg(ts_a);
    if (is_ts_a_dead) {
        mark_dead_arg_temp(op, 0);
        tcg_temp_free_internal(ts_a);
    }

    op->args[1] = temp_arg(ts_b);
    if (is_ts_b_dead) {
        mark_dead_arg_temp(op, 1);
        tcg_temp_free_internal(ts_b);
    }

    op->args[2] = cond;
    op->args[3] = label_arg(label);

    if (op_out)
        *op_out = op;
}

// branch to label (always)
static inline void tcg_br(TCGLabel* label, TCGOp* op_in, TCGOp** op_out,
                          TCGContext* tcg_ctx)
{
    label->refs++;
    TCGOpcode opc = INDEX_op_br;
    TCGOp*    op  = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]   = label_arg(label);

    if (op_out)
        *op_out = op;
}

// add a goto label (referenced by brcond)
static inline void tcg_set_label(TCGLabel* label, TCGOp* op_in, TCGOp** op_out,
                                 TCGContext* tcg_ctx)
{
    label->present = 1;
    TCGOpcode opc  = INDEX_op_set_label;
    TCGOp*    op   = tcg_op_insert_before(tcg_ctx, op_in, opc);
    op->args[0]    = label_arg(label);

    if (op_out)
        *op_out = op;
}

#if SYMBOLIC_CALLSTACK_INSTRUMENTATION

#define CALLSTACK_MAX_SIZE 0x1000

typedef struct {
    uint16_t address; // hash of the address
} CallStackEntry;

typedef struct {
    CallStackEntry entries[CALLSTACK_MAX_SIZE];
    intptr_t       depth;
    uint16_t       hash;
} CallStack;

static CallStack callstack = {.depth = 0};

void helper_instrument_call(target_ulong pc)
{
    // printf("CALL from %lx\n", (uintptr_t) pc);
    pc = (pc >> 4) ^ (pc << 8);
    pc &= BRANCH_BITMAP_SIZE - 1;
    callstack.entries[callstack.depth].address = pc;
    callstack.hash ^= pc;
    callstack.depth += 1;
    if (callstack.depth >= CALLSTACK_MAX_SIZE) {
        tcg_abort();
    }
}

void helper_instrument_ret(target_ulong pc)
{
    // printf("RET to %lx\n", (uintptr_t) pc);

    intptr_t initial_depth          = callstack.depth;
    uint16_t initial_callstack_hash = callstack.hash;

    pc = (pc >> 4) ^ (pc << 8);
    pc &= BRANCH_BITMAP_SIZE - 1;

    callstack.depth -= 1;
    while (callstack.depth >= 0 &&
           callstack.entries[callstack.depth].address != pc) {

        callstack.hash ^= callstack.entries[callstack.depth].address;
        callstack.depth -= 1;
        // printf("Skipping RET address\n");
    }

    if (callstack.depth >= 0) {
        callstack.hash ^= pc;
        // printf("Found RET address\n");
    } else { // not found
        callstack.depth = initial_depth;
        callstack.hash  = initial_callstack_hash;
        // printf("RET address not found. Restoring\n");
    }
}

#endif

#if DEBUG_EXPR_CONSISTENCY
static inline void updatePC(uintptr_t cur_loc)
{
    current_tb_pc = cur_loc;
}
#endif

static inline void visitTB_debug(uintptr_t cur_loc, uintptr_t tb_mode)
{
    if (symbolic_mode == 0) return;
    printf("visiting TB 0x%lx [%d] [%d] [%lu] [DEBUG]\n", cur_loc, symbolic_mode, mode, tb_mode);
    current_tb_pc = cur_loc;
    if (tb_mode != mode) {
        printf("Executing TB in wrong mode\n");
        tcg_abort();
    }
#if 0
    if (GET_QUERY_IDX(next_query) > 9200) {
        if (*((uint8_t*)0x40007ff1a0) == 0x70) {
            printf("[DEBUG] Value at 0x%lx is %x at PC %lx\n", 0x40007ff1a0, 0x70, cur_loc);
        }
    }
#endif
}

static inline void visitTB(uintptr_t cur_loc)
{
#if 0
    if (GET_QUERY_IDX(next_query) > 9200) {
        if (*((uint8_t*)0x40007ff1a0) == 0x70) {
            printf("Value at 0x%lx is %x at PC %lx\n", 0x40007ff1a0, 0x70, cur_loc);
        }
    }
#endif
    // printf("visiting TB 0x%lx\n", cur_loc);
    current_tb_pc = cur_loc;

#if DEBUG_EXPR_CONSISTENCY
    current_tb_pc = cur_loc;
#if BRANCH_COVERAGE != FUZZOLIC
    return;
#endif
#endif

    if (s_config.coverage_tracer_filter_lib > 0 &&
            (cur_loc > symbolic_end_code || cur_loc < symbolic_start_code)) {
        return;
    }

    if (coverage_log_bb_ht) {
        if (s_config.coverage_tracer_filter_lib >= 0) {
            g_hash_table_add(coverage_log_bb_ht, (gpointer)cur_loc);
        }
    }

    cur_loc = (cur_loc >> 4) ^ (cur_loc << 8);
    cur_loc &= BRANCH_BITMAP_SIZE - 1;

    uintptr_t index = (cur_loc ^ prev_loc
#if SYMBOLIC_CALLSTACK_INSTRUMENTATION
                       ^ callstack.hash
#endif
    );

    // printf("Callstack hash %x\n", callstack.hash);

    index &= BRANCH_BITMAP_SIZE - 1;

    if (coverage_log_edges_ht) {
        if (s_config.coverage_tracer_filter_lib >= 0) {
            g_hash_table_add(coverage_log_edges_ht, (gpointer)index);
        }
    }

    // update bitmap for this run
    if (virgin_bitmap[index] < 255) {
        virgin_bitmap[index]++;
    }

#if VISIT_LINEARIZATION
    tb_is_symbolic = 0;
#endif
    prev_loc = cur_loc >> 1;
}

static inline void print_something(char* str) { printf("%s\n", str); }
DEF_HELPER_INFO(print_something);

// the string has to be statically allocated, otherwise it will crash!
static inline void tcg_print_const_str(const char* str, TCGOp* op_in,
                                       TCGOp** op, TCGContext* tcg_ctx)
{
    TCGTemp* t_str = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_str, (uintptr_t)str, 0, op_in, NULL, tcg_ctx);
    add_void_call_1(print_something, t_str, op_in, op, tcg_ctx);
    tcg_temp_free_internal(t_str);
}

static inline void init_reg(size_t reg, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(reg < TCG_MAX_TEMPS);
    debug_printf("Setting expr of reg %lu\n", reg);

    TCGTemp* t_last_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_last_expr, (uintptr_t)&last_expr, 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_last_expr, t_last_expr, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGTemp* t_reg_id = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_reg_id, (uintptr_t)reg, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_last_expr, t_reg_id, offsetof(Expr, op1), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_reg_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_reg_size, (uintptr_t)8, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_last_expr, t_reg_size, offsetof(Expr, op2), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_dst, (uintptr_t)&s_temps[reg], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_dst, t_last_expr, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void make_reg_symbolic(const char* reg_name, TCGOp* op,
                                     TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    for (int i = 0; i < TCG_TARGET_NB_REGS; i++) {
        TCGTemp* t = &tcg_ctx->temps[i];
        if (t->fixed_reg)
            continue; // not a register
        if (strcmp(t->name, reg_name) == 0) {
            debug_printf("Marking %s (id=%d) as symbolic\n", t->name, i);
            add_void_call_0(new_symbolic_expr, op, NULL, tcg_ctx);
            init_reg(i, op, tcg_ctx);
            add_void_call_0(print_reg, op, NULL, tcg_ctx);
        }
    }

    CHECK_TEMPS_COUNT(tcg_ctx);
}

void print_temp(size_t idx);
void print_temp(size_t idx)
{
    if (s_temps[idx]) {
        printf("t[%lu](%s) is ", idx, get_reg_name(tcg_ctx, idx));
        print_expr(s_temps[idx]);
    }
}

static inline void allocate_new_expr_conditional(TCGTemp* t_out, TCGOp* op_in,
                                                 TCGContext* tcg_ctx,
                                                 TCGLabel*   label)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGOp* op;
#if 0
    add_void_call_0(check_pool_expr_capacity, op_in, &op,
                    tcg_ctx); // ToDo: make inline check
    mark_insn_as_instrumentation(op);
#endif
    // assert(next_free_expr);

    TCGTemp* t_next_free_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_next_free_expr_addr, (uintptr_t)&next_free_expr, 0, op_in, &op,
             tcg_ctx);
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    TCGTemp* t_next_free_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_next_free_expr_addr, t_next_free_expr, 0, 0, 0,
               sizeof(uintptr_t), op_in, &op, tcg_ctx);
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    tcg_mov(t_out, t_next_free_expr, 0, 0, op_in, &op, tcg_ctx);
    // required to handle a t_out which already has a reg allocated
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    TCGTemp* t_expr_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_expr_size, sizeof(Expr), 0, op_in, &op, tcg_ctx);
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    tcg_binop(t_next_free_expr, t_next_free_expr, t_expr_size, 0, 0, 1, ADD,
              op_in, &op, tcg_ctx);
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    tcg_store_n(t_next_free_expr_addr, t_next_free_expr, 0, 1, 1, sizeof(void*),
                op_in, &op, tcg_ctx);
    if (label) {
        set_conditional_instrumentation_label(op, label->id);
    }

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_new_expr(TCGTemp* t_out, TCGOp* op_in,
                                     TCGContext* tcg_ctx)
{
    allocate_new_expr_conditional(t_out, op_in, tcg_ctx, NULL);
}

#if DEBUG_EXPR_CONSISTENCY
static inline Expr** debug_expr_addr(uintptr_t addr, size_t size, uint8_t allocate,
                            size_t* n_overflow_bytes)
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

    if ((l3_page_idx + size) > (1 << L3_PAGE_BITS)) {
        // printf("n_overflow_bytes=%p\n", n_overflow_bytes);
        if (n_overflow_bytes) {
            // printf("size=%lu l3_page_idx=%lu\n", size, l3_page_idx);
            *n_overflow_bytes = size - ((1 << L3_PAGE_BITS) - l3_page_idx);
        } else {
            assert(0 && "Cross page access");
        }
    } else {
        if (n_overflow_bytes) {
            *n_overflow_bytes = 0;
        }
    }

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

int count = 0;
static void add_consistency_check(Expr* e, uintptr_t value, size_t size, OPKIND opkind)
{
#if 0
#if 1
    if (GET_QUERY_IDX(next_query - 1) >= 9700) {
        if (*((uint8_t*)0x40007ff1a0) == 0x70) {
            printf("Value at 0x%lx is %x\n", 0x40007ff1a0, 0x70);
            Expr** exprs = debug_expr_addr(0x40007ff1a0, 1, 0, NULL);
            for (size_t i = 0; i < 1; i++) {
                printf("Expr at 0x%lx\n", 0x40007ff1a0 + i);
                print_expr(exprs[i]);
            }
        }
    }
#endif
    if (GET_QUERY_IDX(next_query - 1) >= 9915) { // && *((uint8_t*)0x8b1ba0) == 0x20) {
        printf("PC: %lx\n", current_tb_pc);
        tcg_abort();
    }
#endif

    if (s_config.debug_fuzz_expr) {
        // printf("CONSISTENCY_CHECK id=%lu size=%lu type=%s pc=%lx value=%lu\n",
        //            GET_QUERY_IDX(next_query), size, opkind_to_str(opkind), current_tb_pc, value);
        if (s_config.debug_fuzz_expr_idx == GET_QUERY_IDX(next_query)) {
            printf("CONSISTENCY_CHECK id=%lu size=%lu type=%s pc=%lx value=%lx\n",
                    GET_QUERY_IDX(next_query), size, opkind_to_str(opkind), current_tb_pc, value);
            uint64_t expected = s_config.debug_fuzz_expr_value;
            if (value != expected) {
                printf("Mismatch fuzz debug expression: expected=%lu current=%lu\n", expected, value);
                print_expr(e);
                tcg_abort();
            } else {
                exit(0);
            }
        } else if (s_config.debug_fuzz_expr_idx < GET_QUERY_IDX(next_query)) {
            printf("Consistency check has been bypassed.\n");
            tcg_abort();
        }
        next_query++;
        return;
    }
#if 0
    if (GET_QUERY_IDX(next_query) > 300) {
        return;
    }
#endif
#if 0
    count++;
    if (count < 40000) {
        return;
    }
#endif
    Expr*     consistency_expr = new_expr();
    consistency_expr->opkind   = CONSISTENCY_CHECK;
    consistency_expr->op1      = e;
    SET_EXPR_CONST_OP(consistency_expr->op2, consistency_expr->op2_is_const, value);
    //
    next_query[0].query   = consistency_expr;
    next_query[0].address = current_tb_pc;
    next_query++;
    //
    if (size == 0) {
        size = 8;
    }
    printf("CONSISTENCY_CHECK id=%lu size=%lu type=%s pc=%lx value=%lx\n",
        GET_QUERY_IDX(next_query - 1), size, opkind_to_str(opkind), current_tb_pc, value);
#if 0
    if (GET_QUERY_IDX(next_query - 1) >= 9915) {
        tcg_abort();
    }
#endif
}

static void add_consistency_check_addr(Expr* e, uintptr_t addr, size_t size, OPKIND opkind) 
{
    assert(size > 0);
    uintptr_t concrete_value = 0;
    for (size_t i = 0; i < size; i++) {
        uintptr_t v = *(((uint8_t*)addr) + i);
        concrete_value |= v << (8 * i);
        // printf("Concrete byte: %lx\n", v);
    }
    //
    if (!s_config.debug_fuzz_expr) {
        printf("CONSISTENCY CHECK %s for addr=%lx size=%lu\n", opkind_to_str(opkind), addr, size);
    }
    add_consistency_check(e, concrete_value, size, opkind);
}
#endif

#if DEBUG_EXPR_CONSISTENCY
static inline void move_temp_size_helper(size_t from, size_t to, uintptr_t val, size_t size)
#else
static inline void move_temp_size_helper(size_t from, size_t to, size_t size)
#endif
{
#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[from]) {
        add_consistency_check(s_temps[from], val, size, MOV);
    }
#endif
#if 0
    if (s_temps[to] || s_temps[from]) {
        printf("Move: t[%ld] = t[%ld]\n", to, s_temps[from] ? from : -1);
        if (s_temps[from])
            print_temp(from);
        if (s_temps[to])
            print_temp(to);
    }
#endif
    Expr* from_expr = s_temps[from];
    if (from_expr && size < sizeof(uintptr_t)) {
        if (!(from_expr->opkind == ZEXT && CONST(from_expr->op2) == 32)) {
            Expr* e   = new_expr();
            e->opkind = EXTRACT;
            e->op1    = from_expr;
            SET_EXPR_CONST_OP(e->op2, e->op2_is_const, 31);
            SET_EXPR_CONST_OP(e->op3, e->op3_is_const, 0);
            from_expr = e;
        }
    }

    s_temps[to] = from_expr;
}

#if DEBUG_EXPR_CONSISTENCY
static inline void move_temp_helper(size_t from, size_t to, uintptr_t val)
#else
static inline void move_temp_helper(size_t from, size_t to)
#endif
{
#if 0
    if (*((uint64_t*)0x40007ff0b8) == 0x4000e60700) {
        printf("HERE\n");
    }
#endif
#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[from]) {
        add_consistency_check(s_temps[from], val, sizeof(uintptr_t), MOV);
    }
#endif
#if 0
    if (s_temps[to] || s_temps[from]) {
        printf("Move: t[%ld] = t[%ld]\n", to, s_temps[from] ? from : -1);
        if (s_temps[from])
            print_temp(from);
        if (s_temps[to])
            print_temp(to);
    }
#endif
    s_temps[to] = s_temps[from];
}

static inline void move_temp(size_t from, size_t to, size_t size, TCGOp* op_in,
                             TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(to < TCG_MAX_TEMPS);
    assert(from < TCG_MAX_TEMPS);

    TCGTemp* t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    if (size != 0 && size < sizeof(uintptr_t)) {

        TCGOp* op;

        TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

        TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

        tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
                  tcg_ctx); // force TCG to allocate the temp into a reg

        TCGLabel* label_a_concrete = gen_new_label();
        tcg_brcond(label_a_concrete, t_from, t_zero, TCG_COND_EQ, 0, 0, op_in,
                   NULL, tcg_ctx);

        // FixMe: we assume that Expr is zero-initialzed!
        allocate_new_expr_conditional(t_out, op_in, tcg_ctx, label_a_concrete);

        TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_opkind, EXTRACT, 0, op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);
        tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_store_n(t_out, t_from, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t),
                    op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_one, 1, 0, op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_size, (size * 8) - 1, 0, op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_store_n(t_out, t_size, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t),
                    op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 0,
                    sizeof(uint8_t), op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_store_n(t_out, t_zero, offsetof(Expr, op3), 0, 1, sizeof(uintptr_t),
                    op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_store_n(t_out, t_one, offsetof(Expr, op3_is_const), 0, 1,
                    sizeof(uint8_t), op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_a_concrete->id);

        tcg_set_label(label_a_concrete, op_in, &op, tcg_ctx);

        TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_to, t_out, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);

    } else {
        TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_to, t_from, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);
    }

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void clear_temp_helper(uintptr_t temp_idx)
{
#if 0
    if (s_temps[temp_idx]) {
        printf("Clearing temp %lu at %lx\n", temp_idx, current_tb_pc);
    }
#endif
    assert(temp_idx < TCG_MAX_TEMPS);
    s_temps[temp_idx] = 0;
}

static inline void clear_temp(size_t idx, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    assert(idx < TCG_MAX_TEMPS);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t, (uintptr_t)&s_temps[idx], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t, t_zero, 0, 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

// When adding instrumentation with branches and when accessing
// the operands contents, TCG may move temp loads (i.e., loading
// content of the temp operand from memory) within the branching
// code (which is not always executed), possibly leading to SIGSEGV.
// To avoid this issue, we insert fake uses for each temp operand
// before any branching code, to make temp loads branchless.
static inline void preserve_op_load(TCGTemp* t, TCGOp* op_in,
                                    TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);
    TCGTemp* t_dummy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t);
    tcg_mov(t_dummy, t, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t);
    // this is needed since out temp cannot be marked as dead in tcg_mov
    tcg_temp_free_internal(t_dummy);
    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_binop_helper(uintptr_t opkind, uintptr_t packed_idx,
                                     uintptr_t a, uintptr_t b)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t b_idx   = UNPACK_2(packed_idx);
    uintptr_t size    = UNPACK_3(packed_idx);
#if 0
    if (GET_QUERY_IDX(next_query) >= 116753 && GET_QUERY_IDX(next_query) <= 116773) {
        printf("[0x%lx] bin_op: %lu %s %lu\n", current_tb_pc, a, opkind_to_str(opkind), b);
    }
#endif
    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if ((expr_a == NULL && expr_b == NULL)) {
        s_temps[out_idx] = NULL;
        return; // early exit
    }
#if VISIT_LINEARIZATION
    if (prev_loc) {
        if (!tb_is_symbolic) {
            visit_map[prev_loc] += 1;
        }
        if (visit_map[prev_loc] > VISIT_LINEARIZATION_TR) {
            // printf("Concretizing...\n");
            s_temps[out_idx] = NULL;
            return; // early exit
        }
    }
#endif

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_expr   = new_expr();
    binop_expr->opkind = (OPKIND)opkind;

    if (expr_a)
        binop_expr->op1 = expr_a;
    else {
        binop_expr->op1          = (Expr*)(uintptr_t)a;
        binop_expr->op1_is_const = 1;
    }

    if (expr_b)
        binop_expr->op2 = expr_b;
    else {
        binop_expr->op2          = (Expr*)(uintptr_t)b;
        binop_expr->op2_is_const = 1;
    }

    if (size != 0 && size < sizeof(uintptr_t)) {
        binop_expr->op3          = (Expr*)(uintptr_t)size;
        binop_expr->op3_is_const = 1;
    }

    s_temps[out_idx] = binop_expr;

#if DEBUG_EXPR_CONSISTENCY
    if (expr_a) {
        add_consistency_check(expr_a, a, size, opkind);
    }
    if (expr_b) {
        add_consistency_check(expr_b, b, size, opkind);
    }
#endif
}

// Binary operation: t_out = t_a opkind t_b
static inline void qemu_binop(OPKIND opkind, TCGTemp* t_op_out, TCGTemp* t_op_a,
                              TCGTemp* t_op_b, size_t size, TCGOp* op_in,
                              TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp __attribute__((unused)) * op;

    size_t out = temp_idx(t_op_out);
    size_t a   = temp_idx(t_op_a);
    size_t b   = temp_idx(t_op_b);

    assert(out < TCG_MAX_TEMPS);
    assert(a < TCG_MAX_TEMPS);
    assert(b < TCG_MAX_TEMPS);

    TCGTemp* t_op_a_copy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_op_a_copy, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    TCGTemp* t_op_b_copy = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_op_b_copy, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    // tcg_print_const_str("Binary op:\n", op_in, NULL, tcg_ctx);

    // check if both t_a and t_b are concrete
    // if this is the case, then mark dest as concrete

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
#if 0
    tcg_print_const_str("Checking binary op", op_in, &op, tcg_ctx);

    add_void_call_1(print_expr, t_a, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif
    TCGTemp* t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[b], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
#if 0
    add_void_call_1(print_expr, t_b, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_print_const_str("Checking binary op: DONE", op_in, &op, tcg_ctx);
#endif
    TCGTemp* t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr_conditional(t_out, op_in, tcg_ctx, label_both_concrete);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_both_concrete->id);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_both_concrete->id);

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_both_concrete->id);

    if (size != 0 && size < sizeof(uintptr_t)) {

        TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_size, size, 0, op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_both_concrete->id);

        tcg_store_n(t_out, t_size, offsetof(Expr, op3), 0, 1, sizeof(uintptr_t),
                    op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_both_concrete->id);

        tcg_store_n(t_out, t_one, offsetof(Expr, op3_is_const), 0, 0,
                    sizeof(uint8_t), op_in, &op, tcg_ctx);
        set_conditional_instrumentation_label(op, label_both_concrete->id);
    }

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGLabel* label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in,
               NULL, tcg_ctx);

    tcg_mov(t_a, t_op_a_copy, 0, 1, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_ta_not_concrete->id);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0,
                sizeof(uint8_t), op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_ta_not_concrete->id);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_both_concrete->id);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel* label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in,
               NULL, tcg_ctx);

    tcg_mov(t_b, t_op_b_copy, 0, 1, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_tb_not_concrete->id);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_tb_not_concrete->id);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in,
                &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_both_concrete->id);

#if 0
    tcg_print_const_str("Binary op:", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    //add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);
    //tcg_print_const_str("Binary op: DONE", op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);
#endif

    // add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[out], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);
#if 0
    tcg_temp_free_internal(t_zero);
    tcg_temp_free_internal(t_a);
    tcg_temp_free_internal(t_b);
    tcg_temp_free_internal(t_op_a_copy);
    tcg_temp_free_internal(t_op_b_copy);
#endif
    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_unop_helper(uintptr_t opkind, uintptr_t t_out_idx,
                                    uintptr_t t_op_a_idx, uintptr_t t_op_a,
                                    uintptr_t size)
{
    Expr* expr_a = s_temps[t_op_a_idx];
    if (expr_a == NULL) {
        s_temps[t_out_idx] = NULL;
        return; // early exit
    }

    Expr* unop_expr   = new_expr();
    unop_expr->opkind = (OPKIND)opkind;
    unop_expr->op1    = expr_a;
    SET_EXPR_CONST_OP(unop_expr->op2, unop_expr->op2_is_const, size);
    s_temps[t_out_idx] = unop_expr;

#if DEBUG_EXPR_CONSISTENCY
    add_consistency_check(expr_a, t_op_a, size, opkind);
#endif
}

static inline void qemu_unop(OPKIND opkind, TCGTemp* t_op_out, TCGTemp* t_op_a,
                             TCGTemp* t_size, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp* op;

    size_t out = temp_idx(t_op_out);
    size_t a   = temp_idx(t_op_a);

    // check whether t_op_a is concrete

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr_conditional(t_out, op_in, tcg_ctx, label_a_concrete);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    tcg_store_n(t_out, t_size, offsetof(Expr, op2), 0, 0, sizeof(uintptr_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[out], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_pc_write_helper(uintptr_t value)
{
    printf("Jumping to %lx\n", value);
}

static inline void qemu_pc_write(TCGTemp* t_op_a, TCGOp* op_in,
                                 TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t a = temp_idx(t_op_a);

    // This is an hack to avoid SIGSEGV :/
    TCGTemp* t_op_a_copy = new_non_conflicting_temp(TCG_TYPE_PTR);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_op_a_copy, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr(t_out, op_in, tcg_ctx);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, SYMBOLIC_PC, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_op_a_copy, offsetof(Expr, op2), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    TCGTemp* t_query_addr = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_query_addr, (uintptr_t)&next_query, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_query = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_load_n(t_query_addr, t_query, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    tcg_store_n(t_query, t_out, offsetof(Query, query), 0, 1, sizeof(uintptr_t),
                op_in, NULL, tcg_ctx);

    TCGTemp* t_query_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_query_size, sizeof(Query), 0, op_in, NULL, tcg_ctx);
    tcg_binop(t_query, t_query, t_query_size, 0, 0, 1, ADD, op_in, NULL,
              tcg_ctx);

    tcg_store_n(t_query_addr, t_query, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

#if 0
    TCGOp* op;
    tcg_print_const_str("\nSymbolic PC\n", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif
    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_jump_table(TCGTemp* t_addr, TCGOp* op_in,
                                   TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t a = temp_idx(t_addr);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[a], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    TCGOp* op;
    tcg_print_const_str("\nSymbolic jump table\n", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr(t_out, op_in, tcg_ctx);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, SYMBOLIC_JUMP_TABLE_ACCESS, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_store_n(t_out, t_addr, offsetof(Expr, op2), 0, 0, sizeof(uintptr_t),
                op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_query_addr = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_query_addr, (uintptr_t)&next_query, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_query = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_load_n(t_query_addr, t_query, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);
#if 0
    add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif
    tcg_store_n(t_query, t_out, offsetof(Query, query), 0, 1, sizeof(uintptr_t),
                op_in, NULL, tcg_ctx);

    TCGTemp* t_query_size = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_query_size, sizeof(Query), 0, op_in, NULL, tcg_ctx);
    tcg_binop(t_query, t_query, t_query_size, 0, 0, 1, ADD, op_in, NULL,
              tcg_ctx);

    tcg_store_n(t_query_addr, t_query, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void allocate_l2_page(uintptr_t l1_entry_idx)
{
    assert(l1_entry_idx < 1 << L1_PAGE_BITS);

    debug_printf("Allocating l2 page at idx %lu\n", l1_entry_idx);
    s_memory.table.entries[l1_entry_idx] =
        g_malloc0(sizeof(l2_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l1_entry_idx_addr=%p l2_page_addr=%p\n",
                 &s_memory.table.entries[l1_entry_idx],
                 s_memory.table.entries[l1_entry_idx]);
}

static inline void allocate_l3_page(void** l2_page_idx_addr)
{
    debug_printf("Allocating l3 page at l2_page_idx_addr=%p\n",
                 l2_page_idx_addr);
    *l2_page_idx_addr = g_malloc0(sizeof(l3_page_t)); // FixMe: get mmap lock
    debug_printf("Done: l3_page_addr=%p\n", *l2_page_idx_addr);
}

static inline void print_value(uintptr_t value)
{
    debug_printf("V: %lx\n", value);
}

static inline void print_t_l1_entry_idx_addr(void* l1_entry_addr)
{
    debug_printf("L2 Entry addr: %p\n", l1_entry_addr);
}

static inline void print_t_l3_entry_idx_addr(void* l3_entry_addr)
{
    debug_printf("L3 Entry addr: %p\n", l3_entry_addr);
}

static inline void failure_cross_page_access(void)
{
    printf("A memory access is crossing a L3 page: not yet supported.\n");
    tcg_abort();
}

#define EARLY_EXIT_CONST ((TCGTemp*)1)

static inline void get_expr_addr_for_addr(TCGTemp*  t_addr,
                                          TCGTemp** t_expr_addr,
                                          uintptr_t offset, size_t size,
                                          TCGTemp* early_exit, TCGOp* op_in,
                                          TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp* op;

    TCGTemp* t_addr_with_offset = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_addr_with_offset, offset, 0, op_in, NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_addr);
    tcg_binop(t_addr_with_offset, t_addr, t_addr_with_offset, 0, 0, 0, ADD,
              op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_addr);

    TCGTemp* t_l3_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    if (early_exit) {
        TCGTemp* t_null = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_null, (uintptr_t)0, 0, op_in, NULL, tcg_ctx);
        tcg_binop(t_l3_page_idx_addr, t_null, t_null, 0, 1, 0, XOR, op_in, &op,
                  tcg_ctx); // force TCG to allocate the temp into a reg
        // add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL,
        // tcg_ctx);
    }
    *t_expr_addr = t_l3_page_idx_addr;

    // compute index for L1 page

    TCGTemp* t_l1_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l1_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_l1_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_shr_bit, L1_PAGE_BITS + L2_PAGE_BITS, 0, op_in, NULL,
             tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx, t_l1_page_idx, t_l1_shr_bit, 0, 0, 1, SHR, op_in,
              NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp* t_l1_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l1_page, (uintptr_t)&s_memory, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_l1_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void*) == 8); // 2^3 = 8
    tcg_movi(t_l1_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx, t_l1_page_idx_addr, 0, 0, 0,
              SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l1_page_idx_addr, t_l1_page_idx_addr, t_l1_page, 0, 0, 1, ADD,
              op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_l1_page);

    TCGTemp* t_l2_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGLabel* label_l2_page_is_allocated = gen_new_label();
    tcg_brcond(label_l2_page_is_allocated, t_l2_page, t_zero, TCG_COND_NE, 0, 0,
               op_in, NULL, tcg_ctx);

    // early_exit?
    TCGLabel* label_early_exit = NULL;
    if (early_exit) {
        label_early_exit = gen_new_label();
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0,
                       op_in, NULL, tcg_ctx);
    }

    // if not, allocate L2 page
    add_void_call_1(allocate_l2_page, t_l1_page_idx, op_in, &op, tcg_ctx);
    // mark since it will preserve regs, marking temps as TS_VAL_MEM
    // however this is done only when the helper is executed
    // and its execution depends on the branch condiion!
    mark_insn_as_instrumentation(op);
    tcg_temp_free_internal(t_l1_page_idx);

    tcg_load_n(t_l1_page_idx_addr, t_l2_page, 0, 1, 0, sizeof(uintptr_t), op_in,
               &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l2_page_is_allocated, op_in, NULL, tcg_ctx);

    // add_void_call_1(print_t_l1_entry_idx_addr, t_l1_entry, op_in, NULL,
    // tcg_ctx);

    // compute index for L2 page
    TCGTemp* t_l2_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l2_page_idx, t_addr_with_offset, 0, 0, op_in, NULL, tcg_ctx);

    // FixMe: mask higher bits

    TCGTemp* t_l2_shr_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_shr_bit, L2_PAGE_BITS, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_shr_bit, 0, 0, 1, SHR, op_in,
              NULL, tcg_ctx);

    TCGTemp* t_l2_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l2_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx, t_l2_page_idx, t_l2_and_bit, 0, 0, 1, AND, op_in,
              NULL, tcg_ctx);

    // check whether L2 page is allocated for that index

    TCGTemp* t_l2_page_idx_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    assert(sizeof(void*) == 8); // 2^3 = 8
    tcg_movi(t_l2_page_idx_addr, (uintptr_t)3, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx, t_l2_page_idx_addr, 0, 1, 0,
              SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l2_page_idx_addr, t_l2_page_idx_addr, t_l2_page, 0, 0, 1, ADD,
              op_in, NULL, tcg_ctx);

    TCGTemp* t_l3_page = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    TCGLabel* label_l3_page_is_allocated = gen_new_label();
    tcg_brcond(label_l3_page_is_allocated, t_l3_page, t_zero, TCG_COND_NE, 0, 0,
               op_in, NULL, tcg_ctx);

    // early_exit?
    if (early_exit) {
        if (early_exit == EARLY_EXIT_CONST)
            tcg_br(label_early_exit, op_in, NULL, tcg_ctx);
        else
            tcg_brcond(label_early_exit, early_exit, t_zero, TCG_COND_EQ, 0, 0,
                       op_in, NULL, tcg_ctx);
    }
    tcg_temp_free_internal(t_zero);

    add_void_call_1(allocate_l3_page, t_l2_page_idx_addr, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_load_n(t_l2_page_idx_addr, t_l3_page, 0, 1, 0, sizeof(uintptr_t), op_in,
               &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    tcg_set_label(label_l3_page_is_allocated, op_in, NULL, tcg_ctx);

    // compute index for L3 page

    TCGTemp* t_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(t_l3_page_idx, t_addr_with_offset, 0, 1, op_in, NULL, tcg_ctx);

    TCGTemp* t_l3_and_bit = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_l3_and_bit, 0xFFFF, 0, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_l3_and_bit, 0, 0, 1, AND, op_in,
              NULL, tcg_ctx);

    // compute the address of the Expr in the page

    assert(sizeof(void*) == 8); // 2^3 = 8
    TCGTemp* t_three = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_three, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_three, 0, 0, 1, SHL, op_in,
              &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    // tcg_movi(t_l3_page_idx_addr, (uintptr_t)3, 0, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);
    // tcg_binop(t_l3_page_idx_addr, t_l3_page_idx, t_l3_page_idx_addr, 0, 0, 0,
    // SHL, op_in, NULL, tcg_ctx);

    tcg_binop(t_l3_page_idx_addr, t_l3_page_idx_addr, t_l3_page, 0, 0, 1, ADD,
              op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);

    // check that t_l3_page_idx_addr + size is still within the L3 page,
    // otherwise fail FixMe: handle cross page store/loading

    TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_size, size, 0, op_in, NULL, tcg_ctx);
    tcg_binop(t_l3_page_idx, t_l3_page_idx, t_size, 0, 0, 1, ADD, op_in, NULL,
              tcg_ctx);
    TCGTemp* t_max_l3_page_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_max_l3_page_idx, 1 << L3_PAGE_BITS, 0, op_in, NULL, tcg_ctx);
    TCGLabel* label_no_cross_page_access = gen_new_label();
    tcg_brcond(label_no_cross_page_access, t_l3_page_idx, t_max_l3_page_idx,
               TCG_COND_LT, 1, 1, op_in, NULL, tcg_ctx);
    add_void_call_0(failure_cross_page_access, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_set_label(label_no_cross_page_access, op_in, NULL, tcg_ctx);

    if (early_exit) {
        tcg_set_label(label_early_exit, op_in, NULL, tcg_ctx);
        // add_void_call_1(print_value, t_l3_page_idx_addr, op_in, NULL,
        // tcg_ctx);
    }

    CHECK_TEMPS_COUNT_WITH_DELTA(
        tcg_ctx,
        -1); // t_expr_addr is allocated here, but freed by the caller!
}

static inline size_t get_mem_op_size(TCGMemOp mem_op)
{
    switch (mem_op & MO_SIZE) {
        case MO_8:
            return 1;
        case MO_16:
            return 2;
        case MO_32:
            return 4;
        case MO_64:
            return 8;
        default:
            tcg_abort();
    }
}

static inline size_t get_mem_op_signextend(TCGMemOp mem_op)
{
    return mem_op & MO_SIGN;
}

#define IS_LIKELY_CONST_BASE(c) (c > 0x10000 && c < (0xFFFFFFFFFFFF - 0x10000))

typedef struct {
    Expr*     expr;
    uintptr_t base;
} ConstBaseCache_t;

static unsigned crc32_table[256] = {
    0u,          1996959894u, 3993919788u, 2567524794u, 124634137u,
    1886057615u, 3915621685u, 2657392035u, 249268274u,  2044508324u,
    3772115230u, 2547177864u, 162941995u,  2125561021u, 3887607047u,
    2428444049u, 498536548u,  1789927666u, 4089016648u, 2227061214u,
    450548861u,  1843258603u, 4107580753u, 2211677639u, 325883990u,
    1684777152u, 4251122042u, 2321926636u, 335633487u,  1661365465u,
    4195302755u, 2366115317u, 997073096u,  1281953886u, 3579855332u,
    2724688242u, 1006888145u, 1258607687u, 3524101629u, 2768942443u,
    901097722u,  1119000684u, 3686517206u, 2898065728u, 853044451u,
    1172266101u, 3705015759u, 2882616665u, 651767980u,  1373503546u,
    3369554304u, 3218104598u, 565507253u,  1454621731u, 3485111705u,
    3099436303u, 671266974u,  1594198024u, 3322730930u, 2970347812u,
    795835527u,  1483230225u, 3244367275u, 3060149565u, 1994146192u,
    31158534u,   2563907772u, 4023717930u, 1907459465u, 112637215u,
    2680153253u, 3904427059u, 2013776290u, 251722036u,  2517215374u,
    3775830040u, 2137656763u, 141376813u,  2439277719u, 3865271297u,
    1802195444u, 476864866u,  2238001368u, 4066508878u, 1812370925u,
    453092731u,  2181625025u, 4111451223u, 1706088902u, 314042704u,
    2344532202u, 4240017532u, 1658658271u, 366619977u,  2362670323u,
    4224994405u, 1303535960u, 984961486u,  2747007092u, 3569037538u,
    1256170817u, 1037604311u, 2765210733u, 3554079995u, 1131014506u,
    879679996u,  2909243462u, 3663771856u, 1141124467u, 855842277u,
    2852801631u, 3708648649u, 1342533948u, 654459306u,  3188396048u,
    3373015174u, 1466479909u, 544179635u,  3110523913u, 3462522015u,
    1591671054u, 702138776u,  2966460450u, 3352799412u, 1504918807u,
    783551873u,  3082640443u, 3233442989u, 3988292384u, 2596254646u,
    62317068u,   1957810842u, 3939845945u, 2647816111u, 81470997u,
    1943803523u, 3814918930u, 2489596804u, 225274430u,  2053790376u,
    3826175755u, 2466906013u, 167816743u,  2097651377u, 4027552580u,
    2265490386u, 503444072u,  1762050814u, 4150417245u, 2154129355u,
    426522225u,  1852507879u, 4275313526u, 2312317920u, 282753626u,
    1742555852u, 4189708143u, 2394877945u, 397917763u,  1622183637u,
    3604390888u, 2714866558u, 953729732u,  1340076626u, 3518719985u,
    2797360999u, 1068828381u, 1219638859u, 3624741850u, 2936675148u,
    906185462u,  1090812512u, 3747672003u, 2825379669u, 829329135u,
    1181335161u, 3412177804u, 3160834842u, 628085408u,  1382605366u,
    3423369109u, 3138078467u, 570562233u,  1426400815u, 3317316542u,
    2998733608u, 733239954u,  1555261956u, 3268935591u, 3050360625u,
    752459403u,  1541320221u, 2607071920u, 3965973030u, 1969922972u,
    40735498u,   2617837225u, 3943577151u, 1913087877u, 83908371u,
    2512341634u, 3803740692u, 2075208622u, 213261112u,  2463272603u,
    3855990285u, 2094854071u, 198958881u,  2262029012u, 4057260610u,
    1759359992u, 534414190u,  2176718541u, 4139329115u, 1873836001u,
    414664567u,  2282248934u, 4279200368u, 1711684554u, 285281116u,
    2405801727u, 4167216745u, 1634467795u, 376229701u,  2685067896u,
    3608007406u, 1308918612u, 956543938u,  2808555105u, 3495958263u,
    1231636301u, 1047427035u, 2932959818u, 3654703836u, 1088359270u,
    936918000u,  2847714899u, 3736837829u, 1202900863u, 817233897u,
    3183342108u, 3401237130u, 1404277552u, 615818150u,  3134207493u,
    3453421203u, 1423857449u, 601450431u,  3009837614u, 3294710456u,
    1567103746u, 711928724u,  3020668471u, 3272380065u, 1510334235u,
    755167117u};

#define CONST_BASE_CACHE_SIZE 512
static ConstBaseCache_t const_base_cache[CONST_BASE_CACHE_SIZE];

static inline uintptr_t find_const_base(Expr* e, int depth)
{
#if 0
    printf("Find const base %d %p\n", depth, e);
    print_expr(e);
    if (depth > 10) {
        tcg_abort();
    }
#endif
#if 0
    gpointer key, value;
    if (g_hash_table_lookup_extended(const_base_ht, (gconstpointer) e, &key, &value) == TRUE){
        return (uintptr_t) value;
    }
#endif
    uint8_t hash =
        (crc32_table[((uint8_t)(CONST(e) >> 2))] % CONST_BASE_CACHE_SIZE);
    if (const_base_cache[hash].expr == e) {
        return const_base_cache[hash].base;
    }

    uintptr_t base = 0;
    if (e->opkind == ADD || e->opkind == SUB) {
        if (e->op1_is_const) {
            if (IS_LIKELY_CONST_BASE(CONST(e->op1))) {
                return CONST(e->op1);
            } else {
                base = find_const_base(e->op2, depth + 1);
            }
        } else if (e->op2_is_const) {
            if (IS_LIKELY_CONST_BASE(CONST(e->op2))) {
                return CONST(e->op2);
            } else {
                base = find_const_base(e->op1, depth + 1);
            }
        } else {
            base = find_const_base(e->op1, depth + 1) +
                   find_const_base(e->op2, depth + 1);
        }
    }
#if 0
    g_hash_table_insert(const_base_ht, (gpointer) key, (gpointer) value);
#endif
    const_base_cache[hash].expr = e;
    const_base_cache[hash].base = base;
    return base;
}

#define HASH_ADDR(a)   ((a >> 8) ^ (a << 8))

#if SYMBOLIC_COSTANT_ACCESS
static uintptr_t symbolic_access_id = MAX_INPUT_SIZE;

typedef struct {
    uintptr_t base;
    Expr*     dump;
    uint32_t  used;
    uint8_t   status;
} MemorySlice;

#define CONST_MAP_SIZE 0x1000
static MemorySlice const_mem_map[CONST_MAP_SIZE] = {0};
#endif
static uintptr_t   slices_count                  = 0;

static inline Expr* get_base_expr(Expr* e)
{
    if (e->opkind == ADD) {
        if (e->op1_is_const) {
            return get_base_expr(e->op2);
        } else if (e->op2_is_const) {
            return get_base_expr(e->op1);
        }
    }
    return e;
}

static Expr*       last_load_concretization = NULL;
static inline void load_concretization(Expr* addr_expr, uintptr_t addr)
{
#if 0
    if (CONST(addr_expr) < 0x500000) {
        tcg_abort();
    }
#endif

    Expr* base_expr = get_base_expr(addr_expr);

    if (last_load_concretization != base_expr) {
        Expr* e   = new_expr();
        e->opkind = SYMBOLIC_LOAD;
        e->op1    = addr_expr;
        SET_EXPR_CONST_OP(e->op2, e->op2_is_const, addr);
        last_load_concretization = base_expr;

        // printf("\nSymbolic Load (base_expr=%lu)\n", GET_EXPR_IDX(base_expr));
        // print_expr(addr_expr);

        next_query[0].query   = e;
        next_query[0].address = 0;
        next_query++;

    } else {
        // printf("Symbolic Load (already concretized)\n");
    }
}

static Expr*       last_store_concretization = NULL;
static inline void store_concretization(Expr* addr_expr, uintptr_t addr)
{
    Expr* base_expr = get_base_expr(addr_expr);

    if (last_store_concretization != base_expr) {
        Expr* e   = new_expr();
        e->opkind = SYMBOLIC_STORE;
        e->op1    = addr_expr;
        SET_EXPR_CONST_OP(e->op2, e->op2_is_const, addr);
        last_store_concretization = base_expr;

        // printf("\nSymbolic Store (base_expr=%lu)\n",
        // GET_EXPR_IDX(base_expr)); print_expr(addr_expr);

        next_query[0].query   = e;
        next_query[0].address = 0;
        next_query++;

    } else {
        // printf("Symbolic Store (already concretized)\n");
    }
}

#if DEBUG_EXPR_CONSISTENCY
static void add_consistency_check_load(Expr* e, uintptr_t addr, size_t size) 
{
    uintptr_t concrete_value = 0;
    for (size_t i = 0; i < size; i++) {
        uintptr_t v = *(((uint8_t*)addr) + i);
        concrete_value |= v << (8 * i);
        // printf("Concrete byte: %lx\n", v);
    }
    //
    if (!s_config.debug_fuzz_expr) {
        printf("CONSISTENCY CHECK LOAD for addr=%lx size=%lu value=%lx\n", addr, size, concrete_value);
    }
    add_consistency_check(e, concrete_value, size, SYMBOLIC_LOAD);
#if 0
    if (GET_QUERY_IDX(next_query -1) > 436197) {
        printf("HERE2\n");
        tcg_abort();
    }
#endif
}
#endif

static inline void qemu_load_helper(uintptr_t orig_addr,
                                    uintptr_t mem_op_offset, uintptr_t addr_idx,
                                    uintptr_t val_idx)
{
    TCGMemOp  mem_op = get_mem_op(mem_op_offset);
    uintptr_t offset = get_mem_offset(mem_op_offset);

    // number of bytes to load
    size_t    size = get_mem_op_size(mem_op);
    uintptr_t addr = orig_addr + offset;
#if 0
    if (GET_QUERY_IDX(next_query) >= 116753 && GET_QUERY_IDX(next_query) <= 116773) {
        printf("[0x%lx] load addr=%lx size=%lu value=%lu\n", current_tb_pc, addr, size, *((uint64_t*)addr));
        printf("\nValue at %lx is %lu\n", 0x40007ff378, *((uint64_t*)0x40007ff378));
    }
#endif
#if 0
    printf("Loading %lu bytes from %p at offset %lu\n", size, (void*)orig_addr, offset);
#endif


    if (addr_idx < TCG_MAX_TEMPS && s_temps[addr_idx]) {
#if 0
        if (CONST(s_temps[addr_idx]) < 0x500000) {
           printf("\nSymbolic Access: %p\n", s_temps[addr_idx]);
           tcg_abort();
        }
#endif
#if SYMBOLIC_COSTANT_ACCESS
        uintptr_t base = find_const_base(s_temps[addr_idx], 0);
        if (IS_LIKELY_CONST_BASE(base)) {
#if 0
            printf("Detected base: 0x%lx\n", base);
#endif

            Expr*     initial_free_expr = next_free_expr;
            uintptr_t base_addr         = orig_addr;
            size_t    n_slice           = 1;
            if (orig_addr - base < (SLICE_SIZE * MAX_NUM_SLICES)) {
                base_addr = base;
                n_slice   = MAX_NUM_SLICES;
            }

            uint8_t read_from_slice                  = 1;
            Expr*   slices_addrs[MAX_NUM_SLICES + 1] = {0};
            for (size_t i = 0; i < n_slice; i++) {
                uintptr_t norm_addr = (base_addr / SLICE_SIZE) * SLICE_SIZE;
                uintptr_t hash_addr = HASH_ADDR(norm_addr);
                uintptr_t idx       = hash_addr % CONST_MAP_SIZE;
                uint8_t   status    = const_mem_map[idx].status;

                if (status == 0) {

                    void* page_addr =
                        (void*)((norm_addr / page_size) * page_size);
                    if (msync(page_addr, page_size, MS_ASYNC) != 0) {
                        // printf("Page containing %lx is not allocated\n",
                        // norm_addr);
                        break;
                    } else if (norm_addr + SLICE_SIZE - 1 >
                               ((uintptr_t)page_addr) + page_size) {
                        page_addr =
                            (void*)(((norm_addr + SLICE_SIZE - 1) / page_size) *
                                    page_size);
                        if (msync(page_addr, page_size, MS_ASYNC) != 0) {
                            // printf("Page containing %lx is not allocated\n",
                            // norm_addr);
                            break;
                        }
                    }

                    assert(const_mem_map[idx].base == 0);
                    const_mem_map[idx].status = 1;
                    const_mem_map[idx].used   = 1;
                    const_mem_map[idx].base   = norm_addr;
                    const_mem_map[idx].dump   = next_free_expr;

                    slices_addrs[i] = next_free_expr;

                    memcpy(next_free_expr, &norm_addr, sizeof(uintptr_t));
                    next_free_expr =
                        (Expr*)(((uint8_t*)next_free_expr) + sizeof(uintptr_t));
                    memcpy(next_free_expr, (void*)norm_addr, SLICE_SIZE);
                    next_free_expr += SLICE_SIZE / sizeof(Expr);
#if 0
                    printf("Taking a memory slice #%lu at 0x%lx\n", idx, norm_addr);
#endif
                    slices_count += 1;
                } else if (status == 1) {
                    // reusing taken snapshot
                    const_mem_map[idx].used += 1;
                    slices_addrs[i] = const_mem_map[idx].dump;
                } else {
                    // memory is not constant
                    read_from_slice = 0;
                    break;
                }

                base_addr += SLICE_SIZE;
            }

            if (read_from_slice && slices_count > 0) {

                Expr* offset_addr = s_temps[addr_idx];
                if (offset > 0) {
                    offset_addr = new_expr();
                    offset_addr->opkind = ADD;
                    offset_addr->op1 = s_temps[addr_idx];
                    SET_EXPR_CONST_OP(offset_addr->op2, offset_addr->op2_is_const, offset);
                }

                Expr* q   = new_expr();
                q->opkind = MEMORY_SLICE_ACCESS;
                q->op1    = offset_addr;
                q->op2    = EXPR_CONST_OP(addr);
                q->op3    = EXPR_CONST_OP(symbolic_access_id);

                Expr* e   = new_expr();
                e->opkind = IS_SYMBOLIC;
                e->op1    = EXPR_CONST_OP(symbolic_access_id);
                e->op2    = EXPR_CONST_OP(size);
                switch (size) {
                    case 1:
                        e->op3 = EXPR_CONST_OP(*((uint8_t*)addr));
                        break;
                    case 2:
                        e->op3 = EXPR_CONST_OP(*((uint16_t*)addr));
                        break;
                    case 4:
                        e->op3 = EXPR_CONST_OP(*((uint32_t*)addr));
                        break;
                    case 8:
                        e->op3 = EXPR_CONST_OP(*((uint64_t*)addr));
                        break;
                    default:
                        tcg_abort();
                }

                // printf("Generating new symbolic for slice access: %lu\n", symbolic_access_id);

                size_t k = 0;
                while (slices_addrs[k]) {
                    Expr* s   = new_expr();
                    s->opkind = MEMORY_SLICE;
                    s->op1    = slices_addrs[k];
                    s->op2    = EXPR_CONST_OP(symbolic_access_id);
                    k += 1;
                }

                if (size < 8) {
                    Expr*     n_expr = new_expr();
                    uintptr_t opkind = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
                    n_expr->opkind   = opkind;
                    n_expr->op1      = e;
                    n_expr->op2      = (Expr*)(8 * size);
                    e                = n_expr;
                    // printf("Zero extending on load. %lu\n", (8 * size));
#if 0
                    if (GET_EXPR_IDX(e) == 1028) {
                        tcg_abort();
                    }
#endif
                }

                symbolic_access_id += 1;
                s_temps[val_idx] = e;

                next_query[0].query   = q;
                next_query[0].address = 0;
                next_query++;

#if DEBUG_EXPR_CONSISTENCY
                add_consistency_check_load(e, addr, size);
#endif

                return;
            } else {
                memset(initial_free_expr, 0,
                       ((char*)next_free_expr) - ((char*)initial_free_expr));
                next_free_expr = initial_free_expr;

#if SYMBOLIC_INPUT_ACCESS
                // address is within input bytes and input bytes are constant
                if (input_is_constant && addr >= input_start_addr && addr <= input_end_addr) {

                    Expr* offset_addr = s_temps[addr_idx];
                    if (offset > 0) {
                        offset_addr = new_expr();
                        offset_addr->opkind = ADD;
                        offset_addr->op1 = s_temps[addr_idx];
                        SET_EXPR_CONST_OP(offset_addr->op2, offset_addr->op2_is_const, offset);
                    }

                    Expr* q   = new_expr();
                    q->opkind = MEMORY_INPUT_SLICE_ACCESS;
                    q->op1    = offset_addr;
                    q->op2    = EXPR_CONST_OP(addr);
                    q->op3    = EXPR_CONST_OP(symbolic_access_id);

                    Expr* e   = new_expr();
                    e->opkind = IS_SYMBOLIC;
                    e->op1    = EXPR_CONST_OP(symbolic_access_id);
                    e->op2    = EXPR_CONST_OP(size);
                    e->op3    = EXPR_CONST_OP(addr - input_start_addr);

                    Expr* s   = new_expr();
                    s->opkind = INPUT_SLICE;
                    s->op1    = EXPR_CONST_OP(input_start_addr);
                    s->op2    = EXPR_CONST_OP(input_end_addr);
                    s->op3    = EXPR_CONST_OP(input_offset);

                    if (size < 8) {
                        Expr*     n_expr = new_expr();
                        uintptr_t opkind = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
                        n_expr->opkind   = opkind;
                        n_expr->op1      = e;
                        n_expr->op2      = (Expr*)(8 * size);
                        e                = n_expr;
                    }

                    symbolic_access_id += 1;
                    s_temps[val_idx] = e;

                    next_query[0].query   = q;
                    next_query[0].address = 0;
                    next_query++;

                    return;

                } else {
#endif
                    // printf("Load concretization: expr=%p", s_temps[addr_idx]);
                    load_concretization(s_temps[addr_idx], orig_addr);
#if SYMBOLIC_INPUT_ACCESS
                }
#endif
            }
        } else {
            // printf("Load concretization: expr=%p", s_temps[addr_idx]);
            load_concretization(s_temps[addr_idx], orig_addr);
        }
#else
        load_concretization(s_temps[addr_idx], orig_addr);
#endif
    }

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t  l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t* l3_page     = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    assert(l3_page_idx + size <= 1 << L3_PAGE_BITS); // ToDo: cross page access

    assert(size <= 8);
    Expr*   exprs[8]         = {NULL};
    uint8_t expr_is_not_null = 0;
    for (size_t i = 0; i < size; i++) {
        exprs[i]         = l3_page->entries[l3_page_idx + i];
        expr_is_not_null = expr_is_not_null | (exprs[i] != 0);
    }

    if (expr_is_not_null == 0) // early exit
    {
        s_temps[val_idx] = NULL;
        return;
    }

    Expr* e = NULL;
#if 1
    if (size == 8) {
        for (size_t i = 0; i < size; i++) {
            if (exprs[i] != NULL && exprs[i]->opkind == EXTRACT8 &&
                CONST(exprs[i]->op2) == i) {
                // ToDo: we are assuming that size(op1) == size
                //       which my be not true.
                if (e && e != exprs[i]->op1) {
                    e = NULL;
                    break;
                } else {
                    e = exprs[i]->op1;
                }
            } else {
                e = NULL;
                break;
            }
        }

        if (e) {
            // safety check
            if (l3_page->entries[l3_page_idx + size] != NULL &&
                l3_page->entries[l3_page_idx + size]->opkind == EXTRACT8 &&
                l3_page->entries[l3_page_idx + size]->op1 == e) {

                // the object e is larger than what we are
                // reading!
                e = NULL;
            }
        }
    }
#endif

#if VISIT_LINEARIZATION
    if (prev_loc) {
        if (!tb_is_symbolic) {
            visit_map[prev_loc] += 1;
        }
        if (visit_map[prev_loc] > VISIT_LINEARIZATION_TR) {
            // printf("Concretizing...\n");
            s_temps[val_idx] = NULL;
            return; // early exit
        }
    }
#endif

    if (e == NULL) {
        for (ssize_t i = size - 1; i >= 0; i--) {
            if (i == size - 1) {
                if (exprs[i] == NULL) {
                    // allocate a new expr for the concrete value
                    e                  = new_expr();
                    e->opkind          = IS_CONST;
                    uint8_t* byte_addr = ((uint8_t*)addr) + i;
                    uint8_t  byte      = *byte_addr;
                    e->op1             = (Expr*)((uintptr_t)byte);
#if 0
                    if (addr + i >= 0x40007ff378 && addr + i <= 0x40007ff378 + 8) {
                        printf("\nLoading concrete %lu-byte (%x) from %lx\n", i, byte, addr + i);
                    }
# endif
                } else {
                    e = exprs[i];
#if 0
                    if (addr + i >= 0x40007ff378 && addr + i <= 0x40007ff378 + 8) {
                        printf("\nLoading %lu-byte (%x) from %lx\n", i, *(((uint8_t*)addr) + i), addr + i);
                        print_expr(e);
                    }
#endif
                }
            } else {
                Expr* n_expr   = new_expr();
                n_expr->opkind = CONCAT8R;

                n_expr->op1 = e;

                if (exprs[i] == NULL) {
                    // fetch the concrete value, embed it in the expr
                    uint8_t* byte_addr   = ((uint8_t*)addr) + i;
                    uint8_t  byte        = *byte_addr;
                    n_expr->op2          = (Expr*)((uintptr_t)byte);
                    n_expr->op2_is_const = 1;
#if 0
                    if (addr + i >= 0x40007ff200 && addr + i <= 0x40007ff200 + 8) {
                        printf("\nLoading concrete %lu-byte (%x) from %lx\n", i, *(((uint8_t*)addr) + i), addr + i);
                    }
#endif
                } else {
                    n_expr->op2 = exprs[i];
#if 0
                    if (addr + i >= 0x40007ff200 && addr + i <= 0x40007ff200 + 8) {
                        printf("\nLoading %lu-byte (%x) from %lx\n", i, *(((uint8_t*)addr) + i), addr + i);
                        print_expr(n_expr->op2);
                    }
#endif
                }

                e = n_expr;
            }
        }
    }
#if 0
    else {
        for (size_t i = 0; i < size; i++) {
            if (addr + i >= 0x40007ff378 && addr + i <= 0x40007ff378 + 8) {
                printf("\nLoading byte from %lx [OPTIMIZED]\n", addr + i);
                print_expr(e);
            }
        }
    }
#endif

#if DEBUG_EXPR_CONSISTENCY
    add_consistency_check_load(e, addr, size);
#endif

    if (size < 8) {

        uintptr_t opkind = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;

        if (e->opkind == ZEXT && opkind == SEXT && CONST(e->op2) == (8 * size)) {
            e = e->op1;
        }

        if (!(opkind == SEXT && e->opkind == ZEXT && CONST(e->op2) < (8 * size)) &&
            !(opkind == e->opkind && CONST(e->op2) <= (8 * size))) {

            Expr*     n_expr = new_expr();
            n_expr->opkind   = opkind;
            n_expr->op1      = e;
            n_expr->op2      = (Expr*)(8 * size);
            e                = n_expr;
            // printf("Zero extending on load. %lu\n", (8 * size));
#if 0
            if (GET_EXPR_IDX(e) == 1267) {
                printf("\nEXTENDING: Loading %lu bytes from %lx\n", size, addr);
                print_expr(n_expr);
                tcg_abort();
            }
#endif
        }
    }

    s_temps[val_idx] = e;
}

static inline void qemu_load(TCGTemp* t_addr, TCGTemp* t_val, uintptr_t offset,
                             TCGMemOp mem_op, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert(t_val->base_type == TCG_TYPE_TL);
    assert(t_val->base_type == TCG_TYPE_I64); // FixMe: support other types
    assert((mem_op & MO_BE) == 0);            // FixMe: extend to BE

    // number of bytes to load
    size_t size = get_mem_op_size(mem_op);

    preserve_op_load(t_addr, op_in, tcg_ctx);
    preserve_op_load(t_val, op_in, tcg_ctx);

    TCGOp* op;

    TCGTemp* t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size,
                           EARLY_EXIT_CONST /* FixMe: hack */, op_in, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_end = gen_new_label();

    // early exit
    TCGLabel* label_write_null = gen_new_label();
    tcg_brcond(label_write_null, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0,
               op_in, NULL, tcg_ctx);

    // build expr, if all bytes are concrete goto to label_write_null

    TCGTemp* t_expr_is_null = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_expr_is_null, 0, 0, op_in, NULL, tcg_ctx);

    assert(size <= 8);
    TCGTemp* t_exprs[8] = {NULL};

    for (size_t i = 0; i < size; i++) {
        size_t idx   = (mem_op & MO_BE) ? i : size - i - 1;
        t_exprs[idx] = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_load_n(t_l3_page_idx_addr, t_exprs[idx],
                   sizeof(Expr*) *
                       idx /* Why? Different from the helper but it works...*/,
                   i == size - 1, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);
        tcg_binop(t_expr_is_null, t_expr_is_null, t_exprs[idx], 0, 0, 0, OR,
                  op_in, NULL, tcg_ctx);
    }

    tcg_brcond(label_write_null, t_expr_is_null, t_zero, TCG_COND_EQ, 1, 0,
               op_in, NULL, tcg_ctx);

    TCGTemp* t_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        if (i == 0) {
            // if expr is NULL, use the concrete value
            TCGLabel* label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE,
                       0, 0, op_in, NULL, tcg_ctx);

            allocate_new_expr(t_exprs[i], op_in, tcg_ctx);

            TCGTemp* t_mem_value      = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp* t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp* t_mem_value_addr_offset =
                new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL,
                     tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr,
                      t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL,
                      tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t),
                       op_in, NULL, tcg_ctx);

            tcg_store_n(t_exprs[i], t_mem_value, offsetof(Expr, op1), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, IS_CONST, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_opkind, offsetof(Expr, opkind), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);

            t_expr     = t_exprs[i];
            t_exprs[i] = NULL;
        } else {
            TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
            // FixMe: pre-allocate size exprs outside the loop
            allocate_new_expr(t_new_expr, op_in, tcg_ctx);

            TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_opkind, CONCAT8R, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op2), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            // if expr is NULL, use the concrete value

            TCGLabel* label_expr_is_not_null = gen_new_label();
            tcg_brcond(label_expr_is_not_null, t_exprs[i], t_zero, TCG_COND_NE,
                       0, 0, op_in, NULL, tcg_ctx);

            TCGTemp* t_mem_value      = new_non_conflicting_temp(TCG_TYPE_I64);
            TCGTemp* t_mem_value_addr = new_non_conflicting_temp(TCG_TYPE_I64);
            MARK_TEMP_AS_ALLOCATED(t_addr);
            tcg_mov(t_mem_value_addr, t_addr, 0, 0, op_in, NULL, tcg_ctx);
            MARK_TEMP_AS_NOT_ALLOCATED(t_addr);
            TCGTemp* t_mem_value_addr_offset =
                new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_mem_value_addr_offset, offset + i, 0, op_in, NULL,
                     tcg_ctx);
            tcg_binop(t_mem_value_addr, t_mem_value_addr,
                      t_mem_value_addr_offset, 0, 0, 1, ADD, op_in, NULL,
                      tcg_ctx);
            tcg_load_n(t_mem_value_addr, t_mem_value, 0, 1, 0, sizeof(uint8_t),
                       op_in, NULL, tcg_ctx);
            tcg_store_n(t_exprs[i], t_mem_value, 0, 0, 1, sizeof(Expr*), op_in,
                        NULL, tcg_ctx);

            TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
            tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_one, offsetof(Expr, op1_is_const), 0, 1,
                        sizeof(uint8_t), op_in, NULL, tcg_ctx);

            tcg_set_label(label_expr_is_not_null, op_in, NULL, tcg_ctx);
            tcg_store_n(t_new_expr, t_exprs[i], offsetof(Expr, op1), 0, 1,
                        sizeof(Expr*), op_in, NULL, tcg_ctx);

            // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
            // mark_insn_as_instrumentation(op);

            t_expr     = t_new_expr;
            t_exprs[i] = NULL;
        }
    }

    // if size is less than sizeof(TCG_TYPE_TL), we may have to
    // zero-extend or sign-extend
    if (size < 8) // FixMe: other archs
    {
        TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp*  t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        uintptr_t opkind   = get_mem_op_signextend(mem_op) ? SEXT : ZEXT;
        tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_expr, offsetof(Expr, op1), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_extend_bit = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_extend_bit, 8 * size, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_extend_bit, offsetof(Expr, op2), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
        tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_one, offsetof(Expr, op2_is_const), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        // mark_insn_as_instrumentation(op);

        t_expr = t_new_expr;
    }

    // add_void_call_1(print_expr, t_expr, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    // write expr to destination temp
    TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op,
             tcg_ctx);
    tcg_store_n(t_to, t_expr, 0, 1, 1, sizeof(void*), op_in, &op, tcg_ctx);
    tcg_br(label_end, op_in, NULL, tcg_ctx);

    // store NULL into destination temp
    tcg_set_label(label_write_null, op_in, NULL, tcg_ctx);
    for (size_t i = 0; i < size; i++)
        if (t_exprs[i])
            tcg_temp_free_internal(t_exprs[i]);
    t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[temp_idx(t_val)], 0, op_in, &op,
             tcg_ctx);
    tcg_store_n(t_to, t_zero, 0, 1, 1, sizeof(void*), op_in, &op, tcg_ctx);

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_multi_page_store(l2_page_t* l2_page, uintptr_t l2_page_idx,
                                        l3_page_t* l3_page, uintptr_t l3_page_idx,
                                        uintptr_t size, Expr* v, size_t expr_index)
{
    uintptr_t pa_size  = 1 << L3_PAGE_BITS;
    ssize_t   new_size = (ssize_t)size;

    if (v == NULL) {
        for (size_t i = l3_page_idx; i < pa_size; i++) {
            l3_page->entries[i] = NULL;
            new_size--;
        }
    } else {
        for (size_t i = l3_page_idx; i < pa_size; i++) {
            Expr* e                           = new_expr();
            e->opkind                         = EXTRACT8;
            e->op1                            = v;
            size_t idx                        = expr_index;
            e->op2                            = (Expr*)idx;
            l3_page->entries[l3_page_idx + i] = e;
            new_size--;
            expr_index += 1;
        }
    }

    if(new_size > 0) {
        l2_page_idx += 1;
        assert(l2_page_idx < (1 << L2_PAGE_BITS)); // ToDo: handli this case
        l3_page_t* l3_page = l2_page->entries[l2_page_idx];
        if (l3_page == NULL) return;
        qemu_multi_page_store(l2_page, l2_page_idx, l3_page, 0, new_size, v, expr_index);
    }
}

#if LINEARIZATION
#define MEMORY_BITMAP_SIZE 65536
static uint16_t store_bitmap[MEMORY_BITMAP_SIZE] = { 0 };
#endif

static inline void qemu_store_helper(uintptr_t orig_addr,
                                     uintptr_t mem_op_offset,
                                     uintptr_t addr_idx, 
                                     uintptr_t val_idx
#if DEBUG_EXPR_CONSISTENCY
                                     , uintptr_t concrete_val
#endif
                                     )
{
    TCGMemOp  mem_op = get_mem_op(mem_op_offset);
    uintptr_t offset = get_mem_offset(mem_op_offset);

    size_t    size = get_mem_op_size(mem_op);
    uintptr_t addr = orig_addr + offset;

#if 0
    printf("Store %lu bytes at %lx\n", size, addr);
#endif

#if 0
    for (size_t i = 0; i < size; i++) {
        if (addr + i >= 0x8b1ba0 && addr + i < 0x8b1ba0 + 1) {
            printf("\nStoring (size=%lu, val=%lx) at %lx\n", size, concrete_val, addr + i);
        }
    }
#endif

#if SYMBOLIC_COSTANT_ACCESS
    uintptr_t norm_addr = (orig_addr / SLICE_SIZE) * SLICE_SIZE;
    uintptr_t hash_addr = HASH_ADDR(norm_addr);
    uintptr_t idx       = hash_addr % CONST_MAP_SIZE;
    uint8_t   status    = const_mem_map[idx].status;
    if (status == 0 && s_temps[val_idx]) {
        const_mem_map[idx].status = 2;
        const_mem_map[idx].base   = norm_addr;
    } else if (status == 1) {
#if 0
        if (norm_addr != const_mem_map[idx].base) {
            printf("Hash conflict: %lx vs %lx\n", norm_addr, const_mem_map[idx].base);
        }
        printf("Invalidating memory slice #%lu at 0x%lu used %u times\n", idx, norm_addr, const_mem_map[idx].used);
#endif
        const_mem_map[idx].status = 2;
    }
#endif

#if SYMBOLIC_INPUT_ACCESS
    if (addr >= input_start_addr && addr <= input_end_addr) {
        input_is_constant = 0;
    }
#endif

    if (s_temps[addr_idx]) {
        store_concretization(s_temps[addr_idx], orig_addr);
    }

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) {
        if (s_temps[val_idx] == NULL) // early exit
            return;

        l2_page                             = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t  l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;
    l3_page_t* l3_page     = l2_page->entries[l2_page_idx];
    if (l3_page == NULL) {
        if (s_temps[val_idx] == NULL) // early exit
            return;

        l3_page                       = g_malloc0(sizeof(l3_page_t));
        l2_page->entries[l2_page_idx] = l3_page;
    }

    uintptr_t l3_page_idx = addr & 0xFFFF;
    if (l3_page_idx + size > 1 << L3_PAGE_BITS) {
        qemu_multi_page_store(l2_page, l2_page_idx, l3_page, l3_page_idx, size, s_temps[val_idx], 0);
        return;
    }

    if (s_temps[val_idx] == NULL) {
        for (size_t i = 0; i < size; i++) {
            l3_page->entries[l3_page_idx + i] = NULL;
#if 0
            if (addr + i >= 0x8b1ba0 && addr + i <= 0x8b1ba0 + 1) {
                printf("\nStoring concrete (size=%lu, val=%lx) at %lx+%lu\n", size, concrete_val, addr, i);
            }
#endif
        }
    } else {

        Expr* expr_a = s_temps[val_idx];

        if (expr_a->opkind == DEPOSIT) {
            size_t deposit_len = CONST(expr_a->op3) >> 16;
            size_t deposit_pos = CONST(expr_a->op3) & 0xFFFF;

            if (deposit_pos == 0 && (deposit_len / 8) == size) {

                if (expr_a->op2_is_const) {
                    for (size_t i = 0; i < size; i++) {
                        l3_page->entries[l3_page_idx + i] = NULL;
                    }
                    return;
                } else {
                    if (size == 1 && expr_a->op2->opkind == ZEXT
                            && CONST(expr_a->op2->op2) == 8) {
                        l3_page->entries[l3_page_idx] = expr_a->op2->op1;
                        return;
                    } else {
                        expr_a = expr_a->op2;
                    }
                }
            }
        }

#if DEBUG_EXPR_CONSISTENCY
        if (!s_config.debug_fuzz_expr) {
            printf("CONSISTENCY CHECK STORE for addr=%lx size=%lu\n", addr, size);
        }
        add_consistency_check(s_temps[val_idx], concrete_val, size, SYMBOLIC_STORE);
#endif
#if VISIT_LINEARIZATION
    if (prev_loc) {
        if (!tb_is_symbolic) {
            visit_map[prev_loc] += 1;
        }
        if (visit_map[prev_loc] > VISIT_LINEARIZATION_TR) {
            for (size_t i = 0; i < size; i++) {
                l3_page->entries[l3_page_idx + i] = NULL;
            }
            // printf("Concretizing...\n");
            return; // early exit
        }
    }
#endif
#if LINEARIZATION
        uint64_t hash_addr = HASH_ADDR(addr) % MEMORY_BITMAP_SIZE;
        if (store_bitmap[hash_addr] < 10000) {
            store_bitmap[hash_addr] += 1;
#if 0
            if (store_bitmap[hash_addr] % 1000 == 0) {
                printf("Store at addr=%lx count=%u index=%lu\n", addr, store_bitmap[hash_addr], hash_addr);
            }
#endif
        } else {
            // linearization
            // printf("Concretizing store value\n");
            for (size_t i = 0; i < size; i++) {
                l3_page->entries[l3_page_idx + i] = NULL;
            }
            return;
        }
#endif
        for (size_t i = 0; i < size; i++) {
            size_t idx = (mem_op & MO_BE) ? size - i - 1 : i;

            if (expr_a->opkind == CONCAT8R) {
                Expr* e = expr_a;
                ssize_t nesting = i;
                while (nesting > 0) {
                    if (e->opkind != CONCAT8R) {
                        break;
                    }
                    nesting -= 1;
                    if (e->op1_is_const) {
                        e = NULL;
                        break;
                    } else {
                        e = e->op1;
                    }
                }
                if (nesting == 0) {
                    if (e && e->opkind == CONCAT8R) {
                        if (e->op2_is_const) {
                            e = NULL;
                        } else {
                            e = e->op2;
                        }
                    }
                    if(e == NULL || (e->opkind == EXTRACT8 && CONST(e->op2) == idx)) {
                        l3_page->entries[l3_page_idx + i] = e;
                        continue;
                    }
                }
            }

            Expr* e    = new_expr();
            e->opkind  = EXTRACT8;
            e->op1     = expr_a;
            e->op2     = (Expr*)idx;
            l3_page->entries[l3_page_idx + i] = e;
            // printf("Storing byte at index %lu\n", i);
#if 0
            if (addr + i >= 0x8b1ba0 && addr + i < 0x8b1ba0 + 1) {
                printf("\nStoring at %lx (size=%lu) expression:\n", addr + i, size);
                printf("Index: %lu page=%p\n", l3_page_idx + i, l3_page);
                print_expr(e);
            }
#endif
        }
    }
}

static inline void qemu_store(TCGTemp* t_addr, TCGTemp* t_val, uintptr_t offset,
                              TCGMemOp mem_op, TCGOp* op_in,
                              TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    assert((mem_op & MO_BE) == 0); // FixMe: extend to BE

    // number of bytes to store
    size_t size = get_mem_op_size(mem_op);

    TCGOp __attribute__((unused)) * op;

    // check whether val is concrete
    size_t   val_idx         = temp_idx(t_val);
    TCGTemp* t_val_expr_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_val_expr_addr, (uintptr_t)&s_temps[val_idx], 0, op_in, NULL,
             tcg_ctx);

    TCGTemp* t_val_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_val_expr_addr, t_val_expr, 0, 1, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);

    // get location where to store expression
    TCGTemp* t_l3_page_idx_addr;
    get_expr_addr_for_addr(t_addr, &t_l3_page_idx_addr, offset, size,
                           t_val_expr, op_in, tcg_ctx);

    // add_void_call_1(print_expr, t_val_expr, op_in, &op, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_end = gen_new_label();
    // early exit
    tcg_brcond(label_end, t_l3_page_idx_addr, t_zero, TCG_COND_EQ, 0, 0, op_in,
               NULL, tcg_ctx);

    TCGLabel* label_expr_is_not_concrete = gen_new_label();
    tcg_brcond(label_expr_is_not_concrete, t_val_expr, t_zero, TCG_COND_NE, 0,
               1, op_in, NULL, tcg_ctx);

    // write NULL expr for each byte to store
    for (size_t i = 0; i < size; i++) {
        // set Expr
        tcg_store_n(t_l3_page_idx_addr, t_val_expr, sizeof(Expr*) * i, 0, 0,
                    sizeof(void*), op_in, NULL, tcg_ctx);
    }

    tcg_br(label_end, op_in, NULL, tcg_ctx);

    tcg_set_label(label_expr_is_not_concrete, op_in, NULL, tcg_ctx);

    // write EXT8(expr, index) for each byte to store
    for (size_t i = 0; i < size; i++) {
        // build EXTRACT expr
        TCGTemp* t_new_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
        // FixMe: pre-allocate size exprs outside the loop
        allocate_new_expr(t_new_expr, op_in, tcg_ctx);

        TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_opkind, EXTRACT8, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                    sizeof(uint8_t), op_in, NULL, tcg_ctx);

        tcg_store_n(t_new_expr, t_val_expr, offsetof(Expr, op1), 0,
                    i == size - 1, sizeof(Expr*), op_in, NULL, tcg_ctx);

        TCGTemp* t_index = new_non_conflicting_temp(TCG_TYPE_I64);
        tcg_movi(t_index, size - i - 1, 0, op_in, NULL, tcg_ctx);
        tcg_store_n(t_new_expr, t_index, offsetof(Expr, op2), 0, 1,
                    sizeof(Expr*), op_in, NULL, tcg_ctx);

        // add_void_call_1(print_expr, t_new_expr, op_in, &op, tcg_ctx);
        // mark_insn_as_instrumentation(op);

        // set Expr
        size_t idx = (mem_op & MO_BE) ? i : size - i - 1;
        tcg_store_n(t_l3_page_idx_addr, t_new_expr, sizeof(Expr*) * idx,
                    i == size - 1, 1, sizeof(void*), op_in, NULL, tcg_ctx);
    }

    tcg_set_label(label_end, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_extend_helper(uintptr_t packed_idx
#if DEBUG_EXPR_CONSISTENCY
                                        , uintptr_t val
#endif
                                        )
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t extkind = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

    uint8_t   opkind;
    uintptr_t opkind_const_param;
    switch (extkind) {
        case ZEXT_8:
            opkind             = ZEXT;
            opkind_const_param = 8;
            break;
        case ZEXT_16:
            opkind             = ZEXT;
            opkind_const_param = 16;
            break;
        case ZEXT_32:
            opkind             = ZEXT;
            opkind_const_param = 32;
            break;
        case SEXT_8:
            opkind             = SEXT;
            opkind_const_param = 8;
            break;
        case SEXT_16:
            opkind             = SEXT;
            opkind_const_param = 16;
            break;
        case SEXT_32:
            opkind             = SEXT;
            opkind_const_param = 32;
            break;
        default:
            tcg_abort();
    }

#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[a_idx]) {
        add_consistency_check(s_temps[a_idx], val, 8, ZEXT);
    }
#endif

    if (s_temps[a_idx]->opkind == opkind
            && CONST(s_temps[a_idx]->op2) <= opkind_const_param) {
        s_temps[out_idx] = s_temps[a_idx];
        return;
    }

    if (opkind == SEXT && s_temps[a_idx]->opkind == ZEXT
            && CONST(s_temps[a_idx]->op2) < opkind_const_param) {
        s_temps[out_idx] = s_temps[a_idx];
        return;
    }

    Expr* expr_a = s_temps[a_idx];
    if (opkind == SEXT && expr_a->opkind == ZEXT
            && CONST(expr_a->op2) == opkind_const_param) {
        expr_a = expr_a->op1;
    }

    if (expr_a->opkind == DEPOSIT &&
            opkind_const_param == 0x8 &&
            CONST(expr_a->op3) == 0x80000) {
        if (expr_a->op2_is_const) {
            s_temps[out_idx] = NULL;
        } else {
            s_temps[out_idx] = expr_a->op2;
        }
        return;
    }

    Expr* e   = new_expr();
    e->opkind = opkind;
    e->op1    = expr_a;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, opkind_const_param);
    s_temps[out_idx] = e;
}

static inline void extend(TCGTemp* t_op_to, TCGTemp* t_op_from,
                          EXTENDKIND extkind, TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t to   = temp_idx(t_op_to);
    size_t from = temp_idx(t_op_from);

    TCGOp* op;
#if 0
    tcg_print_const_str("Zero-extending", op_in, &op, tcg_ctx);
    //mark_insn_as_instrumentation(op);
#endif

    // check whether t_op_from is concrete
    TCGTemp* t_from = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_from, (uintptr_t)&s_temps[from], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_from, t_from, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_mov(
        t_out, t_from, 0, 0, op_in, NULL,
        tcg_ctx); // this is needed since we need to always overide t_to expr

    TCGLabel* label_op_is_const = gen_new_label();
    tcg_brcond(label_op_is_const, t_from, t_zero, TCG_COND_EQ, 0, 1, op_in,
               NULL, tcg_ctx);

    // create a ZEXT 32 expr

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr_conditional(t_out, op_in, tcg_ctx, label_op_is_const);

    tcg_store_n(t_out, t_from, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);

    uint8_t   opkind;
    uintptr_t opkind_const_param;
    switch (extkind) {
        case ZEXT_8:
            opkind             = ZEXT;
            opkind_const_param = 8;
            break;
        case ZEXT_16:
            opkind             = ZEXT;
            opkind_const_param = 16;
            break;
        case ZEXT_32:
            opkind             = ZEXT;
            opkind_const_param = 32;
            break;
        case SEXT_8:
            opkind             = SEXT;
            opkind_const_param = 8;
            break;
        case SEXT_16:
            opkind             = SEXT;
            opkind_const_param = 16;
            break;
        case SEXT_32:
            opkind             = SEXT;
            opkind_const_param = 32;
            break;
        default:
            tcg_abort();
    }

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, opkind, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);

    TCGTemp* t_const_param = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_const_param, opkind_const_param, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);
    tcg_store_n(t_out, t_const_param, offsetof(Expr, op2), 0, 1, sizeof(Expr*),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_one, 1, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);
    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_op_is_const->id);

    // add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    // mark_insn_as_instrumentation(op);

    tcg_set_label(label_op_is_const, op_in, NULL, tcg_ctx);

    // overide t_op_to expr
    TCGTemp* t_to = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_to, (uintptr_t)&s_temps[to], 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_to, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void mark_temp_as_in_use(TCGTemp* t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 1;
}

static inline void mark_temp_as_free(TCGTemp* t)
{
    size_t idx = temp_idx(t);
    assert(idx < TCG_MAX_TEMPS);
    used_temps_idxs[idx] = 0;
}

static inline OPKIND get_opkind(TCGOpcode opc)
{
    switch (opc) {
        case INDEX_op_add_i64:;
            return ADD;
        case INDEX_op_sub_i32:
        case INDEX_op_sub_i64:
            return SUB;
        case INDEX_op_mul_i32:
        case INDEX_op_mul_i64:
            return MUL;
        case INDEX_op_div_i64:
            return DIV;
        case INDEX_op_divu_i64:
            return DIVU;
        case INDEX_op_rem_i64:
            return REM;
        case INDEX_op_remu_i64:
            return REMU;
        case INDEX_op_and_i64:
            return AND;
        case INDEX_op_or_i64:
            return OR;
        case INDEX_op_xor_i64:
            return XOR;
        case INDEX_op_shl_i64:
            return SHL;
        case INDEX_op_shr_i64:
            return SHR;
        case INDEX_op_sar_i32:
        case INDEX_op_sar_i64:
            return SAR;
        case INDEX_op_rotl_i32:
        case INDEX_op_rotl_i64:
            return ROTL;
        case INDEX_op_rotr_i32:
        case INDEX_op_rotr_i64:
            return ROTR;
        case INDEX_op_ctz_i64:
            return CTZ;
        case INDEX_op_clz_i64:
            return CLZ;
        case INDEX_op_neg_i64:
            return NEG;
        case INDEX_op_not_i64:
            return NOT;
        case INDEX_op_muls2_i64:
        case INDEX_op_muls2_i32:
            return MUL;
        case INDEX_op_mulu2_i64:
        case INDEX_op_mulu2_i32:
            return MULU;
        case INDEX_op_bswap32_i64:
        case INDEX_op_bswap64_i64:
            return BSWAP;
        case INDEX_op_andc_i64:
            return ANDC;
        default:
            tcg_abort();
    }
}

static inline OPKIND get_opkind_from_cond(TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();

        case TCG_COND_EQ:
            return EQ;
        case TCG_COND_NE:
            return NE;

        case TCG_COND_LT:
            return LT;
        case TCG_COND_LE:
            return LE;
        case TCG_COND_GE:
            return GE;
        case TCG_COND_GT:
            return GT;

        case TCG_COND_LTU:
            return LTU;
        case TCG_COND_LEU:
            return LEU;
        case TCG_COND_GEU:
            return GEU;
        case TCG_COND_GTU:
            return GTU;

        default:
            tcg_abort();
    }
}

static inline OPKIND get_opkind_from_neg_cond(TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();

        case TCG_COND_EQ:
            return NE;
        case TCG_COND_NE:
            return EQ;

        case TCG_COND_LT:
            return GE;
        case TCG_COND_LE:
            return GT;
        case TCG_COND_GE:
            return LT;
        case TCG_COND_GT:
            return LE;

        case TCG_COND_LTU:
            return GEU;
        case TCG_COND_LEU:
            return GTU;
        case TCG_COND_GEU:
            return LTU;
        case TCG_COND_GTU:
            return LEU;

        default:
            tcg_abort();
    }
}

static inline void print_pi(void)
{
    if (!path_constraints)
        printf("\nPath constraints: true\n\n");
    else {
        printf("\nPath constraints:\n");
        print_expr(path_constraints);
        printf("\n");
    }
}

static TCGCond check_branch_cond_helper(uintptr_t a, uintptr_t b, TCGCond cond)
{
    switch (cond) {
        case TCG_COND_NEVER:;
            tcg_abort();
        case TCG_COND_ALWAYS:
            tcg_abort();
        //
        case TCG_COND_EQ:
            if (a == b)
                return TCG_COND_EQ;
            else
                return TCG_COND_NE;
        case TCG_COND_NE:
            if (a != b)
                return TCG_COND_NE;
            else
                return TCG_COND_EQ;
        //
        case TCG_COND_LT:
            if (((intptr_t)a) < ((intptr_t)b))
                return TCG_COND_LT;
            else
                return TCG_COND_GE;
        case TCG_COND_LE:
            if (((intptr_t)a) <= ((intptr_t)b))
                return TCG_COND_LE;
            else
                return TCG_COND_GT;
        case TCG_COND_GE:
            if (((intptr_t)a) >= ((intptr_t)b))
                return TCG_COND_GE;
            else
                return TCG_COND_LT;
        case TCG_COND_GT:
            if (((intptr_t)a) > ((intptr_t)b))
                return TCG_COND_GT;
            else
                return TCG_COND_LE;
        //
        case TCG_COND_LTU:
            if (a < b)
                return TCG_COND_LTU;
            else
                return TCG_COND_GEU;
        case TCG_COND_LEU:
            if (a <= b)
                return TCG_COND_LEU;
            else
                return TCG_COND_GTU;
        case TCG_COND_GTU:
            if (a > b)
                return TCG_COND_GTU;
            else
                return TCG_COND_LEU;
        case TCG_COND_GEU:
            if (a >= b)
                return TCG_COND_GEU;
            else
                return TCG_COND_LTU;
        //
        default:
            tcg_abort();
    }
}

static void setcond_helper(uintptr_t a, uintptr_t b, uintptr_t cond,
                           uintptr_t out_idx, uintptr_t a_idx, uintptr_t b_idx)
{
    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_idx] = NULL;
        return; // early exit
    }

    Expr* setcond_expr   = new_expr();
    setcond_expr->opkind = get_opkind_from_cond(cond);

    if (expr_a)
        setcond_expr->op1 = expr_a;
    else {
        setcond_expr->op1          = (Expr*)(uintptr_t)a;
        setcond_expr->op1_is_const = 1;
    }

    if (expr_b)
        setcond_expr->op2 = expr_b;
    else {
        setcond_expr->op2          = (Expr*)(uintptr_t)b;
        setcond_expr->op2_is_const = 1;
    }

    s_temps[out_idx] = setcond_expr;
}

#if LINEARIZATION
static uint16_t branch_addr_bitmap[MEMORY_BITMAP_SIZE] = { 0 };
#endif

static inline void branch_helper_internal(uintptr_t a, uintptr_t b,
                                          uintptr_t cond, Expr* expr_a,
                                          Expr* expr_b, size_t size,
                                          uintptr_t pc, uintptr_t addr_to)
{
#if 1
    if (mode > 0) {
        return;
    }
#endif

#if LINEARIZATION
    if (pc > 0) {
        uint64_t hash_pc = HASH_ADDR(pc) % MEMORY_BITMAP_SIZE;
        if (branch_addr_bitmap[hash_pc] < 500) {
            branch_addr_bitmap[hash_pc] += 1;
        } else {
            // linearization
            return;
        }
    }
#endif

    Expr*   branch_expr = new_expr();
    TCGCond sat_cond    = check_branch_cond_helper(a, b, cond);
    branch_expr->opkind = get_opkind_from_cond(sat_cond);
    SET_EXPR_OP(branch_expr->op1, branch_expr->op1_is_const, expr_a, a);
    SET_EXPR_OP(branch_expr->op2, branch_expr->op2_is_const, expr_b, b);
    branch_expr->op3 = (Expr*)size;

#if 1
    next_query[0].query   = branch_expr;
    next_query[0].address = pc;
#if BRANCH_COVERAGE == QSYM
    next_query[0].args8.arg0 = cond == sat_cond; // taken?
    next_query[0].args8.arg1 = (pc > symbolic_end_code || pc < symbolic_start_code); // library?
#elif BRANCH_COVERAGE == AFL
    next_query[0].args64 = addr_to;
#elif BRANCH_COVERAGE == FUZZOLIC

    uintptr_t addr_to_jump = cond == sat_cond ? pc : addr_to;
    uint16_t  next_loc     = (addr_to_jump >> 4) ^ (addr_to_jump << 8);
    next_loc &= BRANCH_BITMAP_SIZE - 1;

    uintptr_t index = (next_loc ^ prev_loc
#if SYMBOLIC_CALLSTACK_INSTRUMENTATION
                       ^ callstack.hash
#endif
    );
    index &= BRANCH_BITMAP_SIZE - 1;

    next_query[0].args16.index = index;
    next_query[0].args16.count = virgin_bitmap[index];

    // inverse branch direction (the one that is taken)

    addr_to_jump = cond == sat_cond ? addr_to : pc;
    next_loc     = (addr_to_jump >> 4) ^ (addr_to_jump << 8);
    next_loc &= BRANCH_BITMAP_SIZE - 1;

    index = (next_loc ^ prev_loc
#if SYMBOLIC_CALLSTACK_INSTRUMENTATION
             ^ callstack.hash
#endif
    );
    index &= BRANCH_BITMAP_SIZE - 1;

    next_query[0].args16.index_inv = index;
    next_query[0].args16.count_inv = virgin_bitmap[index];
#endif
    next_query++;
#endif
    // assert(next_query[0].query == 0);
    assert(next_query < query_queue + EXPR_QUERY_CAPACITY);

    // printf("Submitted a query\n");
    // uintptr_t query_id = next_query - queue_query;
    // if (query_id > 0 && query_id % 1000 == 0)
    //    printf("Submitted %ld queries\n", query_id);
#if 0
    printf("Branch at %lx [%lu]\n", pc, GET_QUERY_IDX(next_query - 1));
    print_expr(branch_expr);
    if (0 && GET_QUERY_IDX(next_query) > 100) {
        tcg_abort();
    }
#endif
}

static void branch_helper(uintptr_t a, uintptr_t b, uintptr_t cond,
                          uintptr_t packed_idx, uintptr_t pc, uintptr_t addr_to)
{
    size_t a_idx = UNPACK_0(packed_idx);
    size_t b_idx = UNPACK_1(packed_idx);
    size_t size  = UNPACK_2(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL)
        return; // early exit

#if 0
if (0x400127c2b1 == current_tb_pc) {
    printf("Branch at 0x%lx %lu %s %lu\n", pc, a_idx, opkind_to_str(get_opkind_from_cond(cond)), b_idx);
    print_expr(expr_a);
    print_expr(expr_b);
}
    // print_temp(a_idx);
    // print_temp(b_idx);
#endif

#if DEBUG_EXPR_CONSISTENCY
    if (expr_a) {
        add_consistency_check(expr_a, a, size == 0 ? 8 : size, CMP_EQ);
    }
    if (expr_b) {
        add_consistency_check(expr_b, b, size == 0 ? 8 : size, CMP_EQ);
    }
#endif

    branch_helper_internal(a, b, cond, expr_a, expr_b, size, pc, addr_to);

#if 0
    // if (pc == 0x44B557) {
    if (GET_QUERY_IDX(next_query) > 0) {
        tcg_abort();
    }
#endif
}

static void cmov_helper(uintptr_t a, uintptr_t b, uintptr_t cond,
                          uintptr_t packed_idx, uintptr_t pc, uintptr_t addr_to)
{
    size_t a_idx = UNPACK_0(packed_idx);
    size_t b_idx = UNPACK_1(packed_idx);
    size_t size  = UNPACK_2(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL)
        return; // early exit

    branch_helper_internal(a, b, cond, expr_a, expr_b, size, pc, addr_to);

#if BRANCH_COVERAGE == FUZZOLIC
    TCGCond sat_cond = check_branch_cond_helper(a, b, cond);
    uintptr_t addr_to_jump = cond == sat_cond ? addr_to : pc;
    uint16_t next_loc     = (addr_to_jump >> 4) ^ (addr_to_jump << 8);
    next_loc &= BRANCH_BITMAP_SIZE - 1;

    uintptr_t index = (next_loc ^ prev_loc
#if SYMBOLIC_CALLSTACK_INSTRUMENTATION
             ^ callstack.hash
#endif
    );
    index &= BRANCH_BITMAP_SIZE - 1;
    if (virgin_bitmap[index] < 255) {
        virgin_bitmap[index]++;
    }
    prev_loc = next_loc >> 1;
#endif
}

static inline void branch(TCGTemp* t_op_a, TCGTemp* t_op_b, TCGCond cond,
                          TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // check if both t_op_a and t_op_b are concrete
    // if this is true, skip any further work

    size_t op_a_idx = temp_idx(t_op_a);
    size_t op_b_idx = temp_idx(t_op_b);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[op_b_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    TCGLabel* label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);
    tcg_temp_free_internal(t_a_or_b);

#if 0
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // one of them is symbolic, build the expression

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    // set expr opkind
    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    OPKIND   opkind   = get_opkind_from_cond(cond);
    tcg_movi(t_opkind, opkind, 0, op_in, NULL, tcg_ctx);
    OPKIND   opkind_neg   = get_opkind_from_neg_cond(cond);
    TCGTemp* t_opkind_neg = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind_neg, opkind_neg, 0, op_in, NULL, tcg_ctx);
    TCGTemp* t_opkind_actual = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_cmov(t_opkind_actual, t_op_a, t_op_b, t_opkind, t_opkind_neg, cond, 0,
             0, 0, 1, 1, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);
    tcg_store_n(t_out, t_opkind_actual, offsetof(Expr, opkind), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_a);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel* label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in,
               NULL, tcg_ctx);
    tcg_temp_free_internal(t_zero);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_one);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_b);

#if 0
    tcg_print_const_str("Branch cond expr", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    add_void_call_1(print_expr, t_out, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
    tcg_print_const_str("Branch cond DONE", op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    // build the new expr for path_constraints: t_out AND path_constraints

    TCGTemp* t_new_pi_expr = new_non_conflicting_temp(TCG_TYPE_I64);
    allocate_new_expr(
        t_new_pi_expr, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, AND, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_opkind, offsetof(Expr, opkind), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_opkind);

    TCGTemp* t_pi_addr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_pi_addr, (uintptr_t)&path_constraints, 0, op_in, NULL, tcg_ctx);

    tcg_store_n(t_new_pi_expr, t_out, offsetof(Expr, op1), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_out);

    TCGTemp* t_old_pi_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_load_n(t_pi_addr, t_old_pi_expr, 0, 0, 0, sizeof(uintptr_t), op_in,
               NULL, tcg_ctx);
    tcg_store_n(t_new_pi_expr, t_old_pi_expr, offsetof(Expr, op2), 0, 1,
                sizeof(uintptr_t), op_in, NULL, tcg_ctx);
    tcg_temp_free_internal(t_old_pi_expr);

    tcg_store_n(t_pi_addr, t_new_pi_expr, 0, 1, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);
    tcg_temp_free_internal(t_new_pi_expr);
    tcg_temp_free_internal(t_pi_addr);

#ifdef SYMBOLIC_DEBUG
    TCGOp* op;
    add_void_call_0(print_pi, op_in, &op, tcg_ctx);
    mark_insn_as_instrumentation(op);
#endif

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void read_from_input(intptr_t offset, uintptr_t addr, size_t size)
{
    if (size == 0) return;
    if (symbolic_mode == 0) {
        symbolic_mode = 1;
    }

    assert(offset >= 0 && "Invalid offset");
    // printf("Offset=%ld size=%ld\n", offset, size);
    assert((offset + size) < MAX_INPUT_SIZE && "Offset is too large");

    printf(
        "Reading %lu bytes from input at 0x%lx. Storing them at addr 0x%lx\n",
        size, offset, addr);

#if SYMBOLIC_INPUT_ACCESS
    input_start_addr = addr;
    input_end_addr = addr + size - 1;
    input_offset = offset;
    input_is_constant = 1;
#endif

    uintptr_t  l1_page_idx = addr >> (L1_PAGE_BITS + L2_PAGE_BITS);
    l2_page_t* l2_page     = s_memory.table.entries[l1_page_idx];
    if (l2_page == NULL) {
        l2_page                             = g_malloc0(sizeof(l2_page_t));
        s_memory.table.entries[l1_page_idx] = l2_page;
    }

    uintptr_t l2_page_idx = (addr >> L2_PAGE_BITS) & 0xFFFF;

    while (size > 0) {

        l3_page_t* l3_page = l2_page->entries[l2_page_idx];
        if (l3_page == NULL) {
            l3_page                       = g_malloc0(sizeof(l3_page_t));
            l2_page->entries[l2_page_idx] = l3_page;
        }

        uintptr_t l3_page_idx = addr & 0xFFFF;

        size_t bytes_in_page = size;
        if ((l3_page_idx + size) > (1 << L3_PAGE_BITS)) {
            bytes_in_page = (1 << L3_PAGE_BITS) - l3_page_idx;
        }
        size -= bytes_in_page;

        for (size_t i = 0; i < bytes_in_page; i++) {
            Expr* e_byte = input_exprs[offset];
            if (e_byte == NULL) {
                e_byte              = new_expr();
                e_byte->opkind      = IS_SYMBOLIC;
                e_byte->op1         = (Expr*)(offset); // ID
                e_byte->op2         = (Expr*)1;        // number of bytes
                input_exprs[offset] = e_byte;

                // printf("Input byte %lu: %x\n", offset, *((uint8_t*)addr));
            }
            l3_page->entries[l3_page_idx + i] = e_byte;

#if SYMBOLIC_COSTANT_ACCESS
            uintptr_t norm_addr = (addr / SLICE_SIZE) * SLICE_SIZE;
            uintptr_t hash_addr = HASH_ADDR(norm_addr);
            uintptr_t idx       = hash_addr % CONST_MAP_SIZE;
            uint8_t   status    = const_mem_map[idx].status;
            if (status == 0) {
                const_mem_map[idx].status = 2;
                const_mem_map[idx].base   = norm_addr;
            } else if (status == 1) {
                const_mem_map[idx].status = 2;
            }
#endif

            addr += 1;
            offset += 1;
        }

        if (size > 0) {
            l2_page_idx++;
        }
    }
}

static int         finalization_done = 0;
static inline void end_symbolic_mode(void)
{
    if (finalization_done) {
        return;
    }
    finalization_done = 1;
    //
    next_query[0].query  = FINAL_QUERY;
    query_queue[0].query = SHM_DONE;
    //
    printf("\nNumber of queries: %lu\n", (next_query - query_queue) - 1);
    printf("Number of expressions: %lu\n", GET_EXPR_IDX(next_free_expr));
    printf("Number of memory slices: %lu\n", slices_count);
}

static Expr** get_expr_addr(uintptr_t addr, size_t size, uint8_t allocate,
                            size_t* n_overflow_bytes)
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

    if ((l3_page_idx + size) > (1 << L3_PAGE_BITS)) {
        // printf("n_overflow_bytes=%p\n", n_overflow_bytes);
        if (n_overflow_bytes) {
            // printf("size=%lu l3_page_idx=%lu\n", size, l3_page_idx);
            *n_overflow_bytes = size - ((1 << L3_PAGE_BITS) - l3_page_idx);
        } else {
            assert(0 && "Cross page access");
        }
    } else {
        if (n_overflow_bytes) {
            *n_overflow_bytes = 0;
        }
    }

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

static inline void clear_mem(uintptr_t addr, uintptr_t size)
{
    size_t overflow_n_bytes = 0;
    // printf("A overflow_n_bytes: %lu\n", overflow_n_bytes);
    Expr** exprs = get_expr_addr((uintptr_t)addr, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        if (overflow_n_bytes >= size) {
            printf("B overflow_n_bytes: %lu size=%lu\n", overflow_n_bytes,
                   size);
        }
        assert(overflow_n_bytes < size);
        size -= overflow_n_bytes;
        assert(size);
        clear_mem(addr + size, overflow_n_bytes);
    }

    if (exprs == NULL) {
        return;
    }

    for (size_t i = 0; i < size; i++) {
        exprs[i] = NULL;
        // printf("Clearing memory at %lx\n", addr + i);
    }
}

// from AFL
static const uint8_t count_class_binary[256] = {
    [0] = 0,          [1] = 1,           [2] = 2,
    [3] = 4,          [4 ... 7] = 8,     [8 ... 15] = 16,
    [16 ... 31] = 32, [32 ... 127] = 64, [128 ... 255] = 128};

static int last_open_fp = -1;
static char* last_open_file = NULL;

void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                         uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                         uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                         uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                         uintptr_t ret_val)
{
    if (s_config.coverage_tracer) {
        if (syscall_no == SYS_EXIT && ret_val == main_thread) {

            // merge local bitmap e global bitmap
            for (size_t i = 0; i < BRANCH_BITMAP_SIZE; i++) {
                // normalize the hit count
                virgin_bitmap[i] = count_class_binary[virgin_bitmap[i]];
                // new edge?
                if (!bitmap[i] && virgin_bitmap[i]) {
                    if (s_config.coverage_tracer_filter_lib < 0) {
                        g_hash_table_add(coverage_log_bb_ht, (gpointer)i);
                    }
                }
                // merge
                bitmap[i] |= virgin_bitmap[i];
            }

            save_coverage_bitmap(s_config.coverage_tracer, bitmap,
                                 BRANCH_BITMAP_SIZE);
            if (s_config.coverage_tracer_log_bb) {
                save_coverage_log(s_config.coverage_tracer_log_bb,
                                  &coverage_log_bb_ht);
            }
            if (s_config.coverage_tracer_log_edges) {
                save_coverage_log(s_config.coverage_tracer_log_edges,
                                  &coverage_log_edges_ht);
            }
        }
        return;
    }

    int       fp;
    SyscallNo nr = (SyscallNo)syscall_no;
    switch (nr) {
        case SYS_OPEN:
        case SYS_OPENAT:
            fp = ((int)ret_val);
            if (fp >= 0) {
                const char* fname = nr == SYS_OPEN ? (const char*)syscall_arg0
                                                   : (const char*)syscall_arg1;
                last_open_file = basename(fname);
                last_open_fp = fp;
                // printf("Opening file [%d]: %s\n", fp, basename(fname));
                if (s_config.symbolic_inject_input_mode == FROM_FILE && strcmp(fname, s_config.inputfile) == 0) {

                    if (input_fp[fp]) {
                        if (input_fp[fp]->shared_counter == 1) {
                            free(input_fp[fp]);
                        } else {
                            input_fp[fp]->shared_counter -= 1;
                        }
                        input_fp[fp] = NULL;
                    }

                    input_fp[fp]         = malloc(sizeof(FileDescriptorStatus));
                    input_fp[fp]->offset = 0;
                    input_fp[fp]->shared_counter = 1;
                    // printf("Opening input file: %s\n", fname);
                }
            }
            break;
        //
        case SYS_CLOSE:
            fp = syscall_arg0;
            if (last_open_fp == fp) {
                last_open_fp = -1;
                last_open_file = NULL;
            }
            if (fp >= 0 && ((int)ret_val) >= 0 && input_fp[fp]) {
                if (input_fp[fp]->shared_counter == 1) {
                    free(input_fp[fp]);
                } else {
                    input_fp[fp]->shared_counter -= 1;
                }
                input_fp[fp] = NULL;
            }
            break;
        //
        case SYS_SEEK:
            fp = syscall_arg0;
            if (fp >= 0 && ((int)ret_val) >= 0 && input_fp[fp]) {
                off_t offset = syscall_arg1;
                int   whence = syscall_arg2;
                switch (whence) {
                    case SEEK_CUR:
                        input_fp[fp]->offset += offset;
                        break;
                    case SEEK_SET:
                        input_fp[fp]->offset = offset;
                        break;
                    case SEEK_END:
                        input_fp[fp]->offset = offset;
                        break;
                    default:
                        tcg_abort();
                }
            }
            break;
        //
        case SYS_READ:
            fp = syscall_arg0;
            // printf("read from %d %s %lu bytes\n", fp, last_open_file, ret_val);
            if (fp >= 0 && !input_fp[fp]) {
                // debug: check if we are reading from stdin
                if (s_config.symbolic_inject_input_mode == READ_FD_0 &&
                    fp == FD_STDIN) {
                    printf("Reading from stdin but fp has been previosly "
                           "closed. What do we need to do?");
                    tcg_abort();
                }
                clear_mem(syscall_arg1, ret_val);
            } else if (((int)ret_val) >= 0) {
                read_from_input(input_fp[fp]->offset, syscall_arg1, ret_val);
                input_fp[fp]->offset += ret_val;
            }
            break;
        //
        case SYS_DUP: {
            int oldfp = syscall_arg0;
            fp        = ((int)ret_val);
            if (fp >= 0 && input_fp[oldfp]) {
                input_fp[fp] = input_fp[oldfp];
                input_fp[fp]->shared_counter += 1;
            }
            break;
        }
        //
        case SYS_MMAP: {
            if (ret_val != CONST(MAP_FAILED)) {
                fp = syscall_arg4;
                if (fp >= 0 && last_open_fp == fp && syscall_arg2 & PROT_EXEC) {
                    load_image(last_open_file, ret_val);
                }
                if (fp >= 0 && input_fp[fp]) {
                    size_t length = syscall_arg1;
                    int    flags  = (int)syscall_arg3;
                    off_t offset = syscall_arg5;
                    if (flags & MAP_SHARED) {
                        printf("shared mapping is not yet implemented\n");
                    }
                    // printf("[MMAP] reading from mapped file from fp %d\n", fp);
                    read_from_input(offset, ret_val, length);
                }
            }
            break;
        }
        //
        case SYS_MUNMAP: {
            break;
        }
        //
        case SYS_EXIT: {
            if (ret_val == main_thread) {
#if 0
#if BRANCH_COVERAGE == FUZZOLIC
                // merge local bitmap e global bitmap
                for (size_t i = 0; i < BRANCH_BITMAP_SIZE; i++) {
                    // normalize the hit count
                    virgin_bitmap[i] = count_class_binary[virgin_bitmap[i]];
                    // merge
                    bitmap[i] |= virgin_bitmap[i];
                }
#endif
#endif
                end_symbolic_mode();
            }
            break;
        }
        //
        default:
            tcg_abort();
    }
}

#if 0
static inline void qemu_movcond_store_helper(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, TCGTemp* t_op_true,
                                TCGTemp* t_op_false, TCGCond cond, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{

}
#endif

static inline void qemu_movcond(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, TCGTemp* t_op_true,
                                TCGTemp* t_op_false, TCGCond cond, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    // tcg_print_const_str("Doing a movcond", op_in, NULL, tcg_ctx);
    // branch(t_op_a, t_op_b, cond, op_in, tcg_ctx);

    size_t op_out_idx   = temp_idx(t_op_out);
    size_t op_true_idx  = temp_idx(t_op_true);
    size_t op_false_idx = temp_idx(t_op_false);

    TCGTemp* t_true = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_true, (uintptr_t)&s_temps[op_true_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_true, t_true, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_false = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_false, (uintptr_t)&s_temps[op_false_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_load_n(t_false, t_false, 0, 0, 0, sizeof(uintptr_t), op_in, NULL,
               tcg_ctx);

    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);
    MARK_TEMP_AS_ALLOCATED(t_op_a);
    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_cmov(t_out, t_op_a, t_op_b, t_true, t_false, cond, 0, 0, 0, 1, 1, op_in,
             NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    TCGTemp* t_out_addr = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_out_addr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_addr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline void qemu_deposit_helper(uintptr_t packed_idx, uintptr_t a,
                                       uintptr_t b,
                                       uintptr_t poslen)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t b_idx   = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL && s_temps[b_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[a_idx]) {
        add_consistency_check(s_temps[a_idx], a, 8, DEPOSIT);
    }
    if (s_temps[b_idx]) {
        add_consistency_check(s_temps[b_idx], b, 8, DEPOSIT);
    }
#endif

    Expr* expr_a = s_temps[a_idx];

    if (expr_a && expr_a->opkind == DEPOSIT && CONST(expr_a->op3) == poslen) {
        if (expr_a->op1_is_const) {
            expr_a = NULL;
        } else {
            expr_a = expr_a->op1;
        }
    }

    if (expr_a && expr_a->opkind == ZEXT && poslen == 0x80000 && CONST(expr_a->op2) == 0x8) {
        s_temps[out_idx] = s_temps[b_idx];
        return;
    }

    Expr* e   = new_expr();
    e->opkind = DEPOSIT;
    SET_EXPR_OP(e->op1, e->op1_is_const, expr_a, a);
    SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[b_idx], b);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, poslen);
    s_temps[out_idx] = e;
#if 0
    printf("DEPOSIT pc=%lx\n", pc);
    print_expr(e);

    if (s_temps[b_idx] == NULL && b == 0x55) {
        //tcg_abort();
    }
#endif
}

#if 0
static inline void qemu_deposit(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                TCGTemp* t_op_b, uintptr_t pos, uintptr_t len,
                                TCGOp* op_in, TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    size_t op_out_idx = temp_idx(t_op_out);
    size_t op_a_idx   = temp_idx(t_op_a);
    size_t op_b_idx   = temp_idx(t_op_b);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_b, (uintptr_t)&s_temps[op_b_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_b, t_b, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_a_or_b = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_binop(t_a_or_b, t_a, t_b, 0, 0, 0, OR, op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_both_concrete = gen_new_label();
    tcg_brcond(label_both_concrete, t_a_or_b, t_zero, TCG_COND_EQ, 1, 0, op_in,
               NULL, tcg_ctx);

    allocate_new_expr(
        t_out, op_in,
        tcg_ctx); // FixMe: we assume that Expr is zero-initialzed!

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, DEPOSIT, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, NULL, tcg_ctx);

    uint64_t poslen = 0;
    poslen          = PACK_0(poslen, pos);
    poslen          = PACK_1(poslen, len);

    TCGTemp* t_poslen = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_poslen, poslen, 0, op_in, NULL, tcg_ctx);
    tcg_store_n(t_out, t_poslen, offsetof(Expr, op3), 0, 1, sizeof(uint64_t),
                op_in, NULL, tcg_ctx);

    // if t_a is concrete, then store its concrete value into t_out expr

    TCGTemp* t_one = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_one, 1, 0, op_in, NULL, tcg_ctx);

    TCGLabel* label_ta_not_concrete = gen_new_label();
    tcg_brcond(label_ta_not_concrete, t_a, t_zero, TCG_COND_NE, 0, 0, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_a);
    tcg_mov(t_a, t_op_a, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_a);

    tcg_store_n(t_out, t_one, offsetof(Expr, op1_is_const), 0, 0,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_ta_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    // if t_b is concrete, then store its concrete value into t_out expr

    TCGLabel* label_tb_not_concrete = gen_new_label();
    tcg_brcond(label_tb_not_concrete, t_b, t_zero, TCG_COND_NE, 0, 1, op_in,
               NULL, tcg_ctx);

    MARK_TEMP_AS_ALLOCATED(t_op_b);
    tcg_mov(t_b, t_op_b, 0, 0, op_in, NULL, tcg_ctx);
    MARK_TEMP_AS_NOT_ALLOCATED(t_op_b);

    tcg_store_n(t_out, t_one, offsetof(Expr, op2_is_const), 0, 1,
                sizeof(uint8_t), op_in, NULL, tcg_ctx);

    tcg_set_label(label_tb_not_concrete, op_in, NULL, tcg_ctx);

    tcg_store_n(t_out, t_b, offsetof(Expr, op2), 0, 1, sizeof(uintptr_t), op_in,
                NULL, tcg_ctx);

    tcg_set_label(label_both_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}
#endif

static inline void qemu_extract_helper(uintptr_t packed_idx, uintptr_t a)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t pos     = UNPACK_2(packed_idx);
    uintptr_t len     = UNPACK_2(packed_idx);

    if (s_temps[a_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

    Expr* e   = new_expr();
    e->opkind = QZEXTRACT;
    SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[a_idx], a);
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, pos);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, len);
    s_temps[out_idx] = e;
}

static inline void qemu_extract2_helper(uintptr_t packed_idx, uintptr_t a,
                                        uintptr_t b)
{
    uintptr_t out_idx = UNPACK_0(packed_idx);
    uintptr_t a_idx   = UNPACK_1(packed_idx);
    uintptr_t b_idx   = UNPACK_2(packed_idx);
    uintptr_t pos     = UNPACK_3(packed_idx);

    if (s_temps[a_idx] == NULL && s_temps[b_idx] == NULL) {
        s_temps[out_idx] = NULL;
        return;
    }

#if DEBUG_EXPR_CONSISTENCY
    if (s_temps[a_idx]) {
        add_consistency_check(s_temps[a_idx], a, 8, QZEXTRACT2);
    }
    if (s_temps[b_idx]) {
        add_consistency_check(s_temps[b_idx], b, 8, QZEXTRACT2);
    }
#endif

    Expr* e   = new_expr();
    e->opkind = QZEXTRACT2;
    SET_EXPR_OP(e->op1, e->op1_is_const, s_temps[a_idx], a);
    SET_EXPR_OP(e->op2, e->op2_is_const, s_temps[b_idx], b);
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, pos);
    s_temps[out_idx] = e;
}

static inline void qemu_extract(TCGTemp* t_op_out, TCGTemp* t_op_a,
                                uintptr_t pos, uintptr_t len, TCGOp* op_in,
                                TCGContext* tcg_ctx)
{
    SAVE_TEMPS_COUNT(tcg_ctx);

    TCGOp* op;

    size_t op_out_idx = temp_idx(t_op_out);
    size_t op_a_idx   = temp_idx(t_op_a);

    TCGTemp* t_a = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_a, (uintptr_t)&s_temps[op_a_idx], 0, op_in, NULL, tcg_ctx);
    tcg_load_n(t_a, t_a, 0, 0, 0, sizeof(uintptr_t), op_in, NULL, tcg_ctx);

    TCGTemp* t_zero = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_zero, 0, 0, op_in, NULL, tcg_ctx); // ToDo: make this smarter

    // allocate expr for t_out
    TCGTemp* t_out = new_non_conflicting_temp(TCG_TYPE_I64);

    tcg_binop(t_out, t_zero, t_zero, 0, 0, 0, XOR, op_in, NULL,
              tcg_ctx); // force TCG to allocate the temp into a reg

    TCGLabel* label_a_concrete = gen_new_label();
    tcg_brcond(label_a_concrete, t_a, t_zero, TCG_COND_EQ, 0, 1, op_in, NULL,
               tcg_ctx);

    // FixMe: we assume that Expr is zero-initialzed!
    allocate_new_expr_conditional(t_out, op_in, tcg_ctx, label_a_concrete);

    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_opkind, QZEXTRACT, 0, op_in, NULL, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);
    tcg_store_n(t_out, t_opkind, offsetof(Expr, opkind), 0, 1, sizeof(uint8_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    tcg_store_n(t_out, t_a, offsetof(Expr, op1), 0, 1, sizeof(uint64_t), op_in,
                &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    TCGTemp* t_pos = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_pos, pos, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);
    tcg_store_n(t_out, t_pos, offsetof(Expr, op2), 0, 1, sizeof(uint64_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    TCGTemp* t_len = new_non_conflicting_temp(TCG_TYPE_I64);
    tcg_movi(t_len, len, 0, op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);
    tcg_store_n(t_out, t_len, offsetof(Expr, op3), 0, 1, sizeof(uint64_t),
                op_in, &op, tcg_ctx);
    set_conditional_instrumentation_label(op, label_a_concrete->id);

    tcg_set_label(label_a_concrete, op_in, NULL, tcg_ctx);

    // assign expr to t_out
    TCGTemp* t_out_expr = new_non_conflicting_temp(TCG_TYPE_PTR);
    tcg_movi(t_out_expr, (uintptr_t)&s_temps[op_out_idx], 0, op_in, NULL,
             tcg_ctx);
    tcg_store_n(t_out_expr, t_out, 0, 1, 1, sizeof(uintptr_t), op_in, NULL,
                tcg_ctx);

    CHECK_TEMPS_COUNT(tcg_ctx);
}

static inline OPKIND get_high_opkind(OPKIND opkind)
{
    switch (opkind) {
        case MUL:
            return MUL_HIGH;
        case MULU:
            return MULU_HIGH;

        default:
            tcg_abort();
    }
}

static inline void qemu_binop_low_high_helper(OPKIND    opkind,
                                              uintptr_t packed_idx, uintptr_t a,
                                              uintptr_t b)
{
#if 0
    printf("qemu_binop_low_high_helper\n");
#endif

    uintptr_t out_high_idx = UNPACK_0(packed_idx);
    uintptr_t out_low_idx  = UNPACK_1(packed_idx);
    uintptr_t a_idx        = UNPACK_2(packed_idx);
    uintptr_t b_idx        = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_high_idx] = NULL;
        s_temps[out_low_idx]  = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_low_expr   = new_expr();
    binop_low_expr->opkind = (OPKIND)opkind;

    if (expr_a) {
        binop_low_expr->op1 = expr_a;
    } else {
        binop_low_expr->op1          = (Expr*)(uintptr_t)a;
        binop_low_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_low_expr->op2 = expr_b;
    } else {
        binop_low_expr->op2          = (Expr*)(uintptr_t)b;
        binop_low_expr->op2_is_const = 1;
    }

    s_temps[out_low_idx] = binop_low_expr;

    Expr* binop_high_expr   = new_expr();
    binop_high_expr->opkind = get_high_opkind(opkind);

    if (expr_a) {
        binop_high_expr->op1 = expr_a;
    } else {
        binop_high_expr->op1          = (Expr*)(uintptr_t)a;
        binop_high_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_high_expr->op2 = expr_b;
    } else {
        binop_high_expr->op2          = (Expr*)(uintptr_t)b;
        binop_high_expr->op2_is_const = 1;
    }

    s_temps[out_high_idx] = binop_high_expr;
#if 0
    printf("MULU HIGH LOW\n");
    print_expr(binop_low_expr);
    print_expr(binop_high_expr);
#endif
#if DEBUG_EXPR_CONSISTENCY
    if (expr_a) {
        add_consistency_check(expr_a, a, 8, opkind);
    }
    if (expr_b) {
        add_consistency_check(expr_b, b, 8, opkind);
    }
#endif
}

static inline void qemu_binop_half_helper(OPKIND opkind, uintptr_t packed_idx,
                                          uintptr_t a, uintptr_t b)
{
#if 0
    printf("qemu_binop_half_helper\n");
#endif

    uintptr_t out_high_idx = UNPACK_0(packed_idx);
    uintptr_t out_low_idx  = UNPACK_1(packed_idx);
    uintptr_t a_idx        = UNPACK_2(packed_idx);
    uintptr_t b_idx        = UNPACK_3(packed_idx);

    Expr* expr_a = s_temps[a_idx];
    Expr* expr_b = s_temps[b_idx];
    if (expr_a == NULL && expr_b == NULL) {
        s_temps[out_high_idx] = NULL;
        s_temps[out_low_idx]  = NULL;
        return; // early exit
    }

#if 0
    printf("Binary operation:  %lu = %lu %s %lu\n", t_out_idx, t_op_a_idx,
           opkind_to_str(opkind), t_op_b_idx);
    print_temp(t_op_a_idx);
    print_temp(t_op_b_idx);
#endif

    Expr* binop_low_expr   = new_expr();
    binop_low_expr->opkind = (OPKIND)opkind;

    if (expr_a) {
        binop_low_expr->op1 = expr_a;
    } else {
        binop_low_expr->op1          = (Expr*)(uintptr_t)a;
        binop_low_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_low_expr->op2 = expr_b;
    } else {
        binop_low_expr->op2          = (Expr*)(uintptr_t)b;
        binop_low_expr->op2_is_const = 1;
    }

    binop_low_expr->op3 = (Expr*)4; // ToDo

    s_temps[out_low_idx] = binop_low_expr;

    Expr* binop_high_expr   = new_expr();
    binop_high_expr->opkind = get_high_opkind(opkind);

    if (expr_a) {
        binop_high_expr->op1 = expr_a;
    } else {
        binop_high_expr->op1          = (Expr*)(uintptr_t)a;
        binop_high_expr->op1_is_const = 1;
    }

    if (expr_b) {
        binop_high_expr->op2 = expr_b;
    } else {
        binop_high_expr->op2          = (Expr*)(uintptr_t)b;
        binop_high_expr->op2_is_const = 1;
    }

    binop_high_expr->op3 = (Expr*)(-4); // ToDo

    s_temps[out_high_idx] = binop_high_expr;
#if 0
    printf("MUL(U)_HALF HIGH LOW\n");
    print_expr(binop_low_expr);
    print_expr(binop_high_expr);
#endif
#if DEBUG_EXPR_CONSISTENCY
    if (expr_a) {
        add_consistency_check(expr_a, a, 4, opkind);
    }
    if (expr_b) {
        add_consistency_check(expr_b, b, 4, opkind);
    }
#endif
}

static inline EXTENDKIND get_extend_kind(TCGOpcode opkind)
{
    switch (opkind) {
        case INDEX_op_ext8u_i64:
            return ZEXT_8;
        case INDEX_op_ext8s_i64:
            return SEXT_8;

        case INDEX_op_ext16u_i64:
            return ZEXT_16;
        case INDEX_op_ext16s_i64:
            return SEXT_16;

        case INDEX_op_ext32u_i64:
        case INDEX_op_extu_i32_i64:
            return ZEXT_32;
        case INDEX_op_ext32s_i64:
            return SEXT_32;

        default:
            tcg_abort();
    }
}

static void register_helpers(void)
{
    g_hash_table_insert(helper_table, (gpointer)print_reg,
                        (gpointer)&helper_info_print_reg);
    g_hash_table_insert(helper_table, (gpointer)print_something,
                        (gpointer)&helper_info_print_something);
}

#include "symbolic-i386.c"

static inline void concretize_mem(uintptr_t addr, uintptr_t size)
{
    size_t overflow_n_bytes = 0;
    // printf("A overflow_n_bytes: %lu\n", overflow_n_bytes);
    Expr** exprs = get_expr_addr((uintptr_t)addr, size, 0, &overflow_n_bytes);
    if (overflow_n_bytes > 0) {
        if (overflow_n_bytes >= size) {
            printf("B overflow_n_bytes: %lu size=%lu\n", overflow_n_bytes,
                   size);
        }
        assert(overflow_n_bytes < size);
        size -= overflow_n_bytes;
        assert(size);
        concretize_mem(addr + size, overflow_n_bytes);
    }

    if (exprs == NULL) {
        return;
    }

    // printf("Memory concretization of %lu bytes at %lx\n", size, addr);

    Expr*     bytes_expr  = NULL;
    uintptr_t bytes_value = 0;
    size_t    bytes_count = 0;
    for (size_t i = 0; i < size; i++) {
        if (exprs[i]) {
            if (bytes_expr == NULL) {
                bytes_expr  = exprs[i];
                bytes_value = *(((uint8_t*)addr) + i);
                bytes_count += 1;
            } else {

                Expr* e_byte   = new_expr();
                e_byte->opkind = CONCAT8L;
                e_byte->op1    = exprs[i];
                e_byte->op2    = bytes_expr;

                bytes_expr = e_byte;

                bytes_value |= ((uint64_t)*(((uint8_t*)addr) + i)) << (bytes_count * 8);
                bytes_count += 1;

                if (bytes_count == sizeof(uintptr_t)) {
                    Expr* e   = new_expr();
                    e->opkind = MEMORY_CONCRETIZATION;
                    e->op1    = bytes_expr;
                    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, bytes_value);
                    //
                    next_query[0].query   = e;
                    next_query[0].address = 0;
                    next_query++;
                    //
                    bytes_expr  = NULL;
                    bytes_value = 0;
                    bytes_count = 0;
                }
            }
        }
        exprs[i] = NULL;
    }

    if (bytes_count > 0) {
        Expr* e   = new_expr();
        e->opkind = MEMORY_CONCRETIZATION;
        e->op1    = bytes_expr;
        SET_EXPR_CONST_OP(e->op2, e->op2_is_const, bytes_value);
        //
        next_query[0].query   = e;
        next_query[0].address = 0;
        next_query++;
    }
}

static void collect_label_targets(TCGContext* tcg_ctx, uintptr_t* targets,
                                  size_t size)
{
    memset(targets, 0, sizeof(uintptr_t) * size);

    int    last_label_id = -1;
    TCGOp* op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        if (op->opc == INDEX_op_set_label) {
            last_label_id = (int)((TCGLabel*)op->args[0])->id;
            if (last_label_id >= size) {
                tcg_abort();
            }
        } else if (op->opc == INDEX_op_movi_i64) {
            if (last_label_id >= 0) {
                targets[last_label_id] = CONST(op->args[1]);
            }
        } else if (op->opc == INDEX_op_exit_tb) {
            last_label_id = -1;
        }
    }
}

static void get_brcond_targets(TCGOp* op, uintptr_t* j_true, uintptr_t* j_false,
                               uintptr_t* label_targets, size_t size)
{
    if (op->opc != INDEX_op_brcond_i64) {
        tcg_abort();
    }

    unsigned target_label_id = (int)((TCGLabel*)op->args[3])->id;
    if (target_label_id >= size) {
        tcg_abort();
    }
    *j_true = label_targets[target_label_id];

    while (op) {
        if (op->opc == INDEX_op_movi_i64) {
            *j_false = CONST(op->args[1]);
        }
        if (op->opc == INDEX_op_exit_tb) {
            break;
        }
        op = QTAILQ_NEXT(op, link);
    }

    // printf("j_true=%lx j_false=%lx\n", *j_true, *j_false);
    assert(*j_true > 0x10000 && *j_false > 0x10000);
}

typedef struct {
    uint8_t   is_alive;
    uint8_t   is_const;
    uintptr_t const_value;
} TCGTempStaticState;

static inline int detect_load_loop(TCGContext* tcg_ctx)
{
    uintptr_t first_instr   = 0;
    uintptr_t current_instr = 0;
    uintptr_t base          = 0;
    uintptr_t scale         = 1;
    TCGTemp*  t_offset      = NULL;
    TCGTemp*  t_addr        = NULL;
    uintptr_t is_loop       = 0;
    int       has_done_load = 0;

    TCGTempStaticState temp_static_state[TCG_MAX_TEMPS] = {0};

    TCGOp* op;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
        if (op->opc == INDEX_op_insn_start) {
            current_instr = op->args[0];
            if (!first_instr) {
                first_instr = current_instr;
            }
        }
        if (!current_instr) {
            continue;
        }

        uintptr_t arg0, arg1, arg2;
        switch (op->opc) {
            case INDEX_op_movi_i64:
                arg0 = temp_idx(arg_temp(op->args[0]));
                arg1 = op->args[1];
                temp_static_state[arg0].is_alive    = 1;
                temp_static_state[arg0].is_const    = 1;
                temp_static_state[arg0].const_value = (uintptr_t)arg1;
                break;
            case INDEX_op_mov_i64:
                arg0 = temp_idx(arg_temp(op->args[0]));
                arg1 = temp_idx(arg_temp(op->args[1]));
                temp_static_state[arg0].is_alive = 1;
                temp_static_state[arg0].is_const =
                    temp_static_state[arg1].is_const;
                temp_static_state[arg0].const_value =
                    temp_static_state[arg1].const_value;
                break;
            case INDEX_op_shl_i64:
                arg0 = temp_idx(arg_temp(op->args[0]));
                arg1 = temp_idx(arg_temp(op->args[1]));
                arg2 = temp_idx(arg_temp(op->args[2]));
                if (temp_static_state[arg1].is_alive &&
                    !temp_static_state[arg1].is_const &&
                    temp_static_state[arg2].is_alive &&
                    temp_static_state[arg2].is_const) {

                    scale    = 1 << temp_static_state[arg2].const_value;
                    t_offset = arg_temp(op->args[0]);
                    temp_static_state[arg0].is_alive = 1;
                    temp_static_state[arg0].is_const = 0;
                }
                break;
            case INDEX_op_add_i64:
                arg0 = temp_idx(arg_temp(op->args[0]));
                arg1 = temp_idx(arg_temp(op->args[1]));
                arg2 = temp_idx(arg_temp(op->args[2]));
                if (temp_static_state[arg1].is_alive &&
                    temp_static_state[arg2].is_alive &&
                    temp_static_state[arg1].is_const +
                            temp_static_state[arg2].is_const ==
                        1 &&
                    base == 0) {

                    base = temp_static_state[arg1].is_const
                               ? temp_static_state[arg1].const_value
                               : temp_static_state[arg2].const_value;

                    if (base < 0x1000 || base > (0xFFFFFFFFFFFF - 0x1000)) {
                        base = 0;
                    } else {
                        TCGTemp* t_offset_tmp = temp_static_state[arg1].is_const
                                                    ? arg_temp(op->args[2])
                                                    : arg_temp(op->args[1]);

                        if (t_offset != t_offset_tmp) {
                            scale = 1;
                        }
                        t_offset = t_offset_tmp;

                        temp_static_state[arg0].is_alive = 1;
                        temp_static_state[arg0].is_const = 0;
                        t_addr = arg_temp(op->args[0]);
                        assert(t_addr);
                    }
                }
                break;
            case INDEX_op_qemu_ld_i64:
                arg0 = temp_idx(arg_temp(op->args[0])); // val
                arg1 = temp_idx(arg_temp(op->args[1])); // ptr
                if (t_addr == arg_temp(op->args[1])) {
                    printf("Load from base %lx with scale=%lu\n", base, scale);
                    has_done_load = 1;
                }
                break;
            case INDEX_op_st_i64:
                arg0 = temp_idx(arg_temp(op->args[0])); // val
                arg1 = temp_idx(arg_temp(op->args[1])); // ptr
                arg2 = op->args[2];                     // offset
                if (is_eip_offset(arg2) && temp_static_state[arg0].is_alive &&
                    temp_static_state[arg0].is_const) {

                    uintptr_t addr = temp_static_state[arg0].const_value;
                    if (addr >= first_instr && addr < current_instr) {
                        is_loop = addr;
                        // printf("Detected loop: 0x%lx\n", is_loop);
                    }
                }
                break;
            default:;
                unsigned life = op->life;
                life /= DEAD_ARG;
                if (life) {
                    for (int i = 0; life; ++i, life >>= 1) {
                        if (life & 1) {
                            temp_static_state[temp_idx(arg_temp(op->args[i]))]
                                .is_alive = 0;
                            if (arg_temp(op->args[i]) == t_addr) {
                                t_addr = NULL;
                            }
                            if (arg_temp(op->args[i]) == t_offset) {
                                t_offset = NULL;
                            }
                        } else if (!temp_static_state[temp_idx(arg_temp(
                                                          op->args[i]))]
                                        .is_alive) {
                            temp_static_state[temp_idx(arg_temp(op->args[i]))]
                                .is_alive = 1;
                            temp_static_state[temp_idx(arg_temp(op->args[i]))]
                                .is_const = 0;
                        }
                    }
                }
                break;
        }
    }

    if (base && scale && is_loop && has_done_load) {
        printf("Detected load loop: 0x%lx\n", is_loop);
    }

    return 0;
}

static int instrument = 0;
int        parse_translation_block(TranslationBlock* tb, uintptr_t tb_pc,
                                   uint8_t* tb_code, TCGContext* tcg_ctx)
{
#if 0
    {
        TCGOp* op;
        QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
        {
            // skip TB prologue
            if (op->opc != INDEX_op_insn_start) {
                continue;
            }

            TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
            tcg_movi(t_pc, (uintptr_t)tb_pc, 0, op, NULL, tcg_ctx);
            TCGTemp* t_mode = new_non_conflicting_temp(TCG_TYPE_PTR);
            tcg_movi(t_mode, (uintptr_t)mode, 0, op, NULL, tcg_ctx);
            add_void_call_2(visitTB_debug, t_pc, t_mode, op, NULL, tcg_ctx);
            tcg_temp_free_internal(t_pc);
            tcg_temp_free_internal(t_mode);
            break;
        }
    }
#endif
    if (symbolic_mode == 0)
        return 0;
#if 1
    if (mode == 2) {
        return 0;
    }
#endif
    int force_flush_cache = 0;
    if (symbolic_mode == 1) {
        instrument = 1;
        force_flush_cache = 1;
        symbolic_mode = 2;
    }

    if (s_config.coverage_tracer) {
        TCGOp* op;
        QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
        {

            // skip TB prologue
            if (op->opc != INDEX_op_insn_start) {
                continue;
            }

            TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
            tcg_movi(t_pc, (uintptr_t)tb_pc, 0, op, NULL, tcg_ctx);
            add_void_call_1(visitTB, t_pc, op, NULL, tcg_ctx);
            tcg_temp_free_internal(t_pc);
            break;
        }
        return 0;
    }

    register_helpers();

    JumpTableFinder jump_table_finder_curr_instr = {0};
    JumpTableFinder jump_table_finder_prev_instr = {0};

    TCGTempStaticState temp_static_state[TCG_MAX_TEMPS] = {0};

    if (instrument && 0) {
        detect_load_loop(tcg_ctx);
    }

    size_t    label_targets_size = 16;
    uintptr_t label_targets[label_targets_size];
    collect_label_targets(tcg_ctx, label_targets, label_targets_size);

#if 0
    int ops_to_skip = -1;
    if (instrument) {
        ops_to_skip = detect_memmove_xmm(tcg_ctx);
    }
#endif

    TCGOp* op;
    TCGOp* next_op;
    TCGOp* prev_op         = NULL;
    int    hit_first_instr = 0;

    uintptr_t pc = 0;
    QTAILQ_FOREACH(op, &tcg_ctx->ops, link)
    {
#if 0
        for (size_t idx = 0; idx < op_to_add_size; idx++) {
            tcg_op_insert_before_op(tcg_ctx, op, op_to_add[idx]);
            op_to_add[idx] = NULL;
        }
        op_to_add_size = 0;
#endif

        next_op = QTAILQ_NEXT(op, link);

#if 0
        if (ops_to_skip > 0) {
            instrument = 0;
            ops_to_skip--;
        }
#endif

        // skip TB prologue
        if (op->opc != INDEX_op_insn_start && !hit_first_instr) {
            continue;
        }

        switch (op->opc) {

            case INDEX_op_insn_start:

#if BRANCH_COVERAGE == FUZZOLIC || DEBUG_EXPR_CONSISTENCY || VISIT_LINEARIZATION
                if (hit_first_instr == 0
#if DEBUG_EXPR_CONSISTENCY
                    || 1
#endif
                        ) {
                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_pc, (uintptr_t)op->args[0], 0, op, NULL, tcg_ctx);
                    add_void_call_1(visitTB, t_pc, op, NULL, tcg_ctx);
                    tcg_temp_free_internal(t_pc);
                } else {
#if DEBUG_EXPR_CONSISTENCY
                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_pc, (uintptr_t)op->args[0], 0, op, NULL, tcg_ctx);
                    add_void_call_1(updatePC, t_pc, op, NULL, tcg_ctx);
                    tcg_temp_free_internal(t_pc);
#endif
                }
#endif

                hit_first_instr = 1;
                pc              = op->args[0];

                jump_table_finder_prev_instr = jump_table_finder_curr_instr;
                memset(&jump_table_finder_curr_instr, 0,
                       sizeof(JumpTableFinder));

                if (instrument == 0 &&
                    (s_config.symbolic_exec_start_addr == 0x0 ||
                     pc == s_config.symbolic_exec_start_addr)) {
                    // ToDo: we could start instrumenting when we inject
                    //       for the first time a symbolic data?
                    instrument        = 1;
                    // force_flush_cache = 1;
                } else if (instrument == 1 &&
                           pc == s_config.symbolic_exec_stop_addr) {
                    instrument = 0;
                    end_symbolic_mode();

#if 0
                    for (size_t i = 0; i < CONST_MAP_SIZE; i++) {
                        if (const_mem_map[i].used > 0) {
                            printf("Memory slice #%lu used %u times\n", i, const_mem_map[i].used);
                        }
                    }
#endif
                    force_flush_cache = 1;
                }

                if (instrument) {
                    debug_printf("Instrumenting %lx\n", op->args[0]);
                    if (pc == s_config.symbolic_exec_reg_instr_addr) {
                        make_reg_symbolic(s_config.symbolic_exec_reg_name, op,
                                          tcg_ctx);
                    }
                }

                LIB_MODEL model = 0;
                if (plt_addrs) {
                    model = (LIB_MODEL) g_hash_table_lookup(plt_addrs, (gpointer) pc);
                }
                if (model == REALLOC && 0) {
                    printf("Found model stub %d at %lx\n", model, pc);
#if 0
                if (pc == s_config.plt_stub_malloc ||
                    pc == s_config.plt_stub_realloc ||
                    pc == s_config.plt_stub_free ||
                    pc == s_config.plt_stub_printf) {
#endif
                    TCGTemp* t_rdi = tcg_find_temp_arch_reg(tcg_ctx, "rdi");
                    clear_temp(temp_idx(t_rdi), op, tcg_ctx);
                    TCGTemp* t_rsi = tcg_find_temp_arch_reg(tcg_ctx, "rsi");
                    clear_temp(temp_idx(t_rsi), op, tcg_ctx);
                    TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                    clear_temp(temp_idx(t_rdx), op, tcg_ctx);
                    TCGTemp* t_rcx = tcg_find_temp_arch_reg(tcg_ctx, "rcx");
                    clear_temp(temp_idx(t_rcx), op, tcg_ctx);
                    TCGTemp* t_r8 = tcg_find_temp_arch_reg(tcg_ctx, "r8");
                    clear_temp(temp_idx(t_r8), op, tcg_ctx);
                    TCGTemp* t_r9 = tcg_find_temp_arch_reg(tcg_ctx, "r9");
                    clear_temp(temp_idx(t_r9), op, tcg_ctx);
                }
                break;

            case INDEX_op_set_label:
                break;

            // moving a constant into a temp does not create symbolic exprs
            case INDEX_op_movi_i64:
            case INDEX_op_movi_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                if (instrument) {
                    TCGTemp* t = arg_temp(op->args[0]);
#if 1
                    clear_temp(temp_idx(t), op, tcg_ctx);
#else
                    TCGTemp* t_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_idx, (uintptr_t)temp_idx(t), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_idx);
#endif
                    // static analysis
                    temp_static_state[temp_idx(t)].is_alive    = 1;
                    temp_static_state[temp_idx(t)].is_const    = 1;
                    temp_static_state[temp_idx(t)].const_value = op->args[1];
                }
                break;

            // we always move exprs between temps, avoiding any check on the
            // source ToDo: branchless but more expensive?
            case INDEX_op_mov_i64:
            case INDEX_op_mov_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* from = arg_temp(op->args[1]);
                    TCGTemp* to   = arg_temp(op->args[0]);
                    size_t   size = op->opc == INDEX_op_mov_i64 ? 0 : 4;
#if 1
                    move_temp(temp_idx(from), temp_idx(to), size, op, tcg_ctx);
#else
                    TCGTemp* t_to_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_to_idx, (uintptr_t)temp_idx(to), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_from_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_from_idx, (uintptr_t)temp_idx(from), 0, op, NULL,
                             tcg_ctx);

                    if (size == sizeof(uintptr_t) || size == 0) {
#if DEBUG_EXPR_CONSISTENCY
                        MARK_TEMP_AS_ALLOCATED(from);
                        add_void_call_3(move_temp_helper, t_from_idx, t_to_idx, from,
                                        op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(from);
#else
                        add_void_call_2(move_temp_helper, t_from_idx, t_to_idx,
                                        op, NULL, tcg_ctx);
#endif
                    } else {
                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)size, 0, op, NULL, tcg_ctx);
#if DEBUG_EXPR_CONSISTENCY
                        MARK_TEMP_AS_ALLOCATED(from);
                        add_void_call_4(move_temp_size_helper, t_from_idx,
                                        t_to_idx, from, t_size, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(from);
#else
                        add_void_call_3(move_temp_size_helper, t_from_idx,
                                        t_to_idx, t_size, op, NULL, tcg_ctx);
#endif
                        tcg_temp_free_internal(t_size);
                    }
                    tcg_temp_free_internal(t_to_idx);
                    tcg_temp_free_internal(t_from_idx);
#endif
                    // jump table finder
                    if (jump_table_finder_curr_instr.displacement > 0 &&
                        jump_table_finder_curr_instr.scale_is_addr_size &&
                        jump_table_finder_curr_instr.index &&
                        jump_table_finder_curr_instr.has_done_load &&
                        jump_table_finder_curr_instr.addr &&
                        jump_table_finder_curr_instr.mov == from) {

                        jump_table_finder_curr_instr.mov = to;
                        assert(to != from);
                        assert(jump_table_finder_curr_instr.addr != to);
                        assert(jump_table_finder_curr_instr.addr != from);
                    }
                }
                break;

            case INDEX_op_add_i64:
            case INDEX_op_sub_i32:
            case INDEX_op_sub_i64:
            case INDEX_op_mul_i64:
            case INDEX_op_mul_i32:
            case INDEX_op_div_i64:
            case INDEX_op_divu_i64:
            case INDEX_op_rem_i64:
            case INDEX_op_remu_i64:
            case INDEX_op_and_i64:
            case INDEX_op_or_i64:
            case INDEX_op_xor_i64:
            case INDEX_op_shl_i64:
            case INDEX_op_shr_i64:
            case INDEX_op_sar_i32:
            case INDEX_op_sar_i64:
            case INDEX_op_rotl_i32:
            case INDEX_op_rotl_i64:
            case INDEX_op_rotr_i32:
            case INDEX_op_rotr_i64:
            case INDEX_op_ctz_i64:
            case INDEX_op_clz_i64:
            case INDEX_op_andc_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    OPKIND   bin_opkind = get_opkind(op->opc);
                    TCGTemp* t_out      = arg_temp(op->args[0]);
                    TCGTemp* t_a        = arg_temp(op->args[1]);
                    TCGTemp* t_b        = arg_temp(op->args[2]);

                    size_t size;
                    if (t_a->type == TCG_TYPE_I32) {
                        size = 4;
                    } else {
                        size = 0;
                        assert(t_a->type == TCG_TYPE_I64);
                    }

#if !VISIT_LINEARIZATION
                    qemu_binop(bin_opkind, t_out, t_a, t_b, size, op, tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)bin_opkind, 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_out));
                    v          = PACK_1(v, temp_idx(t_a));
                    v          = PACK_2(v, temp_idx(t_b));
                    v          = PACK_3(v, size);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_helper, t_opkind, t_packed_idx,
                                    t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                    // jump table finder
                    if (op->opc == INDEX_op_shl_i64 &&
                        t_a->name && // native register
                        !temp_static_state[temp_idx(t_a)].is_const &&
                        temp_static_state[temp_idx(t_b)].is_alive &&
                        temp_static_state[temp_idx(t_b)].is_const &&
                        temp_static_state[temp_idx(t_b)].const_value == 3) {

                        jump_table_finder_curr_instr.index              = t_a;
                        jump_table_finder_curr_instr.scale_is_addr_size = 1;
                    }
                    if (op->opc == INDEX_op_add_i64 &&
                        temp_static_state[temp_idx(t_b)].is_alive &&
                        temp_static_state[temp_idx(t_b)].is_const &&
                        temp_static_state[temp_idx(t_b)].const_value > 0x1000) {

                        jump_table_finder_curr_instr.displacement =
                            temp_static_state[temp_idx(t_b)].const_value;
                        jump_table_finder_curr_instr.addr = t_out;
                    }
                }
                break;

            case INDEX_op_discard:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                if (instrument) {
                    TCGTemp* t = arg_temp(op->args[0]);
#if 1
                    clear_temp(temp_idx(t), op, tcg_ctx);
#else
                    TCGTemp* t_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_idx, (uintptr_t)temp_idx(t), 0, op, NULL,
                             tcg_ctx);
                    add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                    tcg_ctx);
                    tcg_temp_free_internal(t_idx);
#endif
                }
                break;

            case INDEX_op_qemu_ld_i32: // ToDo: check this
            case INDEX_op_qemu_ld_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {

                    if (next_op->opc == INDEX_op_st_i64 &&
                        get_mem_op_size(get_memop(op->args[2])) == 8 &&
                        is_xmm_offset(next_op->args[2])) {

                        TCGTemp* t_src = arg_temp(op->args[1]);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)8, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_dst, (uintptr_t)next_op->args[2], 0, op,
                                 NULL, tcg_ctx);

                        TCGTemp* t_env = arg_temp(next_op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);
                        tcg_binop(t_dst, t_dst, t_env, 0, 0, 0, ADD, op, NULL,
                                  tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                        MARK_TEMP_AS_ALLOCATED(t_src);
                        add_void_call_3(qemu_memmove, t_src, t_dst, t_size, op,
                                        NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src);
                        tcg_temp_free_internal(t_dst);
                        tcg_temp_free_internal(t_size);

                    } else {
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 0
                        TCGMemOp  mem_op = get_memop(op->args[2]);
                        uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                        qemu_load(t_ptr, t_val, offset, mem_op, op,
                                tcg_ctx); // bugged
#else
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_mem_op,
                                 make_mem_op_offset(get_memop(op->args[2]),
                                                    get_mmuidx(op->args[2])),
                                 0, op, NULL, tcg_ctx);
                        TCGTemp* t_ptr_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op,
                                 NULL, tcg_ctx);
                        TCGTemp* t_val_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op,
                                 NULL, tcg_ctx);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_4(qemu_load_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                        tcg_temp_free_internal(t_mem_op);
                        tcg_temp_free_internal(t_ptr_idx);
                        tcg_temp_free_internal(t_val_idx);
#endif
                        // jump table finder
                        if (jump_table_finder_curr_instr.displacement > 0 &&
                            jump_table_finder_curr_instr.scale_is_addr_size &&
                            jump_table_finder_curr_instr.index &&
                            t_ptr == jump_table_finder_curr_instr.addr) {

                            jump_table_finder_curr_instr.has_done_load = 1;
                            jump_table_finder_curr_instr.mov           = t_val;
                            TCGTemp* t_addr =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            MARK_TEMP_AS_ALLOCATED(t_ptr);
                            tcg_mov(t_addr, t_ptr, 0, 0, op, NULL, tcg_ctx);
                            MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                            assert(t_addr != t_val);

                            move_temp(temp_idx(t_ptr), temp_idx(t_addr),
                                      sizeof(uintptr_t), op, tcg_ctx);

                            jump_table_finder_curr_instr.addr = t_addr;
                            jump_table_finder_curr_instr.need_to_free_addr = 1;
                            // printf("Jump table finder: load\n");
                        }
                    }
                }
                break;

            case INDEX_op_qemu_st_i32: // ToDo: check this
            case INDEX_op_qemu_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {

                    if (prev_op && prev_op->opc == INDEX_op_ld_i64 &&
                        get_mem_op_size(get_memop(op->args[2])) == 8 &&
                        is_xmm_offset(prev_op->args[2])) {

                        TCGTemp* t_dst = arg_temp(op->args[1]);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)8, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_src = new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_src, (uintptr_t)prev_op->args[2], 0, op,
                                 NULL, tcg_ctx);

                        TCGTemp* t_env = arg_temp(prev_op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);
                        tcg_binop(t_src, t_src, t_env, 0, 0, 0, ADD, op, NULL,
                                  tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                        MARK_TEMP_AS_ALLOCATED(t_dst);
                        add_void_call_3(qemu_memmove, t_src, t_dst, t_size, op,
                                        NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        tcg_temp_free_internal(t_src);
                        tcg_temp_free_internal(t_size);

                    } else {
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
#if 0
                        TCGMemOp  mem_op = get_memop(op->args[2]);
                        uintptr_t offset = (uintptr_t)get_mmuidx(op->args[2]);
                        qemu_store(t_ptr, t_val, offset, mem_op, op, tcg_ctx);
#else
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_mem_op,
                                 make_mem_op_offset(get_memop(op->args[2]),
                                                    get_mmuidx(op->args[2])),
                                 0, op, NULL, tcg_ctx);
                        TCGTemp* t_ptr_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op,
                                 NULL, tcg_ctx);
                        TCGTemp* t_val_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op,
                                 NULL, tcg_ctx);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
#if DEBUG_EXPR_CONSISTENCY
                        MARK_TEMP_AS_ALLOCATED(t_val);
                        add_void_call_5(qemu_store_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, t_val,
                                        op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_val);
#else
                        add_void_call_4(qemu_store_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, op, NULL,
                                        tcg_ctx);
#endif
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                        tcg_temp_free_internal(t_mem_op);
                        tcg_temp_free_internal(t_ptr_idx);
                        tcg_temp_free_internal(t_val_idx);
#endif
                    }
                }
                break;

            case INDEX_op_ld_i64:
            case INDEX_op_ld32s_i64:
            case INDEX_op_ld32u_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    uintptr_t offset = (uintptr_t)op->args[2];

                    if (is_xmm_offset(offset)) {

                        if (op->opc == INDEX_op_ld_i64 &&
                            next_op->opc == INDEX_op_st_i64) {

                            // move between two xmm registers

                            TCGTemp* t_size =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_size, (uintptr_t)8, 0, op, NULL,
                                     tcg_ctx);

                            TCGTemp* t_src =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_src, (uintptr_t)op->args[2], 0, op, NULL,
                                     tcg_ctx);

                            TCGTemp* t_dst =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_dst, (uintptr_t)next_op->args[2], 0, op,
                                     NULL, tcg_ctx);

                            TCGTemp* t_env = arg_temp(next_op->args[1]);

                            MARK_TEMP_AS_ALLOCATED(t_env);
                            tcg_binop(t_src, t_src, t_env, 0, 0, 0, ADD, op,
                                      NULL, tcg_ctx);
                            tcg_binop(t_dst, t_dst, t_env, 0, 0, 0, ADD, op,
                                      NULL, tcg_ctx);
                            MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                            MARK_TEMP_AS_ALLOCATED(t_src);
                            add_void_call_3(qemu_memmove, t_src, t_dst, t_size,
                                            op, NULL, tcg_ctx);
                            MARK_TEMP_AS_NOT_ALLOCATED(t_src);
                            tcg_temp_free_internal(t_dst);
                            tcg_temp_free_internal(t_src);
                            tcg_temp_free_internal(t_size);

                        } else if (op->opc == INDEX_op_ld_i64 ||
                                   op->opc == INDEX_op_ld32u_i64) {

                            // move from xmm register to general purpose
                            // register

                            TCGTemp* t_val = arg_temp(op->args[0]);
                            TCGTemp* t_ptr = arg_temp(op->args[1]);
                            MARK_TEMP_AS_ALLOCATED(t_ptr);
                            TCGTemp* t_mem_op =
                                new_non_conflicting_temp(TCG_TYPE_PTR);

                            uint32_t mem_op_kind =
                                op->opc == INDEX_op_ld_i64 ? MO_LEQ : MO_LEUL;

                            tcg_movi(t_mem_op,
                                     make_mem_op_offset(mem_op_kind, offset), 0,
                                     op, NULL, tcg_ctx);
                            TCGTemp* t_ptr_idx =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_ptr_idx, (uintptr_t) TCG_MAX_TEMPS + 1, 0, op, NULL,
                                     tcg_ctx);
                            TCGTemp* t_val_idx =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0,
                                     op, NULL, tcg_ctx);
                            add_void_call_4(qemu_load_helper, t_ptr, t_mem_op,
                                            t_ptr_idx, t_val_idx, op, NULL,
                                            tcg_ctx);
                            MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                            tcg_temp_free_internal(t_mem_op);
                            tcg_temp_free_internal(t_ptr_idx);
                            tcg_temp_free_internal(t_val_idx);

                        } else if (op->opc == INDEX_op_ld32s_i64) {
                            printf("load from xmm data (offset=%lu) at %lx\n",
                                   offset, pc);
                            tcg_abort();
                        } else if (next_op->opc != INDEX_op_qemu_st_i64) {
                            printf("load from xmm data (offset=%lu) at %lx\n",
                                   offset, pc);
                            tcg_abort();
                        }
                    } else {
                        // this is need, e.g., when the DF
                        // flag is loaded: 
                        //      ld32s_i64 tmp0,env,$0xac
                        TCGTemp* t = arg_temp(op->args[0]);
                        clear_temp(temp_idx(t), op, tcg_ctx);
                    }
                }
                break;

            case INDEX_op_st32_i64:
            case INDEX_op_st_i32:
            case INDEX_op_st_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    uintptr_t offset = (uintptr_t)op->args[2];
                    if (is_eip_offset(offset)) {
                        TCGTemp* t_value = arg_temp(op->args[0]);
#if SYMBOLIC_PC_FINDER
#if 1
                        qemu_pc_write(t_value, op, tcg_ctx);
#else
                        MARK_TEMP_AS_ALLOCATED(t_value);
                        add_void_call_1(qemu_pc_write_helper, t_value, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_value);
#endif
#endif
                        if (jump_table_finder_prev_instr.scale_is_addr_size &&
                            jump_table_finder_prev_instr.displacement &&
                            jump_table_finder_prev_instr.addr &&
                            jump_table_finder_prev_instr.index &&
                            jump_table_finder_prev_instr.has_done_load &&
                            jump_table_finder_prev_instr.mov == t_value) {
#if JUMP_TABLE_FINDER
                            // printf("\nJump Table at %lx?\n", pc);
                            qemu_jump_table(jump_table_finder_prev_instr.addr,
                                            op, tcg_ctx);
#endif
                            if (jump_table_finder_prev_instr
                                    .need_to_free_addr) {
                                tcg_temp_free_internal(
                                    jump_table_finder_prev_instr.addr);
                                clear_temp(
                                    temp_idx(jump_table_finder_prev_instr.addr),
                                    op, tcg_ctx);
                            }
                        }
#if 0
                        if (temp_static_state[temp_idx(t_value)].is_alive &&
                            temp_static_state[temp_idx(t_value)].is_const &&
                            (temp_static_state[temp_idx(t_value)].const_value ==
                                 s_config.plt_stub_malloc ||
                             temp_static_state[temp_idx(t_value)].const_value ==
                                 s_config.plt_stub_realloc ||
                             temp_static_state[temp_idx(t_value)].const_value ==
                                 s_config.plt_stub_free)) {
                            // printf("Call to malloc at %lx\n", pc);
                            // tcg_abort();

                            TCGTemp* t_rdi =
                                tcg_find_temp_arch_reg(tcg_ctx, "rdi");
                            TCGTemp* t_rsi =
                                tcg_find_temp_arch_reg(tcg_ctx, "rsi");
#if 1
                            clear_temp(temp_idx(t_rdi), op, tcg_ctx);
                            clear_temp(temp_idx(t_rsi), op, tcg_ctx);
#else
                            TCGTemp* t_idx =
                                new_non_conflicting_temp(TCG_TYPE_PTR);
                            tcg_movi(t_idx, (uintptr_t)temp_idx(t_rdi), 0, op,
                                     NULL, tcg_ctx);
                            add_void_call_1(clear_temp_helper, t_idx, op, NULL,
                                            tcg_ctx);
                            tcg_temp_free_internal(t_idx);
#endif

                            TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                            clear_temp(temp_idx(t_rdx), op, tcg_ctx);
                            TCGTemp* t_rcx = tcg_find_temp_arch_reg(tcg_ctx, "rcx");
                            clear_temp(temp_idx(t_rcx), op, tcg_ctx);
                            TCGTemp* t_r8 = tcg_find_temp_arch_reg(tcg_ctx, "r8");
                            clear_temp(temp_idx(t_r8), op, tcg_ctx);
                            TCGTemp* t_r9 = tcg_find_temp_arch_reg(tcg_ctx, "r9");
                            clear_temp(temp_idx(t_r9), op, tcg_ctx);
                        }
#endif
                    } else if (is_xmm_offset(offset)) {
                        if (prev_op->opc != INDEX_op_qemu_ld_i64 &&
                            prev_op->opc != INDEX_op_ld_i64) {

                            TCGTemp* t_value = arg_temp(op->args[0]);
                            if (temp_static_state[temp_idx(t_value)].is_alive &&
                                temp_static_state[temp_idx(t_value)].is_const) {
                                // clear the xmm reg
                                uintptr_t size =
                                    op->opc == INDEX_op_st_i64 ? 8 : 4;
                                TCGTemp* t_size =
                                    new_non_conflicting_temp(TCG_TYPE_PTR);
                                tcg_movi(t_size, size, 0, op, NULL, tcg_ctx);

                                TCGTemp* t_dst = new_non_conflicting_temp(TCG_TYPE_PTR);
                                tcg_movi(t_dst, (uintptr_t)op->args[2], 0, op,
                                            NULL, tcg_ctx);

                                TCGTemp* t_env = arg_temp(op->args[1]);
                                MARK_TEMP_AS_ALLOCATED(t_env);
                                tcg_binop(t_dst, t_dst, t_env, 0, 0, 0, ADD, op, NULL,
                                            tcg_ctx);
                                MARK_TEMP_AS_NOT_ALLOCATED(t_env);

                                add_void_call_2(clear_mem, t_dst, t_size, op,
                                                NULL, tcg_ctx);
                                tcg_temp_free_internal(t_size);
                                tcg_temp_free_internal(t_dst);
                            } else {
                                printf(
                                    "store to xmm data (offset=%lu) at %lx\n",
                                    offset, pc);
                                tcg_abort();
                            }
                        }
#if 0
                        TCGTemp* t_val = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        TCGTemp* t_mem_op =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        if (op->opc == INDEX_op_st_i64) {
                            tcg_movi(t_mem_op,
                                     make_mem_op_offset(MO_LEQ, offset), 0, op,
                                     NULL, tcg_ctx);
                        } else {
                            tcg_movi(t_mem_op,
                                     make_mem_op_offset(MO_LEUL, offset), 0, op,
                                     NULL, tcg_ctx);
                        }
                        TCGTemp* t_ptr_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_ptr_idx, (uintptr_t)temp_idx(t_ptr), 0, op,
                                 NULL, tcg_ctx);
                        TCGTemp* t_val_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_val_idx, (uintptr_t)temp_idx(t_val), 0, op,
                                 NULL, tcg_ctx);
                        add_void_call_4(qemu_store_helper, t_ptr, t_mem_op,
                                        t_ptr_idx, t_val_idx, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);
                        tcg_temp_free_internal(t_mem_op);
                        tcg_temp_free_internal(t_ptr_idx);
                        tcg_temp_free_internal(t_val_idx);
#endif
                    }
                }
                break;

            case INDEX_op_setcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
                    TCGTemp* t_b   = arg_temp(op->args[2]);
                    TCGCond  cond  = op->args[3];
#if 0
                    // ToDo
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_b_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_b_idx, (uintptr_t)temp_idx(t_b), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_out_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_out_idx, (uintptr_t)temp_idx(t_out), 0, op, NULL,
                             tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(setcond_helper, t_a, t_b, t_cond, t_out_idx,
                                    t_a_idx, t_b_idx, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_a_idx);
                    tcg_temp_free_internal(t_b_idx);
                    tcg_temp_free_internal(t_out_idx);
#endif
                }
                break;

            case INDEX_op_brcond_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_a  = arg_temp(op->args[0]);
                    TCGTemp* t_b  = arg_temp(op->args[1]);
                    TCGCond  cond = op->args[2];

                    uintptr_t address_false = 0;
                    uintptr_t address_true  = 0;
                    get_brcond_targets(op, &address_true, &address_false,
                                       label_targets, label_targets_size);
#if 0
                    branch(t_a, t_b, cond, op, tcg_ctx);
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_a));
                    v          = PACK_1(v, temp_idx(t_b));
                    v          = PACK_2(v, 0); // size

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
#if BRANCH_COVERAGE == QSYM
                    tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);
#elif BRANCH_COVERAGE == AFL
                    tcg_movi(t_pc, (uintptr_t)tb_pc, 0, op, NULL, tcg_ctx);
#elif BRANCH_COVERAGE == FUZZOLIC
                    tcg_movi(t_pc, (uintptr_t)address_false, 0, op, NULL,
                             tcg_ctx);
#endif
                    TCGTemp* t_addr_to = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_addr_to, (uintptr_t)address_true, 0, op, NULL,
                             tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(branch_helper, t_a, t_b, t_cond,
                                    t_packed_idx, t_pc, t_addr_to, op, NULL,
                                    tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_packed_idx);
                    tcg_temp_free_internal(t_pc);
                    tcg_temp_free_internal(t_addr_to);
#endif
                }
                break;

            case INDEX_op_ext8u_i64:
            case INDEX_op_ext8s_i64:
            case INDEX_op_ext16u_i64:
            case INDEX_op_ext16s_i64:
            case INDEX_op_ext32u_i64:
            case INDEX_op_ext32s_i64:
            case INDEX_op_extu_i32_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_to   = arg_temp(op->args[0]);
                    TCGTemp* t_from = arg_temp(op->args[1]);
#if 1
                    extend(t_to, t_from, get_extend_kind(op->opc), op, tcg_ctx);
#else
                    uint64_t opkind = get_extend_kind(op->opc);

                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_to));
                    v1          = PACK_1(v1, temp_idx(t_from));
                    v1          = PACK_2(v1, opkind);

                    TCGTemp* t_packed = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

#if DEBUG_EXPR_CONSISTENCY
                    MARK_TEMP_AS_ALLOCATED(t_from);
                    add_void_call_2(qemu_extend_helper, t_packed, t_from, op, NULL,
                                    tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_to);
#else
                    add_void_call_1(qemu_extend_helper, t_packed, op, NULL,
                                    tcg_ctx);
#endif
                    tcg_temp_free_internal(t_packed);
#endif
                }
                break;

            case INDEX_op_br:
            case INDEX_op_goto_ptr:
            case INDEX_op_goto_tb:
            case INDEX_op_exit_tb:
                break;

            case INDEX_op_call:
                for (size_t i = 0; i < TCGOP_CALLO(op); i++)
                    mark_temp_as_in_use(arg_temp(op->args[i]));
                for (size_t i = 0; i < TCGOP_CALLI(op); i++)
                    mark_temp_as_in_use(
                        arg_temp(op->args[TCGOP_CALLO(op) + i]));

                if (instrument) {

                    const char* helper_name = tcg_find_helper(
                        tcg_ctx, op->args[TCGOP_CALLI(op) + TCGOP_CALLO(op)]);

                    if (strcmp(helper_name, "syscall") == 0) {

                        // we directly instrment the syscall handler for x86
                        // see syscall.c in linux-user

                        TCGTemp* t_retval =
                            tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        clear_temp(temp_idx(t_retval), op, tcg_ctx);

                    } else if (strcmp(helper_name, "cc_compute_all") == 0) {

                        // if you allocate it after MARK_TEMP_AS_ALLOCATED(...)
                        // it mark as not allocated the temps "..."
                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);

                        TCGTemp* t_ret = arg_temp(op->args[0]);

                        TCGTemp* t_dst = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_dst);

                        TCGTemp* t_src1 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src1);

                        TCGTemp* t_src2 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_src2);

                        TCGTemp* t_ccop = arg_temp(op->args[4]); // cc_op
                        MARK_TEMP_AS_ALLOCATED(t_ccop);

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_ret));
                        v          = PACK_1(v, temp_idx(t_dst));
                        v          = PACK_2(v, temp_idx(t_src1));
                        v          = PACK_3(v, temp_idx(t_src2));

                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_5(qemu_cc_compute_all, t_packed_idx,
                                        t_dst, t_src1, t_src2, t_ccop, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_ccop);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src1);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src2);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "cc_compute_c") == 0) {

                        // if you allocate it after MARK_TEMP_AS_ALLOCATED(...)
                        // it mark as not allocated the temps "..."
                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);

                        TCGTemp* t_ret = arg_temp(op->args[0]);

                        TCGTemp* t_dst = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_dst);

                        TCGTemp* t_src1 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src1);

                        TCGTemp* t_src2 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_src2);

                        TCGTemp* t_ccop = arg_temp(op->args[4]); // cc_op
                        MARK_TEMP_AS_ALLOCATED(t_ccop);

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_ret));
                        v          = PACK_1(v, temp_idx(t_dst));
                        v          = PACK_2(v, temp_idx(t_src1));
                        v          = PACK_3(v, temp_idx(t_src2));

                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_5(qemu_cc_compute_c, t_packed_idx, t_dst,
                                        t_src1, t_src2, t_ccop, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_ccop);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src1);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src2);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "rclq") == 0) {

                        TCGTemp* t_out = arg_temp(op->args[0]);

                        TCGTemp* t_env = arg_temp(op->args[1]);
                        MARK_TEMP_AS_ALLOCATED(t_env);

                        TCGTemp* t_0 = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_0);

                        TCGTemp* t_1 = arg_temp(op->args[3]);
                        MARK_TEMP_AS_ALLOCATED(t_1);

                        TCGTemp* t_ccsrc =
                            tcg_find_temp_arch_reg(tcg_ctx, "cc_src");

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_out));
                        v          = PACK_1(v, temp_idx(t_0));
                        v          = PACK_2(v, temp_idx(t_1));
                        v          = PACK_3(v, temp_idx(t_ccsrc));

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        add_void_call_4(qemu_rcl, t_packed_idx, t_env, t_0, t_1,
                                        op, NULL, tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_0);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_1);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "divq_EAX") == 0 ||
                               strcmp(helper_name, "idivq_EAX") == 0 ||
                               strcmp(helper_name, "divl_EAX") == 0 ||
                               strcmp(helper_name, "idivl_EAX") == 0 ||
                               strcmp(helper_name, "divw_AX") == 0 ||
                               strcmp(helper_name, "idivw_AX") == 0) {

                        TCGTemp* t_rax = tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                        TCGTemp* t_0   = arg_temp(op->args[1]);

                        uint64_t size;
                        uint64_t mode; // 0: div, 1: idiv
                        switch (helper_name[0]) {
                            case 'd':
                                mode = 0;
                                size = suffix_to_slice(helper_name[3], 0);
                                break;
                            case 'i':
                                mode = 1;
                                size = suffix_to_slice(helper_name[4], 0);
                                break;
                            default:
                                tcg_abort();
                        }

                        uint64_t size_mode = (size << 1) | mode;

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_rax));
                        v          = PACK_1(v, temp_idx(t_rdx));
                        v          = PACK_2(v, temp_idx(t_0));
                        v          = PACK_3(v, size_mode);

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_rax);
                        MARK_TEMP_AS_ALLOCATED(t_rdx);
                        MARK_TEMP_AS_ALLOCATED(t_0);

                        if (size == 8) {
                            add_void_call_4(qemu_divq_EAX, t_packed_idx, t_rax,
                                        t_rdx, t_0, op, NULL, tcg_ctx);
                        } else if (size == 4) {
                            add_void_call_4(qemu_divl_EAX, t_packed_idx, t_rax,
                                        t_rdx, t_0, op, NULL, tcg_ctx);
                        } else if (size == 2) {
                            add_void_call_4(qemu_divw_AX, t_packed_idx, t_rax,
                                        t_rdx, t_0, op, NULL, tcg_ctx);
                        } else {
                            tcg_abort();
                        }

                        MARK_TEMP_AS_NOT_ALLOCATED(t_rax);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_rdx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_0);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "divb_AL") == 0 ||
                               strcmp(helper_name, "idivb_AL") == 0) {

                        TCGTemp* t_rax = tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        TCGTemp* t_0   = arg_temp(op->args[1]);

                        uint64_t mode; // 0: div, 1: idiv
                        switch (helper_name[0]) {
                            case 'd':
                                mode = 0;
                                break;
                            case 'i':
                                mode = 1;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_rax));
                        v          = PACK_1(v, temp_idx(t_0));
                        v          = PACK_2(v, mode);

                        TCGTemp* t_packed_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL,
                                 tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_rax);
                        MARK_TEMP_AS_ALLOCATED(t_0);

                        add_void_call_3(qemu_divb_AL, t_packed_idx, t_rax,
                                    t_0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_rax);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_0);
                        tcg_temp_free_internal(t_packed_idx);

                    } else if (strcmp(helper_name, "pand_xmm") == 0 ||
                               strcmp(helper_name, "pandn_xmm") == 0 ||
                               strcmp(helper_name, "pxor_xmm") == 0 ||
                               strcmp(helper_name, "por_xmm") == 0 ||
                               strcmp(helper_name, "paddb_xmm") == 0 ||
                               strcmp(helper_name, "paddw_xmm") == 0 ||
                               strcmp(helper_name, "paddl_xmm") == 0 ||
                               strcmp(helper_name, "paddq_xmm") == 0 ||
                               strcmp(helper_name, "psubb_xmm") == 0 ||
                               strcmp(helper_name, "psubw_xmm") == 0 ||
                               strcmp(helper_name, "psubl_xmm") == 0 ||
                               strcmp(helper_name, "psubq_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqb_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqw_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeql_xmm") == 0 ||
                               strcmp(helper_name, "pcmpeqq_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtb_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtw_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtl_xmm") == 0 ||
                               strcmp(helper_name, "pcmpgtq_xmm") == 0 ||
                               strcmp(helper_name, "pminub_xmm") == 0 ||
                               strcmp(helper_name, "pmaxub_xmm") == 0 ||
                               strcmp(helper_name, "pmullw_xmm") == 0) {

                        OPKIND    opkind;
                        uintptr_t slice;
                        switch (helper_name[1]) {
                            case 'x':
                                opkind = XOR;
                                slice  = 1;
                                break;
                            case 'o':
                                opkind = OR;
                                slice  = 1;
                                break;
                            case 'a': {
                                if (helper_name[2] == 'n') {
                                    if (helper_name[4] == '_') {
                                        opkind = AND;
                                        slice  = 1;
                                    } else {
                                        opkind = NAND;
                                        slice  = 1;
                                    }
                                } else {
                                    opkind = ADD;
                                    slice  = suffix_to_slice(helper_name[4], 0);
                                }
                                break;
                            }
                            case 's':
                                opkind = SUB;
                                slice  = suffix_to_slice(helper_name[4], 0);
                                break;
                            case 'c':
                                if (helper_name[5] == 'q') {
                                    opkind = CMP_EQ;
                                } else if (helper_name[4] == 'g' &&
                                           helper_name[5] == 't') {
                                    opkind = CMP_GT;
                                } else {
                                    tcg_abort();
                                }
                                slice = suffix_to_slice(helper_name[6], 0);
                                break;
                            case 'm': {
                                if (helper_name[2] == 'i') {
                                    opkind = MIN;
                                    slice  = suffix_to_slice(helper_name[5], 0);
                                } else if (helper_name[2] == 'a') {
                                    opkind = MAX;
                                    slice  = suffix_to_slice(helper_name[5], 0);
                                } else if (helper_name[2] == 'u') {
                                    opkind = MUL;
                                    slice  = suffix_to_slice(helper_name[5], 0);
                                } else {
                                    tcg_abort();
                                }
                                break;
                            }
                            default:
                                tcg_abort();
                        }

                        assert(slice > 0);

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)opkind, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);

                        uint64_t v = slice;
                        v          = v | (pc << 8);

                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, v, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_op, t_opkind, t_dst_addr,
                                        t_src_addr, t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);
                        tcg_temp_free_internal(t_slice);

                    } else if (strcmp(helper_name, "pmovmskb_xmm") == 0) {

                        TCGTemp* t_dst_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_dst_idx,
                                 (uintptr_t)temp_idx(arg_temp(op->args[0])), 0,
                                 op, NULL, tcg_ctx);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_2(qemu_xmm_pmovmskb, t_dst_idx,
                                        t_src_addr, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_dst_idx);

                    } else if (strcmp(helper_name, "psllb_xmm") == 0 ||
                               strcmp(helper_name, "psllw_xmm") == 0 ||
                               strcmp(helper_name, "pslld_xmm") == 0 ||
                               strcmp(helper_name, "psllq_xmm") == 0 ||
                               strcmp(helper_name, "pslldq_xmm") == 0 ||
                               strcmp(helper_name, "psrlb_xmm") == 0 ||
                               strcmp(helper_name, "psrlw_xmm") == 0 ||
                               strcmp(helper_name, "psrld_xmm") == 0 ||
                               strcmp(helper_name, "psrlq_xmm") == 0 ||
                               strcmp(helper_name, "psrldq_xmm") == 0 ||
                               strcmp(helper_name, "psrad_xmm") == 0) {

                        OPKIND    opkind;
                        uintptr_t slice;
                        switch (helper_name[2]) {
                            case 'l':
                                opkind = SHL;
                                slice  = suffix_to_slice(helper_name[4],
                                                        helper_name[5]);
                                break;
                            case 'r':
                                if (helper_name[3] == 'l') {
                                    opkind = SHR;
                                } else {
                                    opkind = SAR;
                                }
                                slice  = suffix_to_slice(helper_name[4],
                                                        helper_name[5]);
                                break;
                            default:
                                tcg_abort();
                        }

                        TCGTemp* t_opkind =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_opkind, (uintptr_t)opkind, 0, op, NULL,
                                 tcg_ctx);
                        TCGTemp* t_dst_addr = arg_temp(op->args[1]);
                        TCGTemp* t_src_addr = arg_temp(op->args[2]);
                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, slice, 0, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_op, t_opkind, t_dst_addr,
                                        t_src_addr, t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_opkind);
                        tcg_temp_free_internal(t_slice);

                    } else if (strcmp(helper_name, "pshufd_xmm") == 0 ||
                               strcmp(helper_name, "pshuflw_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);
                        TCGTemp* t_order =
                            arg_temp(op->args[2]); // this is an immediate

                        uint8_t size;
                        if (helper_name[5] == 'd') {
                            size = 4;
                        } else { // pshuflw
                            size = 2;
                        }

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, (uintptr_t)size, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_pshuf, t_dst_addr, t_src_addr,
                                        t_order, t_size, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_size);

                    } else if (strcmp(helper_name, "movl_mm_T0_xmm") == 0 ||
                                strcmp(helper_name, "movq_mm_T0_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src =
                            arg_temp(op->args[1]); // this is 32 bit

                        TCGTemp* t_src_idx =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_src_idx, (uintptr_t)temp_idx(t_src), 0, op,
                                 NULL, tcg_ctx);

                        size_t size;
                        if (helper_name[3] == 'q') {
                            size = 8;
                        } else if (helper_name[3] == 'l') {
                            size = 4;
                        } else {
                            tcg_abort();
                        }

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, size, 0, op,
                                 NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        add_void_call_3(qemu_xmm_mov_mm_T0, t_dst_addr,
                                        t_src_idx, t_size, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        tcg_temp_free_internal(t_src_idx);
                        tcg_temp_free_internal(t_size);

                    } else if (strcmp(helper_name, "punpcklbw_xmm") == 0 ||
                               strcmp(helper_name, "punpcklwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckldq_xmm") == 0 ||
                               strcmp(helper_name, "punpcklqdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhbw_xmm") == 0 ||
                               strcmp(helper_name, "punpckhwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckhdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhqdq_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);

                        uint8_t slice;
                        switch (helper_name[7]) {
                            case 'b':
                                slice = 1;
                                break;
                            case 'w':
                                slice = 2;
                                break;
                            case 'd':
                                slice = 4;
                                break;
                            case 'q':
                                slice = 8;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint8_t lowbytes;
                        if (helper_name[6] == 'l') {
                            lowbytes = 1;
                        } else if (helper_name[6] == 'h') {
                            lowbytes = 0;
                        } else {
                            tcg_abort();
                        }

                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, (uintptr_t)slice, 0, op, NULL,
                                 tcg_ctx);

                        TCGTemp* t_lowbytes =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_lowbytes, lowbytes, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_punpck, t_dst_addr, t_src_addr,
                                        t_slice, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_slice);
                        tcg_temp_free_internal(t_lowbytes);

                    } else if (strcmp(helper_name, "fxsave") == 0) {

                        TCGTemp* t_env = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);

                        MARK_TEMP_AS_ALLOCATED(t_env);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_2(qemu_fxsave, t_env, t_ptr, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                    } else if (strcmp(helper_name, "punpcklbw_xmm") == 0 ||
                               strcmp(helper_name, "punpcklwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckldq_xmm") == 0 ||
                               strcmp(helper_name, "punpcklqdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhbw_xmm") == 0 ||
                               strcmp(helper_name, "punpckhwd_xmm") == 0 ||
                               strcmp(helper_name, "punpckhdq_xmm") == 0 ||
                               strcmp(helper_name, "punpckhqdq_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);

                        uint8_t slice;
                        switch (helper_name[7]) {
                            case 'b':
                                slice = 1;
                                break;
                            case 'w':
                                slice = 2;
                                break;
                            case 'd':
                                slice = 4;
                                break;
                            case 'q':
                                slice = 8;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint8_t lowbytes;
                        if (helper_name[6] == 'l') {
                            lowbytes = 1;
                        } else if (helper_name[6] == 'h') {
                            lowbytes = 0;
                        } else {
                            tcg_abort();
                        }

                        TCGTemp* t_slice =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_slice, (uintptr_t)slice, 0, op, NULL,
                                 tcg_ctx);

                        TCGTemp* t_lowbytes =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_lowbytes, lowbytes, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_4(qemu_xmm_punpck, t_dst_addr, t_src_addr,
                                        t_slice, t_lowbytes, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_slice);
                        tcg_temp_free_internal(t_lowbytes);

                    } else if (strcmp(helper_name, "packuswb_xmm") == 0) {

                        TCGTemp* t_dst_addr = arg_temp(op->args[0]);
                        TCGTemp* t_src_addr = arg_temp(op->args[1]);

                        uint8_t sign;
                        if (helper_name[4] == 'u') {
                            sign = 0;
                        } else if (helper_name[4] == 's') {
                            sign = 1;
                        } else {
                            tcg_abort();
                        }

                        uint8_t unpacked_size;
                        switch (helper_name[6]) {
                            case 'w':
                                unpacked_size = 2;
                                break;
                            case 'd':
                                unpacked_size = 4;
                                break;
                            case 'q':
                                unpacked_size = 8;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint8_t packed_size;
                        switch (helper_name[7]) {
                            case 'b':
                                packed_size = 2;
                                break;
                            case 'w':
                                packed_size = 2;
                                break;
                            case 'd':
                                packed_size = 4;
                                break;
                            default:
                                tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, unpacked_size);
                        v          = PACK_1(v, packed_size);
                        v          = PACK_2(v, sign);

                        TCGTemp* t_packed_info =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_info, v, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_ALLOCATED(t_src_addr);
                        add_void_call_3(qemu_xmm_pack, t_dst_addr, t_src_addr,
                                        t_packed_info, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst_addr);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src_addr);
                        tcg_temp_free_internal(t_packed_info);

                    } else if (strcmp(helper_name, "fxsave") == 0) {

                        TCGTemp* t_env = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);

                        MARK_TEMP_AS_ALLOCATED(t_env);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_2(qemu_fxsave, t_env, t_ptr, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                    } else if (strcmp(helper_name, "fxrstor") == 0) {

                        TCGTemp* t_env = arg_temp(op->args[0]);
                        TCGTemp* t_ptr = arg_temp(op->args[1]);

                        MARK_TEMP_AS_ALLOCATED(t_env);
                        MARK_TEMP_AS_ALLOCATED(t_ptr);
                        add_void_call_2(qemu_fxrstor, t_env, t_ptr, op, NULL,
                                        tcg_ctx);

                        MARK_TEMP_AS_NOT_ALLOCATED(t_env);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr);

                    } else if (strcmp(helper_name, "rdtsc") == 0) {

                        TCGTemp* t_rax = tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        clear_temp(temp_idx(t_rax), op, tcg_ctx);
                        TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                        clear_temp(temp_idx(t_rdx), op, tcg_ctx);

                    } else if (strcmp(helper_name, "cpuid") == 0) {

                        TCGTemp* t_rax = tcg_find_temp_arch_reg(tcg_ctx, "rax");
                        clear_temp(temp_idx(t_rax), op, tcg_ctx);
                        TCGTemp* t_rbx = tcg_find_temp_arch_reg(tcg_ctx, "rbx");
                        clear_temp(temp_idx(t_rbx), op, tcg_ctx);
                        TCGTemp* t_rcx = tcg_find_temp_arch_reg(tcg_ctx, "rcx");
                        clear_temp(temp_idx(t_rcx), op, tcg_ctx);
                        TCGTemp* t_rdx = tcg_find_temp_arch_reg(tcg_ctx, "rdx");
                        clear_temp(temp_idx(t_rdx), op, tcg_ctx);

                        // ToDo:
                        //  QSYM sets RBX to 0x46414b45 to prevent
                        //  that glibc uses optimized libraries
                        //  Should we do the same?

                    } else if (strcmp(helper_name, "cvtsq2sd") == 0 ||
                               strcmp(helper_name, "cvtsq2ss") == 0 ||
                               strcmp(helper_name, "cvtsi2sd") == 0 ||
                               strcmp(helper_name, "cvtsi2ss") == 0 ||
                               strcmp(helper_name, "cvtsi2ssq") == 0 ||
                               strcmp(helper_name, "cvttss2sq") == 0 ||
                               strcmp(helper_name, "cvtdq2pd") == 0
                               ) {

                        // we do not yet support floating point

                        TCGTemp* t_dst = arg_temp(op->args[1]);

                        // ToDo: should we concretize also the src?
                        //       if we do not concretize then we may
                        //       get some false positives.

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, XMM_BYTES, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst);
                        add_void_call_2(clear_mem, t_dst, t_size, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);
                        tcg_temp_free_internal(t_size);

                    } else if (strcmp(helper_name, "divsd") == 0 ||
                               strcmp(helper_name, "divss") == 0 ||
                               strcmp(helper_name, "divpd") == 0 ||
                               strcmp(helper_name, "addsd") == 0 ||
                               strcmp(helper_name, "addss") == 0 ||
                               strcmp(helper_name, "subss") == 0 ||
                               strcmp(helper_name, "subsd") == 0 ||
                               strcmp(helper_name, "mulsd") == 0 ||
                               strcmp(helper_name, "mulss") == 0 ||
                               strcmp(helper_name, "minsd") == 0 ||
                               strcmp(helper_name, "minss") == 0 ||
                               strcmp(helper_name, "maxsd") == 0 ||
                               strcmp(helper_name, "maxss") == 0 ||
                               strcmp(helper_name, "sqrtsd") == 0 ||
                               strcmp(helper_name, "sqrtss") == 0 ||
                               strcmp(helper_name, "cvtss2sd") == 0 ||
                               strcmp(helper_name, "comisd") == 0 ||
                               strcmp(helper_name, "ucomiss") == 0 ||
                               strcmp(helper_name, "comiss") == 0 ||
                               strcmp(helper_name, "ucomisd") == 0 ||
                               strcmp(helper_name, "cvtsd2ss") == 0 ||
                               strcmp(helper_name, "cmpnlesd") == 0 ||
                               strcmp(helper_name, "cmplesd") == 0) {

                        // we do not yet support floating point
                        // concretize src and dst

                        TCGTemp* t_dst = arg_temp(op->args[1]);
                        TCGTemp* t_src = arg_temp(op->args[2]);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, XMM_BYTES, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_dst);
                        add_void_call_2(concretize_mem, t_dst, t_size, op, NULL,
                                        tcg_ctx);
                        add_void_call_2(clear_mem, t_dst, t_size, op,
                                                NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_dst);

                        MARK_TEMP_AS_ALLOCATED(t_src);
                        add_void_call_2(concretize_mem, t_src, t_size, op, NULL,
                                        tcg_ctx);
                        add_void_call_2(clear_mem, t_src, t_size, op,
                                                NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src);

                        tcg_temp_free_internal(t_size);

                    } else if (strcmp(helper_name, "movmskpd") == 0) {

                        // we do not yet support floating point

                        TCGTemp* t_reg = arg_temp(op->args[0]);
                        TCGTemp* t_src = arg_temp(op->args[2]);

                        TCGTemp* t_size =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_size, XMM_BYTES, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_src);
                        add_void_call_2(clear_mem, t_src, t_size, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_src);
                        tcg_temp_free_internal(t_size);

                        clear_temp(temp_idx(t_reg), op, tcg_ctx);

                    } else if (strcmp(helper_name, "fnstcw") == 0 ||
                               strcmp(helper_name, "fstl_ST0") == 0 ||
                               strcmp(helper_name, "cvttsd2sq") == 0 ||
                               strcmp(helper_name, "cvttsd2si") == 0 ||
                               strcmp(helper_name, "cvttss2si") == 0) {

                        // we do not yet support floating point

                        TCGTemp* t_reg = arg_temp(op->args[0]);
                        clear_temp(temp_idx(t_reg), op, tcg_ctx);

                    } else if (strcmp(helper_name, "fildl_ST0") == 0 ||
                               strcmp(helper_name, "flds_FT0") == 0 ||
                               strcmp(helper_name, "flds_ST0") == 0 ||
                               strcmp(helper_name, "fildll_ST0") == 0) {

                        // we do not yet support floating point

                        // ToDo: should we concretize the reg src?

                    } else if (strcmp(helper_name, "fmul_ST0_FT0") == 0 ||
                               strcmp(helper_name, "fpop") == 0 ||
                               strcmp(helper_name, "fmov_FT0_STN") == 0 ||
                               strcmp(helper_name, "fdiv_ST0_FT0") == 0 ||
                               strcmp(helper_name, "fcomi_ST0_FT0") == 0 ||
                               strcmp(helper_name, "fxchg_ST0_STN") == 0 ||
                               strcmp(helper_name, "fmov_STN_ST0") == 0) {

                        // we do not yet support floating point

                    } else if (strcmp(helper_name, "fcomi_ST0_FT0") == 0 ||
                               strcmp(helper_name, "fucomi_ST0_FT0") == 0) {

                        // we do not yet support floating point

                        // clear cc_src
                        TCGTemp* t_ccsrc = tcg_find_temp_arch_reg(tcg_ctx, "cc_src");
                        clear_temp(temp_idx(t_ccsrc), op, tcg_ctx);

                    } else if (strcmp(helper_name, "atomic_fetch_addl_le") ==
                                   0 ||
                                strcmp(helper_name, "atomic_fetch_addq_le") ==
                                   0 ||
                               strcmp(helper_name, "atomic_add_fetchl_le") ==
                                   0 ||
                                strcmp(helper_name, "atomic_add_fetchq_le") ==
                                   0 ||
                               strcmp(helper_name, "atomic_or_fetchl_le") ==
                                   0 ||
                               strcmp(helper_name, "atomic_fetch_orl_le") ==
                                   0 ||
                               strcmp(helper_name, "atomic_and_fetchl_le") ==
                                   0 ||
                               strcmp(helper_name, "atomic_fetch_and_le") ==
                                   0) {

                        TCGTemp* t_out   = arg_temp(op->args[0]);
                        TCGTemp* t_ptr_a = arg_temp(op->args[2]);
                        TCGTemp* t_val_b = arg_temp(op->args[3]);

                        uint64_t size = 4;

                        OPKIND opkind;
                        // order:
                        //  - 0: return the fetched value before op
                        //  - 1: return the result of the op
                        uint64_t order;
                        if (helper_name[7] == 'o') {
                            opkind = OR;
                            order  = 1;
                        } else if (helper_name[7] == 'a') {
                            if (helper_name[8] == 'd') {
                                opkind = ADD;
                                if (helper_name[16] == 'q') {
                                    size = 8;
                                }
                            } else if (helper_name[8] == 'n') {
                                opkind = AND;
                            } else {
                                tcg_abort();
                            }
                            order  = 1;
                        } else if (helper_name[7] == 'f') {
                            if (helper_name[13] == 'a') {
                                if (helper_name[14] == 'd') {
                                    opkind = ADD;
                                    if (helper_name[16] == 'q') {
                                        size = 8;
                                    }
                                } else if (helper_name[14] == 'n') {
                                    opkind = AND;
                                } else {
                                    tcg_abort();
                                }
                                order  = 0;
                            } else if (helper_name[13] == 'o') {
                                opkind = OR;
                                order  = 0;
                            } else {
                                tcg_abort();
                            }
                        } else {
                            tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_out));
                        v          = PACK_1(v, temp_idx(t_ptr_a));
                        v          = PACK_2(v, temp_idx(t_val_b));

                        uintptr_t size_order_opkind = opkind;
                        size_order_opkind |= order << 8;
                        size_order_opkind |= size << 12;
                        v = PACK_3(v, size_order_opkind);

                        TCGTemp* t_packed_info =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_info, v, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_ptr_a);
                        MARK_TEMP_AS_ALLOCATED(t_val_b);
                        add_void_call_3(atomic_fetch_op, t_packed_info, t_ptr_a,
                                        t_val_b, op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr_a);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_val_b);
                        tcg_temp_free_internal(t_packed_info);

                    } else if (strcmp(helper_name, "atomic_cmpxchgl_le") == 0 ||
                               strcmp(helper_name, "atomic_cmpxchgq_le") == 0) {

                        TCGTemp* t_out   = arg_temp(op->args[0]);
                        TCGTemp* t_ptr_a = arg_temp(op->args[2]);
                        TCGTemp* t_val_b = arg_temp(op->args[3]);
                        TCGTemp* t_val_c = arg_temp(op->args[4]);

                        uint64_t size;
                        if (helper_name[14] == 'l') {
                            size = 4;
                        } else if (helper_name[14] == 'q') {
                            size = 8;
                        } else {
                            tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_out));
                        v          = PACK_1(v, temp_idx(t_ptr_a));
                        v          = PACK_2(v, temp_idx(t_val_b));

                        uint64_t t_c_idx_size = size;
                        t_c_idx_size |= temp_idx(t_val_c) << 4;
                        v = PACK_3(v, t_c_idx_size);

                        TCGTemp* t_packed_info =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_info, v, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_pc, pc, 0, op, NULL, tcg_ctx);

                        TCGTemp* t_addr_to =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_addr_to, pc + 2, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_ptr_a);
                        MARK_TEMP_AS_ALLOCATED(t_val_b);
                        add_void_call_5(cmpxchg_handler, t_packed_info, t_ptr_a,
                                        t_val_b, t_pc, t_addr_to, op, NULL,
                                        tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr_a);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_val_b);

                        tcg_temp_free_internal(t_packed_info);
                        tcg_temp_free_internal(t_pc);
                        tcg_temp_free_internal(t_addr_to);

                    } else if (strcmp(helper_name, "atomic_xchgl_le") == 0 ||
                               strcmp(helper_name, "atomic_xchgq_le") == 0) {

                        TCGTemp* t_out   = arg_temp(op->args[0]);
                        TCGTemp* t_ptr_a = arg_temp(op->args[2]);
                        TCGTemp* t_val_b = arg_temp(op->args[3]);

                        uint64_t size;
                        if (helper_name[11] == 'l') {
                            size = 4;
                        } else if (helper_name[11] == 'q') {
                            size = 8;
                        } else {
                            tcg_abort();
                        }

                        uint64_t v = 0;
                        v          = PACK_0(v, temp_idx(t_out));
                        v          = PACK_1(v, temp_idx(t_ptr_a));
                        v          = PACK_2(v, temp_idx(t_val_b));
                        v          = PACK_3(v, size);

                        TCGTemp* t_packed_info =
                            new_non_conflicting_temp(TCG_TYPE_PTR);
                        tcg_movi(t_packed_info, v, 0, op, NULL, tcg_ctx);

                        MARK_TEMP_AS_ALLOCATED(t_ptr_a);
                        add_void_call_2(xchg_handler, t_packed_info, t_ptr_a,
                                        op, NULL, tcg_ctx);
                        MARK_TEMP_AS_NOT_ALLOCATED(t_ptr_a);

                        tcg_temp_free_internal(t_packed_info);

                    } else {

                        const char* helper_whitelist[] = {
                            "lookup_tb_ptr", "rechecking_single_step",
                            "instrument_call", "instrument_ret"};

                        int helper_is_whitelisted = 0;
                        for (size_t i = 0;
                             i < sizeof(helper_whitelist) / sizeof(char*);
                             i++) {
                            if (strcmp(helper_whitelist[i], helper_name) == 0)
                                helper_is_whitelisted = 1;
                        }

                        if (!helper_is_whitelisted) {
                            printf("Helper %s is not instrumented\n",
                                   helper_name);
                            // tcg_abort();
                        }
                    }
                }
                break;

            case INDEX_op_movcond_i64:
            case INDEX_op_movcond_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out   = arg_temp(op->args[0]);
                    TCGTemp* t_a     = arg_temp(op->args[1]);
                    TCGTemp* t_b     = arg_temp(op->args[2]);
                    TCGTemp* t_true  = arg_temp(op->args[3]);
                    TCGTemp* t_false = arg_temp(op->args[4]);
                    TCGCond  cond    = op->args[5];
#if 1
                    size_t size = op->opc == INDEX_op_movcond_i64 ? 0 : 4;
#if 0
                    // ToDo
#else
                    TCGTemp* t_cond = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_cond, (uintptr_t)cond, 0, op, NULL, tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_a));
                    v          = PACK_1(v, temp_idx(t_b));
                    v          = PACK_2(v, size);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, v, 0, op, NULL, tcg_ctx);

                    TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
#if BRANCH_COVERAGE == QSYM
                    tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);
#elif BRANCH_COVERAGE == AFL
                    tcg_movi(t_pc, (uintptr_t)tb_pc, 0, op, NULL, tcg_ctx);
#elif BRANCH_COVERAGE == FUZZOLIC
                    tcg_movi(t_pc, (uintptr_t)pc + 1, 0, op, NULL, tcg_ctx);
#endif
                    TCGTemp* t_addr_to = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_addr_to, (uintptr_t)pc + 2, 0, op, NULL,
                             tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_6(cmov_helper, t_a, t_b, t_cond,
                                    t_packed_idx, t_pc, t_addr_to, op, NULL,
                                    tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_cond);
                    tcg_temp_free_internal(t_packed_idx);
                    tcg_temp_free_internal(t_pc);
                    tcg_temp_free_internal(t_addr_to);
#endif
#endif
                    qemu_movcond(t_out, t_a, t_b, t_true, t_false, cond, op,
                                 tcg_ctx);
                }
                break;

            case INDEX_op_neg_i64:
            case INDEX_op_not_i64:
            case INDEX_op_bswap32_i64:
            case INDEX_op_bswap64_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);

                    TCGTemp* t_size = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_size,
                             (uintptr_t)op->opc == INDEX_op_bswap32_i64 ? 4 : 0,
                             0, op, NULL, tcg_ctx);
#if 1
                    qemu_unop(get_opkind(op->opc), t_out, t_a, t_size, op,
                              tcg_ctx);
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, (uintptr_t)get_opkind(op->opc), 0, op,
                             NULL, tcg_ctx);
                    TCGTemp* t_out_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_out_idx, (uintptr_t)temp_idx(t_out), 0, op, NULL,
                             tcg_ctx);
                    TCGTemp* t_a_idx = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_a_idx, (uintptr_t)temp_idx(t_a), 0, op, NULL,
                             tcg_ctx);
                    MARK_TEMP_AS_ALLOCATED(t_a);
                    add_void_call_5(qemu_unop_helper, t_opkind, t_out_idx,
                                    t_a_idx, t_a, t_size, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_out_idx);
                    tcg_temp_free_internal(t_a_idx);
#endif
                    tcg_temp_free_internal(t_size);
                }
                break;

            case INDEX_op_deposit_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                if (instrument) {
                    TCGTemp*  t_out = arg_temp(op->args[0]);
                    TCGTemp*  t_a   = arg_temp(op->args[1]);
                    TCGTemp*  t_b   = arg_temp(op->args[2]);
                    uintptr_t pos   = (uintptr_t)op->args[3];
                    uintptr_t len   = (uintptr_t)op->args[4];
                    // printf("Deposit pos=%lu len=%lu\n", pos, len);
#if 0 // Bugged?
                    qemu_deposit(t_out, t_a, t_b, pos, len, op, tcg_ctx);
#else
                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_out));
                    v1          = PACK_1(v1, temp_idx(t_a));
                    v1          = PACK_2(v1, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    uint64_t v2 = 0;
                    v2          = PACK_0(v2, pos);
                    v2          = PACK_1(v2, len);

                    TCGTemp* t_poslen = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_poslen, (uintptr_t)v2, 0, op, NULL, tcg_ctx);

                    // TCGTemp* t_pc = new_non_conflicting_temp(TCG_TYPE_PTR);
                    // tcg_movi(t_pc, (uintptr_t)pc, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_deposit_helper, t_packed_idx, t_a, t_b,
                                    t_poslen, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_packed_idx);
                    tcg_temp_free_internal(t_poslen);
                    //tcg_temp_free_internal(t_pc);
#endif
                }
                break;

            case INDEX_op_extract_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp* t_out = arg_temp(op->args[0]);
                    TCGTemp* t_a   = arg_temp(op->args[1]);
#if 0 // Bugged on bloaty
                    uintptr_t pos = (uintptr_t)op->args[2];
                    uintptr_t len = (uintptr_t)op->args[3];
                    qemu_extract(t_out, t_a, pos, len, op, tcg_ctx);
#else
                    uint64_t v1 = 0;
                    v1          = PACK_0(v1, temp_idx(t_out));
                    v1          = PACK_1(v1, temp_idx(t_a));
                    v1          = PACK_2(v1, op->args[2]);
                    v1          = PACK_3(v1, op->args[3]);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    add_void_call_2(qemu_extract_helper, t_packed_idx, t_a, op,
                                    NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            case INDEX_op_extract2_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                if (instrument) {
                    TCGTemp*  t_out = arg_temp(op->args[0]);
                    TCGTemp*  t_a   = arg_temp(op->args[1]);
                    TCGTemp*  t_b   = arg_temp(op->args[2]);
                    uintptr_t pos   = (uintptr_t)op->args[3];
                    uint64_t  v1    = 0;
                    v1              = PACK_0(v1, temp_idx(t_out));
                    v1              = PACK_1(v1, temp_idx(t_a));
                    v1              = PACK_2(v1, temp_idx(t_b));
                    v1              = PACK_3(v1, pos);

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v1, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_3(qemu_extract2_helper, t_packed_idx, t_a,
                                    t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_packed_idx);
                }
                break;

            case INDEX_op_muls2_i64:
            case INDEX_op_mulu2_i64:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out_low  = arg_temp(op->args[0]);
                    TCGTemp* t_out_high = arg_temp(op->args[1]);
                    TCGTemp* t_a        = arg_temp(op->args[2]);
                    TCGTemp* t_b        = arg_temp(op->args[3]);
#if 0
                    // ToDo
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, get_opkind(op->opc), 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_out_high));
                    v          = PACK_1(v, temp_idx(t_out_low));
                    v          = PACK_2(v, temp_idx(t_a));
                    v          = PACK_3(v, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_low_high_helper, t_opkind,
                                    t_packed_idx, t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            case INDEX_op_muls2_i32:
            case INDEX_op_mulu2_i32:
                mark_temp_as_in_use(arg_temp(op->args[0]));
                mark_temp_as_in_use(arg_temp(op->args[1]));
                mark_temp_as_in_use(arg_temp(op->args[2]));
                mark_temp_as_in_use(arg_temp(op->args[3]));
                if (instrument) {
                    TCGTemp* t_out_low  = arg_temp(op->args[0]);
                    TCGTemp* t_out_high = arg_temp(op->args[1]);
                    TCGTemp* t_a        = arg_temp(op->args[2]);
                    TCGTemp* t_b        = arg_temp(op->args[3]);
#if 0
                    // ToDo
#else
                    TCGTemp* t_opkind = new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_opkind, get_opkind(op->opc), 0, op, NULL,
                             tcg_ctx);

                    uint64_t v = 0;
                    v          = PACK_0(v, temp_idx(t_out_high));
                    v          = PACK_1(v, temp_idx(t_out_low));
                    v          = PACK_2(v, temp_idx(t_a));
                    v          = PACK_3(v, temp_idx(t_b));

                    TCGTemp* t_packed_idx =
                        new_non_conflicting_temp(TCG_TYPE_PTR);
                    tcg_movi(t_packed_idx, (uintptr_t)v, 0, op, NULL, tcg_ctx);

                    MARK_TEMP_AS_ALLOCATED(t_a);
                    MARK_TEMP_AS_ALLOCATED(t_b);
                    add_void_call_4(qemu_binop_half_helper, t_opkind,
                                    t_packed_idx, t_a, t_b, op, NULL, tcg_ctx);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_a);
                    MARK_TEMP_AS_NOT_ALLOCATED(t_b);
                    tcg_temp_free_internal(t_opkind);
                    tcg_temp_free_internal(t_packed_idx);
#endif
                }
                break;

            case INDEX_op_mb:
                // memory barrier
                break;

            default:
                if (instrument) {
                    const TCGOpDef* def = &tcg_op_defs[op->opc];
                    printf("Unhandled TCG instruction: %s\n", def->name);
                    // tcg_abort();
                }
        }

        // mark as free any temp that was dead at this instruction
        unsigned life = op->life;
        life /= DEAD_ARG;
        if (life) {
            for (int i = 0; life; ++i, life >>= 1) {
                if (life & 1) {
                    mark_temp_as_free(arg_temp(op->args[i]));
                    temp_static_state[temp_idx(arg_temp(op->args[i]))]
                        .is_alive = 0;
                }
            }
        }

#if 0
        if (ops_to_skip == 0 && instrument == 0) {
            instrument = 1;
            instrument_memmove_xmm(op, tcg_ctx);
        }
#endif
        prev_op = op;
    }

    return force_flush_cache;
}

#include "models.c"

static uintptr_t model_caller_addr = 0;
int is_symbolic_model(uintptr_t pc, CPUArchState *cpu) {
    if (symbolic_mode == 0 || plt_addrs == NULL) {
        return 0;
    }

    // printf("Lookup PC %lx\n", pc);

    CPUX86State* env = (CPUX86State*) cpu;
    LIB_MODEL model = (LIB_MODEL) g_hash_table_lookup(plt_addrs, (gpointer) pc);
    if (mode == 0 && model > 0) {
        uintptr_t rsp = env->regs[R_ESP];
        model_caller_addr = *((uintptr_t*)rsp);
        // printf("Executing LIB MODEL %d at %lx\n", model, pc);
        if (model == STRCMP) {
            // printf("[0x%lx] strcmp(%s, %s)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (char *)(uintptr_t)env->regs[R_ESI]);
            mode = model_strcmp(env, model_caller_addr, 0);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == STRNCMP) {
            // printf("[0x%lx] strncmp(%s, %s, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (char *)(uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            mode = model_strcmp(env, model_caller_addr, env->regs[R_EDX]);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == STRLEN) {
            // printf("[0x%lx] strlen(%s)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI]);
            mode = model_strlen(env, model_caller_addr, 0);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == STRNLEN) {
            // printf("[0x%lx] strnlen(%s, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (uintptr_t)env->regs[R_ESI]);
            mode = model_strlen(env, model_caller_addr, env->regs[R_ESI]);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == MALLOC) {
            // printf("[0x%lx] malloc(%lu)\n", model_caller_addr, (uintptr_t)env->regs[R_EDI]);
            model_alloc(env, model_caller_addr, R_EDI);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        } else if (model == REALLOC) {
            // printf("[0x%lx] realloc(0x%lx, %lu)\n", model_caller_addr, (uintptr_t)env->regs[R_EDI], (uintptr_t)env->regs[R_ESI]);
            model_alloc(env, model_caller_addr, R_ESI);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        } else if (model == FREE) {
            // printf("[0x%lx] free(0x%lx)\n", model_caller_addr, (uintptr_t)env->regs[R_EDI]);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        }  else if (model == CALLOC) {
            // printf("[0x%lx] calloc(%lu)\n", model_caller_addr, (uintptr_t)env->regs[R_EDI]);
            model_alloc(env, model_caller_addr, R_EDI);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        } else if (model == PRINTF) {
            // printf("[0x%lx] printf(%s, ...)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI]);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        }  else if (model == FPRINTF) {
            // printf("[0x%lx] fprintf(%s, ...)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_ESI]);
            clear_call_args_temps();
            clear_xmm_regs(env);
            mode = 1;
        } else if (model == MEMCHR) {
            // printf("[0x%lx] memchr(%p, %c, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (int)(uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            mode = model_memchr(env, model_caller_addr);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == MEMCMP) {
            // printf("[0x%lx] memcmp(%p, %p, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (char*)(uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            mode = model_memcmp(env, model_caller_addr);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == MEMMOVE || model == MEMCPY) {
            // printf("[0x%lx] %s(%p, %p, %lu)\n", model_caller_addr, model == MEMMOVE ? "memmove" : "memcpy", (char *)(uintptr_t)env->regs[R_EDI], (char*)(uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            // FixMe: memmove may overlap!
            qemu_memmove((uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDI], (uintptr_t)env->regs[R_EDX]);
            mode = 2;
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == MEMSET) {
            // printf("[0x%lx] memset(%p, %lx, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            Expr* value = s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rsi"))];
            qemu_memset(value, (uintptr_t)env->regs[R_EDI], (uintptr_t)env->regs[R_EDX]);
            mode = 2;
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == STRCPY) {
            // printf("[0x%lx] strcpy(%p, %p)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (char*)(uintptr_t)env->regs[R_ESI]);
            uintptr_t len = strlen((char*)(uintptr_t)env->regs[R_ESI]);
            mode = model_strlen(env, model_caller_addr, 0);
            qemu_memmove((uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDI], len + 1);
            clear_call_args_temps();
            clear_xmm_regs(env);
        } else if (model == STRNCPY) {
            // printf("[0x%lx] strncpy(%p, %p, %lu)\n", model_caller_addr, (char *)(uintptr_t)env->regs[R_EDI], (char*)(uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDX]);
            uintptr_t n = (uintptr_t)env->regs[R_EDX];
            mode = model_strlen(env, model_caller_addr, n);
            uintptr_t len = strnlen((char*)(uintptr_t)env->regs[R_ESI], n);
            if (len < n) len += 1;
            qemu_memmove((uintptr_t)env->regs[R_ESI], (uintptr_t)env->regs[R_EDI], len);
            clear_call_args_temps();
            clear_xmm_regs(env);
        }  else if (model == FPUTC) {
            // printf("[0x%lx] fputc(%c, ...)\n", model_caller_addr, (char)(uintptr_t)env->regs[R_EDI]);
            mode = 2;
            clear_call_args_temps();
            clear_xmm_regs(env);
        } 
        // printf("Return address is %lx [%lx]\n", model_caller_addr, rsp);
        if (mode == 2) {
            return 1; // switch code cache
        } else {
            return 0;
        }
    }
    if (mode > 0 && pc == model_caller_addr) {
        // printf("Switch mode back\n");
        model_caller_addr = 0;
        int r = 0;
        if (mode == 2) {
            r = 1; // switch code cache
        }
        mode = 0;
        return r;
    }
    return 0;
}