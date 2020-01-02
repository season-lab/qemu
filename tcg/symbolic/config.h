#ifndef SYMBOLIC_CONFIG_H
#define SYMBOLIC_CONFIG_H

typedef enum { NO_INPUT, READ_FD_0, REG, BUFFER } SYMBOLIC_INJECT_INPUT_MODE;

typedef struct SymbolicConfig {
    uintptr_t                  symbolic_exec_start_addr;
    uintptr_t                  symbolic_exec_stop_addr;
    SYMBOLIC_INJECT_INPUT_MODE symbolic_inject_input_mode;
    const char*                symbolic_exec_reg_name;
    uintptr_t                  symbolic_exec_reg_instr_addr;
    uintptr_t                  symbolic_exec_buffer_addr;
    uintptr_t                  symbolic_exec_buffer_instr_addr;
} SymbolicConfig;

#endif // SYMBOLIC_CONFIG_H