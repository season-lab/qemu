static inline void clear_call_args_temps(void)
{
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "rax"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "rdi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "rsi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "rdx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "rcx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "r8"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(internal_tcg_context, "r9"))] = 0;
}

static inline Expr* build_expr(Expr** exprs, void* addr, size_t size)
{
    Expr* dst_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        size_t idx = i; // size - i - 1;
        if (i == 0) {
            dst_expr = exprs ? exprs[idx] : NULL;
            if (dst_expr == NULL) {
                dst_expr           = new_expr();
                dst_expr->opkind   = IS_CONST;
                uint8_t* byte_addr = ((uint8_t*)addr) + idx;
                uint8_t  byte      = *byte_addr;
                dst_expr->op1      = (Expr*)((uintptr_t)byte);
            }
        } else {
            Expr* n_expr   = new_expr();
            n_expr->opkind = CONCAT8L;
            if (exprs == NULL || exprs[idx] == NULL) {
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

static inline int model_strcmp(CPUX86State* env, uintptr_t pc, uintptr_t n)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];
    char* s2 = (char *)(uintptr_t)env->regs[R_ESI];

    if (s1 == NULL || s2 == NULL) {
        return mode;
    }

    size_t s1_len = n == 0 ? strlen(s1) : strnlen(s1, n);
    size_t s2_len = n == 0 ? strlen(s2) : strnlen(s2, n);
    int res = n == 0 ? strcmp(s1, s2) : strncmp(s1, s2, n);
    size_t len = s1_len > s2_len ? s1_len : s2_len;

    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, len, 0, NULL);
    Expr** s2_exprs = get_expr_addr((uintptr_t)s2, len, 0, NULL);

    if (s1_exprs == NULL && s2_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    int s2_is_not_null = 0;
    if (s2_exprs) {
        for (size_t i = 0; i < len && s2_is_not_null == 0; i++) {
            s2_is_not_null |= s2_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null && !s2_is_not_null) {
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, len);
    Expr* s2_expr = build_expr(s2_exprs, s2, len);

    uint64_t v = 0;
    v          = PACK_0(v, res);
    v          = PACK_1(v, s1_len);
    v          = PACK_2(v, s2_len);
    v          = PACK_3(v, n);

    Expr* e = new_expr();
    e->opkind = MODEL_STRCMP;
    e->op1 = s1_expr;
    e->op2 = s2_expr;
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, v);

    next_query[0].query   = e;
    next_query[0].address = pc;
    next_query++;

    return mode;
}

static inline int model_strlen(CPUX86State* env, uintptr_t pc, uintptr_t n)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];

    if (s1 == NULL) {
        return mode;
    }

    size_t s1_len = n == 0 ? strlen(s1) : strnlen(s1, n);
    size_t len = n == 0 || s1_len < n ? s1_len + 1 : s1_len;
    // printf("LEN: %lu\n", len);
    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, len, 0, NULL);

    if (s1_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null) {
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, len);

    uint64_t v = 0;
    v          = PACK_0(v, s1_len);
    v          = PACK_1(v, n);

    Expr* e = new_expr();
    e->opkind = MODEL_STRLEN;
    e->op1 = s1_expr;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, v);

    next_query[0].query   = e;
    next_query[0].address = pc;
    next_query++;

    return mode;
}

static inline int model_memchr(CPUX86State* env, uintptr_t pc)
{
    int mode = 2;

    uintptr_t p = (uintptr_t)env->regs[R_EDI];
    if (p == 0) {
        return mode;
    }

    size_t len = (uintptr_t)env->regs[R_EDX];
    if (len == 0) {
        return mode;
    }

    char c = (char)(uintptr_t)env->regs[R_ESI];

    Expr** exprs = get_expr_addr(p, len, 0, NULL);
    if (exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null) {
        return mode;
    }

    Expr* expr = build_expr(exprs, (void*)p, len);

    void* res = memchr((void*)p, c, len);
    uint16_t offset = res == NULL ? 0 : (((uintptr_t)res) - p) + 1;

    uint64_t v = 0;
    v          = PACK_0(v, offset);
    v          = PACK_1(v, len);
    v          = PACK_2(v, c);

    Expr* e = new_expr();
    e->opkind = MODEL_MEMCHR;
    e->op1 = expr;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, v);

    next_query[0].query   = e;
    next_query[0].address = pc;
    next_query++;

    return mode;
}

static inline int model_memcmp(CPUX86State* env, uintptr_t pc)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];
    char* s2 = (char *)(uintptr_t)env->regs[R_ESI];

    if (s1 == NULL || s2 == NULL) {
        return mode;
    }

    size_t n = (uintptr_t)env->regs[R_EDX];
    if (n == 0) {
        return mode;
    }

    int res = memcmp(s1, s2, n);

    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, n, 0, NULL);
    Expr** s2_exprs = get_expr_addr((uintptr_t)s2, n, 0, NULL);

    if (s1_exprs == NULL && s2_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < n && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    int s2_is_not_null = 0;
    if (s2_exprs) {
        for (size_t i = 0; i < n && s2_is_not_null == 0; i++) {
            s2_is_not_null |= s2_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null && !s2_is_not_null) {
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, n);
    Expr* s2_expr = build_expr(s2_exprs, s2, n);

    uint64_t v = 0;
    v          = PACK_0(v, res);
    v          = PACK_1(v, n);

    Expr* e = new_expr();
    e->opkind = MODEL_MEMCMP;
    e->op1 = s1_expr;
    e->op2 = s2_expr;
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, v);

    next_query[0].query   = e;
    next_query[0].address = pc;
    next_query++;

    return mode;
}