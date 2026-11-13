/* Runs one PeTTa source file through the PeTTa evaluator on tcalc and prints, for every
 * `!` directive, each answer on its own line (the layout of the reference PeTTa runtime).
 *
 * usage: petta_file_driver FILE.metta [MAX_STEPS]
 * exit:  0 run finished; 1 the evaluator reported a fault; 2 step budget exhausted;
 *        3 the file could not be read
 *
 * The loop below is the loop of petta_load_and_run_program, with printing added.
 */
#include "petta_tcalc_eval.h"

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s FILE.metta [MAX_STEPS]\n", argv[0]); return 3; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { fprintf(stderr, "cannot read %s\n", argv[1]); return 3; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *text = (char *)malloc((size_t)n + 1);
    if (!text || fread(text, 1, (size_t)n, f) != (size_t)n) { fprintf(stderr, "cannot read %s\n", argv[1]); return 3; }
    text[n] = 0;
    fclose(f);

    uint64_t max_steps = argc > 2 ? strtoull(argv[2], NULL, 10) : 2000000;
    PettaTcalcEngine *eng = (PettaTcalcEngine *)calloc(1, sizeof(PettaTcalcEngine));
    petta_tcalc_engine_init(eng, max_steps);
    /* Imports resolve against the directory of the file being run, as in PeTTa. */
    char *full = realpath(argv[1], NULL);
    char *slash = full ? strrchr(full, '/') : NULL;
    if (slash) {
        *slash = '\0';
        snprintf(eng->cur_dir, sizeof eng->cur_dir, "%s", full[0] ? full : "/");
    }
    free(full);

    size_t cap = 1u << 20;
    char *buf = (char *)malloc(cap);
    const char *p = text;
    int rc = 0;
    while (true) {
        p = petta_skip_ws(p);
        if (!*p) break;
        bool is_bang = false;
        if (*p == '!') { is_bang = true; p++; }
        const char *before = p;
        PettaAtom *stmt = petta_parse_expr(&p);
        if (!stmt) {
            if (*petta_skip_ws(before)) { printf("<<unparsed input at byte %ld>>\n", (long)(before - text)); rc = 1; }
            break;
        }
        PettaValList vl;
        petta_vallist_init(&vl);
        if (!is_bang &&
            !(stmt->kind == PETTA_ATOM_EXPR && stmt->arity >= 1 &&
              stmt->args[0]->kind == PETTA_ATOM_SYM &&
              (strcmp(stmt->args[0]->text, "=") == 0 || strcmp(stmt->args[0]->text, ":") == 0))) {
            petta_store_add_atom_space(eng, "&self", stmt);
        } else {
            petta_eval_expr(eng, stmt, &vl);
        }
        petta_atom_free(stmt);
        if (is_bang) {
            for (uint32_t i = 0; i < vl.count; i++) {
                const PettaAtom *r = vl.items[i];
                /* `test` belongs to the PeTTa library, which this evaluator does not load: an
                 * answer (test GOT WANT) is reported as the library would judge it. */
                if (r->kind == PETTA_ATOM_EXPR && r->arity == 3 && r->args[0]->kind == PETTA_ATOM_SYM &&
                    strcmp(r->args[0]->text, "test") == 0) {
                    bool same = petta_atom_alpha_eq(r->args[1], r->args[2]);
                    buf[0] = 0;
                    petta_atom_render(r, buf, cap);
                    printf("%s %s\n", same ? "TEST-PASS" : "TEST-FAIL", buf);
                    continue;
                }
                buf[0] = 0;
                petta_atom_render(r, buf, cap);
                printf("%s\n", buf);
            }
        }
        petta_vallist_free(&vl);
        if (eng->status == PETTA_STATUS_FAULT) { printf("<<fault %d>>\n", (int)eng->fault); rc = 1; break; }
        if (eng->status == PETTA_STATUS_BUDGET_EXHAUSTED) { printf("<<step budget exhausted>>\n"); rc = 2; break; }
    }
    fflush(stdout);
    return rc;
}
