/*
 * p1_text.c -- every program in the given files, one per line, in one style.
 *
 *   p1_text --hol|--sexpr FILE...
 *
 * Programs are found as p1_roundtrip finds them (every "(TProg "), read in
 * their own style and printed by tisa_print_program in the style asked for.
 * Exit status 0 iff every program was read.
 */
#include "p1_load.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 3 || (strcmp(argv[1], "--hol") && strcmp(argv[1], "--sexpr"))) {
        fprintf(stderr, "usage: p1_text --hol|--sexpr FILE...\n");
        return 2;
    }
    TcIsaTextStyle want = !strcmp(argv[1], "--hol") ? TISA_TEXT_HOL : TISA_TEXT_SEXPR;
    int status = 0;
    for (int a = 2; a < argc; ++a) {
        FILE *f = fopen(argv[a], "rb");
        if (!f) { fprintf(stderr, "%s: cannot read\n", argv[a]); status = 1; continue; }
        char *text = NULL;
        size_t len = 0, cap = 0, got;
        do {
            if (cap - len < 65536) {
                cap = cap ? 2 * cap : 65536;
                if (!(text = realloc(text, cap))) { fprintf(stderr, "out of memory\n"); return 2; }
            }
            got = fread(text + len, 1, cap - len, f);
            len += got;
        } while (got);
        fclose(f);
        static const char head[] = "(TProg ";
        for (size_t at = 0;;) {
            char *hit = memmem(text + at, len - at, head, sizeof head - 1);
            if (!hit) break;
            size_t start = (size_t)(hit - text), end;
            TcIsaTextStyle style;
            P1Program prog;
            P1Error err;
            if (!p1_detect_style(text + start, len - start, &style) ||
                !p1_parse_prefix(text + start, len - start, style, &prog, &end, &err)) {
                fprintf(stderr, "%s: program at byte %zu does not read\n", argv[a], start);
                status = 1;
                at = start + 1;
                continue;
            }
            if (!tisa_print_program(stdout, want, &prog.prog)) status = 1;
            putchar('\n');
            p1_free(&prog);
            at = start + end;
        }
        free(text);
    }
    return status;
}
