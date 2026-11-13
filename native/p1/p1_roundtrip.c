/*
 * p1_roundtrip.c -- the loader against the printer, on every program in the
 * given files.
 *
 *   p1_roundtrip FILE...
 *
 * A file is a program text, or holds programs inside records: the lines
 * (tisa-case "ID" PROGRAM) of test_tisa and test_tisa_ref, and the HOL
 * records tisa_image "ID" `PROGRAM` ... and tisa_check "ID" `PROGRAM` ....
 * Every "(TProg " starts a program. For each, in its own style:
 *
 *   1. parse, then print: the printed text equals the program's bytes;
 *   2. print in the other style, parse that, print in the first style
 *      again: the same bytes (both spellings name one program);
 *   3. the program is admitted (tisa_admit), counted, not required.
 *
 * Prints one line per file and every failure; exit status 0 iff every
 * program in every file comes back byte for byte.
 */
#include "p1_load.h"
#include "tisa_ref.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    char *text = NULL;
    size_t cap = 0;
    *len = 0;
    for (;;) {
        if (cap - *len < 65536) {
            char *t = realloc(text, cap ? 2 * cap : 65536);
            if (!t) { free(text); fclose(f); return NULL; }
            text = t; cap = cap ? 2 * cap : 65536;
        }
        size_t got = fread(text + *len, 1, cap - *len, f);
        *len += got;
        if (!got) break;
    }
    fclose(f);
    return text;
}

static char *print(const TcIsaProgram *p, TcIsaTextStyle style, size_t *len) {
    char *out = NULL;
    FILE *m = open_memstream(&out, len);
    if (!m) return NULL;
    bool ok = tisa_print_program(m, style, p);
    fclose(m);
    if (!ok) { free(out); return NULL; }
    return out;
}

/* Where two texts first differ. */
static size_t first_difference(const char *a, size_t na, const char *b, size_t nb) {
    size_t k = 0;
    while (k < na && k < nb && a[k] == b[k]) ++k;
    return k;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: p1_roundtrip FILE...\n"); return 2; }
    unsigned long total = 0, total_bad = 0;
    for (int a = 1; a < argc; ++a) {
        size_t len;
        char *text = read_file(argv[a], &len);
        if (!text) { fprintf(stderr, "%s: cannot read\n", argv[a]); total_bad++; continue; }
        unsigned long programs = 0, same = 0, crossed = 0, admitted = 0, bad = 0;
        size_t stmts = 0, deepest = 0, largest = 0;
        size_t at = 0;
        static const char head[] = "(TProg ";
        for (;;) {
            char *hit = memmem(text + at, len - at, head, sizeof head - 1);
            if (!hit) break;
            size_t start = (size_t)(hit - text), end;
            TcIsaTextStyle style;
            P1Program prog;
            P1Error err;
            programs++;
            if (!p1_detect_style(text + start, len - start, &style)) {
                fprintf(stderr, "%s: program at byte %zu: neither style\n", argv[a], start);
                bad++; at = start + 1; continue;
            }
            if (!p1_parse_prefix(text + start, len - start, style, &prog, &end, &err)) {
                fprintf(stderr, "%s: program at byte %zu: ", argv[a], start);
                p1_print_error(stderr, NULL, &err);
                bad++; at = start + 1; continue;
            }
            stmts += prog.nstmts;
            if (prog.nstmts > largest) largest = prog.nstmts;
            if (prog.depth > deepest) deepest = prog.depth;
            size_t n1;
            char *back = print(&prog.prog, style, &n1);
            if (back && n1 == end && !memcmp(back, text + start, end)) same++;
            else {
                size_t k = back ? first_difference(back, n1, text + start, end) : 0;
                fprintf(stderr, "%s: program at byte %zu does not print back: first difference at its byte %zu\n",
                        argv[a], start, k);
                bad++;
            }
            /* The other spelling, and back. */
            TcIsaTextStyle other = style == TISA_TEXT_HOL ? TISA_TEXT_SEXPR : TISA_TEXT_HOL;
            size_t n2, n3;
            char *crossed_text = print(&prog.prog, other, &n2);
            P1Program again;
            if (crossed_text && p1_parse(crossed_text, n2, other, &again, &err)) {
                char *home = print(&again.prog, style, &n3);
                if (home && n3 == end && !memcmp(home, text + start, end)) crossed++;
                else { fprintf(stderr, "%s: program at byte %zu: the other style does not come back\n", argv[a], start); bad++; }
                free(home);
                p1_free(&again);
            } else {
                fprintf(stderr, "%s: program at byte %zu: its other spelling does not parse: ", argv[a], start);
                if (crossed_text) p1_print_error(stderr, NULL, &err); else fputs("not printable\n", stderr);
                bad++;
            }
            free(crossed_text);
            char why[256];
            if (tisa_admit(&prog.prog, NULL, why, sizeof why)) admitted++;
            free(back);
            p1_free(&prog);
            at = start + end;
        }
        printf("%s: %lu programs, %lu print back byte for byte, %lu through the other style, %lu admitted; "
               "%zu statements (largest %zu, deepest nesting %zu); %lu failures\n",
               argv[a], programs, same, crossed, admitted, stmts, largest, deepest, bad);
        total += programs; total_bad += bad;
        free(text);
    }
    printf("p1_roundtrip: %lu programs, %lu failures\n", total, total_bad);
    return total_bad ? 1 : 0;
}
