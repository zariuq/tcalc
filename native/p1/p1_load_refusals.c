/*
 * p1_load_refusals.c -- the loader refuses text outside the grammar, at the
 * first character that leaves it.
 *
 * Each case is a text, the style it is read in, and the tail of the text
 * that starts at the expected error position ("" for the end; NULL when the
 * text must be accepted). The message must contain the given words.
 */
#include "p1_load.h"

#include <stdio.h>
#include <string.h>

typedef struct {
    TcIsaTextStyle style;
    const char *text, *at, *says;
} Case;

#define H TISA_TEXT_HOL
#define S TISA_TEXT_SEXPR

static const Case cases[] = {
    /* accepted: the smallest programs, and the field extremes that print back */
    {H, "(TProg [] [] (TReturn 1 0))", NULL, NULL},
    {S, "(TProg () () (TReturn 1 0))", NULL, NULL},
    {H, "(TProg [(2,16,8)] [(1,TyPtr,0); (5,TyBool,0)] (TSeq TSkip (TInstr (TImm TyU64 3 (word 18446744073709551615)))))", NULL, NULL},
    {H, "(TProg [] [] (TInstr (TAddr 0 1 2 (SOME 254) 3 (-- &2147483648:int))))", NULL, NULL},
    {H, "(TProg [] [] (TInstr (TLoadFrame TyU64 1 268435455)))", NULL, NULL},
    {S, "(TProg () () (TInstr (TStore 8 0 1 -2147483648 2)))", NULL, NULL},
    /* layout: exactly the printer's spaces and punctuation */
    {H, "(TProg [] []  (TReturn 1 0))", " (TReturn 1 0))", "expected \"(\""},
    {H, "(TProg [] [] (TReturn 1 0)) ", " ", "goes on after the program"},
    {H, "(TProg [] [] (TReturn 1 0)", "", "the end of the text"},
    {H, "(TProg [] [] (TReturn 1  0))", " 0))", "a number"},
    {H, "(TProg [(2,8,8);(2,8,8)] [] TSkip)", "(2,8,8)] [] TSkip)", "expected \" \""},
    {H, "(TProg ((2 8 8)) () TSkip)", "((2 8 8)) () TSkip)", "expected \"[\""},
    {S, "(TProg [] [] TSkip)", "[] [] TSkip)", "expected \"(\""},
    {H, "", "", "expected \"(TProg \""},
    /* names */
    {H, "(TProg [] [] (TRet 1 0))", "TRet 1 0))", "not a statement constructor"},
    {H, "(TProg [] [] (TInstr (TImm TyU65 1 (word 0))))", "TyU65 1 (word 0))))", "not a type"},
    {H, "(TProg [] [] (TInstr (TBin BinNand TyU64 1 2 3)))", "BinNand TyU64 1 2 3)))", "not a binary operation"},
    {H, "(TProg [] [] (TInstr (TJump 1)))", "TJump 1)))", "not an instruction constructor"},
    /* numbers: canonical decimal, within their fields */
    {H, "(TProg [] [] (TReturn 01 0))", "01 0))", "leading zero"},
    {H, "(TProg [] [] (TReturn 5 0))", "5 0))", "out of range"},
    {H, "(TProg [] [] (TInstr (TImm TyU64 1 (word 18446744073709551616))))", "18446744073709551616))))", "out of range"},
    {H, "(TProg [] [] (TInstr (TMov TyU64 256 1)))", "256 1)))", "out of range"},
    {H, "(TProg [] [] (TFund 4294967296))", "4294967296))", "out of range"},
    {H, "(TProg [] [] (TInstr (TStore 8 0 1 (&2147483648:int) 2)))", "2147483648:int) 2)))", "out of range"},
    {H, "(TProg [] [] (TInstr (TStore 8 0 1 (-- &0:int) 2)))", "0:int) 2)))", "negative zero"},
    {S, "(TProg () () (TInstr (TStore 8 0 1 -0 2)))", "0 2)))", "negative zero"},
    {S, "(TProg () () (TInstr (TStore 8 0 1 +3 2)))", "+3 2)))", "a number"},
    /* values the printer would spell otherwise */
    {H, "(TProg [] [] (TInstr (TAddr 0 1 2 (SOME 255) 0 (&0:int))))", "255) 0 (&0:int))))", "NONE"},
    {H, "(TProg [] [] (TInstr (TLoad TyU64 8 255 1 2 (&0:int))))", "255 1 2 (&0:int))))", "TLoadFrame"},
    {H, "(TProg [] [] (TInstr (TLoadFrame TyU64 1 268435456)))", "268435456)))", "frame word index"},
    /* declarations */
    {H, "(TProg [(3,8,8)] [] TSkip)", "3,8,8)] [] TSkip)", "region mode"},
    {H, "(TProg [(1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1); (1,1,1)] [] TSkip)",
        "(1,1,1)] [] TSkip)", "at most 9"},
    {H, "(TProg [] [(2,TyU64,0); (1,TyU64,0)] TSkip)", "1,TyU64,0)] TSkip)", "increasing order"},
    {H, "(TProg [] [(1,TyU64,0); (1,TyU64,0)] TSkip)", "1,TyU64,0)] TSkip)", "increasing order"},
    {H, "(TProg [] [(0,TyU64,0)] TSkip)", "0,TyU64,0)] TSkip)", "increasing order"},
    {H, "(TProg [] [(12,TyU64,0)] TSkip)", "12,TyU64,0)] TSkip)", "out of range"},
    {H, "(TProg [] [(1,TyU64,3)] TSkip)", "3)] TSkip)", "region 0"},
};

int main(void) {
    unsigned n = sizeof cases / sizeof cases[0], bad = 0, refused = 0;
    for (unsigned k = 0; k < n; ++k) {
        const Case *c = &cases[k];
        P1Program prog;
        P1Error err;
        size_t len = strlen(c->text);
        bool ok = p1_parse(c->text, len, c->style, &prog, &err);
        if (!c->at) {
            if (!ok) { printf("case %u: refused, should be accepted: ", k); p1_print_error(stdout, NULL, &err); bad++; }
            else p1_free(&prog);
            continue;
        }
        size_t want = len - strlen(c->at);
        if (ok) { printf("case %u: accepted, should be refused at byte %zu\n", k, want); p1_free(&prog); bad++; continue; }
        refused++;
        if (err.offset != want || !strstr(err.message, c->says)) {
            printf("case %u: refused at byte %zu (\"%s\"), expected byte %zu and \"%s\"\n", k, err.offset,
                   err.message, want, c->says);
            bad++;
        }
    }
    printf("p1_load_refusals: %u cases (%u refused at the expected position), %u failures\n", n, refused, bad);
    return bad ? 1 : 0;
}
