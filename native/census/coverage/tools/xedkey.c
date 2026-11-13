/* xedkey: decode one x86-64 buffer per input line with libxed, in the
 * decoder state that `xed -64 -cet` uses (all chips; P4, LZCNT, TZCNT and
 * CET on), and print
 *   LEN ICLASS IFORM CATEGORY EXTENSION ISA_SET EOSZ VEXVALID VL REXW
 * or "ERROR NAME". A line is hex digits, optionally spaced. Read-only:
 * stdin to stdout. Used to build the s2n coverage corpus, where each
 * candidate carries trailing filler and its length is XED's. */
#include "xed/xed-interface.h"
#include <stdio.h>
#include <string.h>
#include <ctype.h>

static int hexval(int c)
{
    if (c >= '0' && c <= '9') return c - '0';
    c = tolower(c);
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

int main(void)
{
    char line[1024];
    xed_state_t st;
    xed_tables_init();
    xed_state_zero(&st);
    xed_state_init2(&st, XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b);
    while (fgets(line, sizeof line, stdin)) {
        xed_uint8_t buf[64];
        unsigned int n = 0;
        int hi = -1;
        for (char *p = line; *p && n < sizeof buf; p++) {
            int v = hexval((unsigned char)*p);
            if (v < 0) continue;
            if (hi < 0) hi = v; else { buf[n++] = (xed_uint8_t)(hi * 16 + v); hi = -1; }
        }
        xed_decoded_inst_t x;
        xed_decoded_inst_zero_set_mode(&x, &st);
        xed_decoded_inst_set_input_chip(&x, XED_CHIP_INVALID);
        xed3_operand_set_p4(&x, 1);
        xed3_operand_set_lzcnt(&x, 1);
        xed3_operand_set_tzcnt(&x, 1);
        xed3_operand_set_cet(&x, 1);
        xed_error_enum_t e = xed_decode(&x, buf, n > 15 ? 15 : n);
        if (e != XED_ERROR_NONE) {
            printf("ERROR %s\n", xed_error_enum_t2str(e));
            continue;
        }
        printf("%u %s %s %s %s %s %u %u %u %u\n",
               xed_decoded_inst_get_length(&x),
               xed_iclass_enum_t2str(xed_decoded_inst_get_iclass(&x)),
               xed_iform_enum_t2str(xed_decoded_inst_get_iform_enum(&x)),
               xed_category_enum_t2str(xed_decoded_inst_get_category(&x)),
               xed_extension_enum_t2str(xed_decoded_inst_get_extension(&x)),
               xed_isa_set_enum_t2str(xed_decoded_inst_get_isa_set(&x)),
               (unsigned)xed3_operand_get_eosz(&x),
               (unsigned)xed3_operand_get_vexvalid(&x),
               (unsigned)xed3_operand_get_vl(&x),
               (unsigned)xed3_operand_get_rexw(&x));
    }
    return 0;
}
