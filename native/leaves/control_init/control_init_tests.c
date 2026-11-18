/* Dirty control arrays, valid policies, refusals and unchanged extra words. */
#include "../common/leaf_tests.h"

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: control_init_tests TESTS\n"); return 2; }
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    const size_t sizes[] = {24,25,32,40,63,64};
    const uint64_t policies[] = {0,1,2,3,4,255,UINT64_MAX,UINT64_C(0x8000000000000000)};
    for (size_t n = 0; n < sizeof sizes / sizeof *sizes; ++n)
        for (size_t p = 0; p < sizeof policies / sizeof *policies; ++p)
            for (unsigned receipt = 0; receipt < 4; ++receipt)
                for (unsigned sample = 0; sample < 32; ++sample) {
                    uint64_t words[64];
                    for (size_t i = 0; i < sizes[n]; ++i) words[i] = leaf_next();
                    leaf_case("controls", 0);
                    leaf_region_words(0,8 * sizes[n],words,sizes[n]);
                    fprintf(leaf_out,"budget %" PRIu64 "\nused %" PRIu64 "\n",
                        (receipt & 1) ? UINT64_MAX : UINT64_C(0),
                        (receipt & 2) ? UINT64_MAX : UINT64_C(0));
                    uint64_t policy = policies[p];
                    int invalid_entry = receipt == 2;
                    int fires = !invalid_entry && policy <= 2;
                    leaf_expect(invalid_entry ? 3 : fires ? 1 : 0,1,
                        invalid_entry ? 3 : fires ? policy : 0);
                    for (size_t i = 0; i < sizes[n]; ++i) {
                        uint64_t expected = words[i];
                        if (fires && i < 24)
                            expected = i <= 6 ? i : i == 7 ? policy :
                                i == 22 ? UINT64_C(14695981039346656037) : 0;
                        leaf_want(0,i,expected);
                    }
                    fprintf(leaf_out,"run arg0=%" PRIu64 "\n",policy);
                }
    if (fclose(leaf_out) != 0) return 2;
    leaf_summary("control_init");
    printf("control_init: invalid-entry controls %lu\n",leaf_outcomes[3]);
    return 0;
}
