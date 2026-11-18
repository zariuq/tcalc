#include "../common/leaf_tests.h"

static uint64_t words[4096];

static void trial(uint64_t length, int chain) {
    size_t count = (size_t)(length / 8);
    for (size_t i = 0; i < count; i++) words[i] = leaf_next();
    leaf_case("zw", chain);
    leaf_region_words(0, length, words, count);
    uint64_t budget = leaf_ncases % 4 == 0 ? 0 : leaf_next();
    uint64_t used = leaf_ncases % 2 == 0 ? budget : budget / 2;
    fprintf(leaf_out, "budget %" PRIu64 "\nused %" PRIu64 "\n", budget, used);
    for (unsigned repeat = 0; repeat < 2; repeat++) {
        int fired = length % 8 == 0;
        leaf_expect(fired ? 1 : 2, 1, count);
        if (count <= 60) {
            for (size_t i = 0; i < count; i++) leaf_want(0, i, fired ? 0 : words[i]);
        } else {
            for (size_t i = 0; i < 24; i++) leaf_want(0, i, fired ? 0 : words[i]);
            for (size_t i = count - 24; i < count; i++) leaf_want(0, i, fired ? 0 : words[i]);
            for (size_t k = 0; k < 12; k++) {
                size_t i = (size_t)leaf_below(count);
                leaf_want(0, i, fired ? 0 : words[i]);
            }
        }
        fprintf(leaf_out, "run\n");
    }
}

static void invalid_receipt(void) {
    uint64_t initial = UINT64_C(0xA5C396785A3C6987);
    leaf_case("invalid_receipt", 1);
    leaf_region_words(0, 8, &initial, 1);
    fprintf(leaf_out, "budget 0\nused 1\n");
    for (unsigned repeat = 0; repeat < 2; repeat++) {
        leaf_expect(3, 1, 3);
        leaf_want(0, 0, initial);
        fprintf(leaf_out, "run\n");
    }
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) {
        fprintf(stderr, "usage: zero_words_tests OUT.p1t [SEED [RANDOM]]\n");
        return 2;
    }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long random = argc > 3 ? strtoul(argv[3], NULL, 0) : 256;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) return 2;
    for (uint64_t length = 0; length < 80; length++) trial(length, 1);
    trial(4096, 1);
    trial(32768, 1);
    for (unsigned long i = 0; i < random; i++) trial(leaf_below(2048), 1);
    invalid_receipt();
    fclose(leaf_out);
    leaf_summary("zero_words_tests");
    return leaf_outcomes[1] && leaf_outcomes[2] ? 0 : 1;
}
