#include "../common/leaf_tests.h"

#define ID_LIMIT (UINT64_C(1) << 62)

static size_t encode_id(unsigned char *output, uint64_t value) {
    size_t length = 0;
    do {
        unsigned char digit = (unsigned char)(value & 127);
        value >>= 7;
        output[length++] = (unsigned char)(digit | (value ? 128 : 0));
    } while (value);
    return length;
}

/* Decode then re-encode to check canonicality. */
static int read_id(const unsigned char *input, size_t length, size_t *cursor, uint64_t *value) {
    const size_t start = *cursor;
    uint64_t decoded = 0;
    for (unsigned shift = 0; shift < 63 && *cursor < length; shift += 7) {
        const unsigned char byte = input[(*cursor)++];
        decoded |= (uint64_t)(byte & 127) << shift;
        if (byte >= 128)
            continue;
        unsigned char canonical[10];
        const size_t width = encode_id(canonical, decoded);
        if (decoded >= ID_LIMIT || width != *cursor - start ||
            memcmp(canonical, input + start, width) != 0)
            return 0;
        *value = decoded;
        return 1;
    }
    return 0;
}

static void specimen(const char *label, const unsigned char *input, size_t length,
                     uint64_t cursor, size_t stack_bytes) {
    const uint64_t initial_state[] = {cursor, UINT64_C(0x1122334455667788), UINT64_C(0xc0120010)};
    const size_t slots = stack_bytes / 8;
    uint64_t initial_stack[20], expected_stack[20];
    if (slots > sizeof initial_stack / sizeof *initial_stack)
        abort();
    for (size_t index = 0; index < slots; index++)
        initial_stack[index] = expected_stack[index] = UINT64_C(0xa51688129bc0d700) + index;
    size_t offset = cursor <= length ? (size_t)cursor : length;
    uint64_t count;
    int status = 0;
    uint64_t expected_cursor = cursor, expected_work = initial_state[1], result = 0;
    if (read_id(input, length, &offset, &count) && count <= length - offset) {
        expected_work = count;
        size_t completed = 0;
        for (; completed < count; completed++) {
            uint64_t id;
            if (!read_id(input, length, &offset, &id))
                break;
            if (count <= slots)
                expected_stack[completed] = id;
        }
        if (completed == count) {
            status = count <= slots ? 1 : 2;
            if (status == 1) {
                result = count;
                expected_cursor = offset;
            }
        }
    }

    leaf_case(label, 0);
    fprintf(leaf_out, "region 0 %zu\n", length);
    if (length) {
        fputs("hex 0 0 ", leaf_out);
        for (size_t index = 0; index < length; index++)
            fprintf(leaf_out, "%02x", (unsigned)input[index]);
        fputc('\n', leaf_out);
    }
    leaf_region_words(1, sizeof initial_state, initial_state, 3);
    leaf_region_words(2, stack_bytes, initial_stack, slots);
    leaf_expect(status, 1, result);
    leaf_want(1, 0, expected_cursor);
    leaf_want(1, 1, expected_work);
    leaf_want(1, 2, initial_state[2]);
    for (size_t index = 0; index < slots; index++)
        leaf_want(2, index, expected_stack[index]);
    fputs("run\n", leaf_out);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) {
        fprintf(stderr, "usage: ids_next_tests OUT.p1t [SEED [RANDOM]]\n");
        return 2;
    }
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) {
        perror(argv[1]);
        return 2;
    }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    const unsigned long randomized = argc > 3 ? strtoul(argv[3], NULL, 0) : 2000;

    const unsigned char empty_list[] = {0, 127};
    const unsigned char two_ids[] = {2, 7, 128, 1, 127};
    const unsigned char bad_tail[] = {2, 7, 128, 0};
    const unsigned char truncated[] = {2, 7, 128};
    specimen("empty_input", empty_list, 0, 0, 0);
    specimen("empty_list", empty_list, sizeof empty_list, 0, 0);
    specimen("cursor_past_end", empty_list, sizeof empty_list, UINT64_MAX, 0);
    specimen("two_ids_exact_fit", two_ids, sizeof two_ids, 0, 16);
    specimen("two_ids_short_stack", two_ids, sizeof two_ids, 0, 15);
    specimen("malformed_after_prefix", bad_tail, sizeof bad_tail, 0, 16);
    specimen("malformed_with_no_stack", bad_tail, sizeof bad_tail, 0, 0);
    specimen("truncated_after_prefix", truncated, sizeof truncated, 0, 16);
    specimen("nonminimal_count", bad_tail, sizeof bad_tail, 2, 0);

    const uint64_t boundaries[] = {0, 1, 127, 128, 129, 16383, 16384,
        UINT64_C(1) << 56, ID_LIMIT - 1, ID_LIMIT, ID_LIMIT + 1, UINT64_MAX};
    unsigned char input[256];
    for (size_t index = 0; index < sizeof boundaries / sizeof *boundaries; index++) {
        size_t length = encode_id(input, boundaries[index]);
        specimen("count_boundary", input, length, 0, 16);
        input[0] = 1;
        length = 1 + encode_id(input + 1, boundaries[index]);
        for (size_t cut = 1; cut <= length; cut++)
            specimen("id_boundary", input, cut, 0, 8);
    }

    for (unsigned long trial = 0; trial < randomized; trial++) {
        const size_t prefix = leaf_below(4);
        const size_t count = leaf_below(16);
        for (size_t index = 0; index < prefix; index++)
            input[index] = (unsigned char)leaf_next();
        size_t length = prefix + encode_id(input + prefix, count);
        for (size_t index = 0; index < count; index++)
            length += encode_id(input + length, leaf_next() >> (2 + leaf_below(62)));
        const size_t capacity = 8 * leaf_below(19) + leaf_below(8);
        const unsigned change = leaf_below(5);
        if (change == 1 && count)
            input[prefix + 1 + leaf_below(length - prefix - 1)] ^= (unsigned char)(1 + leaf_below(255));
        if (change == 2)
            length = prefix + leaf_below(length - prefix);
        if (change == 3)
            input[length++] = 127;
        specimen("generated", input, length, prefix, capacity);
    }
    if (fclose(leaf_out) != 0)
        return 2;
    leaf_summary("ids_next_tests");
    return 0;
}
