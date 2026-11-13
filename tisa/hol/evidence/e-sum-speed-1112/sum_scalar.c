#include <stdint.h>
/* GCC's scalar loop: its own unit, no inlining or cloning, length unknown. */
__attribute__((noipa)) uint64_t sum_scalar(const uint32_t *v, uint64_t n) {
    uint64_t s = 0;
    for (uint64_t i = 0; i < n; ++i) s += v[i];
    return s;
}
