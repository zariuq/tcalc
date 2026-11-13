# tcalc_ref: build, controls, sanitizers, the transform differential and the benchmarks.
# BUILD is where objects and binaries go; CETTA is a CeTTa binary with lib_transform.

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
TESTFLAGS = $(CFLAGS) -D_GNU_SOURCE
SANFLAGS = -std=c11 -D_GNU_SOURCE -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer
CETTA ?= cetta
SEEDS ?= 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29
MICROMATH_REF ?= ../ref

all: $(BUILD)/test_ref $(BUILD)/diff_transform $(BUILD)/bench

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/tcalc_ref.o: tcalc_ref.c tcalc_ref.h | $(BUILD)
	$(CC) $(CFLAGS) -c tcalc_ref.c -o $@

$(BUILD)/%: %.c $(BUILD)/tcalc_ref.o tcalc_ref.h
	$(CC) $(TESTFLAGS) $< $(BUILD)/tcalc_ref.o -o $@

$(BUILD)/test_ref_san: tcalc_ref.c tcalc_ref.h test_ref.c | $(BUILD)
	$(CC) $(SANFLAGS) tcalc_ref.c test_ref.c -o $@

$(BUILD)/diff_transform_san: tcalc_ref.c tcalc_ref.h diff_transform.c | $(BUILD)
	$(CC) $(SANFLAGS) tcalc_ref.c diff_transform.c -o $@

test: $(BUILD)/test_ref
	$(BUILD)/test_ref

sanitize: $(BUILD)/test_ref_san $(BUILD)/diff_transform_san
	$(BUILD)/test_ref_san
	$(BUILD)/diff_transform_san $(CETTA) 7 200 0 $(BUILD)

diff: $(BUILD)/diff_transform
	for s in $(SEEDS); do $(BUILD)/diff_transform $(CETTA) $$s 500 0 $(BUILD) || exit 1; done
	! $(BUILD)/diff_transform $(CETTA) 1 500 1 $(BUILD) > /dev/null 2>&1
	! $(BUILD)/diff_transform $(CETTA) 1 500 2 $(BUILD) > /dev/null 2>&1

bench: $(BUILD)/bench
	for n in 200 1000 3000; do $(BUILD)/bench sieve $$n || exit 1; done
	for n in 10000 1000000; do $(BUILD)/bench store $$n 1000000 known || exit 1; done

# Micromath against its own reference kernel (MICROMATH_REF holds kernel.c and kernel.h).
$(BUILD)/micromath_kernel.o: $(MICROMATH_REF)/kernel.c | $(BUILD)
	$(CC) -std=gnu11 -O2 -w -I$(MICROMATH_REF) -c $< -o $@

$(BUILD)/micromath: micromath.c $(BUILD)/tcalc_ref.o $(BUILD)/micromath_kernel.o tcalc_ref.h
	$(CC) $(TESTFLAGS) -I$(MICROMATH_REF) micromath.c $(BUILD)/tcalc_ref.o $(BUILD)/micromath_kernel.o -o $@

micromath: $(BUILD)/micromath
	for s in 11 12 13 14 15 16 17 18 19 20; do $(BUILD)/micromath $$s 1000000 || exit 1; done
	! $(BUILD)/micromath 1 200000 1 > /dev/null 2>&1
	! $(BUILD)/micromath 1 200000 2 > /dev/null 2>&1

clean:
	rm -f $(BUILD)/tcalc_ref.o $(BUILD)/test_ref $(BUILD)/diff_transform $(BUILD)/bench \
	      $(BUILD)/test_ref_san $(BUILD)/diff_transform_san $(BUILD)/diff_transform_*.metta \
	      $(BUILD)/micromath $(BUILD)/micromath_kernel.o

.PHONY: all test sanitize diff bench micromath clean
