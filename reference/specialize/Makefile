# The specializer: tcs_gen writes C from theories (rules as data); the tests run it.
#   make           the generator, the random-theory differential and the Micromath client
#   make check     rules as tr_firing schemas and as text agree (round trip); the random-theory
#                  differential (three theory sets, two run seeds each); every planted fault caught;
#                  the Micromath differential against its kernel; the sieve (bench.c's CHR sieve as
#                  rules) on both routes
#   make sanitize  the same programs under the address and undefined-behaviour sanitizers
#   make bench     the cost of each Micromath route, at three store sizes
# BUILD is where generated files, objects and binaries go.

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
TESTFLAGS = $(CFLAGS) -D_GNU_SOURCE -I. -I..
SANFLAGS = -std=c11 -D_GNU_SOURCE -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer -I. -I..
MICROMATH_REF ?= ../../ref
THEORY_SEEDS ?= 1 2 3
RUN_SEEDS ?= 11 12
STEPS ?= 5000
FAULTS = 1 2 3 4 5 6 7 8 9 10 11 12 13

all: $(BUILD)/tcs_gen $(BUILD)/rand_theory $(BUILD)/diff_spec1 $(BUILD)/micromath_spec

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/tcs_gen: tcs_gen.c tcs.c tcs.h ../tcalc_ref.c ../tcalc_ref.h | $(BUILD)
	$(CC) $(CFLAGS) tcs_gen.c tcs.c ../tcalc_ref.c -o $@

$(BUILD)/rand_theory: rand_theory.c | $(BUILD)
	$(CC) $(CFLAGS) rand_theory.c -o $@

$(BUILD)/rand%.tcs: $(BUILD)/rand_theory
	$(BUILD)/rand_theory $* 200 > $@

$(BUILD)/gen_rand%.c: $(BUILD)/rand%.tcs $(BUILD)/tcs_gen
	$(BUILD)/tcs_gen $@ $<

$(BUILD)/diff_spec%: $(BUILD)/gen_rand%.c diff_spec.c tcs.c tcs.h tcs_inside.h ../tcalc_ref.c
	$(CC) $(TESTFLAGS) $< diff_spec.c tcs.c -o $@

$(BUILD)/gen_micromath.c: micromath.tcs $(BUILD)/tcs_gen
	$(BUILD)/tcs_gen $@ micromath.tcs

$(BUILD)/micromath_kernel.o: $(MICROMATH_REF)/kernel.c | $(BUILD)
	$(CC) -std=gnu11 -O2 -w -I$(MICROMATH_REF) -c $< -o $@

$(BUILD)/micromath_spec: $(BUILD)/gen_micromath.c micromath_spec.c tcs.c tcs.h tcs_inside.h $(BUILD)/micromath_kernel.o
	$(CC) $(TESTFLAGS) -I$(MICROMATH_REF) $< micromath_spec.c tcs.c $(BUILD)/micromath_kernel.o -o $@

diff: $(addprefix $(BUILD)/diff_spec,$(THEORY_SEEDS))
	for t in $(THEORY_SEEDS); do for s in $(RUN_SEEDS); do $(BUILD)/diff_spec$$t $$s $(STEPS) || exit 1; done; done

# Each planted fault must make the differential fail.
faults: $(BUILD)/tcs_gen $(BUILD)/rand1.tcs
	for f in $(FAULTS); do \
	  $(BUILD)/tcs_gen --fault $$f $(BUILD)/gen_fault.c $(BUILD)/rand1.tcs 2> /dev/null || exit 1; \
	  $(CC) $(TESTFLAGS) $(BUILD)/gen_fault.c diff_spec.c tcs.c -o $(BUILD)/diff_fault || exit 1; \
	  if $(BUILD)/diff_fault 3 2000 > /dev/null 2>&1; then echo "planted fault $$f NOT caught"; exit 1; fi; \
	  echo "planted fault $$f caught"; \
	done

micromath: $(BUILD)/micromath_spec
	for s in 11 12 13; do $(BUILD)/micromath_spec $$s 300000 || exit 1; done
	$(BUILD)/micromath_spec 14 300000 1000

$(BUILD)/gen_sieve.c: sieve.tcs $(BUILD)/tcs_gen
	$(BUILD)/tcs_gen $@ sieve.tcs

$(BUILD)/sieve_spec: $(BUILD)/gen_sieve.c sieve_spec.c tcs.c tcs.h tcs_inside.h ../tcalc_ref.c
	$(CC) $(TESTFLAGS) $< sieve_spec.c tcs.c -o $@

sieve: $(BUILD)/sieve_spec
	$(BUILD)/sieve_spec 200 1000 3000

$(BUILD)/tcs_roundtrip: tcs_roundtrip.c tcs.c tcs.h ../tcalc_ref.c ../tcalc_ref.h | $(BUILD)
	$(CC) $(TESTFLAGS) tcs_roundtrip.c tcs.c ../tcalc_ref.c -o $@

roundtrip: $(BUILD)/tcs_roundtrip $(addprefix $(BUILD)/rand,$(addsuffix .tcs,$(THEORY_SEEDS)))
	$(BUILD)/tcs_roundtrip $(addprefix $(BUILD)/rand,$(addsuffix .tcs,$(THEORY_SEEDS))) micromath.tcs sieve.tcs

check: roundtrip diff faults micromath sieve

$(BUILD)/diff_spec_san: $(BUILD)/gen_rand1.c diff_spec.c tcs.c tcs.h tcs_inside.h ../tcalc_ref.c
	$(CC) $(SANFLAGS) $< diff_spec.c tcs.c -o $@

$(BUILD)/micromath_spec_san: $(BUILD)/gen_micromath.c micromath_spec.c tcs.c tcs.h tcs_inside.h $(MICROMATH_REF)/kernel.c
	$(CC) -std=gnu11 -O1 -g -w -fsanitize=address,undefined -I$(MICROMATH_REF) -c $(MICROMATH_REF)/kernel.c -o $(BUILD)/micromath_kernel_san.o
	$(CC) $(SANFLAGS) -I$(MICROMATH_REF) $< micromath_spec.c tcs.c $(BUILD)/micromath_kernel_san.o -o $@

sanitize: $(BUILD)/diff_spec_san $(BUILD)/micromath_spec_san
	$(BUILD)/diff_spec_san 5 500
	$(BUILD)/micromath_spec_san 15 30000

bench: $(BUILD)/micromath_spec $(BUILD)/sieve_spec
	$(BUILD)/micromath_spec --time 7 1000000 1000 10000 100000
	$(BUILD)/sieve_spec 200 1000 3000

clean:
	rm -f $(BUILD)/tcs_gen $(BUILD)/rand_theory $(BUILD)/rand*.tcs $(BUILD)/gen_*.c $(BUILD)/diff_spec* \
	      $(BUILD)/diff_fault $(BUILD)/micromath_spec* $(BUILD)/micromath_kernel*.o $(BUILD)/sieve_spec* \
	      $(BUILD)/tcs_roundtrip

.PHONY: all diff faults micromath sieve roundtrip check sanitize bench clean
.SECONDARY:
