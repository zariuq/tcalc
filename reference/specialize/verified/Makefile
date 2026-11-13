# The verified specializer's route from rules to C.
#   tcs2lean   a rule file, read by tcs_read, as Lean data
#   $(LEAN)    Lean checks that file: SpecializedAdmission.specialize makes each rule's program and
#              SpecializedAdmission.Printer.printFile writes the programs as C (gen_*.c)
#   drivers    ../diff_spec.c, ../micromath_spec.c and ../sieve_spec.c, unchanged, link the printed C
#
#   make LEAN=CMD         the printed C and the drivers (random theories, Micromath, the sieve)
#   make check LEAN=CMD   the differential, the printer faults, Micromath against its kernel, the sieve
# CMD checks one Lean file, given as its last argument, with the SpecializedAdmission modules built.

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
SPEC = ..
TESTFLAGS = $(CFLAGS) -D_GNU_SOURCE -I$(SPEC) -I$(SPEC)/..
MICROMATH_REF ?= ../../../ref
THEORY_SEEDS ?= 1 2 3
RUN_SEEDS ?= 11 12
STEPS ?= 5000
PRINTER_FAULTS ?= 1 2 3

all: $(addprefix $(BUILD)/diff_spec,$(THEORY_SEEDS)) $(BUILD)/micromath_spec $(BUILD)/sieve_spec

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/tcs2lean: tcs2lean.c $(SPEC)/tcs.c $(SPEC)/tcs.h $(SPEC)/../tcalc_ref.c | $(BUILD)
	$(CC) $(CFLAGS) -I$(SPEC) tcs2lean.c $(SPEC)/tcs.c $(SPEC)/../tcalc_ref.c -o $@

$(BUILD)/rand_theory: $(SPEC)/rand_theory.c | $(BUILD)
	$(CC) $(CFLAGS) $< -o $@

$(BUILD)/rand%.tcs: $(BUILD)/rand_theory
	$(BUILD)/rand_theory $* 200 > $@

$(BUILD)/rules_rand%.lean: $(BUILD)/rand%.tcs $(BUILD)/tcs2lean
	$(BUILD)/tcs2lean $(abspath $<) $@ $(abspath $(BUILD)/gen_rand$*.c)

$(BUILD)/rules_fault%.lean: $(BUILD)/rand1.tcs $(BUILD)/tcs2lean
	$(BUILD)/tcs2lean --fault $* $(abspath $<) $@ $(abspath $(BUILD)/gen_fault$*.c)

$(BUILD)/rules_micromath.lean: $(SPEC)/micromath.tcs $(BUILD)/tcs2lean
	$(BUILD)/tcs2lean $(abspath $<) $@ $(abspath $(BUILD)/gen_micromath.c)

$(BUILD)/rules_sieve.lean: $(SPEC)/sieve.tcs $(BUILD)/tcs2lean
	$(BUILD)/tcs2lean $(abspath $<) $@ $(abspath $(BUILD)/gen_sieve.c)

# Lean specializes and prints; the C appears only when the check succeeds.
$(BUILD)/gen_%.c: $(BUILD)/rules_%.lean
	rm -f $@
	$(LEAN) $(abspath $<) > $(BUILD)/lean_$*.log 2>&1 || (cat $(BUILD)/lean_$*.log; exit 1)
	test -f $@

$(BUILD)/diff_spec%: $(BUILD)/gen_rand%.c $(SPEC)/diff_spec.c $(SPEC)/tcs.c $(SPEC)/tcs.h $(SPEC)/tcs_inside.h
	$(CC) $(TESTFLAGS) $< $(SPEC)/diff_spec.c $(SPEC)/tcs.c -o $@

$(BUILD)/diff_fault%: $(BUILD)/gen_fault%.c $(SPEC)/diff_spec.c $(SPEC)/tcs.c $(SPEC)/tcs.h $(SPEC)/tcs_inside.h
	$(CC) $(TESTFLAGS) -Wno-error $< $(SPEC)/diff_spec.c $(SPEC)/tcs.c -o $@

$(BUILD)/micromath_kernel.o: $(MICROMATH_REF)/kernel.c | $(BUILD)
	$(CC) -std=gnu11 -O2 -w -I$(MICROMATH_REF) -c $< -o $@

$(BUILD)/micromath_spec: $(BUILD)/gen_micromath.c $(SPEC)/micromath_spec.c $(SPEC)/tcs.c $(BUILD)/micromath_kernel.o
	$(CC) $(TESTFLAGS) -I$(MICROMATH_REF) $< $(SPEC)/micromath_spec.c $(SPEC)/tcs.c $(BUILD)/micromath_kernel.o -o $@

$(BUILD)/sieve_spec: $(BUILD)/gen_sieve.c $(SPEC)/sieve_spec.c $(SPEC)/tcs.c
	$(CC) $(TESTFLAGS) $< $(SPEC)/sieve_spec.c $(SPEC)/tcs.c -o $@

diff: $(addprefix $(BUILD)/diff_spec,$(THEORY_SEEDS))
	for t in $(THEORY_SEEDS); do for s in $(RUN_SEEDS); do $(BUILD)/diff_spec$$t $$s $(STEPS) || exit 1; done; done

# Each planted printer fault must make the differential fail.
faults: $(addprefix $(BUILD)/diff_fault,$(PRINTER_FAULTS))
	for f in $(PRINTER_FAULTS); do \
	  if $(BUILD)/diff_fault$$f 3 2000 > /dev/null 2>&1; then echo "printer fault $$f NOT caught"; exit 1; fi; \
	  echo "printer fault $$f caught"; \
	done

micromath: $(BUILD)/micromath_spec
	for s in 11 12 13; do $(BUILD)/micromath_spec $$s 300000 || exit 1; done

sieve: $(BUILD)/sieve_spec
	$(BUILD)/sieve_spec 200 1000 3000

check: diff faults micromath sieve

SANFLAGS = -std=c11 -D_GNU_SOURCE -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined \
  -fno-sanitize-recover=all -fno-omit-frame-pointer -I$(SPEC) -I$(SPEC)/..

$(BUILD)/diff_spec_san: $(BUILD)/gen_rand1.c $(SPEC)/diff_spec.c $(SPEC)/tcs.c
	$(CC) $(SANFLAGS) $< $(SPEC)/diff_spec.c $(SPEC)/tcs.c -o $@

$(BUILD)/micromath_spec_san: $(BUILD)/gen_micromath.c $(SPEC)/micromath_spec.c $(SPEC)/tcs.c $(MICROMATH_REF)/kernel.c
	$(CC) -std=gnu11 -O1 -g -w -fsanitize=address,undefined -I$(MICROMATH_REF) -c $(MICROMATH_REF)/kernel.c \
	  -o $(BUILD)/micromath_kernel_san.o
	$(CC) $(SANFLAGS) -I$(MICROMATH_REF) $< $(SPEC)/micromath_spec.c $(SPEC)/tcs.c $(BUILD)/micromath_kernel_san.o -o $@

sanitize: $(BUILD)/diff_spec_san $(BUILD)/micromath_spec_san
	$(BUILD)/diff_spec_san 5 500
	$(BUILD)/micromath_spec_san 15 30000

clean:
	rm -f $(BUILD)/tcs2lean $(BUILD)/rand_theory $(BUILD)/rand*.tcs $(BUILD)/rules_*.lean $(BUILD)/gen_*.c \
	      $(BUILD)/lean_*.log $(BUILD)/diff_spec* $(BUILD)/diff_fault* $(BUILD)/micromath_spec \
	      $(BUILD)/micromath_kernel.o $(BUILD)/sieve_spec $(BUILD)/diff_spec_san $(BUILD)/micromath_spec_san \
	      $(BUILD)/micromath_kernel_san.o $(BUILD)/check_run*.log

.PHONY: all diff faults micromath sieve check sanitize clean
.SECONDARY:
