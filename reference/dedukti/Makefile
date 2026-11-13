# Dedukti (lambda-Pi modulo rewriting) checked as firings of tcalc_ref's step, on ../binders.
#   make             dk_ref, mutate_dk
#   make check       the binder layer, then: our controls, the upstream review packet, the old
#                    prototype's dk-controls, Dedukti's tests/OK and tests/KO, the planted faults and
#                    lies (each must be caught), and a sampled mutation sweep.  Every file is judged by
#                    dk_ref, by `dk` (upstream master, with the matching bug) and by the fixed candidate;
#                    a difference not listed in classified.txt fails the check.
#   make mutants     the full mutation sweep (about 4,000 mutants)
#   make sanitize    the controls and the packet under the address and undefined-behaviour sanitizers
#   make bench       times against dk and the old dk_tcalc, generic and with the specializer
#   make spec-check  dk_ref_spec (the fixed rules compiled by ../specialize) runs exactly as dk_ref
# DEDUKTI: a Dedukti source tree at 0b67dab (tests/OK, tests/KO, tests/main.ml); DK: upstream `dk`;
# DK_FIXED: the fixed candidate, built here from DEDUKTI and the packet's production.patch.

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
SANFLAGS = -std=c11 -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer
SPECDIR = ../specialize
SRC = dk_ref.c ../binders/bl.c ../binders/rk.c ../tcalc_ref.c $(SPECDIR)/tcs.c
HDR = ../binders/bl.h ../binders/rk.h ../tcalc_ref.h $(SPECDIR)/tcs.h
DEDUKTI ?= ../../../repos/dedukti
DK ?= $(HOME)/.opam/default/bin/dk
OPAMBIN ?= $(HOME)/.opam/default/bin
PACKET ?= /shared/to-claws/2026-11-11-codex-dedukti-pr-ready
CONTROLS ?= ../../dk-controls
OLD ?= ../../dk_tcalc
DK_FIXED ?= $(abspath $(BUILD))/dedukti-fixed/_build/default/commands/main.exe
STRIDE ?= 7

all: $(BUILD)/dk_ref $(BUILD)/mutate_dk

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/dk_ref: $(SRC) $(HDR) | $(BUILD)
	$(CC) $(CFLAGS) -D_GNU_SOURCE -pthread $(SRC) -o $@

$(BUILD)/dk_ref_san: $(SRC) $(HDR) | $(BUILD)
	$(CC) $(SANFLAGS) -D_GNU_SOURCE -pthread $(SRC) -o $@

$(BUILD)/mutate_dk: mutate_dk.c | $(BUILD)
	$(CC) $(CFLAGS) mutate_dk.c -o $@

# The specializer on the fixed rules: dk_ref writes them as schemas, tcs_gen compiles them, and
# dk_ref_spec decides them with that code (one translation unit includes tcalc_ref.c: the generated
# file, through tcs_inside.h).
$(BUILD)/tcs_gen: $(SPECDIR)/tcs_gen.c $(SPECDIR)/tcs.c $(SPECDIR)/tcs.h ../tcalc_ref.c ../tcalc_ref.h | $(BUILD)
	$(CC) $(CFLAGS) $(SPECDIR)/tcs_gen.c $(SPECDIR)/tcs.c ../tcalc_ref.c -o $@

$(BUILD)/dk_rules.tcs: $(BUILD)/dk_ref
	$(BUILD)/dk_ref --emit-tcs $@

$(BUILD)/gen_dk.c: $(BUILD)/dk_rules.tcs $(BUILD)/tcs_gen
	$(BUILD)/tcs_gen $@ $(BUILD)/dk_rules.tcs

SPECSRC = dk_ref.c ../binders/bl.c ../binders/rk.c $(SPECDIR)/tcs.c
$(BUILD)/dk_ref_spec: $(BUILD)/gen_dk.c $(SPECSRC) $(HDR) $(SPECDIR)/tcs_inside.h
	$(CC) $(CFLAGS) -D_GNU_SOURCE -DDK_SPEC -I$(SPECDIR) -I.. -pthread $(BUILD)/gen_dk.c $(SPECSRC) -o $@

# The specialized checker must run exactly as the generic one: the same verdict, message and counts
# of declarations, rules, firings and facts on every file of the controls, the packet, the theories
# and Dedukti's tests/OK (and it must have decided some firings by the compiled code).
spec-check: $(BUILD)/dk_ref $(BUILD)/dk_ref_spec
	sh spec_check.sh $(BUILD)/dk_ref $(BUILD)/dk_ref_spec controls/*.dk $(PACKET)/cases/*.dk \
	  $(DEDUKTI)/libraries/theories/*.dk $(DEDUKTI)/tests/OK/*.dk

# The fixed candidate: Dedukti 0b67dab with the one-line correction of apply_sol (PR #349).
$(DK_FIXED): | $(BUILD)
	rm -rf $(BUILD)/dedukti-fixed && mkdir -p $(BUILD)/dedukti-fixed
	cd $(DEDUKTI) && tar --exclude=./_build -cf - . | (cd $(abspath $(BUILD))/dedukti-fixed && tar -xf -)
	cd $(BUILD)/dedukti-fixed && patch -p1 < $(PACKET)/production.patch
	cd $(BUILD)/dedukti-fixed && PATH=$(OPAMBIN):$$PATH dune build -j 3 commands/main.exe

R = $(abspath $(BUILD))/dk_ref
WK = $(abspath $(BUILD))/work

# A run passes when every DIFFERENT line is classified (classified.txt names the file and why).
define verify
	@tail -1 $(1); grep '^DIFFERENT' $(1) | while read -r c f rest; do \
	  grep -q -F "$$(basename "$$f")" classified.txt || { echo "UNCLASSIFIED: $$c $$f $$rest"; exit 1; }; done
endef

controls: $(BUILD)/dk_ref $(DK_FIXED)
	sh run_files.sh $(R) $(WK) $(DK) $(DK_FIXED) controls/*.dk > $(BUILD)/controls.out
	$(call verify,$(BUILD)/controls.out)

packet: $(BUILD)/dk_ref $(DK_FIXED)
	sh run_files.sh $(R) $(WK) $(DK) $(DK_FIXED) $(PACKET)/cases/*.dk $(PACKET)/absurd.dk $(PACKET)/direct-rejection.dk \
	  $(PACKET)/ground-control.dk > $(BUILD)/packet.out
	$(call verify,$(BUILD)/packet.out)
	@grep -q -E '^(AGREE|DK-MATCHER) *$(PACKET)/absurd.dk .*dk_ref=1' $(BUILD)/packet.out && echo "the absurdity (Z : Prop -> prf Z) is refused"

dkcontrols: $(BUILD)/dk_ref $(DK_FIXED)
	sh run_files.sh $(R) $(WK) $(DK) $(DK_FIXED) $(CONTROLS)/*.dk $(CONTROLS)/adversarial-2/*.dk \
	  $(CONTROLS)/known-differences/*.dk $(CONTROLS)/known-differences/eta/*.dk $(CONTROLS)/profiles/*.dk \
	  $(CONTROLS)/limits/*.dk > $(BUILD)/dkcontrols.out
	$(call verify,$(BUILD)/dkcontrols.out)

suite: $(BUILD)/dk_ref $(DK_FIXED)
	sh run_suite.sh $(R) $(DEDUKTI) $(WK)/suite $(DK) $(DK_FIXED) > $(BUILD)/suite.out
	$(call verify,$(BUILD)/suite.out)

faults: $(BUILD)/dk_ref controls packet dkcontrols
	sh run_faults.sh $(R) $(WK) $(BUILD)/controls.out $(BUILD)/packet.out $(BUILD)/dkcontrols.out

mutants-sample: $(BUILD)/dk_ref $(BUILD)/mutate_dk suite
	grep '^AGREE' $(BUILD)/suite.out | grep 'registered=ok' | grep '\[\]' | sed 's|^AGREE *\([^ ]*\) .*|$(WK)/suite/\1|' > $(BUILD)/corpus.txt
	ls $(CONTROLS)/p*.dk $(CONTROLS)/adversarial-2/p*.dk $(PACKET)/cases/valid_*.dk $(PACKET)/cases/invalid_*.dk >> $(BUILD)/corpus.txt
	sh run_mutants.sh $(R) $(abspath $(BUILD))/mutate_dk $(WK)/mut $(DK) $(DK_FIXED) $(STRIDE) `cat $(BUILD)/corpus.txt` > $(BUILD)/mutants.out
	@tail -1 $(BUILD)/mutants.out; ! grep -q '^ACCEPT-BAD' $(BUILD)/mutants.out

mutants:
	$(MAKE) --no-print-directory mutants-sample STRIDE=1

check: all
	$(MAKE) --no-print-directory -C ../binders check
	$(MAKE) --no-print-directory controls packet dkcontrols suite faults mutants-sample spec-check

sanitize: $(BUILD)/dk_ref_san
	for f in controls/*.dk $(PACKET)/cases/*.dk; do \
	  flags=`head -n 1 $$f | sed -n 's/^(; expect [0-9]\(.*\);)$$/\1/p'`; \
	  $(BUILD)/dk_ref_san -q $$flags $$f > /dev/null 2>&1; rc=$$?; [ $$rc -le 2 ] || { echo "sanitizer: $$f rc=$$rc"; exit 1; }; \
	done; echo "sanitizers: controls and packet clean"

bench: $(BUILD)/dk_ref $(BUILD)/dk_ref_spec
	sh bench.sh $(R) $(DK) $(OLD) $(DEDUKTI) $(WK) $(abspath $(BUILD))/dk_ref_spec

clean:
	rm -rf $(BUILD)/dk_ref $(BUILD)/dk_ref_san $(BUILD)/mutate_dk $(BUILD)/work $(BUILD)/*.out $(BUILD)/corpus.txt
	rm -f $(BUILD)/tcs_gen $(BUILD)/dk_rules.tcs $(BUILD)/gen_dk.c $(BUILD)/dk_ref_spec

.PHONY: all controls packet dkcontrols suite faults mutants-sample mutants check sanitize bench spec-check clean
