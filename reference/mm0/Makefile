# Metamath Zero proof files checked as firings of tcalc_ref's step.
#   make            mm0_ref
#   make check      the MM0 corpus of tcalc's run.sh (17 positives, 79 negatives), its R118 specification
#                   controls, six faults planted in peano.mm0 (each refused), and three lies told by the
#                   reader (each refused by the step)
#   make mutants    single-edit mutants of peano.mmu prefixes against the tree's mm0_tcalc
#   make sanitize   the corpus under the address and undefined-behaviour sanitizers
#   make bench      peano.mmu at three sizes, and peano_hex.mmu
# TCALC is the tcalc directory (mm0-controls/); MM0_ROOT a checkout of the MM0 repository.

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
SANFLAGS = -std=c11 -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer
TCALC ?= ../..
MM0_ROOT ?= $(TCALC)/../repos/mm0
PEANO = $(MM0_ROOT)/examples/peano

all: $(BUILD)/mm0_ref

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/mm0_ref: mm0_ref.c mm0_spec.c ../tcalc_ref.c ../tcalc_ref.h | $(BUILD)
	$(CC) $(CFLAGS) -D_GNU_SOURCE -pthread mm0_ref.c ../tcalc_ref.c -o $@

$(BUILD)/mm0_ref_san: mm0_ref.c mm0_spec.c ../tcalc_ref.c ../tcalc_ref.h | $(BUILD)
	$(CC) $(SANFLAGS) -D_GNU_SOURCE -pthread mm0_ref.c ../tcalc_ref.c -o $@

corpus: $(BUILD)/mm0_ref
	sh run_corpus.sh $(BUILD)/mm0_ref $(TCALC) $(MM0_ROOT)

# Faults planted in peano.mm0: each must be refused against peano.mmu.
specfaults: $(BUILD)/mm0_ref
	mkdir -p $(BUILD)/specfaults
	sed '33s/(ifp p a b <-> a)/(ifp p a b <-> b)/' $(PEANO).mm0 > $(BUILD)/specfaults/concl.mm0
	sed '3s/strict provable sort wff;/provable sort wff;/' $(PEANO).mm0 > $(BUILD)/specfaults/mods.mm0
	sed '250s/(p: wff) (a b: nat)/(p: wff) (b a: nat)/' $(PEANO).mm0 > $(BUILD)/specfaults/binders.mm0
	sed '34d' $(PEANO).mm0 > $(BUILD)/specfaults/missing.mm0
	cp $(PEANO).mm0 $(BUILD)/specfaults/extra.mm0 && echo 'theorem extra_unproved (p: wff): $$ p -> p $$;' >> $(BUILD)/specfaults/extra.mm0
	sed '636s/x, y e. R/y, x e. R/' $(PEANO).mm0 > $(BUILD)/specfaults/defbody.mm0
	for f in concl mods binders missing extra defbody; do \
	  if cmp -s $(BUILD)/specfaults/$$f.mm0 $(PEANO).mm0; then echo "fault $$f not planted"; exit 1; fi; \
	  if $(BUILD)/mm0_ref $(PEANO).mmu $(BUILD)/specfaults/$$f.mm0 > $(BUILD)/specfaults/$$f.out 2>&1; then \
	    echo "spec fault $$f NOT refused"; exit 1; fi; \
	  echo "spec fault $$f refused: `cat $(BUILD)/specfaults/$$f.out`"; \
	done

# The reader lies; the step must refuse each lie, and every targeted negative stays refused.
lies: $(BUILD)/mm0_ref
	! MM0_REF_LIE=1 $(BUILD)/mm0_ref $(PEANO).mmu $(PEANO).mm0 > /dev/null 2>&1
	! MM0_REF_LIE=2 $(BUILD)/mm0_ref $(PEANO).mmu $(PEANO).mm0 > /dev/null 2>&1
	for lie in 1 2 3; do for f in bad-dv dv-ax5 neg-theorem_bound_argument x-dv-regular-first bad-hyp peano-bad-a1i \
	    x-hyp-head neg-axiom-sort neg-concl-sort neg-hyp-sort; do \
	  out=`MM0_REF_LIE=$$lie $(BUILD)/mm0_ref $(TCALC)/mm0-controls/$$f.mmu --proof-only 2>&1`; \
	  case "$$out" in *"FAIL (step)"*) ;; *) echo "lie $$lie on $$f: $$out"; exit 1 ;; esac; \
	done; done
	@echo "reader lies: every one refused by a firing of the step"

r118: $(BUILD)/mm0_ref
	sh run_r118.sh $(BUILD)/mm0_ref $(TCALC)

# Single-edit mutants of two prefixes of peano.mmu, judged by mm0_ref and by the tree's mm0_tcalc
# (an independent checker): a disagreement is printed with its edit, for a reader to judge.
$(BUILD)/mutate_mmu: mutate_mmu.c | $(BUILD)
	$(CC) $(CFLAGS) mutate_mmu.c -o $@

MUTANTS ?= 3000
mutants: $(BUILD)/mm0_ref $(BUILD)/mutate_mmu
	$(BUILD)/mutate_mmu --prefix 400 < $(PEANO).mmu > $(BUILD)/base400.mmu
	$(BUILD)/mutate_mmu --prefix 1500 < $(PEANO).mmu > $(BUILD)/base1500.mmu
	sh diff_mutants.sh $(BUILD)/mm0_ref $(TCALC)/mm0_tcalc $(BUILD)/base400.mmu 1 $(MUTANTS) $(BUILD)/mutants
	sh diff_mutants.sh $(BUILD)/mm0_ref $(TCALC)/mm0_tcalc $(BUILD)/base1500.mmu 100001 $(MUTANTS) $(BUILD)/mutants

check: corpus r118 specfaults lies

sanitize: $(BUILD)/mm0_ref_san
	sh run_corpus.sh $(BUILD)/mm0_ref_san $(TCALC) $(MM0_ROOT)

bench: $(BUILD)/mm0_ref
	for n in 700 1400 2800; do $(BUILD)/mm0_ref --first $$n $(PEANO).mmu --proof-only; done
	$(BUILD)/mm0_ref $(PEANO).mmu $(PEANO).mm0
	$(BUILD)/mm0_ref $(MM0_ROOT)/examples/peano_hex.mmu --proof-only

clean:
	rm -rf $(BUILD)/mm0_ref $(BUILD)/mm0_ref_san $(BUILD)/specfaults $(BUILD)/*.log $(BUILD)/peano.out \
	       $(BUILD)/mutate_mmu $(BUILD)/mutants $(BUILD)/base*.mmu

.PHONY: all corpus r118 mutants specfaults lies check sanitize bench clean
