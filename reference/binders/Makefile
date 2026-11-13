# The binder layer on tcalc_ref: de Bruijn terms as first-order data, substitution as rules.
#   make            test_bl
#   make check      the controls and the model differential, then every planted fault caught
#   make sanitize   the same under the address and undefined-behaviour sanitizers

BUILD ?= build
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -O2
SANFLAGS = -std=c11 -Wall -Wextra -Werror -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer
SRC = bl.c rk.c ../tcalc_ref.c
HDR = bl.h rk.h ../tcalc_ref.h
CASES ?= 20000

all: $(BUILD)/test_bl

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/test_bl: test_bl.c $(SRC) $(HDR) | $(BUILD)
	$(CC) $(CFLAGS) test_bl.c $(SRC) -o $@

$(BUILD)/test_bl_san: test_bl.c $(SRC) $(HDR) | $(BUILD)
	$(CC) $(SANFLAGS) test_bl.c $(SRC) -o $@

# Each fault planted in the rules (1-4, 7) or in the Miller renaming (5: the missing depth - arity
# transport, 6: arguments numbered the wrong way) must be caught.
faults: $(BUILD)/test_bl
	@for f in 1 2 3 4 5 6 7; do \
	  if BL_FAULT=$$f $(BUILD)/test_bl 2000 > $(BUILD)/fault$$f.log 2>&1; then \
	    echo "fault $$f NOT caught"; exit 1; fi; \
	  echo "fault $$f caught: `grep -c FAIL $(BUILD)/fault$$f.log` failures"; \
	done

check: $(BUILD)/test_bl
	$(BUILD)/test_bl $(CASES) 1
	$(BUILD)/test_bl $(CASES) 2
	$(MAKE) --no-print-directory faults

sanitize: $(BUILD)/test_bl_san
	$(BUILD)/test_bl_san 5000 3

clean:
	rm -rf $(BUILD)

.PHONY: all faults check sanitize clean
