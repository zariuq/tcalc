# t-ISA p1 programs as text: loader, round trip, differential harness.
# The t-ISA sources are linked from tcalc/tisa, never changed here.
CC ?= gcc
TISA = ../../tisa
BUILD ?= build
CFLAGS ?= -std=gnu11 -O2 -g -D_GNU_SOURCE -Wall -Wextra -Werror
CPPFLAGS += -I$(TISA) -I.
TISA_SRCS = $(TISA)/tisa_ref.c $(TISA)/tisa_x86.c $(TISA)/tisa_print.c
TISA_HDRS = $(TISA)/tisa.h $(TISA)/tisa_ref.h $(TISA)/tisa_x86.h $(TISA)/tisa_print.h

.PHONY: all check clean
all: $(BUILD)/p1_roundtrip $(BUILD)/p1_load_refusals $(BUILD)/p1run $(BUILD)/p1_text

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/p1_load_refusals: p1_load_refusals.c p1_load.c p1_load.h $(TISA_HDRS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) p1_load_refusals.c p1_load.c $(TISA)/tisa_print.c -o $@

$(BUILD)/p1_roundtrip: p1_roundtrip.c p1_load.c p1_load.h $(TISA_SRCS) $(TISA_HDRS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) p1_roundtrip.c p1_load.c $(TISA_SRCS) -o $@

$(BUILD)/p1_text: p1_text.c p1_load.c p1_load.h $(TISA_HDRS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) p1_text.c p1_load.c $(TISA)/tisa_print.c -o $@

$(BUILD)/p1run: p1run.c p1_load.c p1_load.h $(TISA_SRCS) $(TISA_HDRS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) p1run.c p1_load.c $(TISA_SRCS) -o $@

clean:
	rm -f $(BUILD)/p1_roundtrip $(BUILD)/p1_load_refusals $(BUILD)/p1run $(BUILD)/p1_text
