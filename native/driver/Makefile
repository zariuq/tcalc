# The plan driver and the record loop: each assembled relocation-free; its
# .text as the bytes the proofs read (build/driver.o, build/records.o) and
# the harnesses check (build/driver.bin, build/records.bin); linked with the
# leaves' proved images for the differential harnesses.
CC ?= gcc
TISA = ../../tisa
P1 = ../p1
BUILD ?= build
CFLAGS ?= -std=gnu11 -O2 -g -D_GNU_SOURCE -Wall -Wextra -Werror
CPPFLAGS += -I$(TISA) -I$(P1)
TISA_SRCS = $(TISA)/tisa_ref.c $(TISA)/tisa_x86.c $(TISA)/tisa_print.c

.PHONY: all clean
all: $(BUILD)/driver.o $(BUILD)/driver.bin $(BUILD)/records.o $(BUILD)/records.bin \
     $(BUILD)/test_driver $(BUILD)/test_records

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/driver.o: driver.S | $(BUILD)
	$(CC) -c driver.S -o $@
	@readelf -r $@ | grep -q 'There are no relocations in this file' || { echo "driver.o has relocations"; rm -f $@; exit 1; }

$(BUILD)/driver.bin: $(BUILD)/driver.o
	objcopy -O binary --only-section=.text $< $@

$(BUILD)/records.o: records.S | $(BUILD)
	$(CC) -c records.S -o $@
	@readelf -r $@ | grep -q 'There are no relocations in this file' || { echo "records.o has relocations"; rm -f $@; exit 1; }

$(BUILD)/records.bin: $(BUILD)/records.o
	objcopy -O binary --only-section=.text $< $@

$(BUILD)/intern16_image.S: ../intern/intern16b.hol gen_image.sh | $(BUILD)
	./gen_image.sh ../intern/intern16b.hol tisa_leaf_intern16 > $@

$(BUILD)/fnv_image.S: ../reader/fnv.hol gen_image.sh | $(BUILD)
	./gen_image.sh ../reader/fnv.hol tisa_leaf_fnv > $@

$(BUILD)/leb128_image.S: ../reader/leb128.hol gen_image.sh | $(BUILD)
	./gen_image.sh ../reader/leb128.hol tisa_leaf_leb128 > $@

$(BUILD)/name_image.S: ../names/intern_name.hol gen_image.sh | $(BUILD)
	./gen_image.sh ../names/intern_name.hol tisa_leaf_name > $@

$(BUILD)/test_driver: test_driver.c cet_profile.h $(BUILD)/driver.o $(BUILD)/intern16_image.S $(P1)/p1_load.c $(TISA_SRCS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) test_driver.c $(BUILD)/driver.o $(BUILD)/intern16_image.S \
	  $(P1)/p1_load.c $(TISA_SRCS) -o $@

LEAF_IMAGES = $(BUILD)/intern16_image.S $(BUILD)/fnv_image.S $(BUILD)/leb128_image.S $(BUILD)/name_image.S

$(BUILD)/test_records: test_records.c cet_profile.h $(BUILD)/driver.o $(BUILD)/records.o $(LEAF_IMAGES) $(P1)/p1_load.c $(TISA_SRCS) | $(BUILD)
	$(CC) $(CPPFLAGS) $(CFLAGS) test_records.c $(BUILD)/driver.o $(BUILD)/records.o $(LEAF_IMAGES) \
	  $(P1)/p1_load.c $(TISA_SRCS) -o $@

clean:
	rm -f $(BUILD)/driver.o $(BUILD)/driver.bin $(BUILD)/records.o $(BUILD)/records.bin $(LEAF_IMAGES) \
	  $(BUILD)/test_driver $(BUILD)/test_records
