CC ?= gcc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra -Werror
# Micromath's own C kernel, the reference of the differential test.
REF ?= ../ref

all: micromath_gen.h diff_micromath controls diff_step

tc0_compile: tc0_compile.c tc0.c tc0.h micromath.c micromath.h
	$(CC) $(CFLAGS) tc0_compile.c -o $@

micromath_gen.h: tc0_compile
	./tc0_compile

diff_micromath: test/diff_micromath.c tc0.c tc0.h micromath.c micromath.h micromath_gen.h $(REF)/kernel.c $(REF)/kernel.h
	$(CC) $(CFLAGS) -D_GNU_SOURCE -I. -I$(REF) test/diff_micromath.c tc0.c micromath.c $(REF)/kernel.c -o $@

controls: test/controls.c tc0.c tc0.h
	$(CC) $(CFLAGS) -I. test/controls.c tc0.c -o $@

diff_step: test/diff_step.c tc0.c tc0.h
	$(CC) $(CFLAGS) -I. test/diff_step.c tc0.c -o $@

check: all
	./run.sh

clean:
	rm -f tc0_compile micromath_gen.h diff_micromath controls diff_step

.PHONY: all check clean
