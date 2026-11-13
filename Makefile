CC ?= gcc
CFLAGS ?= -O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -Wall -Wextra -Werror
# Generators and the compiled-leaf tests are built without LTO.
GENFLAGS = -O3 -march=native -Wall -Wextra -Werror
LEAFFLAGS = -O2 -Wall -Wextra -Werror
MICROMATH ?= ref
CESTA ?= ../cesta/build/cesta
FLAT_RUNTIME = compiled/ordinary_flat_cesta_runtime.o
TISA_HDRS = tisa/tisa.h tisa/tc_theory_inspect.h tisa/tisa_manifest_export.h
TISA_SRCS = tisa/tisa_core.c tisa/tisa_emit_x86.c tisa/tisa_specialize.c tisa/native_alu.S
# The proved native producers add64, sub64, and64, or64, xor64 (tisa/native_alu.S): their images and
# digests. Every program that links them is checked after the link against the digests (NATIVE_CHECK:
# tisa/native_alu/check.sh); a mismatch removes the program and fails the build.
NATIVE_ALU = tisa/native_alu.S tisa/native_alu/add64.bin tisa/native_alu/sub64.bin tisa/native_alu/and64.bin tisa/native_alu/or64.bin tisa/native_alu/xor64.bin tisa/native_alu/SHA256SUMS tisa/native_alu/check.sh
NATIVE_CHECK = sh tisa/native_alu/check.sh $@ || { rm -f $@; exit 1; }
# Every program links the kernel; these are the files the kernel's own source includes.
KERNEL = tcalc.c tcalc.h compiled/ordinary_flat_adapter.h tisa/tc_theory_inspect.h $(FLAT_RUNTIME)
BRIDGE = bridge/tc_cetta_bridge.h bridge/tc_cetta_bridge.c
DL_HDRS = gslt_syntax.h gslt_packed_bridge.h petta_tcalc_eval.h gold_langs_tcalc.h

LEAF_TESTS = test_ordinary_flat_cesta_adapter test_tcalc_cesta_pack
BINS = test_tcalc test_tisa test_tisa_ref test_cetta_bridge mm0_tcalc mmb_tcalc hol_tcalc mg_tcalc dk_tcalc dl_tcalc lean_tcalc tcalc_compile lean_tcalc_compile diff_micromath
# Admission controls: sealed guards over spaces and protected value facts (tisa/admission/run.sh).
ADMISSION = tisa/admission/admission_kernel tisa/admission/admission_tisa tisa/admission/tc_init_reuse tisa/admission/admission_native tisa/admission/admission_native_patched

.PHONY: all check cesta-check admission-check clean

all: $(LEAF_TESTS) $(BINS) $(ADMISSION)

compiled/ordinary_flat_cesta_runtime.o: compiled/ordinary_flat_cesta_runtime.S compiled/ordinary_flat_cesta_linked.text
	cd compiled && as --64 ordinary_flat_cesta_runtime.S -o ordinary_flat_cesta_runtime.o

test_ordinary_flat_cesta_adapter: compiled/test_ordinary_flat_cesta_adapter.c compiled/ordinary_flat_adapter.h $(FLAT_RUNTIME)
	$(CC) $(LEAFFLAGS) -Icompiled compiled/test_ordinary_flat_cesta_adapter.c $(FLAT_RUNTIME) -o $@

test_tcalc_cesta_pack: compiled/test_tcalc_cesta.c compiled/tcalc_cesta.c compiled/tcalc_cesta.h
	$(CC) $(LEAFFLAGS) -Icompiled compiled/test_tcalc_cesta.c compiled/tcalc_cesta.c -o $@

test_tcalc: $(KERNEL) test_tcalc.c
	$(CC) $(CFLAGS) -DTC_ORDINARY_FLAT_TEST_HOOKS tcalc.c test_tcalc.c $(FLAT_RUNTIME) -o $@

test_tisa: $(KERNEL) lean_tcalc_theory.h lean_tcalc_gen.h compiled/flat_fire.h $(TISA_HDRS) $(TISA_SRCS) $(NATIVE_ALU) tisa/tisa_ref.h tisa/tisa_ref.c tisa/tisa_x86.h tisa/tisa_x86.c tisa/tisa_print.h tisa/tisa_print.c tisa/test_tisa.c
	$(CC) $(CFLAGS) tcalc.c $(TISA_SRCS) tisa/tisa_ref.c tisa/tisa_x86.c tisa/tisa_print.c tisa/test_tisa.c $(FLAT_RUNTIME) -o $@
	$(NATIVE_CHECK)

# t-ISA profile p1 (tisa/SEMANTICS.txt): the reference checked against p0's
# evaluator, against a build that keeps p0's Boolean loads, and against the
# types its own admission assigned, under the sanitizers.
TISA_REF_FLAGS = -std=gnu11 -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -Wall -Wextra -Werror -Itisa
test_tisa_ref: $(KERNEL) $(TISA_HDRS) tisa/tisa_core.c $(NATIVE_ALU) tisa/tisa_ref.h tisa/tisa_ref.c tisa/tisa_x86.h tisa/tisa_x86.c tisa/tisa_print.h tisa/tisa_print.c tisa/test_tisa_ref.c
	$(CC) $(TISA_REF_FLAGS) -DTISA_REF_P0_COMPAT -Dtisa_admit=tisa_admit_p0compat -Dtisa_run=tisa_run_p0compat -Dtisa_entry_valid=tisa_entry_valid_p0compat -c tisa/tisa_ref.c -o test_tisa_ref.p0compat.o
	$(CC) $(TISA_REF_FLAGS) -DTISA_REF_CHECK_TYPES -Dtisa_admit=tisa_admit_checked -Dtisa_run=tisa_run_checked -Dtisa_entry_valid=tisa_entry_valid_checked -c tisa/tisa_ref.c -o test_tisa_ref.checked.o
	$(CC) $(TISA_REF_FLAGS) tcalc.c tisa/tisa_core.c tisa/native_alu.S tisa/tisa_ref.c tisa/tisa_x86.c tisa/tisa_print.c test_tisa_ref.p0compat.o test_tisa_ref.checked.o tisa/test_tisa_ref.c $(FLAT_RUNTIME) -o $@
	rm -f test_tisa_ref.p0compat.o test_tisa_ref.checked.o
	$(NATIVE_CHECK)

test_cetta_bridge: $(KERNEL) $(BRIDGE) bridge/test_cetta_bridge.c
	$(CC) $(CFLAGS) -DTC_ORDINARY_FLAT_TEST_HOOKS tcalc.c $(FLAT_RUNTIME) bridge/tc_cetta_bridge.c bridge/test_cetta_bridge.c -o $@

mm0_tcalc: $(KERNEL) mm0_spec.h mm0_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) mm0_tcalc.c -o $@

mmb_tcalc: $(KERNEL) mm0_spec.h mmb_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) mmb_tcalc.c -o $@

hol_tcalc: $(KERNEL) tc_stack_guard.h hol_std_data.inc hol_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) hol_tcalc.c -o $@

mg_tcalc: $(KERNEL) tc_stack_guard.h mg_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) mg_tcalc.c -o $@

dk_tcalc: $(KERNEL) tc_stack_guard.h dk_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) dk_tcalc.c -o $@

dl_tcalc: $(KERNEL) $(BRIDGE) $(DL_HDRS) dl_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) bridge/tc_cetta_bridge.c dl_tcalc.c -o $@

lean_tcalc_compile: lean_tcalc_compile.c lean_tcalc_theory.h $(KERNEL)
	$(CC) $(GENFLAGS) lean_tcalc_compile.c $(FLAT_RUNTIME) -o $@

lean_tcalc_gen.h: lean_tcalc_compile
	./lean_tcalc_compile

lean_tcalc: $(KERNEL) $(BRIDGE) lean_tcalc_theory.h lean_tcalc_gen.h $(TISA_HDRS) $(TISA_SRCS) $(NATIVE_ALU) lean_tcalc.c
	$(CC) $(CFLAGS) tcalc.c $(FLAT_RUNTIME) $(TISA_SRCS) bridge/tc_cetta_bridge.c lean_tcalc.c -o $@
	$(NATIVE_CHECK)

tcalc_compile: tcalc_compile.c micromath_tcalc.c micromath_tcalc.h $(KERNEL)
	$(CC) $(GENFLAGS) tcalc_compile.c $(FLAT_RUNTIME) -o $@

micromath_tcalc_gen.h: tcalc_compile
	./tcalc_compile

diff_micromath: diff_micromath.c $(KERNEL) micromath_tcalc.c micromath_tcalc.h micromath_tcalc_gen.h $(MICROMATH)/kernel.c $(MICROMATH)/kernel.h $(TISA_HDRS) $(TISA_SRCS) $(NATIVE_ALU)
	$(CC) -O3 -march=native -flto -D_GNU_SOURCE -c $(MICROMATH)/kernel.c -I$(MICROMATH) -o micromath_kernel.o
	$(CC) $(CFLAGS) -D_GNU_SOURCE -DTC_HAVE_GEN -I$(MICROMATH) diff_micromath.c tcalc.c micromath_tcalc.c $(TISA_SRCS) micromath_kernel.o $(FLAT_RUNTIME) -o $@
	rm -f micromath_kernel.o
	$(NATIVE_CHECK)

CESTA_EXPORTS = cesta/tc_scanner.export.h cesta/tc_scanner.export.c cesta/tc_lean_guard.export.h cesta/tc_lean_guard.export.c cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c
CESTA_BINS = test_tcalc_cesta test_cetta_bridge_cesta dk_tcalc_cesta mg_tcalc_cesta dl_tcalc_cesta lean_tcalc_cesta

cesta/tc_scanner.export.h cesta/tc_scanner.export.c: cesta/tc_scanner.cesta
	$(CESTA) checked check cesta/tc_scanner.cesta
	$(CESTA) checked header cesta/tc_scanner.cesta -o cesta/tc_scanner.export.h
	$(CESTA) export-c cesta/tc_scanner.cesta -o cesta/tc_scanner.export.c --

cesta/tc_lean_guard.export.h cesta/tc_lean_guard.export.c: cesta/tc_lean_guard.cesta
	$(CESTA) checked check cesta/tc_lean_guard.cesta
	$(CESTA) checked header cesta/tc_lean_guard.cesta -o cesta/tc_lean_guard.export.h
	$(CESTA) export-c cesta/tc_lean_guard.cesta -o cesta/tc_lean_guard.export.c --

cesta/tc_bridge.export.c: cesta/tc_bridge.cesta tcalc.h
	$(CESTA) cc --cc $(CC) -std=c11 -I. -fsyntax-only cesta/tc_bridge.cesta
	$(CESTA) export-c cesta/tc_bridge.cesta --std=c11 --cc $(CC) -o cesta/tc_bridge.export.c -- -I.

cesta/tc_event_view.export.c: cesta/tc_event_view.cesta tcalc.h bridge/tc_cetta_bridge.h $(CESTA)
	$(CESTA) cc --cc $(CC) -std=c11 -I. -fsyntax-only cesta/tc_event_view.cesta
	$(CESTA) export-c cesta/tc_event_view.cesta --std=c11 --cc $(CC) -o $@ -- -I.

cesta/tc_recorded_cursor.export.c: cesta/tc_recorded_cursor.cesta tcalc.h bridge/tc_cetta_bridge.h ../cesta/macros/Records.module $(CESTA)
	$(CESTA) export-c cesta/tc_recorded_cursor.cesta --std=c11 --cc $(CC) -o $@ -- -I.

test_tcalc_cesta: $(KERNEL) test_tcalc.c cesta/tc_bridge.export.c
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -DTC_ORDINARY_FLAT_TEST_HOOKS -I. tcalc.c $(FLAT_RUNTIME) cesta/tc_bridge.export.c test_tcalc.c -o $@

test_cetta_bridge_cesta: $(KERNEL) $(BRIDGE) bridge/test_cetta_bridge.c cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -DTC_ORDINARY_FLAT_TEST_HOOKS -I. tcalc.c $(FLAT_RUNTIME) cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c bridge/tc_cetta_bridge.c bridge/test_cetta_bridge.c -o $@

dk_tcalc_cesta: $(KERNEL) tc_stack_guard.h dk_tcalc.c $(CESTA_EXPORTS)
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -I. tcalc.c $(FLAT_RUNTIME) cesta/tc_bridge.export.c cesta/tc_scanner.export.c dk_tcalc.c -o $@

mg_tcalc_cesta: $(KERNEL) tc_stack_guard.h mg_tcalc.c $(CESTA_EXPORTS)
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -I. tcalc.c $(FLAT_RUNTIME) cesta/tc_bridge.export.c cesta/tc_scanner.export.c mg_tcalc.c -o $@

dl_tcalc_cesta: $(KERNEL) $(BRIDGE) $(DL_HDRS) dl_tcalc.c cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -I. tcalc.c $(FLAT_RUNTIME) cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c bridge/tc_cetta_bridge.c dl_tcalc.c -o $@

lean_tcalc_cesta: $(KERNEL) $(BRIDGE) lean_tcalc_theory.h lean_tcalc_gen.h $(TISA_HDRS) $(TISA_SRCS) $(NATIVE_ALU) lean_tcalc.c cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c cesta/tc_lean_guard.export.h cesta/tc_lean_guard.export.c
	$(CC) $(CFLAGS) -DTC_USE_CESTA_EXPORT -I. tcalc.c $(FLAT_RUNTIME) $(TISA_SRCS) cesta/tc_bridge.export.c cesta/tc_event_view.export.c cesta/tc_recorded_cursor.export.c cesta/tc_lean_guard.export.c bridge/tc_cetta_bridge.c lean_tcalc.c -o $@
	$(NATIVE_CHECK)

tisa/admission/admission_kernel: $(KERNEL) tisa/admission/admission_kernel.c
	$(CC) $(CFLAGS) tcalc.c tisa/admission/admission_kernel.c $(FLAT_RUNTIME) -o $@

tisa/admission/admission_tisa: $(KERNEL) $(TISA_HDRS) tisa/tisa_core.c $(NATIVE_ALU) tisa/admission/admission_tisa.c
	$(CC) $(CFLAGS) tcalc.c tisa/admission/admission_tisa.c tisa/native_alu.S $(FLAT_RUNTIME) -o $@
	$(NATIVE_CHECK)

# The native producers: their bytes, registration and the kernel's call (admission_native); and a
# build with one byte of add64's .text copy changed, which registration must refuse and the build
# check must reject (admission_native_patched; run.sh runs check.sh on it and expects failure).
tisa/admission/admission_native: $(KERNEL) $(TISA_HDRS) tisa/tisa_core.c $(NATIVE_ALU) tisa/admission/admission_native.c tisa/admission/cb_probe.S
	$(CC) $(CFLAGS) tcalc.c tisa/admission/admission_native.c tisa/native_alu.S tisa/admission/cb_probe.S $(FLAT_RUNTIME) -o $@
	$(NATIVE_CHECK)

tisa/admission/admission_native_patched: $(KERNEL) $(TISA_HDRS) tisa/tisa_core.c $(NATIVE_ALU) tisa/admission/admission_native.c tisa/admission/cb_probe.S
	$(CC) $(CFLAGS) -DTISA_NATIVE_ALU_PATCHED tcalc.c tisa/admission/admission_native.c tisa/native_alu.S tisa/admission/cb_probe.S $(FLAT_RUNTIME) -o $@

tisa/admission/tc_init_reuse: $(KERNEL) tisa/admission/tc_init_reuse.c
	$(CC) $(CFLAGS) -DTC_INIT_VERIFY tcalc.c tisa/admission/tc_init_reuse.c $(FLAT_RUNTIME) -o $@

# The hosted t-ISA cost bench (public API only; not a test): bench_hosted --stats | --time REPS
tisa/admission/bench_hosted: $(KERNEL) $(TISA_HDRS) tisa/tisa_core.c $(NATIVE_ALU) tisa/admission/bench_hosted.c
	$(CC) $(CFLAGS) tcalc.c tisa/tisa_core.c tisa/native_alu.S tisa/admission/bench_hosted.c $(FLAT_RUNTIME) -o $@
	$(NATIVE_CHECK)

admission-check: $(ADMISSION)
	sh tisa/admission/run.sh

check:
	./run.sh
	$(MAKE) -s admission-check

cesta-check:
	sh ./cesta/diff_cesta.sh

clean:
	rm -f $(LEAF_TESTS) $(BINS) $(ADMISSION) tisa/admission/bench_hosted $(CESTA_BINS) $(CESTA_EXPORTS) micromath_tcalc_gen.h lean_tcalc_gen.h micromath_kernel.o
