#!/usr/bin/env python3
"""x86 instruction census: what machine code actually uses.

  x86_census.py [--json OUT] TARGET...

A TARGET is an ELF binary (its executable sections are disassembled) or a
t-ISA image record (.hol, whose program bytes are the hex string in the
record). For each target: the instruction mix by mnemonic, and the classes
that matter for verification against s2n-bignum's x86 model:

  indirect-branch   call/jmp through a register or memory (FF /2, FF /4):
                    rejected by current upstream s2n-bignum, mis-modelled
                    as relative by older commits
  push-pop-rm       push/pop of a memory operand (FF /6, 8F /0)
  jump-table        indirect jmp through a scaled table
  bitscan           lzcnt, tzcnt, popcnt, bsf, bsr (CPU-feature dependent)
  bmi2              shlx, shrx, sarx, rorx, pdep, pext, mulx, bzhi
  adx               adcx, adox
  simd              any xmm/ymm/zmm or mm register, or a vector mnemonic
  string            rep/repe/repne prefixed string operations
  endbr             endbr64 (IBT landing pads)
  syscall-privileged syscall, int, cpuid, rdtsc, ...

Read-only: it runs objdump and reads files; it changes nothing.
"""
import json, re, subprocess, sys, tempfile, os, collections

CLASSES = {
    "bitscan": {"lzcnt", "tzcnt", "popcnt", "bsf", "bsr"},
    "bmi2": {"shlx", "shrx", "sarx", "rorx", "pdep", "pext", "mulx", "bzhi"},
    "adx": {"adcx", "adox"},
    "privileged": {"syscall", "int", "int3", "cpuid", "rdtsc", "rdtscp", "hlt", "ud2"},
}

def disasm_elf(path):
    out = subprocess.run(["objdump", "-d", "-w", "--no-addresses", "-M", "att", path],
                         capture_output=True, text=True, check=True).stdout
    return parse_objdump(out)

def disasm_image(path):
    txt = open(path).read()
    m = re.search(r'"([0-9a-f]{16,})"', txt)
    if not m:
        raise ValueError("no image bytes in " + path)
    data = bytes.fromhex(m.group(1))
    with tempfile.NamedTemporaryFile(suffix=".bin", delete=False) as f:
        f.write(data); name = f.name
    try:
        out = subprocess.run(["objdump", "-D", "-w", "--no-addresses", "-b", "binary",
                              "-m", "i386:x86-64", "-M", "att", name],
                             capture_output=True, text=True, check=True).stdout
    finally:
        os.unlink(name)
    return parse_objdump(out), len(data)

LINE = re.compile(r'^\s*((?:[0-9a-f]{2} )+)\s*(.*)$')

def parse_objdump(out):
    insns = []
    for line in out.splitlines():
        if not line.startswith("\t") and not line.startswith(" "):
            continue
        m = LINE.match(line.replace("\t", " "))
        if not m:
            continue
        rest = m.group(2).strip()
        if not rest or rest.startswith("("):
            continue
        parts = rest.split(None, 1)
        mnem = parts[0]
        ops = parts[1] if len(parts) > 1 else ""
        prefixes = []
        while mnem in ("rep", "repz", "repe", "repnz", "repne", "lock", "notrack", "bnd", "data16", "cs", "ds") and ops:
            prefixes.append(mnem)
            sub = ops.split(None, 1)
            mnem = sub[0]; ops = sub[1] if len(sub) > 1 else ""
        insns.append((m.group(1).strip(), prefixes, mnem, ops))
    return insns

def classify(insns):
    mix = collections.Counter()
    cls = collections.Counter()
    examples = collections.defaultdict(list)
    for hexb, prefixes, mnem, ops in insns:
        base = re.sub(r'[bwlq]$', '', mnem) if mnem not in ("call", "jmp") else mnem
        mix[mnem] += 1
        tags = []
        if mnem.startswith("call") and "*" in ops:
            tags.append("indirect-branch")
        if mnem.startswith("jmp") and "*" in ops:
            tags.append("jump-table" if "(" in ops and "," in ops else "indirect-branch")
        if (mnem.startswith("push") or mnem.startswith("pop")) and "(" in ops:
            tags.append("push-pop-rm")
        if any(p.startswith("rep") for p in prefixes):
            tags.append("string")
        if mnem == "endbr64":
            tags.append("endbr")
        if re.search(r'%[xyz]mm\d|%mm\d|%k\d\b', ops) or (mnem.startswith("v") and mnem not in ("verr", "verw")):
            tags.append("simd")
        for c, names in CLASSES.items():
            if mnem in names or base in names:
                tags.append(c)
        for t in tags:
            cls[t] += 1
            if len(examples[t]) < 4:
                examples[t].append(f"{hexb}  {' '.join(prefixes + [mnem])} {ops}".strip())
    return mix, cls, examples

def main():
    args = sys.argv[1:]
    out_json = None
    if args[:1] == ["--json"]:
        out_json = args[1]; args = args[2:]
    report = {}
    for t in args:
        if t.endswith(".hol"):
            insns, nbytes = disasm_image(t)
            kind = f"t-ISA image, {nbytes} bytes"
        else:
            insns = disasm_elf(t)
            kind = "ELF"
        mix, cls, ex = classify(insns)
        report[t] = {"kind": kind, "instructions": len(insns), "distinct": len(mix),
                     "classes": dict(cls), "examples": ex,
                     "top": mix.most_common(25), "mnemonics": sorted(mix)}
        print(f"== {t} ({kind}): {len(insns)} instructions, {len(mix)} distinct mnemonics")
        for c in sorted(cls):
            print(f"   {c:18s} {cls[c]:6d}   e.g. {ex[c][0]}")
    if len(args) > 1:
        imgs = [t for t in args if t.endswith(".hol")]
        elfs = [t for t in args if not t.endswith(".hol")]
        if imgs and elfs:
            img_m = set().union(*(report[t]["mnemonics"] for t in imgs))
            elf_m = set().union(*(report[t]["mnemonics"] for t in elfs))
            print(f"== mnemonics in the GCC binaries but in no proved image: {len(elf_m - img_m)}")
            print("   " + " ".join(sorted(elf_m - img_m)[:120]))
            print(f"== mnemonics in the proved images: {len(img_m)}: " + " ".join(sorted(img_m)))
    if out_json:
        json.dump(report, open(out_json, "w"), indent=1, default=list)

if __name__ == "__main__":
    main()
