"""Independent check of the census XED mode (x86_census.metta).

    python3 -I check_xed_census.py XED_REPORT_OUTPUT

Recomputes, for each target, the instruction and encoding counts, the
iclass and iform counts, the extension, ISA-set and category histograms,
the XED classes and the s2n allowed/outside split, decoding with
tools/xedkey (libxed called directly, not the xed command the census
parses) and reading s2n_allowlist.metta, then compares with the census's
(census-xed ...) terms."""
import collections, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build_coverage as B

CENSUS = os.path.expanduser("~/aihub/tcalc/native/census")


def allowlist():
    txt = open(os.path.join(CENSUS, "s2n_allowlist.metta")).read()
    body = txt.split("(= (census:s2n-allowed-keys)", 1)[1].split("))", 1)[0]
    return set(re.findall(r'"([^"]+)"', body))


def xclasses(iclass, iform, ext, table):
    tags = []
    ind = iform in ("CALL_NEAR_GPRv", "CALL_NEAR_MEMv", "JMP_GPRv", "JMP_MEMv", "CALL_FAR_MEMp2", "JMP_FAR_MEMp2")
    if ind and not table:
        tags.append("indirect-branch")
    if table:
        tags.append("jump-table")
    if iform in ("PUSH_MEMv", "POP_MEMv"):
        tags.append("push-pop-rm")
    if iclass.startswith(("REP_", "REPE_", "REPNE_")):
        tags.append("string")
    if iclass in ("ENDBR64", "ENDBR32"):
        tags.append("endbr")
    suffix = iform[len(iclass) + 1:] if len(iform) > len(iclass) + 1 else ""
    if iclass in ("VZEROUPPER", "VZEROALL") or any(
            t.startswith(("XMM", "YMM", "ZMM", "MMX", "MASK")) for t in suffix.split("_") if t):
        tags.append("simd")
    if iclass in ("BSF", "BSR", "LZCNT", "TZCNT", "POPCNT"):
        tags.append("bitscan")
    if ext == "BMI2":
        tags.append("bmi2")
    if ext == "ADOX_ADCX":
        tags.append("adx")
    if iclass in ("SYSCALL", "INT", "INT3", "CPUID", "RDTSC", "RDTSCP", "HLT", "UD2"):
        tags.append("privileged")
    return tags or ["base"]


def scaled_index(enc):
    # JMP_MEMv through an index register: ModRM rm=100 with a SIB whose index is not 100
    # (or REX.X set). Read from the bytes, independently of xed's MEM0 text.
    h = enc
    i = 0
    while h[i:i + 2] in B.LEGACY:
        i += 2
    rex = 0
    if h[i] == "4":
        rex = int(h[i:i + 2], 16)
        i += 2
    assert h[i:i + 2] == "FF"
    modrm = int(h[i + 2:i + 4], 16)
    if (modrm & 7) != 4 or (modrm >> 6) == 3:
        return False
    sib = int(h[i + 4:i + 6], 16)
    index = ((sib >> 3) & 7) | (8 if rex & 2 else 0)
    return index != 4


def main():
    report = open(sys.argv[1]).read()
    allow = allowlist()
    ok = True
    for name, path in B.TARGETS:
        hexes = B.target_hex(path)
        cnt = collections.Counter(hexes)
        enc = sorted(cnt)
        out = B.run([B.XEDKEY], "\n".join(enc) + "\n").splitlines()
        rec = dict(zip(enc, (l.split() for l in out)))
        ext, isa, cat, cls, s2n = (collections.Counter() for _ in range(5))
        iclasses, iforms = set(), set()
        for h, n in cnt.items():
            x = rec[h]
            assert x[0] != "ERROR" and int(x[0]) * 2 == len(h), (h, x)
            _, ic, ifm, c, e, s = x[:6]
            iclasses.add(ic)
            iforms.add(ifm)
            ext[e] += n
            isa[s] += n
            cat[c] += n
            for t in xclasses(ic, ifm, e, ifm == "JMP_MEMv" and scaled_index(h)):
                cls[t] += n
            s2n["allowed" if B.key_of(h, x) in allow else "outside"] += n
        m = re.search(r'\(census-xed "%s" (.*?)\(disagreements' % re.escape(path), report, re.S)
        if not m:
            print("MISSING", name)
            ok = False
            continue
        body = m.group(1)

        def hist(tag):
            seg = re.search(r"\(%s \(((?:\([^()]*\)\s*)*)\)\)" % tag, body).group(1)
            return {k.strip('"'): float(v) for k, v in re.findall(r'\(("?[A-Za-z0-9_-]+"?) ([0-9.]+)\)', seg)}

        mine = {
            "instructions": len(hexes), "encodings": len(enc), "iclasses": len(iclasses), "iforms": len(iforms)}
        theirs = {k: int(re.search(r"\(%s (\d+)\)" % k, body).group(1)) for k in mine}
        checks = [("counts", mine, theirs),
                  ("extensions", dict(ext), hist("extensions")),
                  ("isa-sets", dict(isa), hist("isa-sets")),
                  ("categories", dict(cat), hist("categories")),
                  ("classes", dict(cls), hist("classes")),
                  ("s2n", dict(s2n), hist("s2n"))]
        for what, a, b in checks:
            same = {k: float(v) for k, v in a.items()} == {k: float(v) for k, v in b.items()}
            ok &= same
            print("%-12s %-10s %s" % (name, what, "same" if same else "DIFFERENT %s vs %s" % (a, b)))
    print("ALL SAME" if ok else "DIFFERENCES FOUND")


if __name__ == "__main__":
    main()
