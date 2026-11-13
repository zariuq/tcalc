"""Build the s2n-bignum x86 coverage table and the census gate's allowlist.

    python3 -I build_coverage.py OUTDIR CENSUS_DIR

Sources of encodings, each decoded by XED (tools/xedkey, the same decoder
state as `xed -64 -cet`) and judged by the reading of upstream decode.ml
(s2n_decode_reading.py):
  target    every instruction of the seven census targets (objdump)
  upstream  upstream's cosimulation encodings (simulator.ml, simulator_forms.ml)
  harness   the stack, branch and string forms upstream leaves to harnesses
  family    probes for the fast-path families (families.py, GNU as)
  sweep     a generated sweep of the legacy one-byte, 0F, 0F38, 0F3A and
            VEX maps with prefixes, REX and ModRM variants; each buffer
            carries filler and is cut to XED's length.
A key is IFORM|SHAPE|PREFIXES, where SHAPE is oN (XED's effective operand
size, with r2 after it for an APX REX2 prefix) for legacy encodings and
vVlLwW (VEXVALID, VL, REXW) for VEX and EVEX, and PREFIXES is the set of legacy prefix bytes before REX or VEX, in
byte order, with ".dup" if a byte other than 66 repeats. The census gate
computes the same key from `xed -v 4` output.
"""
import collections, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import s2n_decode_reading as R
from families import FAMILIES

XEDKEY = os.path.join(HERE, "tools", "xedkey")
TCALC = os.path.expanduser("~/aihub/tcalc")
TARGETS = [("hol_tcalc", TCALC + "/hol_tcalc"), ("dk_tcalc", TCALC + "/dk_tcalc"),
           ("intern16b", TCALC + "/native/intern/intern16b.hol"),
           ("leb128", TCALC + "/native/reader/leb128.hol"),
           ("fnv", TCALC + "/native/reader/fnv.hol"),
           ("intern_name", TCALC + "/native/names/intern_name.hol"),
           ("bind_walk", TCALC + "/native/walks/bind_walk.hol")]
IMAGES = {"intern16b", "leb128", "fnv", "intern_name", "bind_walk"}
LEGACY = {"66", "F2", "F3", "F0", "2E", "36", "3E", "26", "64", "65", "67"}


def run(argv, data=None):
    return subprocess.run(argv, input=data, capture_output=True, text=True, check=True).stdout


def objdump_hex(out):
    hexes = []
    for line in out.splitlines():
        f = line.split("\t")
        if len(f) == 3 and f[0] == "" and not f[2].lstrip().startswith("("):
            hexes.append(f[1].replace(" ", "").upper())
    return hexes


def target_hex(path):
    if path.endswith(".hol"):
        txt = open(path).read()
        hx = max((s for s in txt.split('"') if s and re.fullmatch(r"[0-9a-fA-F]+", s)), key=len)
        with tempfile.TemporaryDirectory(dir=os.path.join(HERE, "proto")) as d:
            b = os.path.join(d, "image.bin")
            open(b, "wb").write(bytes.fromhex(hx))
            return objdump_hex(run(["objdump", "-D", "-w", "--no-addresses", "-b", "binary",
                                    "-m", "i386:x86-64", "-M", "att", b]))
    return objdump_hex(run(["objdump", "-d", "-w", "--no-addresses", "-M", "att", path]))


def family_hex():
    rows = []
    for fam, text in FAMILIES.items():
        lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
        src = ".intel_syntax noprefix\n" + "\n".join(lines) + "\n"
        with tempfile.TemporaryDirectory(dir=os.path.join(HERE, "proto")) as d:
            o = os.path.join(d, "f.o")
            subprocess.run(["as", "--64", "-o", o, "-"], input=src, text=True, check=True,
                           capture_output=True)
            hexes = objdump_hex(run(["objdump", "-d", "-w", "--no-addresses", "-M", "intel", o]))
        assert len(hexes) == len(lines), (fam, len(hexes), len(lines))
        rows += [(fam, l, h) for l, h in zip(lines, hexes)]
    return rows


# Forms upstream cosimulates in harnesses (simulator.ml: branch_iclasses, the
# call, push, pop and push-immediate harnesses, and cosimulate_movsb_full_harness
# at 2040-2056 for A4, F3 A4 and F2 A4 with counts 0-7), and REX.W A4, which
# no harness runs.
HARNESS = ["%02X07" % (0x70 + c) for c in range(16)] + \
          ["0F%02X07000000" % (0x80 + c) for c in range(16)] + \
          ["EB05", "E905000000", "E800000000", "C3", "50", "57", "4150", "4157",
           "58", "5F", "4158", "415F", "6A15", "6878563412", "A4", "F3A4", "F2A4"]
UNHARNESSED = ["48A4"]


def prefix_sig(h):
    seen = []
    i = 0
    while i + 2 <= len(h) and h[i:i + 2] in LEGACY:
        seen.append(h[i:i + 2])
        i += 2
    if not seen:
        return "-"
    c = collections.Counter(seen)
    sig = ".".join(sorted(c))
    if any(n > 1 for b, n in c.items() if b != "66"):
        sig += ".dup"
    return sig


def after_prefixes(h):
    i = 0
    while i + 2 <= len(h) and h[i:i + 2] in LEGACY:
        i += 2
    return h[i:i + 2]


def key_of(h, x):
    _, iclass, iform, cat, ext, isa, eosz, vv, vl, w = x
    if vv == "0":
        shape = "o%s" % {"1": "16", "2": "32", "3": "64"}.get(eosz, "?")
        if after_prefixes(h) == "D5":
            shape += "r2"                                # APX REX2
    else:
        shape = "v%sl%sw%s" % (vv, vl, w)
    return "%s|%s|%s" % (iform, shape, prefix_sig(h))


# ---- the sweep ---------------------------------------------------------------

FILL = "112233445566778899AA"
MODRM_A = [("%02X" % (0xC1 | r << 3)) for r in range(8)] + \
          [("%02X2408" % (0x44 | r << 3)) for r in range(8)] + \
          [("%02X10000000" % (0x05 | r << 3)) for r in range(8)]
MODRM_B = MODRM_A[:16]
PFX_A = ["", "66", "F3", "F2"]
PFX_B = ["", "66", "F3", "F2", "6666", "2E", "3E", "26", "36", "64", "65", "F0", "67",
         "662E", "66662E", "F366", "66F3", "F266", "F3F3", "2E2E", "F2F3", "663E"]
REX_A = ["", "48"]
REX_B = ["", "40", "48", "41", "44", "4D"]


def legacy_opcodes():
    skip = {int(b, 16) for b in LEGACY} | set(range(0x40, 0x50)) | {0x0F, 0xC4, 0xC5, 0x62}
    ops = ["%02X" % b for b in range(256) if b not in skip]
    ops += ["0F%02X" % b for b in range(256) if b not in (0x38, 0x3A, 0x0F)]
    ops += ["0F38%02X" % b for b in range(256)] + ["0F3A%02X" % b for b in range(256)]
    return ops


def vex_bytes(m, op, pp, L, W, vvvv, two=False):
    if two:
        return "C5%02X%02X" % (0x80 | (vvvv << 3) | (L << 2) | pp, op)   # R=0 (no REX.R)
    return "C4%02X%02X%02X" % (0xE0 | m, (W << 7) | (vvvv << 3) | (L << 2) | pp, op)


class Corpus:
    def __init__(self):
        self.items = []        # (source, label, buffer, exact)

    def add(self, source, label, buf, exact):
        self.items.append((source, label, buf, exact))


def decode_all(bufs):
    data = "\n".join(bufs) + "\n"
    out = run([XEDKEY], data).splitlines()
    assert len(out) == len(bufs)
    return [l.split() for l in out]


def main():
    outdir, census_dir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    C = Corpus()
    tcounts = {}
    for name, path in TARGETS:
        hexes = target_hex(path)
        tcounts[name] = collections.Counter(hexes)
        for h in tcounts[name]:
            C.add("target", name, h, True)
    for line in open(os.path.join(HERE, "upstream-positive.tsv")):
        h, where, comment = line.rstrip("\n").split("\t")
        C.add("upstream", where, h, True)
    for h in HARNESS:
        C.add("harness", "harness", h, True)
    for h in UNHARNESSED:
        C.add("reading", "movsb", h, True)
    fam_rows = family_hex()
    for fam, asm, h in fam_rows:
        C.add("family", fam + ": " + asm, h, True)

    # sweep, stage A
    ops = legacy_opcodes()
    stageA = []
    for op in ops:
        for p in PFX_A:
            for rex in REX_A:
                for m in MODRM_A:
                    stageA.append((op, p + rex + op + m + FILL))
    resA = decode_all([b for _, b in stageA])
    live = set()
    for (op, b), x in zip(stageA, resA):
        if x[0] == "ERROR":
            continue
        enc = b[:2 * int(x[0])]
        if R.verdict(bytes.fromhex(enc))["status"] != "rejected":
            live.add(op)
    for op in ops:
        if op in live:
            for p in PFX_B:
                for rex in REX_B:
                    for m in MODRM_B:
                        C.add("sweep", "legacy", p + rex + op + m + FILL, False)
        else:
            for p in PFX_A:
                for rex in REX_A:
                    for m in MODRM_A:
                        C.add("sweep", "legacy", p + rex + op + m + FILL, False)
    # VEX, stage A: vvvv unused, W0
    vexA = []
    for m in (1, 2, 3):
        for op in range(256):
            for pp in range(4):
                for L in (0, 1):
                    for mm in MODRM_B:
                        vexA.append(((m, op), vex_bytes(m, op, pp, L, 0, 15) + mm + FILL))
    resV = decode_all([b for _, b in vexA])
    vlive = set()
    for (mo, b), x in zip(vexA, resV):
        if x[0] == "ERROR":
            continue
        if R.verdict(bytes.fromhex(b[:2 * int(x[0])]))["status"] != "rejected":
            vlive.add(mo)
    for m in (1, 2, 3):
        for op in range(256):
            Ws = (0, 1) if (m, op) in vlive else (0,)
            vvs = (15, 6) if (m, op) in vlive else (15,)
            for pp in range(4):
                for L in (0, 1):
                    for W in Ws:
                        for vv in vvs:
                            for mm in MODRM_B:
                                C.add("sweep", "vex", vex_bytes(m, op, pp, L, W, vv) + mm + FILL, False)
                            if (m, op) in vlive:
                                for pre in ("2E", "66", "F3", "40", "64"):
                                    C.add("sweep", "vex", pre + vex_bytes(m, op, pp, L, W, vv) + MODRM_B[1] + FILL, False)
                    if m == 1:
                        for mm in MODRM_B:
                            C.add("sweep", "vex2", vex_bytes(1, op, pp, L, 0, 15, two=True) + mm + FILL, False)

    print("corpus items:", len(C.items), file=sys.stderr)
    res = decode_all([b for _, _, b, _ in C.items])

    keys = {}          # key -> record
    iforms = {}        # iform -> record
    enc_verdict = {}   # encoding -> verdict
    xed_fail = collections.Counter()
    exact_fail = []
    for (src, label, buf, exact), x in zip(C.items, res):
        if x[0] == "ERROR":
            if exact:
                exact_fail.append((src, label, buf, x[1]))
            xed_fail[src] += 1
            continue
        n = int(x[0])
        enc = buf[:2 * n]
        if exact and enc != buf:
            exact_fail.append((src, label, buf, "length %d" % n))
            continue
        v = enc_verdict.get(enc)
        if v is None:
            v = R.verdict(bytes.fromhex(enc))
            enc_verdict[enc] = v
        k = key_of(enc, x)
        r = keys.get(k)
        if r is None:
            r = keys[k] = dict(iform=x[2], iclass=x[1], cat=x[3], ext=x[4], isa=x[5],
                               status=collections.Counter(), ctors=collections.Counter(),
                               reasons=collections.Counter(), sources=set(), example={},
                               targets=collections.Counter(), families=set())
        r["status"][v["status"]] += 1
        if v["ctor"] and v["status"] != "rejected":
            r["ctors"][v["ctor"]] += 1
        if v["status"] != "decoded":
            r["reasons"]["%s (decode.ml:%s)" % (v["reason"], v["line"])] += 1
        r["sources"].add(src)
        r["example"].setdefault(v["status"], enc)
        if src == "target":
            r["targets"][label] += tcounts[label][enc]
        if src == "family":
            r["families"].add(label.split(":")[0])
        f = iforms.setdefault(x[2], dict(iclass=x[1], cat=x[3], ext=x[4], isa=x[5], keys=set()))
        f["keys"].add(k)

    # key verdicts
    def kstatus(r):
        st = r["status"]
        kinds = [s for s in ("decoded", "caveat", "rejected") if st[s]]
        return kinds[0] if len(kinds) == 1 else "mixed"

    mixed = [k for k, r in keys.items() if kstatus(r) == "mixed"]
    print("keys:", len(keys), "iforms:", len(iforms), "mixed keys:", len(mixed),
          "xed errors:", dict(xed_fail), "exact failures:", len(exact_fail), file=sys.stderr)
    for e in exact_fail[:20]:
        print("EXACT-FAIL", e, file=sys.stderr)

    with open(os.path.join(outdir, "s2n-keys.tsv"), "w") as o:
        o.write("# key\tstatus\tdecoded\tcaveat\trejected\tconstructors\treason\tsources\ttarget_count\texample\n")
        for k in sorted(keys):
            r = keys[k]
            st = r["status"]
            o.write("\t".join([k, kstatus(r), str(st["decoded"]), str(st["caveat"]), str(st["rejected"]),
                               ",".join(sorted(r["ctors"])) or "-",
                               (r["reasons"].most_common(1)[0][0] if r["reasons"] else "-"),
                               ",".join(sorted(r["sources"])), str(sum(r["targets"].values())),
                               " ".join("%s:%s" % (s, e) for s, e in sorted(r["example"].items()))]) + "\n")
    with open(os.path.join(outdir, "s2n-mixed.tsv"), "w") as o:
        for k in sorted(mixed):
            r = keys[k]
            o.write("%s\t%s\t%s\t%s\n" % (k, dict(r["status"]), r["reasons"].most_common(3), r["example"]))

    # iform rows
    def summarize(iform):
        ks = sorted(iforms[iform]["keys"])
        dec = [k.split("|", 1)[1] for k in ks if kstatus(keys[k]) == "decoded"]
        cav = [k.split("|", 1)[1] for k in ks if kstatus(keys[k]) == "caveat"]
        mix = [k.split("|", 1)[1] for k in ks if kstatus(keys[k]) == "mixed"]
        rej = [k for k in ks if kstatus(keys[k]) == "rejected"]
        # the reason of the plainest rejected forms: fewest legacy prefixes
        def npfx(k):
            sig = k.rsplit("|", 1)[1]
            return 0 if sig == "-" else len(sig.split("."))
        plain = [k for k in rej if npfx(k) == min(map(npfx, rej))] if rej else []
        reasons = collections.Counter()
        for k in plain:
            reasons.update(keys[k]["reasons"])
        if dec:
            status = "decoded"
        elif cav:
            status = "caveat"
        elif mix:
            status = "mixed"
        else:
            status = "not-decoded"
        ctors = collections.Counter()
        for k in ks:
            ctors.update(keys[k]["ctors"])
        tc = collections.Counter()
        fams = set()
        srcs = set()
        for k in ks:
            tc.update(keys[k]["targets"])
            fams |= keys[k]["families"]
            srcs |= keys[k]["sources"]
        attested = any(kstatus(keys[k]) == "decoded" and keys[k]["sources"] & {"upstream", "harness"} for k in ks)
        cavwhy = collections.Counter()
        for k in ks:
            if kstatus(keys[k]) == "caveat":
                cavwhy.update(keys[k]["reasons"])
        return dict(status=status, dec=dec, cav=cav, mix=mix, nrej=len(rej), attested=attested,
                    caveat=(cavwhy.most_common(1)[0][0] if cavwhy else "-"),
                    reason=(reasons.most_common(1)[0][0] if reasons else "-"),
                    ctors=sorted(ctors), tc=tc, fams=sorted(fams), srcs=sorted(srcs))

    interesting = set()
    for iform, f in iforms.items():
        s = summarize(iform)
        f["summary"] = s
        if s["tc"] or s["fams"] or s["status"] != "not-decoded":
            interesting.add(iform)
    with open(os.path.join(outdir, "s2n-coverage.tsv"), "w") as o:
        o.write("# s2n-bignum x86 decoder coverage by XED iform: a textual reading of upstream "
                "76604c2 x86/proofs/decode.ml (see s2n_decode_reading.py). The authoritative check "
                "is s2n's decode run in HOL Light on these encodings, a later pass.\n")
        o.write("# Columns: s2n is decoded (some form decodes without caveat), caveat (decodes only with\n"
                "# the caveat given), or not-decoded. decoded_forms and caveat_forms list SHAPE|PREFIXES\n"
                "# (oN operand size, vVlLwW for VEX/EVEX; legacy prefix set). rejected_forms counts the\n"
                "# other forms seen; reason is the decode.ml clause for the plainest of them. attested:\n"
                "# some decoded form has an encoding in upstream's cosimulation lists or harnesses.\n")
        o.write("# iform\ticlass\textension\tisa_set\tcategory\ts2n\tdecoded_forms\tcaveat_forms"
                "\tcaveat\trejected_forms\treason\tattested\ts2n_constructors\thol_tcalc\tdk_tcalc\timages"
                "\tfamilies\tsources\n")
        for iform in sorted(interesting):
            f = iforms[iform]
            s = f["summary"]
            img = sum(n for t, n in s["tc"].items() if t in IMAGES)
            o.write("\t".join([iform, f["iclass"], f["ext"], f["isa"], f["cat"], s["status"],
                               " ".join(s["dec"]) or "-", " ".join(s["cav"]) or "-", s["caveat"], str(s["nrej"]),
                               s["reason"] if s["nrej"] else "-", "yes" if s["attested"] else "no",
                               ",".join(s["ctors"]) or "-", str(s["tc"]["hol_tcalc"]),
                               str(s["tc"]["dk_tcalc"]), str(img), ",".join(s["fams"]) or "-",
                               ",".join(s["srcs"])]) + "\n")

    # the gate's allowlist: keys decoded without caveat, no mixed verdicts
    allow = sorted(k for k, r in keys.items() if kstatus(r) == "decoded")
    attested = sorted(k for k in allow if keys[k]["sources"] & {"upstream", "harness"})
    known = sorted(k for k, r in keys.items()
                   if kstatus(r) != "decoded" and r["sources"] & {"target", "family", "upstream", "harness", "reading"})
    with open(os.path.join(census_dir, "s2n_allowlist.metta"), "w") as o:
        o.write("; s2n_allowlist.metta -- generated; do not edit by hand.\n")
        o.write("; The forms that s2n-bignum's x86 decoder (upstream 76604c2, x86/proofs/decode.ml)\n")
        o.write("; decodes without caveat, by a textual reading of the decoder checked against\n")
        o.write("; upstream's cosimulation encodings; the authoritative check is the decoder run\n")
        o.write("; in HOL Light. A key is IFORM|SHAPE|PREFIXES (see census:xed-key).\n")
        o.write("; Generated by native/census/coverage/build_coverage.py: %d keys seen, %d decoded,\n"
                % (len(keys), len(allow)))
        o.write("; %d of them attested by an encoding in upstream's cosimulation lists or harnesses.\n"
                % len(attested))
        o.write('(= (census:s2n-allowlist-source) (s2n-bignum "76604c2" (keys %d) (attested %d)))\n\n'
                % (len(allow), len(attested)))
        o.write("(= (census:s2n-allowed-keys)\n   (")
        o.write("\n    ".join('"%s"' % k for k in allow))
        o.write("))\n\n")
        o.write("; Allowed keys that upstream cosimulates against hardware.\n")
        o.write("(= (census:s2n-attested-keys)\n   (")
        o.write("\n    ".join('"%s"' % k for k in attested))
        o.write("))\n\n")
        o.write("; Forms seen in the targets, families or upstream lists that are not allowed, with why.\n")
        for k in known:
            r = keys[k]
            reason = r["reasons"].most_common(1)[0][0] if r["reasons"] else "-"
            o.write('(census:s2n-known "%s" %s "%s")\n' % (k, kstatus(r), reason.replace('"', "'")))
    # verification corpus for the HOL pass: every exact encoding with its predicted verdict
    with open(os.path.join(outdir, "s2n-verdicts.tsv"), "w") as o:
        o.write("# encoding\tpredicted\tconstructor\tdecode.ml line\treason\tsources\n")
        seen = {}
        for src, label, buf, exact in C.items:
            if exact:
                seen.setdefault(buf, set()).add(src)
        for h in sorted(seen):
            v = enc_verdict.get(h)
            if v is None:
                continue
            o.write("\t".join([h, v["status"], v["ctor"] or "-", str(v["line"]), v["reason"] or "-",
                               ",".join(sorted(seen[h]))]) + "\n")
    print("allowlist keys:", len(allow), "known non-allowed:", len(known), file=sys.stderr)


if __name__ == "__main__":
    main()
