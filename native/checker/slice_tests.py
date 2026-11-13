#!/usr/bin/env python3
"""slice_tests.py -- HOLR streams for the checker slice, CeTTa's verdict on
each, and a p1run test description expecting that verdict from the checker.

  slice_tests.py OUTDIR [SEED] [RANDOM] [FLIPS]

Writes OUTDIR/streams/*.holr, OUTDIR/verdicts.tsv (CeTTa's verdict per
stream), and OUTDIR/slice.p1t. A case expects CeTTa's verdict: its state
(control word 0), reason (word 34) and record count (the run's return
value). Where the stream reaches a record outside the slice first (or is a
probe stream), the case expects the checker's UNSUPPORTED at that record
instead, and the stream does not count as compared.

Streams: well-formed random streams over the slice's records; each of them
mutated once per refusal and malformation kind; random byte flips (with the
END checksum left or recomputed); and fixed edge cases (headers, LEB128
forms, limits, empty input).
"""
import os
import random
import struct
import subprocess
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from holr import *  # noqa: E402,F401

# CeTTa's HolReason names, in enum order (native/hol_light/hol_api.c).
REASONS = [
    "none", "null-arg", "bad-handle", "wrong-kind", "stale-handle", "future-handle",
    "foreign-kernel", "incompatible-env", "bad-name", "bad-index",
    "mk_type: undeclared", "mk_type: arity", "dest_type", "dest_vartype",
    "mk_const: undeclared", "const: not an instance", "mk_abs: not a variable",
    "mk_comb: types do not agree", "dest_var", "dest_const", "dest_comb", "dest_abs",
    "dest_eq", "rator", "rand", "variant: not a variable", "vsubst: bad substitution list",
    "TRANS", "MK_COMB: not both equations", "MK_COMB: types do not agree",
    "ABS: not a variable or not an equation", "ABS: variable free in hypothesis",
    "BETA: not a trivial beta-redex", "ASSUME: not a proposition", "EQ_MP",
    "new_type: already declared", "new_constant: already declared",
    "new_axiom: not a proposition", "axiom policy", "policy cannot be loosened",
    "new_basic_definition: shape", "new_basic_definition: already defined",
    "new_definition: term not closed", "new_definition: type variables not reflected",
    "new_basic_type_definition: constants in use",
    "new_basic_type_definition: assumptions in theorem",
    "new_basic_type_definition: not a combination",
    "new_basic_type_definition: predicate not closed",
    "new_basic_type_definition: type already defined",
    "new_basic_type_definition: abs and rep names equal (native atomic refusal)",
    "out of memory", "depth limit", "fuel exhausted", "interrupted",
    "stream: bad magic", "stream: unsupported version", "stream: bad header",
    "stream: truncated", "stream: bad integer encoding", "stream: unknown opcode",
    "stream: future reference", "stream: dropped reference", "stream: failed reference",
    "stream: trailing bytes", "stream: checksum mismatch", "stream: record count mismatch",
    "stream: limit exceeded", "stream: expectation failed", "stream: unknown label",
    "stream: record after END", "stream: missing END", "stream: bad value"]

ACCEPTED, REFUSED, MALFORMED, RESOURCE, UNSUPPORTED = 2, 3, 4, 5, 6
OUTCOME = {ACCEPTED: "FIRED", REFUSED: "REFUSED", MALFORMED: "UNSUPPORTED", RESOURCE: "UNSUPPORTED",
           UNSUPPORTED: "UNSUPPORTED"}
SLICE = {NAME, TYVAR, TYAPP, VAR, CONST, COMB, REFL, TRANS, EXPECT_ALPHA, END}
LAYOUT = {  # HOLR v1 layouts (hol_stream.c op_table)
    0x01: "b", 0x02: "N", 0x03: "N*Y", 0x04: "NY", 0x05: "NY", 0x06: "TT", 0x07: "TT",
    0x10: "T", 0x11: "HH", 0x12: "HH", 0x13: "TH", 0x14: "T", 0x15: "T", 0x16: "HH", 0x17: "HH",
    0x18: "%YYH", 0x19: "%TTH", 0x20: "Nu", 0x21: "NY", 0x22: "T", 0x23: "T", 0x24: "NNNH", 0x25: "u",
    0x30: "H*TT", 0x31: "HN", 0x32: "H", 0x33: "", 0x34: "H*H", 0x35: "H*TT",
    0x40: "y", 0x41: "t", 0x42: "h", 0x7f: "uc"}


# ---- well-formed random streams -----------------------------------------------------

class Builder:
    """A stream with a model of its ids: types and terms by structure."""

    def __init__(self, rng):
        self.rng = rng
        self.s = Stream()
        self.name_ids = {}     # text -> N ids
        self.ty = []           # Y id -> structure
        self.ty_of = {}        # structure -> a Y id
        self.tm = []           # T id -> (structure, type structure)
        self.tm_of = {}
        self.th = []           # H id -> conclusion structure (an equation l = r)

    def name(self, text):
        ids = self.name_ids.get(text)
        if ids and self.rng.random() < 0.7:
            return self.rng.choice(ids)
        n = self.s.name(text)
        self.name_ids.setdefault(text, []).append(n)
        return n

    def type_app(self, op, args):
        key = ("app", op, tuple(self.ty[a] for a in args))
        if key in self.ty_of and self.rng.random() < 0.6:
            return self.ty_of[key]
        y = self.s.tyapp(self.name(op), args)
        self.ty.append(key)
        self.ty_of.setdefault(key, y)
        return y

    def type_var(self, v):
        key = ("var", v)
        if key in self.ty_of and self.rng.random() < 0.6:
            return self.ty_of[key]
        y = self.s.tyvar(self.name(v))
        self.ty.append(key)
        self.ty_of.setdefault(key, y)
        return y

    def bool_(self):
        return self.type_app("bool", [])

    def fun(self, a, b):
        return self.type_app("fun", [a, b])

    def some_type(self, depth=0):
        r = self.rng.random()
        if self.ty and r < 0.4:
            return self.rng.randrange(len(self.ty))
        if r < 0.6 or depth > 2:
            return self.bool_()
        if r < 0.75:
            return self.type_var(self.rng.choice(["A", "B", "C"]))
        return self.fun(self.some_type(depth + 1), self.some_type(depth + 1))

    def add_term(self, t, key, tykey):
        self.tm.append((key, tykey))
        self.tm_of.setdefault(key, t)
        return t

    def var(self, text, y):
        t = self.s.var(self.name(text), y)
        return self.add_term(t, ("v", text, self.ty[y]), self.ty[y])

    def const_eq(self, y):
        # = at y -> y -> bool
        yy = self.fun(y, self.fun(y, self.bool_()))
        t = self.s.const(self.name("="), yy)
        return self.add_term(t, ("c", "=", self.ty[yy]), self.ty[yy])

    def comb(self, f, x):
        fk, fty = self.tm[f]
        xk, xty = self.tm[x]
        assert fty[0] == "app" and fty[1] == "fun" and fty[2][0] == xty
        t = self.s.comb(f, x)
        return self.add_term(t, ("a", fk, xk), fty[2][1])

    def some_term(self, depth=0):
        r = self.rng.random()
        if self.tm and r < 0.45:
            return self.rng.randrange(len(self.tm))
        if r < 0.75 or depth > 2:
            return self.var(self.rng.choice(["x", "y", "z", "f", "p"]), self.some_type())
        # a combination: a variable of function type applied to a term
        x = self.some_term(depth + 1)
        f = self.var(self.rng.choice(["f", "g", "h"]), self.fun(self.ty_of[self.tm[x][1]], self.some_type(depth + 1)))
        return self.comb(f, x)

    def eq_term(self, t):
        """The term t = t, built from records."""
        ty = self.ty_of[self.tm[t][1]] if self.tm[t][1] in self.ty_of else None
        if ty is None:
            return None
        e = self.const_eq(ty)
        return self.comb(self.comb(e, t), t)

    def refl(self, t):
        h = self.s.refl(t)
        k = self.tm[t][0]
        self.th.append((k, k))
        return h

    def trans(self, h1, h2):
        assert self.th[h1][1] == self.th[h2][0]
        h = self.s.trans(h1, h2)
        self.th.append((self.th[h1][0], self.th[h2][1]))
        return h

    def expect(self, h):
        l, r = self.th[h]
        # find terms with these structures, building l = r
        tl = self.tm_of.get(l)
        if tl is None:
            return False
        eq = self.eq_term(tl)
        if eq is None or l != r:
            return False
        self.s.expect_alpha(h, [], eq)
        return True

    def step(self):
        r = self.rng.random()
        if r < 0.15:
            self.name(self.rng.choice(["x", "y", "z", "bool", "fun", "=", "A", "q", "c"]))
        elif r < 0.30:
            self.some_type()
        elif r < 0.55:
            self.some_term()
        elif r < 0.70 and self.tm:
            self.refl(self.rng.randrange(len(self.tm)))
        elif r < 0.82 and self.th:
            h1 = self.rng.randrange(len(self.th))
            cands = [h for h in range(len(self.th)) if self.th[h][0] == self.th[h1][1]]
            self.trans(h1, self.rng.choice(cands))
        elif self.th:
            self.expect(self.rng.randrange(len(self.th)))
        elif self.tm:
            self.refl(self.rng.randrange(len(self.tm)))


def valid_stream(rng, steps):
    b = Builder(rng)
    for _ in range(steps):
        b.step()
    return b


# ---- mutations -------------------------------------------------------------------------

def mutate(rng, b, kind):
    """Append one record of the given kind to the builder's stream; return the bytes."""
    s = b.s
    if kind == "comb-types":
        # a variable of type bool applied to a term
        x = b.var("p", b.bool_())
        y = b.some_term()
        s.comb(x, y)
    elif kind == "arity":
        s.tyapp(b.name(rng.choice(["bool", "fun"])), [b.bool_()] * rng.choice([1, 3]))
    elif kind == "undeclared-type":
        s.tyapp(b.name(rng.choice(["x", "A", "="])), [])
    elif kind == "undeclared-const":
        s.const(b.name(rng.choice(["x", "fun", "bool"])), b.bool_())
    elif kind == "not-instance":
        bo = b.bool_()
        a = b.type_var("A")
        choices = [bo, b.fun(bo, bo), b.fun(a, b.fun(bo, bo)), b.fun(bo, b.fun(bo, a)), b.fun(a, a)]
        s.const(b.name("="), rng.choice(choices))
    elif kind == "trans":
        t1 = b.var("x", b.bool_())
        t2 = b.var("y", b.bool_())
        s.trans(b.refl(t1), b.refl(t2))
    elif kind == "expect":
        t = b.some_term()
        h = b.refl(t)
        e = b.eq_term(t)
        if e is None:
            e = t
        if rng.random() < 0.5:
            s.expect_alpha(h, [t], e)          # a hypothesis the theorem does not have
        else:
            other = b.var("z", b.type_var("B"))
            s.expect_alpha(h, [], other)       # another conclusion
    elif kind == "future":
        op = rng.choice(["tyvar", "tyapp", "var", "comb", "refl", "trans", "expect"])
        big = lambda n: n + rng.choice([0, 1, 7, 1000])
        if op == "tyvar":
            s.raw(bytes([TYVAR]) + uv(big(s.names)))
        elif op == "tyapp":
            s.raw(bytes([TYAPP]) + uv(b.name("fun")) + uv(2) + uv(0) + uv(big(s.types)))
        elif op == "var":
            s.raw(bytes([VAR]) + uv(b.name("x")) + uv(big(s.types)))
        elif op == "comb":
            s.raw(bytes([COMB]) + uv(big(s.terms)) + uv(0))
        elif op == "refl":
            s.raw(bytes([REFL]) + uv(big(s.terms)))
        elif op == "trans":
            s.raw(bytes([TRANS]) + uv(0) + uv(big(s.thms)))
        else:
            s.raw(bytes([EXPECT_ALPHA]) + uv(0) + uv(1) + uv(big(s.terms)) + uv(0))
    elif kind == "opcode":
        s.raw(bytes([rng.choice([0x00, 0x08, 0x0f, 0x1a, 0x26, 0x2f, 0x36, 0x43, 0x50, 0x7e, 0x80, 0xff])]))
    elif kind == "outside":
        s.raw(rng.choice([bytes([ABS]) + uv(0) + uv(0), bytes([ASSUME]) + uv(0), bytes([EMIT]) + uv(0),
                          bytes([DROP_TERM]) + uv(0), bytes([0x33]), bytes([0x25]) + uv(1)]))
    elif kind == "leb-nonminimal":
        s.raw(bytes([REFL]) + b"\x80\x00")
    elif kind == "leb-long":
        s.raw(bytes([REFL]) + b"\x80" * 9 + b"\x00")
    elif kind == "leb-big":
        s.raw(bytes([REFL]) + uv(1 << 62))
    elif kind == "list-limit":
        s.raw(bytes([TYAPP]) + uv(0) + uv((1 << 20) + 1))
    elif kind == "name-limit":
        s.raw(bytes([NAME]) + uv((1 << 20) + 1) + b"abc")
    end = {"count": dict(count=s.records + 1), "checksum": dict(checksum=12345),
           "trailing": dict(trailing=b"\x00")}.get(kind, {})
    data = s.finish(**end)
    if kind == "truncate":
        data = data[:rng.randrange(0, len(data))]
    elif kind == "missing-end":
        data = bytes(s.data)
    return data


def flips(rng, body, count, fix):
    """Flip 1 to 3 bits of a stream's records; END keeps the count and gets
    the checksum of the old bytes, or of the new ones (fix)."""
    d = bytearray(body)
    for _ in range(rng.choice([1, 1, 2, 3])):
        i = rng.randrange(len(d))
        d[i] ^= 1 << rng.randrange(8)
    return bytes(d) + bytes([END]) + uv(count) + struct.pack("<Q", fnv1a(bytes(d) if fix else body))


# ---- a structural scan, as CeTTa decodes ----------------------------------------------

def scan(data):
    """(records [(offset, opcode)], reached) up to END, an undecodable record or the end."""
    if len(data) < 40:
        return [], 0
    p = 40
    for _ in range(4):
        v, p = read_uv(data, p)
        if v is None:
            return [], p
    recs = []
    while p < len(data):
        op = data[p]
        recs.append((p, op))
        lay = LAYOUT.get(op)
        if lay is None:
            return recs, p
        q = p + 1
        i = 0
        while i < len(lay):
            c = lay[i]
            if c == "b":
                n, q = read_uv(data, q)
                if n is None:
                    return recs, p
                q += n
            elif c == "c":
                q += 8
            elif c in "*%":
                n, q = read_uv(data, q)
                if n is None or n > (1 << 20):
                    return recs, p
                for _ in range(n * (1 if c == "*" else 2)):
                    v, q = read_uv(data, q)
                    if v is None:
                        return recs, p
                i += 1 if c == "*" else 2
            else:
                v, q = read_uv(data, q)
                if v is None:
                    return recs, p
            i += 1
        if q > len(data):
            return recs, p
        if op == END:
            return recs, q
        p = q
    return recs, p


def read_uv(data, p):
    v = 0
    for i in range(9):
        if p >= len(data):
            return None, p
        b = data[p]
        p += 1
        v |= (b & 0x7f) << (7 * i)
        if not b & 0x80:
            if (i > 0 and b == 0) or v >= (1 << 62):
                return None, p
            return v, p
    return None, p


# ---- CeTTa ------------------------------------------------------------------------------

def cetta_verdict(path):
    r = subprocess.run(["cetta", "--lang", "hol-light", path], capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip().splitlines()
    for line in out:
        line = line.strip()
        if line.startswith("(hol:accepted"):
            return ACCEPTED, 0, int(line[1:-1].split()[1])
        if line == '(hol:refused "probe stream contains refused records")':
            return REFUSED, 0, 0          # a probe stream: the checker's answer is UNSUPPORTED
        if line.startswith("(hol:refused") or line.startswith("(hol:error"):
            # (hol:KIND "STATUS" "REASON" N)
            parts = line[1:-1].split('"')
            status, reason, n = parts[1], parts[3], int(parts[4].strip())
            if line.startswith("(hol:refused"):
                return REFUSED, REASONS.index(reason), n
            if status in ("MALFORMED", "LIMIT"):
                return MALFORMED, REASONS.index(reason), n
            return RESOURCE, REASONS.index(reason), n
    raise RuntimeError("no verdict from CeTTa for %s: %r" % (path, out))


# ---- the test description ----------------------------------------------------------------

# Region sizes (bytes) and R8 sub-ranges (offset, length), in the control
# block's order: name table, type table, db table, N map, Y map, dropped
# marks, stack, memo, sort buffer, theory flags.
SIZES = {2: 16 * 4096, 3: 1 << 16, 4: 16 * 8192, 5: 40 * 8192, 6: 16 * 16384, 7: 16 * 8192}
SUBRANGES = [8 * 4096, 8 * 16384, 8 * 32768, 8 * 8192, 8 * 8192, 0, 8 * 8192, 0, 8 * 8192, 16 * 4096]


def layout_words():
    words, off = [], 0
    for n in SUBRANGES:
        words += [off, n]
        off += n
    return words, off


def header_fields(data):
    """The four header values when magic and kernel id are right and all four
    decode, else None."""
    if len(data) < 40 or data[:8] != MAGIC or data[8:40] != KERNEL_SHA:
        return None
    vals, p = [], 40
    for _ in range(4):
        v, p = read_uv(data, p)
        if v is None:
            return None
        vals.append(v)
    return vals


def expectation(data, verdict):
    """What the checker should report: CeTTa's verdict, or its own UNSUPPORTED
    where the stream leaves the slice first. (state, reason, records, compared)"""
    state, reason, n = verdict
    h = header_fields(data)
    if h is None or h[0] != 1 or h[1] != 0 or h[2] > 2 or h[3] > 1:
        return state, reason, n, True                                # the header decides
    if h[3] == 1:
        return UNSUPPORTED, 102, 0, False                           # a probe stream
    recs, _ = scan(data)
    for i, (off, op) in enumerate(recs):
        if i > n:
            break
        if op in LAYOUT and op not in SLICE:
            return UNSUPPORTED, 103, i, False
    return state, reason, n, True


def main():
    out = sys.argv[1]
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    nrandom = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    nflips = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    rng = random.Random(seed)
    os.makedirs(os.path.join(out, "streams"), exist_ok=True)
    streams = []

    def add(name, data):
        streams.append((name, data))

    kinds = ["comb-types", "arity", "undeclared-type", "undeclared-const", "not-instance", "trans",
             "expect", "future", "opcode", "outside", "leb-nonminimal", "leb-long", "leb-big",
             "list-limit", "name-limit", "count", "checksum", "trailing", "truncate", "missing-end"]
    valid = []
    for i in range(nrandom):
        b = valid_stream(rng, rng.randrange(1, 60))
        data = b.s.finish()
        valid.append((bytes(b.s.data), b.s.records))
        add("valid%d" % i, data)
    for i in range(nrandom // 4):
        for kind in kinds:
            r2 = random.Random(rng.random())
            b = valid_stream(r2, r2.randrange(0, 30))
            add("%s%d" % (kind, i), mutate(r2, b, kind))
    for i in range(nflips):
        body, count = rng.choice(valid)
        add("flip%d" % i, flips(rng, body, count, fix=bool(i % 2)))
    # fixed edge cases
    good = valid[0][0] + bytes([END]) + uv(valid[0][1]) + struct.pack("<Q", fnv1a(valid[0][0]))
    add("empty", b"")
    add("short-magic", good[:5])
    add("bad-magic", b"HOLRPLY2" + good[8:])
    add("short-sha", good[:30])
    add("bad-sha", good[:8] + bytes(32) + good[40:])
    for name, hdr in [("version2", dict(version=2)), ("profile1", dict(profile=1)), ("policy3", dict(policy=3)),
                      ("flags2", dict(flags=2)), ("probe", dict(flags=1)), ("policy2", dict(policy=2)),
                      ("policy1", dict(policy=1))]:
        add("hdr-" + name, Stream(**hdr).finish())
    add("hdr-only", header())
    add("hdr-leb", header()[:40] + b"\x81\x00\x00\x00\x00")
    add("end-only", Stream().finish())
    add("after-end", Stream().finish() + Stream().finish())

    words, work_len = layout_words()
    lines = ["# checker slice: CeTTa's verdict expected from the checker, ref and x86 compared",
             "# regions: 0 stream, 1 control, 2 names, 3 bytes, 4 types, 5 terms, 6 db, 7 theorems, 8 work"]
    tally = {}
    compared = 0
    with open(os.path.join(out, "verdicts.tsv"), "w") as vt:
        for name, data in streams:
            path = os.path.join(out, "streams", name + ".holr")
            with open(path, "wb") as f:
                f.write(data)
            verdict = cetta_verdict(path)
            state, reason, n, cmp_ = expectation(data, verdict)
            compared += cmp_
            key = ("compared " if cmp_ else "outside  ") + {2: "accepted", 3: "refused", 4: "malformed",
                                                              5: "resource", 6: "unsupported"}[state]
            tally[key] = tally.get(key, 0) + 1
            vt.write("%s\t%d\t%s\t%d\t%s\n" % (name, verdict[0], REASONS[verdict[1]], verdict[2],
                                                 "compared" if cmp_ else "outside"))
            lines.append("case %s" % name)
            lines.append("file 0 %s" % path)
            lines.append("region 1 %d" % 640)
            lines.append("words 1 96 " + " ".join(str(w) for w in words))
            for r, size in SIZES.items():
                lines.append("region %d %d" % (r, size))
            lines.append("region 8 %d" % work_len)
            lines.append("expect %s %d" % (OUTCOME[state], n))
            lines.append("want 1 0 %d" % state)
            lines.append("want 1 272 %d" % reason)
            lines.append("run")
    with open(os.path.join(out, "slice.p1t"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("slice_tests: %d streams, %d compared with CeTTa" % (len(streams), compared))
    for k in sorted(tally):
        print("  %-22s %d" % (k, tally[k]))


if __name__ == "__main__":
    main()
