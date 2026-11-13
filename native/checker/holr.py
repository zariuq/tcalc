"""holr.py -- writing HOLR v1 streams (CeTTa docs/hol_light_stream.txt), for tests.

A Stream collects records; finish() appends END with the record count and
the FNV-1a 64 checksum of every byte before END's opcode. Ids are the
caller's: each space counts from 0 in definition order.
"""
import struct

KERNEL_SHA = bytes([0x29, 0x54, 0x4b, 0xe9, 0x2d, 0x9c, 0xc1, 0xe6, 0xb3, 0xb5, 0x9b, 0xa5,
                    0xb2, 0x10, 0x60, 0x4b, 0x9a, 0x74, 0x83, 0x66, 0xa6, 0x8b, 0x3b, 0xcd,
                    0xc2, 0x61, 0x97, 0x17, 0xd6, 0x8f, 0xd9, 0x8a])
MAGIC = b"HOLRPLY1"
FNV_OFFSET, FNV_PRIME = 0xcbf29ce484222325, 0x100000001b3

NAME, TYVAR, TYAPP, VAR, CONST, COMB, ABS = 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
REFL, TRANS, MK_COMB, ABS_RULE, BETA, ASSUME, EQ_MP, DEDUCT = 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17
EXPECT, LABEL, EMIT, EXPECT_REFUSED, EXPECT_AXIOMS, EXPECT_ALPHA = 0x30, 0x31, 0x32, 0x33, 0x34, 0x35
DROP_TYPE, DROP_TERM, DROP_THM, END = 0x40, 0x41, 0x42, 0x7f


def fnv1a(data, h=FNV_OFFSET):
    for b in data:
        h = ((h ^ b) * FNV_PRIME) & 0xFFFFFFFFFFFFFFFF
    return h


def uv(v):
    """Unsigned LEB128, minimal form."""
    assert 0 <= v
    out = bytearray()
    while True:
        b = v & 0x7f
        v >>= 7
        if v:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def header(version=1, profile=0, policy=0, flags=0, magic=MAGIC, sha=KERNEL_SHA):
    return magic + sha + uv(version) + uv(profile) + uv(policy) + uv(flags)


class Stream:
    def __init__(self, **hdr):
        self.data = bytearray(header(**hdr))
        self.records = 0
        self.names = self.types = self.terms = self.thms = 0

    def raw(self, rec):
        """One encoded record, counted."""
        self.data += rec
        self.records += 1

    def name(self, text):
        b = text.encode() if isinstance(text, str) else bytes(text)
        self.raw(bytes([NAME]) + uv(len(b)) + b)
        self.names += 1
        return self.names - 1

    def tyvar(self, n):
        self.raw(bytes([TYVAR]) + uv(n)); self.types += 1; return self.types - 1

    def tyapp(self, n, args):
        self.raw(bytes([TYAPP]) + uv(n) + uv(len(args)) + b"".join(uv(a) for a in args))
        self.types += 1; return self.types - 1

    def var(self, n, y):
        self.raw(bytes([VAR]) + uv(n) + uv(y)); self.terms += 1; return self.terms - 1

    def const(self, n, y):
        self.raw(bytes([CONST]) + uv(n) + uv(y)); self.terms += 1; return self.terms - 1

    def comb(self, f, x):
        self.raw(bytes([COMB]) + uv(f) + uv(x)); self.terms += 1; return self.terms - 1

    def refl(self, t):
        self.raw(bytes([REFL]) + uv(t)); self.thms += 1; return self.thms - 1

    def trans(self, h1, h2):
        self.raw(bytes([TRANS]) + uv(h1) + uv(h2)); self.thms += 1; return self.thms - 1

    def expect_alpha(self, h, hyps, concl):
        self.raw(bytes([EXPECT_ALPHA]) + uv(h) + uv(len(hyps)) + b"".join(uv(t) for t in hyps) + uv(concl))

    def finish(self, count=None, checksum=None, trailing=b""):
        sum_ = fnv1a(self.data) if checksum is None else checksum
        n = self.records if count is None else count
        return bytes(self.data) + bytes([END]) + uv(n) + struct.pack("<Q", sum_) + trailing
