"""A transcription of s2n-bignum's x86 decoder, for building the coverage
table: upstream commit 76604c2, x86/proofs/decode.ml, read as text.

    verdict(bytes) -> dict(status, ctor, length, reason, line)

status is "decoded", "caveat" or "rejected". "decoded" means the reading
says decode returns SOME(instruction, []) on exactly these bytes; ctor
names the instruction constructor (with a size or condition where that
distinguishes forms). "rejected" gives the reason and the decode.ml line
of the clause that returns NONE. Caveats: LZCNT and TZCNT are decoded
whatever CPUID says (on a CPU without ABM or BMI1 the same bytes run as
BSR or BSF); REPNE MOVSB (F2 A4) is decoded as REP MOVSB, which the
manuals do not define (REPNE is for CMPS and SCAS), though upstream's MOVSB
harness cosimulates it against hardware.

This is a reading, not the decoder: the authoritative check is s2n's own
`decode` evaluated in HOL Light on the same bytes.
"""

class Reject(Exception):
    def __init__(self, reason, line):
        self.reason, self.line = reason, line


def reject(reason, line):
    raise Reject(reason, line)


class Bytes:
    def __init__(self, b):
        self.b, self.i = b, 0

    def byte(self, line):
        if self.i >= len(self.b):
            reject("ran out of bytes", line)
        x = self.b[self.i]
        self.i += 1
        return x

    def int32(self, line):
        for _ in range(4):
            self.byte(line)

    def int16(self, line):
        for _ in range(2):
            self.byte(line)

    def int64(self, line):
        for _ in range(8):
            self.byte(line)


# ---- prefixes (decode.ml 45-101) ------------------------------------------

def read_prefixes(s):
    opo, rep, seg = False, None, None
    while True:
        x = s.byte(77)
        if x == 0x66:
            opo = True                                   # 45: repeatable
        elif x in (0xF2, 0xF3):
            if rep is not None:
                reject("second F2/F3 prefix", 51 if x == 0xF3 else 56)
            rep = "z" if x == 0xF3 else "nz"
        elif x in (0x2E, 0x36, 0x3E, 0x26):
            if seg is not None:
                reject("second segment prefix", 61)
            seg = {0x2E: "cs", 0x36: "ss", 0x3E: "ds", 0x26: "es"}[x]
        elif x == 0xF0:
            reject("LOCK prefix", 90)
        elif x == 0x64:
            reject("FS segment prefix", 91)
        elif x == 0x65:
            reject("GS segment prefix", 92)
        elif x == 0x67:
            reject("address-size prefix", 93)
        else:
            s.i -= 1
            return (opo, rep, seg)


def has_pfxs(p):
    return p != (False, None, None)                      # 28


def has_unhandled(p):
    return p[1] is not None or p[2] is not None          # 30-32


def op_size(have_rex, w, v, p):                          # 113-117
    if not v:
        return 8
    if w:
        return 64
    if p[0]:
        return 16
    return 32


def rex_w(rex):
    return rex is not None and bool(rex & 8)


def op_size_W(rex, v, p):                                # 137
    return op_size(rex is not None, rex_w(rex), v, p)


# ---- ModRM, SIB, displacement (161-208) ------------------------------------

def read_ModRM(s, rex, line):
    """Returns (reg3, is_mem); consumes SIB and displacement."""
    m = s.byte(line)
    md, reg, rm = m >> 6, (m >> 3) & 7, m & 7
    if md == 0 and rm == 5:
        s.int32(line)                                    # 197: RIP-relative
        return reg, True
    if md == 3:
        return reg, False                                # 200
    if rm == 4:                                          # 202: SIB
        sib = s.byte(line)
        bs = sib & 7
        if bs == 5 and md == 0:
            s.int32(line)                                # 173
        elif md == 1:
            s.byte(line)
        elif md == 2:
            s.int32(line)
        return reg, True
    if md == 1:
        s.byte(line)
    elif md == 2:
        s.int32(line)
    return reg, True


def read_imm(s, size, line):                             # 143-150
    if size == 8:
        s.byte(line)
    elif size == 16:
        s.int16(line)
    else:
        s.int32(line)                                    # Doubleword and Quadword


def read_full_imm(s, size, line):                        # 152-159
    if size == 8:
        s.byte(line)
    elif size == 16:
        s.int16(line)
    elif size == 32:
        s.int32(line)
    else:
        s.int64(line)


BINOP = ["ADD", "OR", "ADC", "SBB", "AND", "SUB", "XOR", "CMP",
         "ROL", "ROR", "RCL", "RCR", "SHL", "SHR", "TEST", "SAR"]   # 291-297
BT = ["BT", "BTS", "BTR", "BTC"]                         # 299-300
CC = ["O", "NO", "B", "NB", "Z", "NZ", "BE", "NBE",
      "S", "NS", "P", "NP", "L", "NL", "LE", "NLE"]      # 279-289


def sz(n):
    return {8: "8", 16: "16", 32: "32", 64: "64", 128: "x", 256: "y"}[n]


# ---- decode_aux (318-1335) -------------------------------------------------

def decode_aux(s, p, rex):
    b = s.byte(319)
    hi2, mid3, lo3 = b >> 6, (b >> 3) & 7, b & 7

    if hi2 == 0 and (b & 4) == 0:                        # 321 ALU r/m,r
        if has_unhandled(p):
            reject("REP or segment prefix on ALU r/m,r", 321)
        v = bool(b & 1)
        n = op_size_W(rex, v, p)
        read_ModRM(s, rex, 323)
        return "%s%s" % (BINOP[mid3], sz(n))
    if hi2 == 0 and (b & 6) == 4:                        # 326 ALU acc,imm
        if has_unhandled(p):
            reject("REP or segment prefix on ALU acc,imm", 326)
        v = bool(b & 1)
        n = op_size_W(rex, v, p)
        read_imm(s, n, 328)
        return "%s%s" % (BINOP[mid3], sz(n))
    if b == 0x0F:
        return decode_0f(s, p, rex)
    if 0x50 <= b <= 0x57:                                # 626
        if has_pfxs(p):
            reject("prefix on PUSH r64", 626)
        return "PUSH64"
    if 0x58 <= b <= 0x5F:                                # 628
        if has_pfxs(p):
            reject("prefix on POP r64", 628)
        return "POP64"
    if b == 0x63:                                        # 630
        if has_pfxs(p):
            reject("prefix on MOVSXD", 630)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 632)
        return "MOVSX%s_32" % sz(n)
    if b in (0x68, 0x6A):                                # 634
        if has_pfxs(p):
            reject("prefix on PUSH imm", 634)
        read_imm(s, 8 if b == 0x6A else 64, 635)
        return "PUSHimm"
    if b in (0x69, 0x6B):                                # 637
        if has_pfxs(p):
            reject("prefix on IMUL r,r/m,imm", 637)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 639)
        read_imm(s, 8 if b == 0x6B else 64, 640)
        return "IMUL3_%s" % sz(n)
    if 0x70 <= b <= 0x7F:                                # 642
        if has_pfxs(p):
            reject("prefix on Jcc rel8", 642)
        s.byte(643)
        return "J%s" % CC[b & 15]
    if b in (0x80, 0x81):                                # 645
        if has_unhandled(p):
            reject("REP or segment prefix on ALU r/m,imm", 645)
        n = op_size_W(rex, bool(b & 1), p)
        reg, _ = read_ModRM(s, rex, 647)
        read_imm(s, n, 648)
        return "%s%s" % (BINOP[reg], sz(n))
    if b == 0x83:                                        # 650
        if has_unhandled(p):
            reject("REP or segment prefix on ALU r/m,imm8", 650)
        n = op_size_W(rex, True, p)
        reg, _ = read_ModRM(s, rex, 652)
        s.byte(653)
        return "%s%s" % (BINOP[reg], sz(n))
    if b in (0x84, 0x85):                                # 655
        if has_pfxs(p):
            reject("prefix on TEST r/m,r", 655)
        n = op_size_W(rex, bool(b & 1), p)
        read_ModRM(s, rex, 657)
        return "TEST%s" % sz(n)
    if b in (0x86, 0x87):                                # 659
        if has_unhandled(p):
            reject("REP or segment prefix on XCHG r,r/m", 659)
        n = op_size_W(rex, bool(b & 1), p)
        read_ModRM(s, rex, 661)
        return "XCHG%s" % sz(n)
    if 0x88 <= b <= 0x8B:                                # 663
        if has_unhandled(p):
            reject("REP or segment prefix on MOV", 663)
        n = op_size_W(rex, bool(b & 1), p)
        read_ModRM(s, rex, 665)
        return "MOV%s" % sz(n)
    if b == 0x8D:                                        # 668
        if has_pfxs(p):
            reject("prefix on LEA", 668)
        n = op_size(True, rex_w(rex), True, p)
        _, mem = read_ModRM(s, rex, 670)
        if not mem:
            reject("LEA with a register operand", 673)
        return "LEA%s" % sz(n)
    if 0x90 <= b <= 0x97:                                # 674
        if has_unhandled(p):
            reject("REP or segment prefix on 90+r", 674)
        reg = (b & 7) | (8 if rex is not None and rex & 1 else 0)
        if reg == 0:
            return "NOP"                                 # 676
        if p[0]:
            reject("66 prefix on XCHG r,rAX", 677)
        n = op_size_W(rex, True, p)
        return "XCHG%s" % sz(n)
    if b == 0xA4:                                        # 680
        if p == (False, None, None):
            return "MOVSB"
        if p == (False, "z", None):
            return "REP_MOVSB"
        if p == (False, "nz", None):
            return "REPNE_MOVSB"
        reject("66 or segment prefix on MOVSB", 685)
    if b in (0xA8, 0xA9):                                # 686
        if has_pfxs(p):
            reject("prefix on TEST acc,imm", 686)
        n = op_size(True, rex_w(rex), bool(b & 1), p)
        read_imm(s, n, 688)
        return "TEST%s" % sz(n)
    if 0xB0 <= b <= 0xBF:                                # 690
        if has_unhandled(p):
            reject("REP or segment prefix on MOV r,imm", 690)
        n = op_size_W(rex, bool(b & 8), p)
        read_full_imm(s, n, 692)
        return "MOV%s_imm" % sz(n)
    if b in (0xC0, 0xC1):                                # 695
        if has_unhandled(p):
            reject("REP or segment prefix on shift r/m,imm8", 695)
        n = op_size_W(rex, bool(b & 1), p)
        reg, _ = read_ModRM(s, rex, 697)
        if reg == 6:
            reject("C0/C1 /6 (SAL alias)", 698)
        s.byte(699)
        return "%s%s" % (BINOP[8 + reg], sz(n))
    if b == 0xC3:                                        # 701
        if has_pfxs(p):
            reject("prefix on RET", 701)
        return "RET"
    if b in (0xC4, 0xC5):                                # 703
        if has_pfxs(p):
            reject("legacy prefix before VEX", 703)
        if rex is not None:
            reject("REX before VEX", 704)
        return decode_vex(s, b == 0xC5)
    if b in (0xC6, 0xC7):                                # 1302
        if has_unhandled(p):
            reject("REP or segment prefix on MOV r/m,imm", 1302)
        n = op_size_W(rex, bool(b & 1), p)
        reg, _ = read_ModRM(s, rex, 1304)
        if reg != 0:
            reject("C6/C7 with /reg other than 0", 1308)
        read_imm(s, n, 1306)
        return "MOV%s_imm" % sz(n)
    if 0xD0 <= b <= 0xD3:                                # 1309
        if has_pfxs(p):
            reject("prefix on shift r/m,1 or CL", 1309)
        n = op_size_W(rex, bool(b & 1), p)
        reg, _ = read_ModRM(s, rex, 1311)
        if reg == 6:
            reject("D0-D3 /6 (SAL alias)", 1312)
        return "%s%s_%s" % (BINOP[8 + reg], sz(n), "CL" if b & 2 else "1")
    if b == 0xE8:                                        # 1315
        if has_pfxs(p):
            reject("prefix on CALL rel32", 1315)
        s.int32(1316)
        return "CALL"
    if b in (0xE9, 0xEB):                                # 1318
        if has_pfxs(p):
            reject("prefix on JMP rel", 1318)
        read_imm(s, 8 if b == 0xEB else 64, 1319)
        return "JMP"
    if b in (0xF5, 0xF8, 0xF9, 0xFC, 0xFD):              # 1321-1330
        if has_pfxs(p):
            reject("prefix on flag instruction", 1321)
        return {0xF5: "CMC", 0xF8: "CLC", 0xF9: "STCF", 0xFC: "CLD", 0xFD: "STD"}[b]
    if b in (0xF6, 0xF7, 0xFE, 0xFF):                    # 1331
        if has_pfxs(p):
            reject("prefix on F6/F7/FE/FF group", 1331)
        x, v = bool(b & 8), bool(b & 1)
        n = op_size_W(rex, v, p)
        reg, _ = read_ModRM(s, rex, 1333)
        return decode_hi(s, x, v, n, reg)
    reject("no clause for opcode %02X" % b, 1335)


def decode_hi(s, x, v, n, opc):                          # 302-316
    if not x:
        if opc == 0:
            read_imm(s, n, 304)
            return "TEST%s" % sz(n)
        if opc in (2, 3, 4, 5):
            return "%s%s" % ({2: "NOT", 3: "NEG", 4: "MUL2_", 5: "IMUL2_"}[opc], sz(n))
        reject({1: "F6/F7 /1 (TEST alias)", 6: "DIV", 7: "IDIV"}[opc], 316)
    if opc in (0, 1):
        return "%s%s" % ("INC" if opc == 0 else "DEC", sz(n))
    if v and opc == 2:
        reject("indirect CALL (FF /2)", 313)
    if v and opc == 4:
        reject("indirect JMP (FF /4)", 313)
    if v and opc == 6:
        reject("PUSH r/m (FF /6)", 313)
    if v and opc in (3, 5):
        reject("far CALL/JMP (FF /3, /5)", 316)
    reject("FE/FF /%d" % opc, 316)


def need66(p, what, line):
    if p != (True, None, None):
        reject("%s needs exactly the 66 prefix" % what, line)


def decode_0f(s, p, rex):                                # 330-625
    b = s.byte(330)
    if b in (0x10, 0x11):                                # 332
        if has_pfxs(p):
            reject("prefix on 0F 10/11 (only MOVUPS)", 332)
        read_ModRM(s, rex, 334)
        return "MOVUPS"
    if b == 0x1E:                                        # 339
        x = s.byte(340)
        if x != 0xFA:
            reject("0F 1E other than ENDBR64", 346)
        if p != (False, "z", None):
            reject("0F 1E FA without exactly F3", 345)
        return "ENDBR64"
    if b == 0x1F:                                        # 347
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 349)
        if p[1] is not None:
            reject("F2/F3 prefix on NOP r/m", 361)
        return "NOP_N%s" % sz(n)
    if b in (0x28, 0x29):                                # 362
        if has_pfxs(p):
            reject("prefix on 0F 28/29 (only MOVAPS)", 362)
        read_ModRM(s, rex, 364)
        return "MOVAPS"
    if b == 0x38:                                        # 369
        c = s.byte(369)
        if c in (0x00, 0xDC, 0xDD, 0xDE, 0xDF):
            read_ModRM(s, rex, 373)
            need66(p, "0F 38 %02X" % c, 376)
            return {0x00: "PSHUFB", 0xDC: "AESENC", 0xDD: "AESENCLAST",
                    0xDE: "AESDEC", 0xDF: "AESDECLAST"}[c]
        if c == 0xF6:                                    # 401
            n = 64 if rex_w(rex) else 32
            read_ModRM(s, rex, 403)
            if p == (True, None, None):
                return "ADCX%s" % sz(n)
            if p == (False, "z", None):
                return "ADOX%s" % sz(n)
            reject("0F 38 F6 without exactly 66 or F3", 407)
        reject("no clause for 0F 38 %02X" % c, 408)
    if b == 0x3A:                                        # 409
        c = s.byte(409)
        if c in (0x0E, 0xDF):
            read_ModRM(s, rex, 413)
            s.byte(414)
            need66(p, "0F 3A %02X" % c, 417)
            return {0x0E: "PBLENDW", 0xDF: "AESKEYGENASSIST"}[c]
        if c == 0x22:                                    # 418
            if has_unhandled(p):
                reject("REP or segment prefix on PINSRD/Q", 418)
            read_ModRM(s, rex, 419)
            s.byte(420)
            need66(p, "PINSRD/Q", 428)
            return "PINSRQ" if rex_w(rex) else "PINSRD"
        reject("no clause for 0F 3A %02X" % c, 436)
    if 0x40 <= b <= 0x4F:                                # 437
        if has_pfxs(p):
            reject("prefix on CMOVcc", 437)
        n = op_size(True, rex_w(rex), True, p)
        read_ModRM(s, rex, 439)
        return "CMOV%s%s" % (CC[b & 15], sz(n))
    if b in (0x65, 0x66):                                # 441, 447
        read_ModRM(s, rex, 443)
        need66(p, "PCMPGTW/D", 446)
        return "PCMPGTW" if b == 0x65 else "PCMPGTD"
    if b == 0x6E:                                        # 453
        if has_unhandled(p):
            reject("REP or segment prefix on 0F 6E", 453)
        read_ModRM(s, rex, 454)
        need66(p, "MOVD/MOVQ xmm,r/m", 461)
        return "MOVQ_to_xmm" if rex_w(rex) else "MOVD_to_xmm"
    if b in (0x6F, 0x7F):                                # 462
        read_ModRM(s, rex, 464)
        if p == (True, None, None):
            return "MOVDQA"
        if p == (False, "z", None):
            return "MOVDQU"
        reject("0F 6F/7F without exactly 66 or F3", 471)
    if b == 0x70:                                        # 472
        read_ModRM(s, rex, 474)
        s.byte(475)
        need66(p, "PSHUFD", 478)
        return "PSHUFD"
    if b in (0x71, 0x72):                                # 479, 491
        reg, mem = read_ModRM(s, rex, 481)
        if p != (True, None, None):
            reject("0F %02X without exactly 66" % b, 490)
        if mem:
            reject("0F %02X with a memory operand" % b, 489)
        want = 2 if b == 0x71 else 4
        if reg != want:
            reject("0F %02X /%d" % (b, reg), 488)
        s.byte(486)
        return "PSRLW" if b == 0x71 else "PSRAD"
    if b == 0x7E:                                        # 503
        reg, mem = read_ModRM(s, rex, 504)
        if p == (True, None, None):
            return "MOVQ_from_xmm" if rex_w(rex) else "MOVD_from_xmm"
        if p == (False, "z", None):
            return "MOVQ_xmm_load"
        reject("0F 7E without exactly 66 or F3", 520)
    if 0x80 <= b <= 0x8F:                                # 521
        if has_pfxs(p):
            reject("prefix on Jcc rel32", 521)
        s.int32(522)
        return "J%s" % CC[b & 15]
    if 0x90 <= b <= 0x9F:                                # 524
        if has_pfxs(p):
            reject("prefix on SETcc", 524)
        read_ModRM(s, rex, 526)
        return "SET%s" % CC[b & 15]
    if b in (0xA3, 0xAB, 0xB3, 0xBB):                    # 528
        if has_pfxs(p):
            reject("prefix on BT* r/m,r", 528)
        n = op_size_W(rex, True, p)
        _, mem = read_ModRM(s, rex, 530)
        if mem:
            reject("BT* with a memory destination and register bit offset", 531)
        return "%s%s" % (BT[(b >> 3) & 3], sz(n))
    if b in (0xA4, 0xAC):                                # 533
        if has_pfxs(p):
            reject("prefix on SHLD/SHRD imm8", 533)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 535)
        s.byte(536)
        return "%s%s" % ("SHRD" if b == 0xAC else "SHLD", sz(n))
    if b in (0xA5, 0xAD):                                # 538
        if has_pfxs(p):
            reject("prefix on SHLD/SHRD CL", 538)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 540)
        return "%s%s_CL" % ("SHRD" if b == 0xAD else "SHLD", sz(n))
    if b == 0xAF:                                        # 542
        if has_pfxs(p):
            reject("prefix on IMUL r,r/m", 542)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 544)
        return "IMUL%s" % sz(n)
    if b == 0xB8:                                        # 546
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 548)
        if p == (False, "z", None):
            return "POPCNT%s" % sz(n)
        reject("0F B8 without exactly F3", 551)
    if b == 0xBA:                                        # 552
        if has_pfxs(p):
            reject("prefix on BT* r/m,imm8", 552)
        n = op_size_W(rex, True, p)
        reg, _ = read_ModRM(s, rex, 554)
        if reg < 4:
            reject("0F BA /%d" % reg, 559)
        s.byte(557)
        return "%s%s_imm" % (BT[reg & 3], sz(n))
    if b in (0xBC, 0xBD):                                # 560, 567
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 562)
        if p == (False, None, None):
            return "%s%s" % ("BSF" if b == 0xBC else "BSR", sz(n))
        if p == (False, "z", None):
            return "%s%s" % ("TZCNT" if b == 0xBC else "LZCNT", sz(n))
        reject("0F %02X with a prefix other than one F3" % b, 566)
    if b in (0xB6, 0xB7, 0xBE, 0xBF):                    # 574
        if has_pfxs(p):
            reject("prefix on MOVZX/MOVSX", 574)
        n = op_size_W(rex, True, p)
        read_ModRM(s, rex, 577)
        return "%s%s_%s" % ("MOVSX" if b & 8 else "MOVZX", sz(n), "16" if b & 1 else "8")
    if 0xC8 <= b <= 0xCF:                                # 580
        if has_pfxs(p):
            reject("prefix on BSWAP", 580)
        return "BSWAP%s" % sz(op_size_W(rex, True, p))
    if b in (0xD4, 0xDB, 0xEF, 0xFE):                    # 584-624
        read_ModRM(s, rex, 586)
        need66(p, "0F %02X" % b, 589)
        return {0xD4: "PADDQ", 0xDB: "PAND", 0xEF: "PXOR", 0xFE: "PADDD"}[b]
    if b == 0xD6:                                        # 590
        read_ModRM(s, rex, 591)
        need66(p, "MOVQ xmm/m64,xmm", 598)
        return "MOVQ_store"
    if b == 0xD7:                                        # 599
        _, mem = read_ModRM(s, rex, 600)
        if mem:
            reject("PMOVMSKB with a memory operand", 601)
        need66(p, "PMOVMSKB", 606)
        return "PMOVMSKB"
    reject("no clause for 0F %02X" % b, 625)


# ---- VEX (264-273, 703-1301) -----------------------------------------------

def decode_vex(s, two):
    if two:                                              # 265: C5
        x = s.byte(266)
        R = not (x >> 7)
        rex = (4 if R else 0)
        m = 1
    else:                                                # 269: C4
        x = s.byte(270)
        rxb = (~x >> 5) & 7
        m = x & 31
        x = s.byte(271)
        rex = ((x >> 7) << 3) | rxb
        if m not in (1, 2, 3):
            reject("VEX map other than 0F, 0F38, 0F3A", 255)
    vvvv_enc = (x >> 3) & 15
    L = bool(x & 4)
    pp = x & 3
    W = bool(rex & 8)
    unused = vvvv_enc == 15
    op = s.byte(708)
    name = "VEX.%s.%s.%02X" % ({1: "0F", 2: "0F38", 3: "0F3A"}[m], "L1" if L else "L0", op)

    def need(cond, why, line):
        if not cond:
            reject("%s: %s" % (name, why), line)

    def modrm(line):
        return read_ModRM(s, rex, line)

    if m == 2:                                           # 707 VEXM_0F38
        simple = {0x00: "VPSHUFB", 0x04: "VPMADDUBSW", 0x0B: "VPMULHRSW",
                  0x28: "VPMULDQ", 0x40: "VPMULLD"}
        if op in simple:
            modrm(712)
            need(pp == 1, "needs 66", 715)
            return simple[op]
        if op in (0x17, 0x1E, 0x21, 0x30, 0x31):
            need(unused, "vvvv must be 1111", 734)
            modrm(730)
            need(pp == 1, "needs 66", 733)
            return {0x17: "VPTEST", 0x1E: "VPABSD", 0x21: "VPMOVSXBD",
                    0x30: "VPMOVZXBW", 0x31: "VPMOVZXBD"}[op]
        if op == 0x36:                                   # 781
            need(L, "VPERMD needs L1", 789)
            modrm(784)
            need(not W, "VPERMD needs W0", 785)
            need(pp == 1, "needs 66", 788)
            return "VPERMD"
        if op == 0x45:                                   # 790
            modrm(792)
            need(pp == 1, "needs 66", 799)
            return "VPSRLVQ" if W else "VPSRLVD"
        if op == 0x47:                                   # 800
            modrm(802)
            need(not W, "VPSLLVD needs W0", 803)
            need(pp == 1, "needs 66", 806)
            return "VPSLLVD"
        if op in (0x58, 0x59, 0x79):                     # 807-839
            need(unused, "vvvv must be 1111", 817)
            modrm(809)
            need(not W, "broadcast needs W0", 810)
            need(pp == 1, "needs 66", 816)
            return {0x58: "VPBROADCASTD", 0x59: "VPBROADCASTQ", 0x79: "VPBROADCASTW"}[op]
        if op == 0xF5:                                   # 846
            modrm(848)
            need(pp == 2, "0F38 F5 is decoded only as PEXT (F3)", 853)
            need(not L, "PEXT needs L0", 851)
            return "PEXT%s" % ("64" if W else "32")
        if op == 0xF6:                                   # 854
            modrm(856)
            need(pp == 3, "0F38 F6 is decoded only as MULX (F2)", 861)
            need(not L, "MULX needs L0", 859)
            return "MULX%s" % ("64" if W else "32")
        reject("no clause for %s" % name, 862)
    if m == 1:                                           # 863 VEXM_0F
        if op in (0x12, 0x16):                           # 866, 891
            need(unused, "vvvv must be 1111", 872)
            modrm(868)
            need(pp == 2, "needs F3", 871)
            return "VMOVSLDUP" if op == 0x12 else "VMOVSHDUP"
        if op in (0x50, 0xD7):                           # 873, 882
            need(unused and L, "needs vvvv=1111 and L1", 881)
            _, mem = modrm(874)
            need(not mem, "register source only", 875)
            need(pp == (0 if op == 0x50 else 1), "wrong pp", 880)
            return "VMOVMSKPS" if op == 0x50 else "VPMOVMSKB"
        if op == 0x17:                                   # 898
            need(unused, "vvvv must be 1111", 909)
            need(not L, "needs L0", 899)
            _, mem = modrm(900)
            need(pp == 1, "needs 66", 908)
            need(mem, "VMOVHPD store needs a memory destination", 907)
            return "VMOVHPD"
        if op == 0x77:                                   # 910
            need(unused, "vvvv must be 1111", 915)
            need(not L, "VZEROALL (L1) is not decoded", 911)
            need(pp == 0, "needs no pp", 914)
            return "VZEROUPPER"
        three = {0x6C: "VPUNPCKLQDQ", 0x6D: "VPUNPCKHQDQ", 0x67: "VPACKUSWB",
                 0x65: "VPCMPGTW", 0x66: "VPCMPGTD", 0xD4: "VPADDQ", 0xD5: "VPMULLW",
                 0xDB: "VPAND", 0xDF: "VPANDN", 0xE4: "VPMULHUW", 0xE5: "VPMULHW",
                 0xEB: "VPOR", 0xEF: "VPXOR", 0xF5: "VPMADDWD", 0xF8: "VPSUBB",
                 0xF9: "VPSUBW", 0xFA: "VPSUBD", 0xFB: "VPSUBQ", 0xFC: "VPADDB",
                 0xFD: "VPADDW", 0xFE: "VPADDD"}
        if op in three:
            modrm(918)
            need(pp == 1, "needs 66", 921)
            return three[op]
        if op == 0x6E:                                   # 934
            need(unused, "vvvv must be 1111", 948)
            need(not L, "needs L0", 935)
            modrm(936)
            need(pp == 1, "needs 66", 947)
            return "VMOVQ_to_xmm" if W else "VMOVD_to_xmm"
        if op in (0x6F, 0x7F):                           # 949, 977
            need(unused, "vvvv must be 1111", 956)
            modrm(951)
            if pp == 1:
                return "VMOVDQA"
            if pp == 2:
                return "VMOVDQU"
            reject("%s: needs 66 or F3" % name, 955)
        if op == 0x7E:                                   # 957
            need(unused, "vvvv must be 1111", 976)
            need(not L, "needs L0", 958)
            modrm(959)
            if pp == 1:
                return "VMOVQ_from_xmm" if W else "VMOVD_from_xmm"
            if pp == 2:
                return "VMOVQ_xmm_load"
            reject("%s: needs 66 or F3" % name, 975)
        if op in (0x71, 0x72, 0x73):                     # 1093-1140
            reg, mem = modrm(1095)
            need(not mem, "register operand only", 1108)
            s.byte(1098)
            need(pp == 1, "needs 66", 1107)
            table = {0x71: {2: "VPSRLW", 4: "VPSRAW", 6: "VPSLLW"},
                     0x72: {2: "VPSRLD", 4: "VPSRAD", 6: "VPSLLD"},
                     0x73: {2: "VPSRLQ", 3: "VPSRLDQ", 6: "VPSLLQ"}}[op]
            need(reg in table, "/%d is not decoded" % reg, 1106)
            return table[reg]
        if op == 0xC4:                                   # 1141
            need(not L, "needs L0", 1142)
            modrm(1143)
            s.byte(1144)
            need(pp == 1, "needs 66", 1151)
            return "VPINSRW"
        if op == 0xC5:                                   # 1152
            need(unused, "vvvv must be 1111", 1164)
            need(not L, "needs L0", 1154)
            _, mem = modrm(1155)
            need(not mem, "register source only", 1156)
            s.byte(1157)
            need(not W, "needs W0", 1158)
            need(pp == 1, "needs 66", 1163)
            return "VPEXTRW"
        if op == 0xD6:                                   # 1165
            need(unused, "vvvv must be 1111", 1175)
            need(not L, "needs L0", 1166)
            modrm(1167)
            need(pp == 1, "needs 66", 1174)
            return "VMOVQ_store"
        reject("no clause for %s" % name, 1176)
    # m == 3, VEXM_0F3A                                  # 1177
    if op == 0x00:                                       # 1180
        need(unused, "vvvv must be 1111", 1191)
        need(L, "VPERMQ needs L1", 1190)
        modrm(1183)
        s.byte(1184)
        need(W, "VPERMQ needs W1", 1189)
        need(pp == 1, "needs 66", 1188)
        return "VPERMQ"
    if op in (0x02, 0x0E):                               # 1192, 1200
        modrm(1194)
        s.byte(1195)
        if op == 0x02:
            need(not W, "VPBLENDD needs W0", 1196)
        need(pp == 1, "needs 66", 1199)
        return "VPBLENDD" if op == 0x02 else "VPBLENDW"
    if op == 0x15:                                       # 1207
        need(unused, "vvvv must be 1111", 1219)
        need(not L, "needs L0", 1209)
        modrm(1210)
        s.byte(1211)
        need(not W, "needs W0", 1212)
        need(pp == 1, "needs 66", 1218)
        return "VPEXTRW"
    if op == 0x16:                                       # 1220
        need(unused, "vvvv must be 1111", 1233)
        need(not L, "needs L0", 1222)
        modrm(1223)
        s.byte(1224)
        need(pp == 1, "needs 66", 1232)
        return "VPEXTRQ" if W else "VPEXTRD"
    if op == 0x22:                                       # 1234
        need(not L, "needs L0", 1235)
        modrm(1236)
        s.byte(1237)
        need(pp == 1, "needs 66", 1246)
        return "VPINSRQ" if W else "VPINSRD"
    if op == 0x38:                                       # 1247
        need(L, "VINSERTI128 needs L1", 1260)
        modrm(1250)
        s.byte(1251)
        need(not W, "needs W0", 1252)
        need(pp == 1, "needs 66", 1259)
        return "VINSERTI128"
    if op == 0x39:                                       # 1261
        need(unused, "vvvv must be 1111", 1274)
        need(L, "VEXTRACTI128 needs L1", 1273)
        modrm(1265)
        s.byte(1266)
        need(not W, "needs W0", 1267)
        need(pp == 1, "needs 66", 1272)
        return "VEXTRACTI128"
    if op == 0x44:                                       # 1275
        modrm(1277)
        s.byte(1278)
        need(pp == 1, "needs 66", 1281)
        return "VPCLMULQDQ"
    if op == 0x46:                                       # 1282
        need(L, "VPERM2I128 needs L1", 1291)
        modrm(1285)
        s.byte(1286)
        need(not W, "needs W0", 1287)
        need(pp == 1, "needs 66", 1290)
        return "VPERM2I128"
    if op == 0x4C:                                       # 1292
        modrm(1294)
        s.byte(1295)
        need(not W, "needs W0", 1296)
        need(pp == 1, "needs 66", 1299)
        return "VPBLENDVB"
    reject("no clause for %s" % name, 1300)


# ---- decode (1337-1340) ----------------------------------------------------

def verdict(b):
    s = Bytes(b)
    try:
        p = read_prefixes(s)
        rex = None
        if s.i < len(b) and (b[s.i] >> 4) == 4:          # 96-101
            rex = b[s.i] & 15
            s.i += 1
        ctor = decode_aux(s, p, rex)
    except Reject as e:
        return dict(status="rejected", ctor="", length=s.i, reason=e.reason, line=e.line)
    if s.i != len(b):
        return dict(status="rejected", ctor=ctor, length=s.i,
                    reason="decoder consumes %d of %d bytes" % (s.i, len(b)), line=1337)
    if ctor.startswith(("LZCNT", "TZCNT")):
        return dict(status="caveat", ctor=ctor, length=s.i, line=565 if ctor[0] == "T" else 572,
                    reason="decoded whatever CPUID says: without %s the bytes run as %s"
                    % ("BMI1" if ctor[0] == "T" else "ABM/LZCNT", "BSF" if ctor[0] == "T" else "BSR"))
    if ctor == "REPNE_MOVSB":
        return dict(status="caveat", ctor=ctor, length=s.i, line=684,
                    reason="F2 A4 is decoded as REP MOVSB; the manuals define REPNE only for CMPS and SCAS "
                           "(upstream cosimulates it, simulator.ml:2050)")
    return dict(status="decoded", ctor=ctor, length=s.i, reason="", line=0)


if __name__ == "__main__":
    import sys
    for line in sys.stdin:
        hx = line.split()[0] if line.strip() else ""
        if not hx:
            continue
        v = verdict(bytes.fromhex(hx))
        print("%s\t%s\t%s\t%s\t%s" % (hx, v["status"], v["ctor"], v["line"], v["reason"]))
