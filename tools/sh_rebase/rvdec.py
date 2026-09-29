"""RV64IMC decoder emitting the Lean Sail AST in the EXPANDED form the
per-pc facts state (`c.sdsp` is `STORE`, `c.mv` is `RTYPE … ADD`, ...).
Validated against every existing fact (see check_old)."""


def bits(x, hi, lo):
    return (x >> lo) & ((1 << (hi - lo + 1)) - 1)


def sext(v, n):
    return v - (1 << n) if v & (1 << (n - 1)) else v


def u(v, n):  # the Lean `k#n` literal of a signed value v
    return '%d#%d' % (v % (1 << n), n)


def R(r):
    return '.Regidx %d#5' % r


def decode(enc, w):
    if w == 2:
        return decode_c(enc)
    return decode_32(enc)


def decode_32(i):
    op = bits(i, 6, 0); rd = bits(i, 11, 7); f3 = bits(i, 14, 12); rs1 = bits(i, 19, 15)
    rs2 = bits(i, 24, 20); f7 = bits(i, 31, 25)
    immI = bits(i, 31, 20)
    if op == 0x37:
        return '.UTYPE (%s, %s, .LUI)' % (u(bits(i, 31, 12), 20), R(rd))
    if op == 0x17:
        return '.UTYPE (%s, %s, .AUIPC)' % (u(bits(i, 31, 12), 20), R(rd))
    if op == 0x6f:
        imm = (bits(i, 31, 31) << 20) | (bits(i, 19, 12) << 12) | (bits(i, 20, 20) << 11) | (bits(i, 30, 21) << 1)
        return '.JAL (%s, %s)' % (u(imm, 21), R(rd))
    if op == 0x67 and f3 == 0:
        return '.JALR (%s, %s, %s)' % (u(immI, 12), R(rs1), R(rd))
    if op == 0x63:
        imm = (bits(i, 31, 31) << 12) | (bits(i, 7, 7) << 11) | (bits(i, 30, 25) << 5) | (bits(i, 11, 8) << 1)
        o = {0: 'BEQ', 1: 'BNE', 4: 'BLT', 5: 'BGE', 6: 'BLTU', 7: 'BGEU'}[f3]
        return '.BTYPE (%s, %s, %s, .%s)' % (u(imm, 13), R(rs2), R(rs1), o)
    if op == 0x03:
        wd = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}[f3]
        return '.LOAD (%s, %s, %s, %s, %d)' % (u(immI, 12), R(rs1), R(rd), 'true' if f3 >= 4 else 'false', wd)
    if op == 0x23:
        imm = (bits(i, 31, 25) << 5) | bits(i, 11, 7)
        return '.STORE (%s, %s, %s, %d)' % (u(imm, 12), R(rs2), R(rs1), 1 << f3)
    if op == 0x13:
        if f3 in (1, 5):
            sh = bits(i, 25, 20); hi = bits(i, 31, 26)
            o = 'SLLI' if f3 == 1 else ('SRAI' if hi == 0x10 else 'SRLI')
            return '.SHIFTIOP (%s, %s, %s, .%s)' % (u(sh, 6), R(rs1), R(rd), o)
        o = {0: 'ADDI', 2: 'SLTI', 3: 'SLTIU', 4: 'XORI', 6: 'ORI', 7: 'ANDI'}[f3]
        return '.ITYPE (%s, %s, %s, .%s)' % (u(immI, 12), R(rs1), R(rd), o)
    if op == 0x1b:
        if f3 == 0:
            return '.ADDIW (%s, %s, %s)' % (u(immI, 12), R(rs1), R(rd))
        sh = bits(i, 24, 20)
        o = 'SLLIW' if f3 == 1 else ('SRAIW' if f7 == 0x20 else 'SRLIW')
        return '.SHIFTIWOP (%s, %s, %s, .%s)' % (u(sh, 5), R(rs1), R(rd), o)
    if op == 0x33:
        if f7 == 1:
            o = ['MUL', 'MULH', 'MULHSU', 'MULHU', 'DIV', 'DIVU', 'REM', 'REMU'][f3]
            return None  # not stated by these facts
        o = {(0, 0): 'ADD', (0x20, 0): 'SUB', (0, 1): 'SLL', (0, 2): 'SLT', (0, 3): 'SLTU', (0, 4): 'XOR',
             (0, 5): 'SRL', (0x20, 5): 'SRA', (0, 6): 'OR', (0, 7): 'AND'}[(f7, f3)]
        return '.RTYPE (%s, %s, %s, .%s)' % (R(rs2), R(rs1), R(rd), o)
    if op == 0x3b:
        if f7 == 1:
            return None
        o = {(0, 0): 'ADDW', (0x20, 0): 'SUBW', (0, 1): 'SLLW', (0, 5): 'SRLW', (0x20, 5): 'SRAW'}[(f7, f3)]
        return '.RTYPEW (%s, %s, %s, .%s)' % (R(rs2), R(rs1), R(rd), o)
    if i == 0x00000073:
        return '.ECALL ()'
    return None


def decode_c(i):
    q = bits(i, 1, 0); f3 = bits(i, 15, 13)
    rdp = bits(i, 4, 2) + 8; rs1p = bits(i, 9, 7) + 8
    rd = bits(i, 11, 7); rs2 = bits(i, 6, 2)
    if q == 0:
        if f3 == 0:
            imm = (bits(i, 10, 7) << 6) | (bits(i, 12, 11) << 4) | (bits(i, 5, 5) << 3) | (bits(i, 6, 6) << 2)
            return '.ITYPE (%s, %s, %s, .ADDI)' % (u(imm, 12), R(2), R(rdp))
        if f3 == 2:
            imm = (bits(i, 5, 5) << 6) | (bits(i, 12, 10) << 3) | (bits(i, 6, 6) << 2)
            return '.LOAD (%s, %s, %s, false, 4)' % (u(imm, 12), R(rs1p), R(rdp))
        if f3 == 3:
            imm = (bits(i, 6, 5) << 6) | (bits(i, 12, 10) << 3)
            return '.LOAD (%s, %s, %s, false, 8)' % (u(imm, 12), R(rs1p), R(rdp))
        if f3 == 6:
            imm = (bits(i, 5, 5) << 6) | (bits(i, 12, 10) << 3) | (bits(i, 6, 6) << 2)
            return '.STORE (%s, %s, %s, 4)' % (u(imm, 12), R(rdp), R(rs1p))
        if f3 == 7:
            imm = (bits(i, 6, 5) << 6) | (bits(i, 12, 10) << 3)
            return '.STORE (%s, %s, %s, 8)' % (u(imm, 12), R(rdp), R(rs1p))
        return None
    if q == 1:
        imm6 = sext((bits(i, 12, 12) << 5) | bits(i, 6, 2), 6)
        if f3 == 0:
            if rd == 0:
                return None  # c.nop
            return '.ITYPE (%s, %s, %s, .ADDI)' % (u(imm6, 12), R(rd), R(rd))
        if f3 == 1:
            return '.ADDIW (%s, %s, %s)' % (u(imm6, 12), R(rd), R(rd))
        if f3 == 2:
            return '.ITYPE (%s, %s, %s, .ADDI)' % (u(imm6, 12), R(0), R(rd))
        if f3 == 3:
            if rd == 2:
                imm = sext((bits(i, 12, 12) << 9) | (bits(i, 4, 3) << 7) | (bits(i, 5, 5) << 6) |
                           (bits(i, 2, 2) << 5) | (bits(i, 6, 6) << 4), 10)
                return '.ITYPE (%s, %s, %s, .ADDI)' % (u(imm, 12), R(2), R(2))
            return '.UTYPE (%s, %s, .LUI)' % (u(imm6, 20), R(rd))
        if f3 == 4:
            f2 = bits(i, 11, 10)
            if f2 == 0:
                return '.SHIFTIOP (%s, %s, %s, .SRLI)' % (u((bits(i, 12, 12) << 5) | bits(i, 6, 2), 6), R(rs1p), R(rs1p))
            if f2 == 1:
                return '.SHIFTIOP (%s, %s, %s, .SRAI)' % (u((bits(i, 12, 12) << 5) | bits(i, 6, 2), 6), R(rs1p), R(rs1p))
            if f2 == 2:
                return '.ITYPE (%s, %s, %s, .ANDI)' % (u(imm6, 12), R(rs1p), R(rs1p))
            o2 = bits(i, 6, 5)
            if bits(i, 12, 12) == 0:
                o = ['SUB', 'XOR', 'OR', 'AND'][o2]
                return '.RTYPE (%s, %s, %s, .%s)' % (R(rdp), R(rs1p), R(rs1p), o)
            o = ['SUBW', 'ADDW'][o2]
            return '.RTYPEW (%s, %s, %s, .%s)' % (R(rdp), R(rs1p), R(rs1p), o)
        if f3 == 5:
            imm = sext((bits(i, 12, 12) << 11) | (bits(i, 8, 8) << 10) | (bits(i, 10, 9) << 8) | (bits(i, 6, 6) << 7) |
                       (bits(i, 7, 7) << 6) | (bits(i, 2, 2) << 5) | (bits(i, 11, 11) << 4) | (bits(i, 5, 3) << 1), 12)
            return '.JAL (%s, %s)' % (u(imm, 21), R(0))
        if f3 in (6, 7):
            imm = sext((bits(i, 12, 12) << 8) | (bits(i, 6, 5) << 6) | (bits(i, 2, 2) << 5) |
                       (bits(i, 11, 10) << 3) | (bits(i, 4, 3) << 1), 9)
            return '.BTYPE (%s, %s, %s, .%s)' % (u(imm, 13), R(0), R(rs1p), 'BEQ' if f3 == 6 else 'BNE')
    if q == 2:
        if f3 == 0:
            return '.SHIFTIOP (%s, %s, %s, .SLLI)' % (u((bits(i, 12, 12) << 5) | bits(i, 6, 2), 6), R(rd), R(rd))
        if f3 == 2:
            imm = (bits(i, 3, 2) << 6) | (bits(i, 12, 12) << 5) | (bits(i, 6, 4) << 2)
            return '.LOAD (%s, %s, %s, false, 4)' % (u(imm, 12), R(2), R(rd))
        if f3 == 3:
            imm = (bits(i, 4, 2) << 6) | (bits(i, 12, 12) << 5) | (bits(i, 6, 5) << 3)
            return '.LOAD (%s, %s, %s, false, 8)' % (u(imm, 12), R(2), R(rd))
        if f3 == 4:
            if bits(i, 12, 12) == 0:
                if rs2 == 0:
                    return '.JALR (%s, %s, %s)' % (u(0, 12), R(rd), R(0))
                return '.RTYPE (%s, %s, %s, .ADD)' % (R(rs2), R(0), R(rd))
            if rs2 == 0:
                if rd == 0:
                    return None
                return '.JALR (%s, %s, %s)' % (u(0, 12), R(rd), R(1))
            return '.RTYPE (%s, %s, %s, .ADD)' % (R(rs2), R(rd), R(rd))
        if f3 == 6:
            imm = (bits(i, 8, 7) << 6) | (bits(i, 12, 9) << 2)
            return '.STORE (%s, %s, %s, 4)' % (u(imm, 12), R(rs2), R(2))
        if f3 == 7:
            imm = (bits(i, 9, 7) << 6) | (bits(i, 12, 10) << 3)
            return '.STORE (%s, %s, %s, 8)' % (u(imm, 12), R(rs2), R(2))
    return None
