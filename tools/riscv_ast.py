#!/usr/bin/env python3
"""riscv_ast.py -- decode a RISC-V word into the Sail AST spelling the proofs use.

This is the core of tools/gen_code.py: given an encoding word it returns the
Rocq text of the `instruction` term the Sail model's decoder yields, so a
Code<F>.v can be emitted from the image with nothing parsed out of the tree.

Two things a caller needs per instruction:

  * `ast`      -- the term an [instr pc rvc <ast>] fact states.  For a
                  compressed instruction this is the EXPANDED base form, which
                  is what `execute` reduces the C_* constructor to.
  * `cast`     -- (compressed only) the C_* term the decode lemma states, and
                  the name of the exec lemma that bridges the two.

Register spellings follow the tree's conventions: `Regidx (mword_of_int n)`,
`zreg` for x0, `sp` for x2 in the compressed stack forms, and
`creg2reg_idx (Cregidx (mword_of_int n))` for a 3-bit compressed register.
"""

# --------------------------------------------------------------------------
# register spellings
# --------------------------------------------------------------------------

def reg(n):
    """A 5-bit register index as the proofs spell it."""
    if n == 0:
        return 'zreg'
    return 'Regidx (mword_of_int %d)' % n


def creg(n):
    """A 3-bit compressed register index, kept in its widening form.

    The branch forms state the register this way; the load/store forms state
    the RESOLVED index instead (see cregr), because that is the shape their
    WP leaves take."""
    return 'creg2reg_idx (Cregidx (mword_of_int %d))' % n


def cregr(n):
    """A 3-bit compressed register index, RESOLVED (c -> c + 8)."""
    return reg(n + 8)


def sx(width, val, inner_width):
    """sign_extend' to `width` of an `inner_width`-bit literal."""
    return "sign_extend' %d (mword_of_int %d : mword %d)" % (width, val, inner_width)


def zx_shift(width, val, inner_width, shift_bits):
    """zero_extend' of a literal concatenated with `shift_bits` zero bits --
    how the compressed stack forms spell a scaled displacement."""
    return "zero_extend' %d (concat_vec (mword_of_int %d : mword %d) ('b\"%s\"))" % (
        width, val, inner_width, shift_bits)


def bits(v, hi, lo):
    return (v >> lo) & ((1 << (hi - lo + 1)) - 1)


def sign(v, w):
    """interpret the low w bits of v as two's complement"""
    v &= (1 << w) - 1
    return v - (1 << w) if v >> (w - 1) else v


def residue(v, w):
    """the POSITIVE residue a decode fact's immediate must carry"""
    return v & ((1 << w) - 1)


# --------------------------------------------------------------------------
# base (32-bit) instructions
# --------------------------------------------------------------------------

BRANCH_OP = {0: 'BEQ', 1: 'BNE', 4: 'BLT', 5: 'BGE', 6: 'BLTU', 7: 'BGEU'}
# funct3 -> (width in bytes, is_UNSIGNED).  The boolean is "zero-extend",
# not "sign-extend": LB/LH/LW/LD are false, LBU/LHU/LWU are true.
LOAD_W = {0: ('1', 'false'), 1: ('2', 'false'), 2: ('4', 'false'),
          3: ('8', 'false'), 4: ('1', 'true'), 5: ('2', 'true'), 6: ('4', 'true')}
STORE_W = {0: '1', 1: '2', 2: '4', 3: '8'}
OPIMM = {0: 'ADDI', 2: 'SLTI', 3: 'SLTIU', 4: 'XORI', 6: 'ORI', 7: 'ANDI'}
OP_RTYPE = {(0, 0): 'ADD', (0, 32): 'SUB', (1, 0): 'SLL', (2, 0): 'SLT',
            (3, 0): 'SLTU', (4, 0): 'XOR', (5, 0): 'SRL', (5, 32): 'SRA',
            (6, 0): 'OR', (7, 0): 'AND'}
MULOP = {0: 'mulop_mul', 1: 'mulop_mulh', 2: 'mulop_mulhsu', 3: 'mulop_mulhu'}


def decode_base(w):
    """The Sail AST for a 4-byte encoding, or None if unhandled."""
    op = w & 0x7f
    rd, rs1, rs2 = bits(w, 11, 7), bits(w, 19, 15), bits(w, 24, 20)
    f3, f7 = bits(w, 14, 12), bits(w, 31, 25)

    if op == 0x37:
        return 'UTYPE (mword_of_int %d : mword 20, %s, LUI)' % (bits(w, 31, 12), reg(rd))
    if op == 0x17:
        return 'UTYPE (mword_of_int %d : mword 20, %s, AUIPC)' % (bits(w, 31, 12), reg(rd))
    if op == 0x6f:
        imm = ((bits(w, 31, 31) << 20) | (bits(w, 19, 12) << 12)
               | (bits(w, 20, 20) << 11) | (bits(w, 30, 21) << 1))
        return 'JAL (mword_of_int %d : mword 21, %s)' % (residue(imm, 21), reg(rd))
    if op == 0x67:
        imm = residue(bits(w, 31, 20), 12)
        immt = "zeros' 12" if imm == 0 else 'mword_of_int %d : mword 12' % imm
        return 'JALR (%s, %s, %s)' % (immt, reg(rs1), reg(rd))
    if op == 0x63:
        imm = ((bits(w, 31, 31) << 12) | (bits(w, 7, 7) << 11)
               | (bits(w, 30, 25) << 5) | (bits(w, 11, 8) << 1))
        if f3 not in BRANCH_OP:
            return None
        return 'BTYPE (mword_of_int %d : mword 13, %s, %s, %s)' % (
            residue(imm, 13), reg(rs2), reg(rs1), BRANCH_OP[f3])
    if op == 0x03:
        if f3 not in LOAD_W:
            return None
        width, signed = LOAD_W[f3]
        return 'LOAD (mword_of_int %d : mword 12, %s, %s, %s, %s)' % (
            residue(bits(w, 31, 20), 12), reg(rs1), reg(rd), signed, width)
    if op == 0x23:
        if f3 not in STORE_W:
            return None
        imm = (f7 << 5) | rd
        return 'STORE (mword_of_int %d : mword 12, %s, %s, %s)' % (
            residue(imm, 12), reg(rs2), reg(rs1), STORE_W[f3])
    if op == 0x13:
        if f3 in (1, 5):                      # shift: the immediate is a shamt
            sh = bits(w, 25, 20)
            kind = 'SLLI' if f3 == 1 else ('SRAI' if f7 & 0x20 else 'SRLI')
            return 'SHIFTIOP (mword_of_int %d : mword 6, %s, %s, %s)' % (
                sh, reg(rs1), reg(rd), kind)
        if f3 not in OPIMM:
            return None
        return 'ITYPE (mword_of_int %d : mword 12, %s, %s, %s)' % (
            residue(bits(w, 31, 20), 12), reg(rs1), reg(rd), OPIMM[f3])
    if op == 0x1b:
        if f3 == 0:
            return 'ADDIW (mword_of_int %d : mword 12, %s, %s)' % (
                residue(bits(w, 31, 20), 12), reg(rs1), reg(rd))
        if f3 in (1, 5):
            sh = bits(w, 24, 20)
            kind = 'SLLIW' if f3 == 1 else ('SRAIW' if f7 & 0x20 else 'SRLIW')
            return 'SHIFTIWOP (mword_of_int %d : mword 5, %s, %s, %s)' % (
                sh, reg(rs1), reg(rd), kind)
        return None
    if op == 0x33:
        if f7 == 1:                            # M extension
            if f3 in MULOP:
                return 'MUL (%s, %s, %s, %s)' % (reg(rs2), reg(rs1), reg(rd), MULOP[f3])
            if f3 == 4:
                return 'DIV (%s, %s, %s, false)' % (reg(rs2), reg(rs1), reg(rd))
            if f3 == 5:
                return 'DIV (%s, %s, %s, true)' % (reg(rs2), reg(rs1), reg(rd))
            if f3 == 6:
                return 'REM (%s, %s, %s, false)' % (reg(rs2), reg(rs1), reg(rd))
            if f3 == 7:
                return 'REM (%s, %s, %s, true)' % (reg(rs2), reg(rs1), reg(rd))
            return None
        key = (f3, f7)
        if key not in OP_RTYPE:
            return None
        return 'RTYPE (%s, %s, %s, %s)' % (reg(rs2), reg(rs1), reg(rd), OP_RTYPE[key])
    if op == 0x3b:
        if f7 == 1 and f3 == 0:
            return 'MULW (%s, %s, %s)' % (reg(rs2), reg(rs1), reg(rd))
        kind = {(0, 0): 'ADDW', (0, 32): 'SUBW', (1, 0): 'SLLW',
                (5, 0): 'SRLW', (5, 32): 'SRAW'}.get((f3, f7))
        if kind is None:
            return None
        return 'RTYPEW (%s, %s, %s, %s)' % (reg(rs2), reg(rs1), reg(rd), kind)
    if op == 0x0f:
        if f3 == 1:
            imm = residue(bits(w, 31, 20), 12)
            immt = "zeros' 12" if imm == 0 else 'mword_of_int %d : mword 12' % imm
            return 'FENCEI (%s, %s, %s)' % (immt, reg(rs1), reg(rd))
        if f3 == 0:
            return ('FENCE (mword_of_int %d : mword 4, mword_of_int %d : mword 4, '
                    'mword_of_int %d : mword 4, %s, %s)') % (
                bits(w, 31, 28), bits(w, 27, 24), bits(w, 23, 20), reg(rs1), reg(rd))
        return None
    if op == 0x73:
        if w == 0x10200073:
            return 'SRET tt'
        if w == 0x30200073:
            return 'MRET tt'
        if w == 0x10500073:
            return 'WFI tt'
        if f3 == 0 and f7 == 0x09:
            return 'SFENCE_VMA (%s, %s)' % (reg(rs1), reg(rs2))
        csr = bits(w, 31, 20)
        kind = {1: 'CSRRW', 2: 'CSRRS', 3: 'CSRRC'}.get(f3 & 3)
        if kind is None:
            return None
        if f3 & 4:                             # immediate form
            return 'CSRImm (%s, mword_of_int %d, %s, %s)' % (
                csr_name(csr), rs1, reg(rd), kind)
        return 'CSRReg (%s, %s, %s, %s)' % (csr_name(csr), reg(rs1), reg(rd), kind)
    return None


CSR_NAMES = {
    0x100: 'csr_sstatus', 0x104: 'csr_sie', 0x105: 'csr_stvec', 0x140: 'csr_sscratch',
    0x141: 'csr_sepc', 0x142: 'csr_scause', 0x143: 'csr_stval', 0x144: 'csr_sip',
    0x180: 'csr_satp', 0x300: 'csr_mstatus', 0x304: 'csr_mie', 0x305: 'csr_mtvec',
    0x340: 'csr_mscratch', 0x341: 'csr_mepc', 0x342: 'csr_mcause', 0x343: 'csr_mtval',
    0x344: 'csr_mip', 0x302: 'csr_medeleg', 0x303: 'csr_mideleg', 0x30a: 'csr_menvcfg',
    0x3a0: 'csr_pmpcfg0', 0x3b0: 'csr_pmpaddr0', 0xc01: 'csr_time', 0xf14: 'csr_mhartid',
    0x747: 'csr_mseccfg', 0xb00: 'csr_mcycle', 0xb02: 'csr_minstret',
    0x14d: 'csr_stimecmp', 0x106: 'csr_scounteren', 0x306: 'csr_mcounteren',
    0x30c: 'csr_menvcfgh', 0x10a: 'csr_senvcfg', 0x3a1: 'csr_pmpcfg1',
    0x3a2: 'csr_pmpcfg2', 0x3b1: 'csr_pmpaddr1', 0xc00: 'csr_cycle',
    0xc02: 'csr_instret', 0x301: 'csr_misa', 0xf11: 'csr_mvendorid',
    0xf12: 'csr_marchid', 0xf13: 'csr_mimpid', 0x7a0: 'csr_tselect',
}


def csr_name(c):
    """A CSR as its NUMERIC literal.

    The readable names (csr_satp, csr_time, ...) are per-file definitions
    scattered across the tree, not model constants, so a generated file
    cannot rely on any of them being in scope.  The number always is."""
    return 'mword_of_int %d : mword 12' % c


# --------------------------------------------------------------------------
# compressed (16-bit) instructions
#
# Each returns (expanded_ast, c_ast, exec_lemma): the base-form AST an
# [instr] fact states, the C_* term its decode lemma states, and the lemma
# bridging the two.  Where the tree spelled the same word two ways (x2 as
# `sp` in one file and `Regidx csp_rs1` in another), generation picks one --
# that inconsistency is a thing to remove, not to reproduce.
# --------------------------------------------------------------------------

def _ci_imm(w):
    """the 6-bit CI immediate: {bit12, bits6:2}"""
    return (bits(w, 12, 12) << 5) | bits(w, 6, 2)


def _cl_off(w, scale):
    """CL/CS displacement, in units of `scale` bytes"""
    if scale == 4:
        return (bits(w, 5, 5) << 6) | (bits(w, 12, 10) << 3) | (bits(w, 6, 6) << 2)
    return (bits(w, 6, 5) << 6) | (bits(w, 12, 10) << 3)


def decode_compressed(w):
    if w == 0:
        # the all-zero halfword is not an instruction (objdump prints `unimp`);
        # it appears as tail padding and no proof ever steps it.
        return None
    f3, op = bits(w, 15, 13), bits(w, 1, 0)
    rd, rs2 = bits(w, 11, 7), bits(w, 6, 2)
    rdc, rs1c = bits(w, 4, 2), bits(w, 9, 7)

    if op == 0 and f3 == 0:                                  # C.ADDI4SPN
        n = ((bits(w, 10, 7) << 6) | (bits(w, 12, 11) << 4)
             | (bits(w, 5, 5) << 3) | (bits(w, 6, 6) << 2))
        return ('ITYPE (caddi4spn_imm (mword_of_int %d : mword 8), sp, %s, ADDI)'
                % (n >> 2, creg(rdc)),
                'C_ADDI4SPN (Cregidx (mword_of_int %d), mword_of_int %d)' % (rdc, n >> 2),
                'C_ADDI4SPN')
    if op == 0 and f3 == 2:                                  # C.LW
        off = _cl_off(w, 4)
        return ('LOAD (mword_of_int %d : mword 12, %s, %s, false, 4)' % (off, cregr(rs1c), cregr(rdc)),
                'C_LW (mword_of_int %d, Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))'
                % (off >> 2, rs1c, rdc), 'C_LW')
    if op == 0 and f3 == 3:                                  # C.LD
        off = _cl_off(w, 8)
        return ('LOAD (mword_of_int %d : mword 12, %s, %s, false, 8)' % (off, cregr(rs1c), cregr(rdc)),
                'C_LD (mword_of_int %d, Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))'
                % (off >> 3, rs1c, rdc), 'C_LD')
    if op == 0 and f3 == 6:                                  # C.SW
        off = _cl_off(w, 4)
        return ('STORE (mword_of_int %d : mword 12, %s, %s, 4)' % (off, cregr(rdc), cregr(rs1c)),
                'C_SW (mword_of_int %d, Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))'
                % (off >> 2, rs1c, rdc), 'C_SW')
    if op == 0 and f3 == 7:                                  # C.SD
        off = _cl_off(w, 8)
        return ('STORE (mword_of_int %d : mword 12, %s, %s, 8)' % (off, cregr(rdc), cregr(rs1c)),
                'C_SD (mword_of_int %d, Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))'
                % (off >> 3, rs1c, rdc), 'C_SD')

    if op == 1 and f3 == 0:                                  # C.ADDI / C.NOP
        n = _ci_imm(w)
        if rd == 0:
            # rd = x0 is C.NOP, a distinct constructor -- and it is what the
            # inter-function alignment padding decodes to.
            if n != 0:
                return None                    # a HINT; gcc does not emit one
            return ('ITYPE (%s, zreg, zreg, ADDI)' % sx(12, 0, 6),
                    'C_NOP (mword_of_int 0)', 'C_NOP')
        return ('ITYPE (%s, %s, %s, ADDI)' % (sx(12, n, 6), reg(rd), reg(rd)),
                'C_ADDI (mword_of_int %d, Regidx (mword_of_int %d))' % (n, rd),
                'C_ADDI')
    if op == 1 and f3 == 1:                                  # C.ADDIW
        n = _ci_imm(w)
        return ('ADDIW (%s, %s, %s)' % (sx(12, n, 6), reg(rd), reg(rd)),
                'C_ADDIW (mword_of_int %d, Regidx (mword_of_int %d))' % (n, rd),
                'C_ADDIW')
    if op == 1 and f3 == 2:                                  # C.LI
        n = _ci_imm(w)
        return ('ITYPE (%s, zreg, %s, ADDI)' % (sx(12, n, 6), reg(rd)),
                'C_LI (mword_of_int %d, %s)' % (n, reg(rd)), 'C_LI')
    if op == 1 and f3 == 3:                                  # C.ADDI16SP / C.LUI
        if rd == 2:
            n = ((bits(w, 12, 12) << 5) | (bits(w, 4, 3) << 3)
                 | (bits(w, 5, 5) << 2) | (bits(w, 2, 2) << 1) | bits(w, 6, 6))
            return ('ITYPE (caddi16sp_imm (mword_of_int %d : mword 6), sp, sp, ADDI)' % n,
                    'C_ADDI16SP (mword_of_int %d)' % n, 'C_ADDI16SP')
        n = _ci_imm(w)
        # C.LUI's immediate is SIGN-extended from 6 bits into the 20-bit field
        return ('UTYPE (%s, %s, LUI)' % (sx(20, n, 6), reg(rd)),
                'C_LUI (mword_of_int %d, Regidx (mword_of_int %d))' % (n, rd),
                'C_LUI')
    if op == 1 and f3 == 5:                                  # C.J
        imm = ((bits(w, 12, 12) << 11) | (bits(w, 8, 8) << 10) | (bits(w, 10, 9) << 8)
               | (bits(w, 6, 6) << 7) | (bits(w, 7, 7) << 6) | (bits(w, 2, 2) << 5)
               | (bits(w, 11, 11) << 4) | (bits(w, 5, 3) << 1))
        n = residue(imm >> 1, 11)
        return ("JAL (sign_extend' 21 (concat_vec (mword_of_int %d : mword 11) ('b\"0\")), zreg)" % n,
                'C_J (mword_of_int %d)' % n, 'C_J')
    if op == 1 and f3 in (6, 7):                             # C.BEQZ / C.BNEZ
        imm = ((bits(w, 12, 12) << 8) | (bits(w, 6, 5) << 6) | (bits(w, 2, 2) << 5)
               | (bits(w, 11, 10) << 3) | (bits(w, 4, 3) << 1))
        n = residue(imm >> 1, 8)
        kind = 'BEQ' if f3 == 6 else 'BNE'
        cn = 'C_BEQZ' if f3 == 6 else 'C_BNEZ'
        return ("BTYPE (sign_extend' 13 (concat_vec (mword_of_int %d : mword 8) ('b\"0\")), zreg, %s, %s)"
                % (n, creg(rs1c), kind),
                '%s (mword_of_int %d, Cregidx (mword_of_int %d))' % (cn, n, rs1c),
                '%s' % cn)
    if op == 1 and f3 == 4:                                  # C.SRLI/SRAI/ANDI/ALU
        sub = bits(w, 11, 10)
        if sub in (0, 1):
            sh = (bits(w, 12, 12) << 5) | bits(w, 6, 2)
            kind = 'SRLI' if sub == 0 else 'SRAI'
            cn = 'C_SRLI' if sub == 0 else 'C_SRAI'
            return ('SHIFTIOP (mword_of_int %d : mword 6, %s, %s, %s)' % (sh, creg(rs1c), creg(rs1c), kind),
                    '%s (mword_of_int %d, Cregidx (mword_of_int %d))' % (cn, sh, rs1c),
                    '%s' % cn)
        if sub == 2:
            n = _ci_imm(w)
            return ('ITYPE (%s, %s, %s, ANDI)' % (sx(12, n, 6), creg(rs1c), creg(rs1c)),
                    'C_ANDI (mword_of_int %d, Cregidx (mword_of_int %d))' % (n, rs1c),
                    'C_ANDI')
        hi, lo = bits(w, 12, 12), bits(w, 6, 5)
        if hi == 0:
            kind = {0: 'SUB', 1: 'XOR', 2: 'OR', 3: 'AND'}[lo]
            cn = {0: 'C_SUB', 1: 'C_XOR', 2: 'C_OR', 3: 'C_AND'}[lo]
            return ('RTYPE (%s, %s, %s, %s)' % (creg(rdc), creg(rs1c), creg(rs1c), kind),
                    '%s (Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))' % (cn, rs1c, rdc),
                    '%s' % cn)
        kind = {0: 'SUBW', 1: 'ADDW'}.get(lo)
        cn = {0: 'C_SUBW', 1: 'C_ADDW'}.get(lo)
        if kind is None:
            return None
        return ('RTYPEW (%s, %s, %s, %s)' % (creg(rdc), creg(rs1c), creg(rs1c), kind),
                '%s (Cregidx (mword_of_int %d), Cregidx (mword_of_int %d))' % (cn, rs1c, rdc),
                '%s' % cn)

    if op == 2 and f3 == 0:                                  # C.SLLI
        sh = (bits(w, 12, 12) << 5) | bits(w, 6, 2)
        return ('SHIFTIOP (mword_of_int %d : mword 6, %s, %s, SLLI)' % (sh, reg(rd), reg(rd)),
                'C_SLLI (mword_of_int %d, Regidx (mword_of_int %d))' % (sh, rd),
                'C_SLLI')
    if op == 2 and f3 == 2:                                  # C.LWSP
        off = (bits(w, 3, 2) << 6) | (bits(w, 12, 12) << 5) | (bits(w, 6, 4) << 2)
        return ('LOAD (%s, sp, %s, false, 4)' % (zx_shift(12, off >> 2, 6, '00'), reg(rd)),
                'C_LWSP (mword_of_int %d, Regidx (mword_of_int %d))' % (off >> 2, rd),
                'C_LWSP')
    if op == 2 and f3 == 3:                                  # C.LDSP
        off = (bits(w, 4, 2) << 6) | (bits(w, 12, 12) << 5) | (bits(w, 6, 5) << 3)
        return ('LOAD (%s, sp, %s, false, 8)' % (zx_shift(12, off >> 3, 6, '000'), reg(rd)),
                'C_LDSP (mword_of_int %d, Regidx (mword_of_int %d))' % (off >> 3, rd),
                'C_LDSP')
    if op == 2 and f3 == 6:                                  # C.SWSP
        off = (bits(w, 8, 7) << 6) | (bits(w, 12, 9) << 2)
        return ('STORE (%s, %s, sp, 4)' % (zx_shift(12, off >> 2, 6, '00'), reg(rs2)),
                'C_SWSP (mword_of_int %d, Regidx (mword_of_int %d))' % (off >> 2, rs2),
                'C_SWSP')
    if op == 2 and f3 == 7:                                  # C.SDSP
        off = (bits(w, 9, 7) << 6) | (bits(w, 12, 10) << 3)
        return ('STORE (%s, %s, sp, 8)' % (zx_shift(12, off >> 3, 6, '000'), reg(rs2)),
                'C_SDSP (mword_of_int %d, Regidx (mword_of_int %d))' % (off >> 3, rs2),
                'C_SDSP')
    if op == 2 and f3 == 4:                                  # C.MV / C.ADD / C.JR / C.JALR
        if bits(w, 12, 12) == 0:
            if rs2 == 0:
                return ("JALR (zeros' 12, %s, zreg)" % reg(rd),
                        'C_JR (Regidx (mword_of_int %d))' % rd, 'C_JR')
            return ('RTYPE (%s, zreg, %s, ADD)' % (reg(rs2), reg(rd)),
                    'C_MV (Regidx (mword_of_int %d), Regidx (mword_of_int %d))' % (rd, rs2),
                    'C_MV')
        if rs2 == 0:
            return ("JALR (zeros' 12, %s, Regidx (mword_of_int 1))" % reg(rd),
                    'C_JALR (Regidx (mword_of_int %d))' % rd, 'C_JALR')
        return ('RTYPE (%s, %s, %s, ADD)' % (reg(rs2), reg(rd), reg(rd)),
                'C_ADD (Regidx (mword_of_int %d), Regidx (mword_of_int %d))' % (rd, rs2),
                'C_ADD')
    return None
