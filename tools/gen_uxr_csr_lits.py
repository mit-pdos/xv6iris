#!/usr/bin/env python3
"""Generate the literal-CSR table of MachCSL/UExecCsrDflt.lean (`uxrLits`, `uxrLitMask`).

The generated model's `is_CSR_accessible` (model/Lean_RV64D/LeanRV64D/SysControl.lean) is, since
sail-riscv 0.16, a chain of `if`s on the csr number: literal tests `b__0 == 0x…#12` and eleven
range guards (the PMP `0x3A?`-`0x3E?` blocks and six `csr[11:5] = k ∧ csr[4:0] ≥ 3` blocks),
ending in `pure false`.  This script walks the chain's ELSE spine, collects its literals in the
model's order, checks that the other guards are exactly the eleven range guards
`MachCSL.uxrDflt` names (a new kind of guard is an error: the Lean side would be wrong), and
writes the block between the BEGIN/END GENERATED markers of MachCSL/UExecCsrDflt.lean.

    tools/gen_uxr_csr_lits.py           # check: exit 1 if the checked-in block differs
    tools/gen_uxr_csr_lits.py --write   # rewrite the block

The Lean side re-checks the mask against the list (`uxrLitMask_eq`, kernel evaluation), and
`uxr_isAcc_dflt` fails if a literal of the chain is missing from the mask.
"""
import os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
MODEL = os.path.join(ROOT, 'model', 'Lean_RV64D', 'LeanRV64D', 'SysControl.lean')
TARGET = os.path.join(ROOT, 'MachCSL', 'UExecCsrDflt.lean')
BEGIN = '-- BEGIN GENERATED (tools/gen_uxr_csr_lits.py; do not edit)'
END = '-- END GENERATED'

TOK = re.compile(r'\(|\)|\bif\b|\bthen\b|\belse\b|\bdo\b|[^\s()]+')


def func_tokens(path, name):
    src = open(path).read()
    i = src.index('def ' + name + ' ')
    ends = [x for x in (src.find('\ndef ', i + 1), src.find('\n/--', i + 1)) if x != -1]
    body = src[i:min(ends) if ends else len(src)]
    return TOK.findall(body[body.index(':= do') + len(':= do'):])


def strip(ts):
    """Drop a leading `do` and redundant outer parentheses."""
    while ts:
        if ts[0] == 'do':
            ts = ts[1:]
            continue
        if ts[0] == '(' and close(ts, 0) == len(ts):
            ts = ts[1:-1]
            continue
        break
    return ts


def close(ts, i):
    """`ts[i] == '('`: the index after its matching `)`."""
    d = 0
    for j in range(i, len(ts)):
        if ts[j] == '(':
            d += 1
        elif ts[j] == ')':
            d -= 1
            if d == 0:
                return j + 1
    raise ValueError('unbalanced')


def split_if(ts):
    """`if (C) then T else E` -> (C, E), or None."""
    ts = strip(ts)
    if not ts or ts[0] != 'if':
        return None
    ce = close(ts, 1)
    if ts[ce] != 'then':
        raise ValueError('expected then: %s' % ' '.join(ts[ce:ce + 8]))
    d = pend = 0
    for j in range(ce + 1, len(ts)):
        t = ts[j]
        if t == '(':
            d += 1
        elif t == ')':
            d -= 1
        elif d == 0 and t == 'if':
            pend += 1
        elif d == 0 and t == 'else':
            if pend == 0:
                return ' '.join(ts[1:ce]), ts[j + 1:]
            pend -= 1
    raise ValueError('no else')


LIT = re.compile(r'\( \( b__0 == \( (0x[0-9A-F]+)#12 : \( BitVec 12 \) \) \) : Bool \)')
PMP = re.compile(r'\( \( \( Sail\.BitVec\.extractLsb b__0 11 4 \) == \( (0x3[A-E])#8 : \( BitVec 8 \) \) \) : Bool \)')
HPM = re.compile(r'\( \( \( \( Sail\.BitVec\.extractLsb b__0 11 5 \) == \( (0b[01]{7})#7 : \( BitVec 7 \) \) \) && '
                 r'\( let index : \( BitVec 5 \) := \( Sail\.BitVec\.extractLsb b__0 4 0 \) '
                 r'\( \( BitVec\.toNatInt index \) ≥b 3 \) : Bool \) \) : Bool \)')
# the range guards `MachCSL.uxrDflt` excludes, by kind
RANGES = {('pmp', k) for k in ('0x3A', '0x3B', '0x3C', '0x3D', '0x3E')} | \
         {('hpm', k) for k in ('0b0011001', '0b1011000', '0b1011100', '0b1100000', '0b1100100', '0b0111001')}


def literals():
    ts = func_tokens(MODEL, 'is_CSR_accessible')
    lits, ranges = [], set()
    while True:
        r = split_if(ts)
        if r is None:
            break
        cond, ts = r
        m = LIT.fullmatch(cond)
        if m:
            lits.append(int(m.group(1), 16))
            continue
        m = PMP.fullmatch(cond)
        if m:
            ranges.add(('pmp', m.group(1)))
            continue
        m = HPM.fullmatch(cond)
        if m:
            ranges.add(('hpm', m.group(1)))
            continue
        sys.exit('gen_uxr_csr_lits: unexpected guard in is_CSR_accessible: %s' % cond[:200])
    if ' '.join(strip(ts)) != 'pure false':
        sys.exit('gen_uxr_csr_lits: the chain does not end in `pure false`: %s' % ' '.join(ts)[:200])
    if ranges != RANGES:
        sys.exit('gen_uxr_csr_lits: the range guards moved: %s' % sorted(ranges ^ RANGES))
    if len(set(lits)) != len(lits):
        sys.exit('gen_uxr_csr_lits: a literal is tested twice')
    return lits


def block(lits):
    mask = 0
    for c in lits:
        mask |= 1 << c
    rows = ['  [' if i == 0 else '   ' for i in range(0, len(lits), 13)]
    items = ['0x%03X' % c for c in lits]
    lines = []
    for n, i in enumerate(range(0, len(items), 13)):
        chunk = ', '.join(items[i:i + 13])
        last = i + 13 >= len(items)
        lines.append(rows[n] + chunk + (']' if last else ','))
    out = [BEGIN,
           '/-- The literal tests of `is_CSR_accessible`\'s chain, in the model\'s order (%d numbers). -/'
           % len(lits),
           'def uxrLits : List Nat :='] + lines + [
           '',
           '/-- `uxrLits` as a bitmask (bit `n` set iff `n` is listed): the kernel tests',
           'membership with two GMP operations (a `List.contains` over `Nat` literals costs',
           '~80µs per comparison in the kernel). -/',
           'def uxrLitMask : Nat :=',
           '  %d' % mask,
           END]
    return '\n'.join(out)


def main():
    new = block(literals())
    src = open(TARGET).read()
    i, j = src.find(BEGIN), src.find(END)
    if i < 0 or j < 0:
        sys.exit('gen_uxr_csr_lits: markers not found in %s' % TARGET)
    cur = src[i:j + len(END)]
    if '--write' in sys.argv[1:]:
        open(TARGET, 'w').write(src[:i] + new + src[j + len(END):])
        print('gen_uxr_csr_lits: wrote %s' % os.path.relpath(TARGET, ROOT))
        return 0
    if cur != new:
        print('gen_uxr_csr_lits: %s is stale; run tools/gen_uxr_csr_lits.py --write'
              % os.path.relpath(TARGET, ROOT))
        return 1
    print('gen_uxr_csr_lits: OK')
    return 0


if __name__ == '__main__':
    sys.exit(main())
