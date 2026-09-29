"""Re-point sh's Lean files from the 7b2c1b1b image to d66e41c.

- fact names ush{I,RI,MI,EI}_<pc>  -> the mapped pc
- hex literals that are sh addresses (text/rodata/auipc temporaries) -> mapped
- every stated instruction AST (`uinstrIs … (BitVec.ofNat 64 PC) rvc (AST)`,
  `ushm_uis X PC rvc (AST)`) re-decoded from the NEW image
- fact docstrings "/-- `0xPC  asm` -/" re-read from the new dump
- objdump targets in comments ("jal ca6 <write>", "# 1290 <...>") mapped
Reports every literal it could not classify.
"""
import re, os, sys, glob, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import OLDPC, NEWPC, amap, R, D
from rvdec import decode
from temps import TEMPS
from oldfacts import paren_arg

LOW_TEMPS = {v for v, nv in TEMPS.items() if v == nv and v in OLDPC}  # auipc temps of unshifted pcs
SKIP_VALUES = {0x954}
REPORT = collections.defaultdict(list)


def mapv(v, fname, low_file):
    if v < 0x1d2:
        return v
    if 0x1d2 <= v < 0x310:
        REPORT['ctor'].append((fname, hex(v)))
        return v
    if v in SKIP_VALUES:
        return v
    if v in LOW_TEMPS and low_file:
        return v
    if v in LOW_TEMPS:
        REPORT['lowtemp-as-pc'].append((fname, hex(v)))
    if 0x310 <= v < 0x13f0:
        return amap(v)
    if v in TEMPS:
        return TEMPS[v]
    if v == 0x1c64:
        return 0x1c74
    if 0x13f0 <= v < 0x2000:
        REPORT['unknown'].append((fname, hex(v)))
        return v
    return v


HEX = re.compile(r'(?<![\w#+])0x([0-9a-fA-F]+)(?![\w])(#64)?')
NAME = re.compile(r'\b(ush(?:I|RI|MI|EI))_([0-9a-f]+)\b')
FACT_PATS = [re.compile(r'uinstrIs (?:γt|N\.t|N\'\.t|[A-Za-z.\']+) \(BitVec\.ofNat 64 (0x[0-9a-f]+)\) (true|false) (?=\()'),
             re.compile(r'ushm?_uis (?:γt|N\.t|N\'\.t|[A-Za-z.\']+) (0x[0-9a-f]+) (true|false) (?=\()')]
OBJ = re.compile(r'\b([0-9a-f]{1,4}) <([A-Za-z_.0-9]+)(\+0x[0-9a-f]+)?>')


def objdump_text(pc):
    w, e, s = NEWPC[pc]
    return s.replace('\t', ' ')


def rewrite(s, fname, low_file):
    # 1. hex literals and names (one pass, positions preserved via re.sub)
    def hexsub(m):
        if m.group(2) is None and s[m.end():m.end() + 1] == '#':
            return m.group(0)
        v = int(m.group(1), 16)
        nv = mapv(v, fname, low_file)
        if nv == v:
            return m.group(0)
        return '0x%x%s' % (nv, m.group(2) or '')

    def namesub(m):
        v = int(m.group(2), 16)
        if 0x1d2 <= v < 0x310:
            REPORT['ctor-name'].append((fname, m.group(0)))
            return m.group(0)
        nv = mapv(v, fname, low_file)
        return '%s_%0*x' % (m.group(1), len(m.group(2)) if nv < 16 ** len(m.group(2)) else 0, nv)

    s = NAME.sub(namesub, s)
    s = HEX.sub(hexsub, s)

    # 2. objdump comment targets (bare hex before <sym>)
    def objsub(m):
        v = int(m.group(1), 16)
        nv = mapv(v, fname, low_file)
        if m.group(3):  # <sym+0xoff>: recompute from the new symbol table is overkill; drop the offset
            return '%x <%s>' % (nv, m.group(2)) if nv != v else m.group(0)
        return '%x <%s>' % (nv, m.group(2))
    s = OBJ.sub(objsub, s)

    # 3. re-decode stated ASTs at their (already mapped) pcs
    out = []; i = 0
    while True:
        best = None
        for P in FACT_PATS:
            m = P.search(s, i)
            if m and (best is None or m.start() < best.start()):
                best = m
        if not best:
            break
        pc = int(best.group(1), 16)
        j = best.end()
        ast, k = paren_arg(s, j)
        out.append(s[i:j])
        if pc in NEWPC:
            w, e, _ = NEWPC[pc]
            d = decode(e, w)
            if d is None:
                REPORT['nodecode'].append((fname, hex(pc)))
                d = ast
            if ('spIdx' in ast) and d.replace('.Regidx 2#5', '.Regidx spIdx') == ' '.join(ast.split()):
                d = ' '.join(ast.split())
            rvc = 'true' if w == 2 else 'false'
            if best.group(2) != rvc:
                REPORT['rvc'].append((fname, hex(pc)))
            out[-1] = out[-1][:best.start() - i] + best.group(0).replace(' ' + best.group(2) + ' ', ' ' + rvc + ' ')
            out.append('(' + d + ')')
        else:
            REPORT['notinstr'].append((fname, hex(pc)))
            out.append(s[j:k])
        i = k
    out.append(s[i:])
    s = ''.join(out)

    # 4. fact docstrings
    def docsub(m):
        pc = int(m.group(1), 16)
        if pc in NEWPC:
            return '/-- `0x%x  %s` -/' % (pc, objdump_text(pc))
        return m.group(0)
    s = re.sub(r'/-- `0x([0-9a-f]+)  [^`]*` -/', docsub, s)
    return s


if __name__ == '__main__':
    import json
    files = [l.strip() for l in open(sys.argv[1][1:])] if sys.argv[1].startswith("@") else sys.argv[1:]
    cfg = json.load(open(os.path.join(D, 'lowfiles.json')))
    for f in files:
        nm = os.path.basename(f)[:-5]
        s = open(f).read()
        t = rewrite(s, nm, nm in cfg)
        if t != s:
            open(f, 'w').write(t)
    for k, v in REPORT.items():
        print('==', k, len(v))
        for x in sorted(set(v))[:200]:
            print('   ', x)
