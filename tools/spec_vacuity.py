import re, glob, os, sys
# VACUITY CHECK.  In bi_scope a [forall] extends MAXIMALLY, so an unparenthesised
# forall inside the WAND CHAIN swallows the trailing [WP …] and the contract
# degenerates to something trivially provable.  Compiling does NOT catch it, and
# neither does the Module Type seal.  Introduced once already, by dropping a
# [wp_next b (fun CID => …)] wrapper and its closing paren while re-indenting.
#
# A forall BEFORE the first depth-0 [-∗] is fine (ordinary Coq premises); only
# one AFTER the separation chain has started is suspect.  Depth is tracked per
# CHARACTER, since premise lines like [(⊢ kernel_text -∗ instr …)] contain a
# wand that opens and closes inside parens on one line.
#
# USAGE
#   spec_vacuity.py                     the CI run: Spec*.v / Wp*.v / Code*.v,
#                                       the [_body] spec definitions only.
#   spec_vacuity.py [--lemmas] FILE...  scan exactly these files; with --lemmas,
#                                       scan every top-level Lemma / Theorem /
#                                       Example / Definition STATEMENT instead
#                                       of just [_body] definitions -- which is
#                                       what a layer whose contracts ARE plain
#                                       lemmas needs (the weak-memory Weak*.v
#                                       files have no [_body] at all, so the
#                                       default run says nothing about them).
def scan(body):
    depth = 0; in_chain = False; i = 0
    while i < len(body):
        c = body[i]
        if c == '(': depth += 1
        elif c == ')': depth -= 1
        elif depth == 0:
            if body.startswith('-∗', i): in_chain = True
            elif in_chain and (body.startswith('∀', i) or
                               re.match(r'forall\b', body[i:])):
                return body[i:i+58].split('\n')[0]
        i += 1
    return None

args = sys.argv[1:]
lemmas = '--lemmas' in args
paths = [a for a in args if not a.startswith('--')]

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'iris')
files = [os.path.relpath(os.path.abspath(p), root) for p in paths]
os.chdir(root)
if not files:
    # a _body Definition can live in any per-function file; Code*.v joined the
    # set when the decode/instr layer was renamed out of Wp*.v.
    files = glob.glob('Spec*.v') + glob.glob('Wp*.v') + glob.glob('Code*.v')
files = sorted(files)
if not files:
    sys.exit("spec_vacuity: found no files to scan -- refusing to report CLEAN")

# A [_body] spec definition, always; every top-level statement under --lemmas.
DECL = (r'^(?:Definition|Lemma|Theorem|Example|Corollary)\s+(\w+)\b'
        if lemmas else r'^Definition\s+(\w*_body)\b')
STOP = r'^(?:Definition|Module|End|Lemma|Theorem|Example|Corollary|Proof)\b'

bad = []
for f in files:
    src = open(f, errors='ignore').read()
    for m in re.finditer(DECL, src, re.M):
        rest = src[m.end():]
        nxt = re.search(STOP, rest, re.M)
        body = rest[:nxt.start()] if nxt else rest
        hit = scan(body)
        if hit: bad.append((f, m.group(1), hit))
print(f"scanned {len(files)} files ({'statements' if lemmas else '_body defs'})")
if bad:
    print(f"\n*** {len(bad)} VACUOUS ***")
    for f,b,l in bad: print(f"  {f:28s} {b:34s} {l}")
else:
    print("\nCLEAN -- no unparenthesised forall inside any wand chain")
sys.exit(1 if bad else 0)
