import re, glob
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
bad = []; files = sorted(glob.glob('Spec*.v') + glob.glob('Wp*.v'))
for f in files:
    src = open(f, errors='ignore').read()
    for m in re.finditer(r'^Definition\s+(\w*_body)\b', src, re.M):
        nxt = re.search(r'^(Definition|Module|End|Lemma)\b', src[m.start()+10:], re.M)
        body = src[m.start(): m.start()+10+(nxt.start() if nxt else len(src))]
        hit = scan(body)
        if hit: bad.append((f, m.group(1), hit))
print(f"scanned {len(files)} files")
if bad:
    print(f"\n*** {len(bad)} VACUOUS ***")
    for f,b,l in bad: print(f"  {f:28s} {b:34s} {l}")
else:
    print("\nCLEAN -- no unparenthesised forall inside any wand chain")
