#!/usr/bin/env python3
"""lock_ctx_sweep.py -- the M3 lock-surface client sweeps (tso-port.md 0.6'/0.7').

Three mechanical passes over iris/*.v, one per stage of the lock-payload
conversion.  All were first applied on branch `tso`; they are kept here,
per owner instruction, TO BE RE-APPLIED TO MAIN when the port goes
upstream.  Each pass is idempotent (a second run is a no-op) and runs as
a DRY RUN by default; pass --apply to write.

  wrap     Wrap concrete lock payloads at is_lock/lock_openable/lock_inv
           MENTION sites in the constant embedding `<{ P }>` (TsoCtx.v).
           This is the statement-side pass that follows the in-place
           payload-arity flip of WpLock/SpecAcquire/SpecRelease
           (R : iProp becomes R : CtxId -> iProp): every statement that
           passes a concrete unconverted payload keeps meaning under the
           constant embedding.  Converted payloads are spelled
           (fun xi : CtxId, ...) BY HAND and are recognizable by the
           lambda -- this pass never touches them.

  erase    [REJECTED -- DO NOT APPLY; kept as the record of the
           experiment so main does not repeat it.]  Replaces the explicit
           payload argument(s) at acquire/release call sites with `_`.
           Correctness holds (the evar unifies from the framed is_lock /
           payload-in-hand hypotheses, and single-file tests pass), but
           PROOF PERFORMANCE degenerates: the specs' implicit
           {!CtxMorph R} argument runs typeclass search while R is still
           a flexible evar, and the structural instances
           (ctx_morph_sep/exist/big_sepL) unify with an evar by INVENTING
           structure, then backtrack -- the pipe proofs went from minutes
           to unbounded (15+ min, killed).  Owner ruling 2026-08-25: call
           sites keep the payload EXPLICIT; a payload conversion includes
           a mechanical call-site pass (the old payload expression is the
           grep key), which the kmem conversion showed is ~10 sed sites
           per lock.  (A `Hint Mode CtxMorph - - !` would suspend the
           search instead, but the explicit spelling was preferred for
           readability and for not betting proof time on postponed
           unification.)

  receipt  Insert the `_` slot for the M2 view receipt
           (exists K, hart_view_lb K) into the continuation intro pattern
           of every SPINLOCK-acquire call site (the receipt sits between
           the payload name and the cpu_own name).  Sleeplock
           continuations are untouched (their spec shape did not change).

Hard-won matcher rules (each encodes a bug found on `tso`):
  - payload matchers are BALANCED-TOKEN based and skip comments: a
    same-line regex once swallowed a multi-line `(* ... *)` into the
    wrapper (ProofKexit);
  - `erase`/`receipt` skip a slot that is already `_` -- re-running the
    receipt pass once double-inserted and the deduplication regex then
    collapsed LEGITIMATE `_ _` slots in unrelated intro patterns (13
    sites, restored from the diff).  Never post-process with a broader
    regex than the insertion used;
  - `wrap` requires the lock-name string literal ADJACENT to the payload
    so it cannot fire on unrelated arguments, and it must NOT fire on
    the sleeplock spec family, whose payloads stayed iProp.

Usage:  tools/lock_ctx_sweep.py {wrap|erase|receipt} [--apply] [FILES...]
        (default file set: iris/*.v minus the lock surface itself)
"""

import re, sys, glob, os

IRIS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'iris')

# the lock surface itself and its deriving functors: never touched by the
# client sweeps (they are converted by hand, in place)
SKIP = {
    'WpLock.v', 'WpLockAt.v', 'WpSconfLock.v',
    'SpecAcquire.v', 'SpecRelease.v', 'SpecHolding.v',
    'SpecAcquiresleep.v', 'SpecReleasesleep.v', 'SpecHoldingsleep.v',
    'ProofAcquire.v', 'ProofRelease.v',
    'TsoCtx.v', 'TsoCtxShim.v', 'TsoCtxTwin.v', 'TsoCtxTwin2.v',
    'TsoCtxRehearsal.v', 'KallocInv.v',
}

# ---------------------------------------------------------------- tokens

def skip_ws_and_comments(src, i):
    n = len(src)
    while i < n:
        if src[i].isspace():
            i += 1
        elif src.startswith('(*', i):
            depth = 1; i += 2
            while i < n and depth:
                if src.startswith('(*', i): depth += 1; i += 2
                elif src.startswith('*)', i): depth -= 1; i += 2
                else: i += 1
        else:
            break
    return i

def read_token(src, i):
    """One balanced argument token starting at i (caller skipped ws).
    Returns (end, kind) with kind in {'paren','wrap','string','ident','other'}."""
    n = len(src)
    if i >= n: return i, 'other'
    c = src[i]
    if src.startswith('<{', i):
        depth = 1; j = i + 2
        while j < n and depth:
            if src.startswith('<{', j): depth += 1; j += 2
            elif src.startswith('}>', j): depth -= 1; j += 2
            else: j += 1
        return j, 'wrap'
    if c == '(':
        # a comment is not an argument
        if src.startswith('(*', i): return i, 'other'
        depth = 1; j = i + 1
        while j < n and depth:
            if src.startswith('(*', j):          # comment inside args
                j = skip_ws_and_comments(src, j)
                continue
            if src[j] == '(': depth += 1
            elif src[j] == ')': depth -= 1
            elif src[j] == '"':                  # string inside parens
                j += 1
                while j < n and src[j] != '"': j += 1
            j += 1
        return j, 'paren'
    if c == '"':
        j = i + 1
        while j < n and src[j] != '"': j += 1
        j += 1
        if src.startswith('%string', j): j += len('%string')
        return j, 'string'
    m = re.match(r'[A-Za-z0-9_.\'γξ]+(?:%\w+)?', src[i:])
    if m:
        return i + m.end(), 'ident'
    return i + 1, 'other'

# ---------------------------------------------------------------- erase

# verb -> number of payload arguments immediately after the lock-name
# string (spinlock: R; sleeplock gen: R and H)
ERASE_VERBS = [
    ('wp_acquire_gen_fresh_sconf', 1), ('wp_acquire_gen_sconf', 1),
    ('wp_acquire_fresh_sconf', 1), ('wp_acquire_sconf', 1),
    ('wp_release_gen_sconf', 1), ('wp_release_cancel_sconf', 1),
    ('wp_release_sconf', 1),
    ('wp_acquiresleep_gen_sconf', 2), ('wp_acquiresleep_sconf', 1),
    ('wp_acquiresleep_nb', 1),
    ('wp_releasesleep_gen_sconf', 2), ('wp_releasesleep_sconf', 1),
]
ERASE_RE = re.compile(
    r'\b(' + '|'.join(v for v, _ in ERASE_VERBS) + r')\b(?!_body|\w)')
ERASE_K = dict(ERASE_VERBS)

def pass_erase(src):
    out = []; pos = 0; count = 0
    for m in ERASE_RE.finditer(src):
        k = ERASE_K[m.group(1)]
        i = m.end()
        # find the lock-name string among the next arguments
        spans = []          # (start, end, kind)
        j = i
        for _ in range(40):
            j = skip_ws_and_comments(src, j)
            if j >= len(src) or src[j] in ')|.' or src.startswith('with', j):
                break
            e, kind = read_token(src, j)
            if e == j: break
            spans.append((j, e, kind)); j = e
            if kind == 'string': break
        if not spans or spans[-1][2] != 'string':
            continue                       # no inline name: leave alone
        # the K payload tokens after the string
        j = spans[-1][1]; repl = []
        for _ in range(k):
            j0 = skip_ws_and_comments(src, j)
            e, kind = read_token(src, j0)
            if kind not in ('paren', 'wrap', 'ident') or src[j0:e] == '_':
                repl = []; break           # already erased / unexpected
            repl.append((j0, e)); j = e
        if not repl:
            continue
        out.append(src[pos:repl[0][0]])
        prev_end = None
        for (a, b) in repl:
            if prev_end is not None:
                out.append(src[prev_end:a])
            out.append('_')
            prev_end = b
        pos = prev_end
        count += len(repl)
    out.append(src[pos:])
    return ''.join(out), count

# ---------------------------------------------------------------- wrap

WRAP_HEADS = r'(?:is_lock|lock_openable|lock_inv)'
WRAP_RE = re.compile(
    r'(' + WRAP_HEADS + r'\b[^\n]*?"[^"]*"(?:%string)?)(\s+)')

def pass_wrap(src):
    """Wrap the argument following the lock-name string, if it is a
    parenthesized expression or a known bare payload ident and not
    already wrapped/lambda'd/underscore."""
    out = []; pos = 0; count = 0
    for m in WRAP_RE.finditer(src):
        j = skip_ws_and_comments(src, m.end(1))
        e, kind = read_token(src, j)
        tok = src[j:e]
        if kind == 'wrap' or tok == '_' or tok.startswith('(λ') or tok.startswith('(fun'):
            continue
        if kind == 'paren' or (kind == 'ident' and tok.endswith('_res')):
            out.append(src[pos:j])
            inner = tok[1:-1] if kind == 'paren' else tok
            out.append('<{ ' + inner + ' }>')
            pos = e; count += 1
    out.append(src[pos:])
    return ''.join(out), count

# ---------------------------------------------------------------- receipt

ACQ_RE = re.compile(r'\bwp_acquire_(?:gen_)?(?:fresh_)?sconf\b(?!_body|\w)')
INTRO_RE = re.compile(r'^(\s*iIntros \([^)]*\) ")([^"]*)("\.)(.*)$')

def toks_pattern(pat):
    out = []; depth = 0; cur = ''
    for ch in pat:
        if ch == ' ' and depth == 0:
            if cur: out.append(cur); cur = ''
        else:
            if ch in '([': depth += 1
            if ch in ')]': depth -= 1
            cur += ch
    if cur: out.append(cur)
    return out

def pass_receipt(src):
    lines = src.split('\n'); count = 0
    for i, l in enumerate(lines):
        if not ACQ_RE.search(l):
            continue
        for j in range(i, min(i + 14, len(lines))):
            m = INTRO_RE.match(lines[j])
            if m:
                t = toks_pattern(m.group(2))
                # tail is [locked, payload, cpu_own, arm_pay]; the receipt
                # goes before cpu_own.  Skip if a `_` is already there.
                if len(t) >= 6 and t[-3] != '_':
                    t.insert(len(t) - 2, '_')
                    lines[j] = m.group(1) + ' '.join(t) + m.group(3) + m.group(4)
                    count += 1
                break
    return '\n'.join(lines), count

# ---------------------------------------------------------------- main

def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ('wrap', 'erase', 'receipt'):
        print(__doc__); sys.exit(1)
    mode = sys.argv[1]
    apply_ = '--apply' in sys.argv
    files = [a for a in sys.argv[2:] if not a.startswith('--')]
    if not files:
        files = sorted(glob.glob(os.path.join(IRIS, '*.v')))
    fn = {'wrap': pass_wrap, 'erase': pass_erase, 'receipt': pass_receipt}[mode]
    total = 0
    for f in files:
        if os.path.basename(f) in SKIP:
            continue
        src = open(f).read()
        new, n = fn(src)
        if n:
            total += n
            print(f'{os.path.basename(f)}: {n}')
            if apply_:
                open(f, 'w').write(new)
    print(f'-- {mode}: {total} site(s){" (dry run)" if not apply_ else ""}')

if __name__ == '__main__':
    main()
