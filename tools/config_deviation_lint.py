#!/usr/bin/env python3
"""config_deviation_lint.py -- every deviation of the model configuration is marked in the header
AND inline (notes/model-policy.md, tier T0: "Marked inline and in the file's header").

model/sail-config-rv64d.json is upstream's config/config.json.in resolved for this tree, with the
deviations from upstream's defaults enumerated in its header (`//   1. ...` .. `//   N. ...`) and
each changed field marked inline by an `// xv6iris: ... deviation K ...` comment (the comment may
continue on the following `//` lines).  A refresh that re-applies the deviations by hand can lose
one silently (the first 0.16 refresh dropped item 7); this lint makes that loud.  It fails if

  * the header's items are not numbered 1..N (a gap or a repeat);
  * a header item has no inline marker;
  * an inline marker names an item the header does not have;
  * an inline `xv6iris:` marker names no item at all.

Text only: no JSON parsing (the file has comments), no toolchain.

    python3 tools/config_deviation_lint.py [FILE]     # default: model/sail-config-rv64d.json
"""
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
DEFAULT = os.path.join(ROOT, 'model', 'sail-config-rv64d.json')

ITEM = re.compile(r'^//\s+(\d+)\.\s')
MARK = re.compile(r'^\s*//\s*xv6iris:')
COMMENT = re.compile(r'^\s*//')
DEVIATION = re.compile(r'\bdeviation\s+(\d+)', re.I)


def header_end(lines):
    """The header is this tree's comment block at the top: it ends where upstream's own header
    begins ("Original file header ...") or at the first line that is not a comment."""
    for i, l in enumerate(lines):
        if not l.startswith('//') or 'Original file header' in l:
            return i
    return len(lines)


def check(text):
    """-> (problems, items, markers): a list of messages (empty = pass), the header's item
    numbers, and {item: [line numbers of its inline markers]}."""
    lines = text.splitlines()
    end = header_end(lines)
    items = [int(m.group(1)) for l in lines[:end] for m in [ITEM.match(l)] if m]
    probs = []
    if items != list(range(1, len(items) + 1)):
        probs.append('the header\'s deviation items are %s, not 1..%d' % (items, len(items)))
    markers = {}
    i = end
    while i < len(lines):
        if MARK.match(lines[i]):
            start = i
            block = [lines[i]]
            i += 1
            while i < len(lines) and COMMENT.match(lines[i]) and not MARK.match(lines[i]):
                block.append(lines[i])
                i += 1
            ks = {int(k) for k in DEVIATION.findall(' '.join(block))}
            if not ks:
                probs.append('line %d: an xv6iris marker names no deviation' % (start + 1))
            for k in ks:
                markers.setdefault(k, []).append(start + 1)
        else:
            i += 1
    for k in sorted(set(items) - set(markers)):
        probs.append('header item %d has no inline "xv6iris: ... deviation %d" marker' % (k, k))
    for k in sorted(set(markers) - set(items)):
        probs.append('line %s: an inline marker names deviation %d, which the header does not list'
                     % (', '.join(map(str, markers[k])), k))
    return probs, items, markers


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    path = argv[0] if argv else DEFAULT
    with open(path, encoding='utf-8') as f:
        probs, items, markers = check(f.read())
    rel = os.path.relpath(path, ROOT)
    for p in probs:
        print('deviations: %s: %s' % (rel, p))
    if probs:
        return 1
    print('deviations: ok (%s: %d header items, each marked inline; %d markers)'
          % (rel, len(items), sum(len(v) for v in markers.values())))
    return 0


if __name__ == '__main__':
    sys.exit(main())
