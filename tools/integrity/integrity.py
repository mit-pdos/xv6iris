#!/usr/bin/env python3
"""integrity.py -- proof-integrity gate for the xv6iris fork (see README.md beside this file).

    integrity.py check  [--base REF] [--tree REF|INDEX|WORK] [--upstream REF|none] [--quiet]
    integrity.py audit  [--switch S] [--opam-root DIR] [--from-log FILE] [--no-record]
    integrity.py hook   pre-commit | commit-msg FILE

`check` compares two trees and sorts what it finds into
  BLOCK   -- ours, or unconditional: a commit to main needs INTEGRITY_ALLOW=<fingerprint>
  REVIEW  -- attributed to upstream, or ours but non-blocking (Module Type fields, vanished
             declarations, _CoqProject rows, pin bumps, CI files): read, do not approve
and reports the audit gate: whether the exact tree being committed has a recorded
`Print Assumptions` result identical to tools/integrity/audit-baseline.txt (`audit` writes it).
Exit status 1 iff something blocks.

Everything is computed on git tree objects, so the hook checks what is being committed (the
index), not what happens to be on disk.  WORK = a temporary index of the working tree
(tracked + untracked, .gitignore respected).
"""
import argparse, hashlib, os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
BASELINE = os.path.join(HERE, "audit-baseline.txt")
PROOF_DIRS = ("iris/", "model-xv6iris/", "kernel-rocq/", "user-rocq/")
AUDIT_FILES = ("iris/SystemAssumptions.v", "iris/TreeAssumptions.v", "iris/UnionAssumptions.v")
AUDIT_TARGETS = (("audit-only", "SystemAssumptions.v"), ("audit-tree-only", "TreeAssumptions.v"),
                 ("audit-union-only", "UnionAssumptions.v"))
# Makefile lines whose change moves the trust base: the audit recipes, what runs coqc, the switch.
TRUST_MK = re.compile(r"audit|AUDIT_FLAGS|^\s*RUN\b|^\s*SWITCH\b|coqc|coq_makefile|Assumptions\.v|"
                      r"^\s*proofs:|CoqMakefile:")
# our own files that decide what "green" means: always ours, always blocking
TRUST_OURS = ("opam/xv6rocq.export", "tools/integrity/")

# ---------------------------------------------------------------- git plumbing
def git(*args, check=True, binary=False):
    r = subprocess.run(["git", *args], capture_output=True, check=False)
    if check and r.returncode != 0:
        raise SystemExit(f"git {' '.join(args)}: {r.stderr.decode(errors='replace').strip()}")
    return r.stdout if binary else r.stdout.decode("utf-8", "replace")

def common_dir():
    return os.path.abspath(git("rev-parse", "--git-common-dir").strip())

def resolve_tree(spec):
    if spec == "INDEX":
        return git("write-tree").strip()
    if spec == "WORK":
        with tempfile.TemporaryDirectory() as d:
            env = dict(os.environ, GIT_INDEX_FILE=os.path.join(d, "index"))
            subprocess.run(["git", "read-tree", "HEAD"], env=env, check=True)
            subprocess.run(["git", "add", "-A", "--", "."], env=env, check=True,
                           capture_output=True)
            return subprocess.run(["git", "write-tree"], env=env, check=True,
                                  capture_output=True, text=True).stdout.strip()
    return git("rev-parse", f"{spec}^{{tree}}").strip()

def show(tree, path):
    r = subprocess.run(["git", "show", f"{tree}:{path}"], capture_output=True)
    return r.stdout.decode("utf-8", "replace") if r.returncode == 0 else None

def changed(base, tree):
    out = []
    for l in git("diff", "--name-status", "--no-renames", base, tree).splitlines():
        st, path = l.split("\t", 1)
        out.append((st, path))
    return out

def grep_tree(tree, pattern, pathspec):
    r = subprocess.run(["git", "grep", "-l", "-E", pattern, tree, "--", pathspec],
                       capture_output=True, text=True)
    return [l.split(":", 1)[1] for l in r.stdout.splitlines()]

def importers(tree, modname):
    """Files in the tree whose CODE (not comments) has a Require sentence naming modname."""
    cands = grep_tree(tree, r"Require[^.]*\b" + re.escape(modname) + r"\b", "*.v")
    rx = re.compile(r"\bRequire\b[^.]*\b" + re.escape(modname) + r"\b")
    return [f for f in cands if rx.search(code_only(show(tree, f) or ""))]

def newest_upstream(commits):
    """The most recent upstream/main commit contained in any of the given commits, or None."""
    if subprocess.run(["git", "rev-parse", "-q", "--verify", "upstream/main"],
                      capture_output=True).returncode != 0:
        return None
    best = None
    for c in commits:
        r = subprocess.run(["git", "merge-base", c, "upstream/main"], capture_output=True, text=True)
        if r.returncode != 0:
            continue
        mb = r.stdout.strip()
        if best is None or subprocess.run(["git", "merge-base", "--is-ancestor", best, mb]).returncode == 0:
            best = mb
    return best

# ---------------------------------------------------------------- Rocq source scanning
def code_only(src):
    """Blank out comments (nested) and string literals, keeping line structure."""
    out, i, depth, instr, n = [], 0, 0, False, len(src)
    while i < n:
        if not instr and src.startswith("(*", i):
            depth += 1; i += 2; out.append("  "); continue
        if depth and src.startswith("*)", i):
            depth -= 1; i += 2; out.append("  "); continue
        c = src[i]
        if depth == 0 and c == '"':
            instr = not instr; out.append(" "); i += 1; continue
        out.append(c if (depth == 0 and not instr) or c == "\n" else " ")
        i += 1
    return "".join(out)

KW_PREFIX = r"^\s*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*"
RE_ASSUME = re.compile(KW_PREFIX + r"(Axioms?|Parameters?|Conjectures?)\b")
RE_SECVAR = re.compile(KW_PREFIX + r"(Variables?|Hypothes[ie]s|Context)\b")
RE_ADMIT = re.compile(r"(?<![A-Za-z_'])Admitted\s*\.|(?<![A-Za-z_'])(admit|give_up)\s*(\.|;|\)|$)|"
                      r"(?<![A-Za-z_'])admit\s*$")
RE_ADMIT_ANY = re.compile(r"(?<![A-Za-z_'])(Admitted|admit|give_up)(?![A-Za-z0-9_'])")
RE_ABORT = re.compile(r"^\s*Abort\s*\.")
RE_CHECKER = re.compile(r"Unset\s+(Guard|Positivity|Universe)\s+Checking|bypass_check|"
                        r"Admit\s+Obligations")
RE_OPEN = re.compile(r"^\s*(Module\s+Type|Module|Section)\s+([A-Za-z_][A-Za-z0-9_']*)")
RE_END = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.")
RE_RISKY_RAW = re.compile(r"\b(Admitted|admit|give_up|Axioms?|Parameters?|Conjectures?)\b|"
                          r"Unset (Guard|Positivity|Universe) Checking|bypass_check|Admit Obligations")

def scan(src):
    """Findings in the code of one file: list of (kind, lineno, text, in_module_type)."""
    code = code_only(src)
    out, stack = [], []
    for ln, line in enumerate(code.splitlines(), 1):
        m = RE_OPEN.match(line)
        if m and not re.search(r":=\s*\S", line):
            stack.append((m.group(1).split()[0] + (" Type" if "Type" in m.group(1) else ""), m.group(2)))
        e = RE_END.match(line)
        if e:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][1] == e.group(1):
                    del stack[k:]; break
        in_mt = any(t == "Module Type" for t, _ in stack)
        in_sec = any(t == "Section" for t, _ in stack)
        text = line.strip()
        if RE_CHECKER.search(line):
            out.append(("CHECKER", ln, text, in_mt))
        if RE_ADMIT.search(line):
            out.append(("ADMIT", ln, text, in_mt))
        elif RE_ABORT.match(line):
            out.append(("ABORT", ln, text, in_mt))
        if RE_ASSUME.match(line) or (RE_SECVAR.match(line) and not in_sec):
            out.append(("ASSUME", ln, text, in_mt))
    return out

def raw_hits(src):
    return sum(1 for l in src.splitlines() if RE_RISKY_RAW.search(l))

def decls(src):
    """name -> keyword of every declaration, on comment-free text (upstream's lemma_diff regex)."""
    sys.path.insert(0, os.path.dirname(HERE))
    try:
        import lemma_diff  # tools/lemma_diff.py
        rx = lemma_diff.DECL
    except Exception:
        rx = re.compile(KW_PREFIX + r"(Lemma|Theorem|Corollary|Remark|Fact|Proposition|Definition|"
                        r"Fixpoint|CoFixpoint|Inductive|Record|Class|Instance|Axiom|Parameter|"
                        r"Hypothesis|Module Type|Module|Notation|Ltac)\s+([A-Za-z_][A-Za-z0-9_']*)",
                        re.MULTILINE)
    out = {}
    for kw, name in rx.findall(code_only(src)):
        out.setdefault(name, kw)
    return out

RE_STMT = re.compile(KW_PREFIX + r"(Lemma|Theorem|Corollary|Remark|Fact|Proposition|Definition|Fixpoint|"
                     r"CoFixpoint|Instance|Axiom|Parameter|Hypothesis|Inductive|Record|Class|Example)\s+"
                     r"([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)

def sentence_end(code, i):
    """Index just past the '.' that ends the vernac sentence starting at i (a '.' followed by
    whitespace or EOF; '.' inside qualified names, projections and '..' does not count)."""
    n = len(code)
    while i < n:
        j = code.find(".", i)
        if j < 0:
            return n
        if (j + 1 >= n or code[j + 1].isspace()) and (j == 0 or code[j - 1] != "."):
            return j + 1
        i = j + 1
    return n

def statements(src):
    """name -> list of normalised statement texts (the whole declaring sentence, so a Definition's
    body counts), on comment-free text. Several declarations may share a name across sections."""
    code = code_only(src)
    out = {}
    for m in RE_STMT.finditer(code):
        end = sentence_end(code, m.end())
        text = re.sub(r"\s+", " ", code[m.start():end]).strip()
        out.setdefault(m.group(2), []).append(text)
    return out

# ---------------------------------------------------------------- the check
class Report:
    def __init__(self):
        self.block, self.review, self.notes = [], [], []
        self.ignored = 0
    def add(self, blocking, who, kind, path, text):
        (self.block if blocking else self.review).append((who, kind, path, text))
    def collapse(self, limit=5):
        """Group items of one kind, origin and file when there are many (regenerated catalogs,
        upstream's statement changes). The fingerprint is taken over the ungrouped BLOCK list."""
        self._fp = self._fingerprint(self.block)
        def group(items):
            groups, out = {}, []
            for it in items:
                groups.setdefault(it[:3], []).append(it[3])
            for key, texts in groups.items():
                if len(texts) <= limit:
                    out += [(*key, t) for t in texts]
                else:
                    out.append((*key, f"{len(texts)} items: " + "; ".join(t[:80] for t in texts[:3]) + f"; ... (+{len(texts) - 3})"))
            return out
        self.review, self.block = group(self.review), group(self.block)
    @staticmethod
    def _fingerprint(block):
        # path without its :line suffix, so an unrelated edit above a finding keeps the approval valid
        h = hashlib.sha256("\n".join(sorted(f"{k}|{re.sub(r':[0-9]+$', '', p)}|{t}"
                                            for _, k, p, t in block)).encode())
        return h.hexdigest()[:12]
    def fingerprint(self):
        return getattr(self, "_fp", None) or self._fingerprint(self.block)

def coqproject_parts(text):
    flags, rows, off = [], set(), set()
    for l in (text or "").splitlines():
        s = l.strip()
        if s.startswith("-"):
            flags.append(s)
        elif re.match(r"^[A-Za-z0-9_/.-]+\.v$", s):
            rows.add(s)
        elif re.match(r"^#\s*[A-Za-z0-9_/.-]+\.v$", s):
            off.add(s.lstrip("# "))
    return flags, rows, off

def in_upstream(up_text, text):
    return up_text is not None and text.strip() in {l.strip() for l in up_text.splitlines()}

def check(base, tree, upstream, gate_tree=None):
    """gate_tree: the tree the audit record is looked up for (the index when `tree` is the working
    tree, since only what is staged can be committed); defaults to `tree`."""
    gate_tree = gate_tree or tree
    rep = Report()
    up = (lambda p: show(upstream, p)) if upstream else (lambda p: None)
    proofs_touched = False
    for st, path in changed(base, tree):
        old, new = show(base, path), show(tree, path)
        u = up(path)
        def who_line(text):
            return "upstream" if in_upstream(u, text) else "ours"
        if path.endswith(".v") and path.startswith(PROOF_DIRS):
            proofs_touched = True
            if st == "D":
                users = importers(tree, os.path.basename(path)[:-2])
                who = "upstream" if (upstream and u is None) else "ours"   # deleted upstream too
                rep.add(bool(users), who, "DELETED", path,
                        f"file deleted" + (f"; still named in {', '.join(users[:3])}" if users else ""))
                continue
            if path.startswith("model-xv6iris/"):
                who = "upstream" if (u is not None and u == new) else "ours"
                rep.add(True, who, "MODEL", path, "generated model file changed")
            if path in AUDIT_FILES:
                who = "upstream" if (u is not None and u == new) else "ours"
                rep.add(True, who, "AUDITFILE", path, "audit file changed")
            rep.ignored += max(0, raw_hits(new) - len(scan(new)))
            before = {}
            for k, _, t, mt in (scan(old) if old else []):
                before[(k, t, mt)] = before.get((k, t, mt), 0) + 1
            for k, ln, t, mt in scan(new):
                if before.get((k, t, mt), 0):
                    before[(k, t, mt)] -= 1; continue
                who = who_line(t)
                where = f"{path}:{ln}"
                if k == "CHECKER":
                    rep.add(True, who, k, where, t)
                elif k == "ADMIT":
                    rep.add(True, who, k, where, t)
                elif k == "ABORT":
                    rep.add(False, who, k, where, t)
                elif k == "ASSUME":
                    if mt:
                        rep.add(False, who, "MT-FIELD", where, t)      # a Module Type field: the spec pattern
                    else:
                        rep.add(True, who, "AXIOM", where, t)  # a real assumption
            if old is not None:
                b, a = decls(old), decls(new)
                for name, kw in b.items():
                    if name not in a:
                        gone_up = bool(upstream) and (u is None or name not in decls(u))
                        rep.add(False, "upstream" if gone_up else "ours", "GONE", path, f"{kw} {name}")
                # the statement diff: a declaration kept under its name but saying something else
                sb, sa = statements(old), statements(new)
                su = statements(u) if u is not None else None
                for name in sb:
                    if name not in sa or sorted(sb[name]) == sorted(sa[name]):
                        continue
                    if su is not None and name in su and sorted(su[name]) == sorted(sa[name]):
                        who = "upstream"            # upstream's version says exactly this
                    elif su is not None and (name not in su or sorted(su[name]) != sorted(sb[name])):
                        who = "upstream~"           # upstream changed it too; ours differs textually (renames?)
                    else:
                        who = "ours"
                    was = [t for t in sb[name] if t not in sa[name]][:1]
                    now = [t for t in sa[name] if t not in sb[name]][:1]
                    rep.add(True, who, "STATEMENT", path, f"{name}: was `{was[0] if was else '?'}` now `{now[0] if now else '?'}`")
        elif os.path.basename(path) == "_CoqProject":
            proofs_touched = True
            of, orows, ooff = coqproject_parts(old); nf, nrows, noff = coqproject_parts(new)
            uf = coqproject_parts(u)[0] if u is not None else None
            if of != nf:
                who = "upstream" if uf == nf else "ours"
                d = [f"-{x}" for x in of if x not in nf] + [f"+{x}" for x in nf if x not in of]
                rep.add(True, who, "FLAGS", path, "flags/load paths changed: " + " ".join(d))
            add, rem = sorted(nrows - orows), sorted(orows - nrows)
            if add or rem:
                probs = []
                for r in add:
                    if show(tree, os.path.join(os.path.dirname(path), r)) is None:
                        probs.append(f"{r} listed but missing")
                for r in rem:
                    f = os.path.join(os.path.dirname(path), r)
                    if show(tree, f) is not None and r not in noff:
                        probs.append(f"{r} unlisted but still present (not built any more)")
                who = "upstream" if (u is not None and coqproject_parts(u)[1] == nrows) else "ours"
                rep.add(bool(probs), who, "ROWS", path,
                        f"+{len(add)} -{len(rem)} rows" + ("; " + "; ".join(probs) if probs else ""))
            if ooff != noff:
                rep.add(False, "upstream" if (u is not None and coqproject_parts(u)[2] == noff) else "ours",
                        "AUDIT-ROWS", path, "commented (audit) rows changed: " +
                        " ".join(sorted(noff - ooff)) + " " + " ".join("-" + x for x in sorted(ooff - noff)))
        elif path == "Makefile":
            proofs_touched = True
            diff = git("diff", "-U0", base, tree, "--", path)
            lines = [l for l in diff.splitlines() if l[:1] in "+-" and not l.startswith(("+++", "---"))]
            # per changed line: a '+' line upstream also has, or a '-' line upstream also lacks, is
            # upstream's; comment lines never move the trust base
            def mk_who(l):
                if u is None:
                    return "ours"
                present = in_upstream(u, l[1:])
                return "upstream" if (present if l[0] == "+" else not present) else "ours"
            trust = [l for l in lines if not l[1:].lstrip().startswith("#") and TRUST_MK.search(l[1:])]
            ours_trust = [l for l in trust if mk_who(l) == "ours"]
            up_trust = [l for l in trust if mk_who(l) == "upstream"]
            if ours_trust:
                rep.add(True, "ours", "MAKEFILE", path, "audit/toolchain recipe lines changed: " +
                        " | ".join(t.strip() for t in ours_trust[:6]))
            if up_trust:
                rep.add(True, "upstream", "MAKEFILE", path, "audit/toolchain recipe lines changed: " +
                        " | ".join(t.strip() for t in up_trust[:6]))
            rest = [l for l in lines if l not in trust and l[1:].strip()]
            if rest:
                n_up = sum(1 for l in rest if mk_who(l) == "upstream")
                rep.add(False, "upstream" if n_up == len(rest) else "ours", "MAKEFILE", path,
                        f"{len(rest)} other changed line(s) ({n_up} upstream's), e.g. " +
                        " | ".join(l.strip() for l in rest if mk_who(l) == "ours" or n_up == len(rest))[:200])
        elif path.startswith(TRUST_OURS) or path == BASELINE_REL():
            proofs_touched = proofs_touched or path.startswith("opam/")
            rep.add(True, "ours", "TRUST", path, {"A": "added", "D": "deleted"}.get(st, "changed"))
        elif path.startswith(".github/"):
            who = "upstream" if (u is not None and u == new) else "ours"
            rep.add(False, who, "CI", path, {"A": "added", "D": "deleted"}.get(st, "changed"))
    # the audit gate
    rec = audit_record(gate_tree)
    if rec:
        rep.notes.append(f"audit gate: tree {gate_tree[:12]} audited {rec.strip()}")
    elif proofs_touched:
        rep.add(True, "ours", "NOT-AUDITED", gate_tree[:12],
                "proof-relevant files changed and this exact tree has no recorded audit "
                "(build it, then run integrity.py audit)")
    else:
        rep.notes.append("audit gate: no proof-relevant change; not required")
    if gate_tree != tree:
        extra = [p for _, p in changed(gate_tree, tree) if proof_relevant(p)]
        if extra:
            rep.notes.append(f"note: {len(extra)} proof-relevant path(s) differ between the working tree "
                             f"and the index (unstaged or untracked), e.g. {', '.join(extra[:3])}: "
                             "they are checked above but cannot be committed or audited as they are")
    rep.collapse()
    return rep

def proof_relevant(path):
    return ((path.endswith(".v") and path.startswith(PROOF_DIRS)) or os.path.basename(path) == "_CoqProject"
            or path == "Makefile" or path.startswith(TRUST_OURS))

def BASELINE_REL():
    return os.path.relpath(BASELINE, git("rev-parse", "--show-toplevel").strip())

def audit_record(tree):
    p = os.path.join(common_dir(), "integrity", "audits", tree)
    return open(p).read() if os.path.exists(p) else None

def print_report(rep, base, tree, upstream, quiet=False):
    print(f"integrity check: {base[:12]}..{tree[:12]}"
          + (f"  (upstream contained: {upstream[:12]})" if upstream else "  (no upstream attribution)"))
    def dump(title, items):
        if not items:
            return
        print(f"\n== {title}")
        for who, kind, path, text in items:
            print(f"  [{who:8}] {kind:11} {path}: {text[:150]}")
    dump(f"BLOCKING  -- a commit to main needs INTEGRITY_ALLOW={rep.fingerprint()}", rep.block)
    if not quiet:
        dump("REVIEW    -- read; nothing to approve", rep.review)
    else:
        print(f"\n== REVIEW: {len(rep.review)} item(s) (run without --quiet to list them)")
    for n in rep.notes:
        print(f"\n{n}")
    if rep.ignored:
        print(f"ignored: {rep.ignored} keyword match(es) inside comments or strings")
    print("\nintegrity: " + ("BLOCKED" if rep.block else "OK"))

# ---------------------------------------------------------------- the audit
def parse_audit_log(text):
    """{audit-target-file: sorted distinct axiom names} from `make audit-*-only` output."""
    res, cur, in_ax = {}, None, False
    for l in text.splitlines():
        m = re.search(r"-noglob\s+(\S+Assumptions\.v)", l)
        if m:
            cur = m.group(1); res.setdefault(cur, set()); in_ax = False; continue
        if cur is None:
            continue
        if l.startswith("Axioms:"):
            in_ax = True; continue
        if l.startswith("Closed under the global context"):
            in_ax = False; continue
        if in_ax and re.match(r"^[A-Za-z_][A-Za-z0-9_.']*\s*:", l):
            res[cur].add(l.split(":", 1)[0].strip())
    return {k: sorted(v) for k, v in res.items()}

def read_baseline():
    res, cur = {}, None
    for l in open(BASELINE):
        s = l.strip()
        if not s or s.startswith("#"):
            continue
        m = re.match(r"^\[(\S+)\]\s+(\S+)$", s)
        if m:
            cur = m.group(2); res[cur] = []; continue
        res[cur].append(s)
    return {k: sorted(v) for k, v in res.items()}

def make_env(opam_root):
    env = dict(os.environ)
    if opam_root:
        env["OPAMROOT"] = opam_root; env.pop("OPAMSWITCH", None)
    return env

def tree_is_built(switch, env):
    pending = []
    for d in PROOF_DIRS:
        d = d.rstrip("/")
        if not os.path.exists(os.path.join(d, "CoqMakefile")):
            pending.append(f"{d}: no CoqMakefile"); continue
        r = subprocess.run(["opam", "exec", f"--switch={switch}", "--", "make", "-f", "CoqMakefile", "-n"],
                           cwd=d, env=env, capture_output=True, text=True)
        n = len([l for l in r.stdout.splitlines() if re.search(r"coqc|rocq (c|compile)", l)])
        if n:
            pending.append(f"{d}: {n} file(s) not built")
    return pending

def audit(switch, opam_root, from_log, record):
    os.chdir(git("rev-parse", "--show-toplevel").strip())
    env = make_env(opam_root)
    pending = tree_is_built(switch, env)
    if pending:
        print("tree not fully built -- an audit of it would be archaeology:\n  " + "\n  ".join(pending))
        return 2
    if from_log:
        log = open(from_log).read()
    else:
        targets = [t for t, _ in AUDIT_TARGETS]
        print(f"running make {' '.join(targets)} SWITCH={switch} ...", flush=True)
        r = subprocess.run(["make", "-j3", "--output-sync=target", *targets, f"SWITCH={switch}"],
                           env=env, capture_output=True, text=True)
        log = r.stdout + r.stderr
        if r.returncode != 0:
            print(log[-3000:]); print(f"audit build failed (exit {r.returncode})"); return 2
    got, want = parse_audit_log(log), read_baseline()
    ok = True
    for _, f in AUDIT_TARGETS:
        g, w = got.get(f), want.get(f)
        if g is None:
            print(f"{f}: no output found"); ok = False; continue
        if g == w:
            print(f"{f}: {len(g)} axioms, IDENTICAL to the baseline")
        else:
            ok = False
            print(f"{f}: DIFFERS from the baseline: +{sorted(set(g) - set(w))} -{sorted(set(w) - set(g))}")
    if not ok:
        return 1
    if record:
        # the record names the INDEX tree: only what is staged can be committed, and a later
        # `git add` of a proof file changes that tree, which voids the record -- as it should
        unstaged = [l for l in git("status", "--porcelain").splitlines()
                    if l[1] in "MDA?" and proof_relevant(l[3:].strip())]
        if unstaged:
            print("not recorded: the working tree has unstaged/untracked proof-relevant changes "
                  f"({len(unstaged)}, e.g. {unstaged[0].strip()}); stage or drop them, rebuild if needed, rerun")
            return 3
        tree = resolve_tree("INDEX")
        d = os.path.join(common_dir(), "integrity", "audits"); os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, tree), "w") as fh:
            fh.write(f"{time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime())} switch={switch} "
                     + " ".join(f"{f}={len(got[f])}" for _, f in AUDIT_TARGETS) + " = baseline\n")
        print(f"recorded: tree {tree} audited (all three identical to the baseline)")
    return 0

# ---------------------------------------------------------------- hooks
def hook_pre_commit():
    if git("rev-parse", "--abbrev-ref", "HEAD").strip() != "main":
        return 0
    heads = ["HEAD"]
    if os.path.exists(os.path.join(git("rev-parse", "--git-dir").strip(), "MERGE_HEAD")):
        heads.append("MERGE_HEAD")
    upstream = newest_upstream(heads)
    tree = resolve_tree("INDEX")
    rep = check("HEAD", tree, upstream)
    os.makedirs(os.path.join(common_dir(), "integrity"), exist_ok=True)
    with open(os.path.join(common_dir(), "integrity", "last-report"), "w") as fh:
        fh.write(f"{rep.fingerprint()}\n" + "\n".join(f"{k} {p}: {t}" for _, k, p, t in rep.block) + "\n")
    if not rep.block:
        return 0
    allow = os.environ.get("INTEGRITY_ALLOW", "")
    if allow == rep.fingerprint():
        print(f"integrity: {len(rep.block)} blocking finding(s) approved by INTEGRITY_ALLOW={allow}")
        return 0
    print_report(rep, "HEAD", tree, upstream, quiet=True)
    if allow:
        print(f"\nINTEGRITY_ALLOW={allow} does not match this report's fingerprint "
              f"{rep.fingerprint()} -- re-read the BLOCKING list above, then set it to that value.")
    return 1

def hook_commit_msg(path):
    if git("rev-parse", "--abbrev-ref", "HEAD").strip() != "main":
        return 0
    allow = os.environ.get("INTEGRITY_ALLOW", "")
    rp = os.path.join(common_dir(), "integrity", "last-report")
    if not allow or not os.path.exists(rp):
        return 0
    fp, *lines = open(rp).read().splitlines()
    if fp != allow or not lines:
        return 0
    msg = open(path).read()
    if f"Integrity-Allow: {fp}" in msg:
        return 0
    with open(path, "w") as fh:
        fh.write(msg.rstrip("\n") + f"\n\nIntegrity-Allow: {fp}\n" +
                 "".join(f"  {l}\n" for l in lines if l))
    return 0

# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("--base", help="default: merge-base with main (HEAD when on main)")
    c.add_argument("--tree", default="WORK", help="REF, INDEX or WORK (default)")
    c.add_argument("--upstream", help="upstream commit for attribution; default: newest upstream/main "
                                       "commit contained in the tree's commit(s); 'none' disables")
    c.add_argument("--quiet", action="store_true")
    a = sub.add_parser("audit")
    a.add_argument("--switch", default="/shared/xv6rocq")
    a.add_argument("--opam-root", default=None)
    a.add_argument("--from-log", default=None, help="parse an existing make audit-*-only log instead of running")
    a.add_argument("--no-record", action="store_true")
    h = sub.add_parser("hook"); h.add_argument("which", choices=["pre-commit", "commit-msg"]); h.add_argument("file", nargs="?")
    args = ap.parse_args()
    os.chdir(git("rev-parse", "--show-toplevel").strip())
    if args.cmd == "hook":
        return hook_pre_commit() if args.which == "pre-commit" else hook_commit_msg(args.file)
    if args.cmd == "audit":
        return audit(args.switch, args.opam_root, args.from_log, not args.no_record)
    on_main = git("rev-parse", "--abbrev-ref", "HEAD").strip() == "main"
    base = args.base or ("HEAD" if on_main else git("merge-base", "HEAD", "main").strip())
    base_tree = resolve_tree(base)
    tree = resolve_tree(args.tree)
    if args.upstream == "none":
        upstream = None
    elif args.upstream:
        upstream = git("rev-parse", args.upstream).strip()
    else:
        cands = ["HEAD"] if args.tree in ("INDEX", "WORK") else [args.tree]
        if os.path.exists(os.path.join(git("rev-parse", "--git-dir").strip(), "MERGE_HEAD")):
            cands.append("MERGE_HEAD")
        upstream = newest_upstream(cands)
    gate = resolve_tree("INDEX") if args.tree == "WORK" else tree
    rep = check(base_tree, tree, upstream, gate)
    print_report(rep, base_tree, tree, upstream, args.quiet)
    return 1 if rep.block else 0

if __name__ == "__main__":
    sys.exit(main())
