# Duplicate-theorem finder (cleanup lane B, Sept 29 2026)

- `Dups.lean`: metaprogram that groups theorems whose statements are identical up to binder names, and
  definitions with identical type and body. Run on a machine sized for a Lean build: `lake env lean tools/dups/Dups.lean`.
- `analyze.py` / `apply.py`: classification and the mechanical merge (keep one copy, re-point users, add
  imports only to strictly-lower modules).
- `dups.jsonl`: the groups found at 97b85e825; `home_skipped.txt`: why each unmerged group was left
  (Link re-exports, kernel-address equations, no good shared name, name clashes, non-compiling moves).
