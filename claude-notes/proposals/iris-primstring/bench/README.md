# Iris `ident` representation benchmark

Self-contained; needs only `coq-iris` + `coq-stdpp` on Rocq >= 9.0.

- `repr.v` — node cost of one hypothesis-name literal, Stdlib `string` vs
  `PrimString.string` (read with `rocq compile -q -d hconstr repr.v`, which
  prints each constant's proof-term tree size).
- `feas.v` — the `string -> PrimString.string` bridge: it reduces to a 1-node
  literal under `vm_compute`, and three kernel-checked `eq_refl`s show it is
  correct.
- `gen.py` — generates a proofmode proof holding N hypotheses and performing M
  context-preserving steps, parameterised by hypothesis-name length (or `anon`,
  which uses `?` and so `IAnon`).
- `run.sh` — sweep driver; prints `N M mode tree bindings wall_s peak_RSS_KB`.
- `raw-results.txt` — the runs quoted in `../PR.md`.

```bash
rocq compile -q -d hconstr repr.v
rocq compile -q -d hconstr feas.v
./run.sh 40 200 4 8 12 16 anon
```

See `../PR.md` for the numbers and what they mean.
