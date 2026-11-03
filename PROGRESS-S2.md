# S2 progress — ownership-free core (plan rev 7 §2, §8 S2)

## Status (top): GREEN; no kill criterion fired
- K2a: no forbidden row needed a program hypothesis (rows 2–6 use only A0's exports + Ψ/π proved step by step).
- K2b: A0 `Weak.Prom.PF.adequacy` proved with NO named assumption; `#print axioms`: propext, Classical.choice,
  Quot.sound. It uses the proved `validRun_factorL` (via `validRun_statePhase`).
- K2c: rows 2, 3, 4, 5 all closed in the logic (row 5 non-vacuous: `mach_lrsc`, row 31).
- K2d: 4.1k lines (bound 15k).
- Build: `lake build Weak.Prom.CoreLit6` green (closure = all Core files); lint: only expected drift findings.

## Files (Weak/Prom/)
1. `CoreDefs.lean` — `PFRun.trace/fulfils/traceWf/obsLoad/done`, `PF.validRun`, `Proto`, `Valid`, guard `grd`
   (⟦V⟧) + rules, `protoOk`, `validInduction`, A/D vocabulary (vacuous on v2: no A/D class), `devFreeProg`/`reachP`.
2. `CoreRun.lean` — machine lemmas: device-general hart separation `validRun_soloD`, `solo_fulfils`,
   A0 (iii) `validRun_partition`, A0 (v) `validRun_traceWf`.
3. `CoreFwd.lean` — forward-bank knowledge invariant FK, fetch bound FI, `fulPv` (EXT pre-view), `fwd_step`;
   `stFloor`/`floors_mono` (moved from CoreRules).
4. `CoreWp.lean` — hart language (one machine-v2 state step per label), `hartSt`, state interpretation with the
   guarded step invariant (Ψ guard, protoOk, FI, FK), `wpH`/`wpPF`, `wpH_liftF`/`wpH_lift` (▷ + £1 per step),
   ⟦·⟧ᵢ (`validUpTo`, `grdI`) + rules.
5. `CoreAdeq.lean` — A0 `PF.adequacy` (exports (i)–(vi)) via iris-lean `wp_strong_adequacy_gen`.
6. `CoreRules.lean` — leaf rules LOAD (+ `wpH_load_fwd`), REGW, INSTR, CTRL, FENCE, FULFIL, LR, SC, EXFAIL, any,
   done; (X4) `loadRun_ldv`, (X5) `regv_regW`/`regv_instr`, (X6) `store_ext`; `fwdRead`, `fwdMono`, `fwdMono_bound`.
7. `CoreLitBase.lean` — closed functor bundle `pfGF`; litmus program-half lemmas; Ψ (P0)–(P4) `ΨLB`, row-5 Ψ
   `ΨLS`; contradictions `lb_contra`, `lrsc_contra` (from exports (ii), (iii), (v) only).
8. `CoreLit.lean` — `lit_lbdd` (row 2), `lit_lbfd` (row 3), `lit_lbctrl` (row 4), `lit_lb_allowed` (row 1 =
   `mach_lb` + remark).
9. `CoreLit5.lean` — `lit_lbLrsc` (row 5).
10. `CoreLit6.lean` — `lit_oota42` (row 6, through the ⟦·⟧ protocol "every byte is 0"; Ψ = True; exports (iv), (v)).

## Open items
- Row 38 (guarded Ψ on a doomed branch): not done (the litmus front end has no fault event; needs a Ψ like
  "every ld base ∈ {x, z}" proved under ⟦s⟧ from the pointer protocol).
- Rows 8–25, 28, 28c, 32, 37, 46, 48 not attempted. Row 50 negative lemma skipped (translation deferred, [OWN.P3]).
- `devFreeProg` is a premise of A0 as stated but unused by the proof (the per-hart wp is over every fabric value).
