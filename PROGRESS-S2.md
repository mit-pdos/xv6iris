# S2 progress — ownership-free core (plan rev 7 §2, §8 S2)

## Status (top): GREEN; no kill criterion fired (S2b increment, 2026-11-03)
- K2a: no forbidden row needed a program hypothesis: every `lit_` uses only A0's exports (i)–(v) + Ψ/π/Φ proved
  step by step by each hart's wp (none uses a `mach_` enumeration checker).
- K2b: A0 `Weak.Prom.PF.adequacy` proved with NO named assumption (unchanged); every `lit_` theorem's
  `#print axioms`: propext, Classical.choice, Quot.sound.
- K2c: rows 2, 3, 4, 5 all closed in the logic (row 5 non-vacuous: `mach_lrsc`, row 31).
- K2d: 10.2k lines in `Core*.lean` (bound 15k).
- Build: `lake build Weak.Prom.CoreLitDR Weak.Prom.CoreFwdRel` green (closure = all Core files); lint: only the
  expected drift findings (Weak/Prom files are not imported from the roots, by design).
- All FORBIDDEN rows of plan §8 S2 that machine v2 / RefTests cover are now closed in the logic, plus row 38:
  2, 3, 4, 5, 6, 8, 8′, 9, 10, 11, 11b, 13, 16, 18, 21′, 22 (×7), 23, 24 (×2), 25, 28, 28c, 32, 37, 38.
  Out of scope (phase 1, [OWN.P3] translation deferred; machine v2 has no walks / A/D): 46, 48.

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

## S2b increment (forbidden rows beyond the LB family) — done
- New kit (no new rule of the logic; every lemma composes CoreRules' leaf rules):
  `CoreKit.lean` (memory entries `memEv`, `wrOk`, `ΨK`, `lh`; one-label rules `wpK_q1/drain/load1/store1/rmw1/lr1/sc1`;
  instruction rules `wpK_ld/sw/alu/alui/fence/br/amo/lr/sc/end`), `CoreKitV.lean` (view facts: `loadRun_b0`,
  `loadRun_mono`, `storeRun_mono`, `ldPre_ge`, `stPreA_ge`, `loadOk_b0nc`, `loadOk_sp2`, field simp set; A0 wrapper
  `kitAdeq`; toolkit `kit_writer`, `kit_read`, `lastByte`, `finalMem_b0`, `lastByte_cases`), `CoreKitQ.lean`
  (prefix patterns `q1..q4`, entry shapes `isLd/isSt/isRmw`, `progs_get`, `LPstep_at`).
- Generic harts `CoreLitH.lean` (each hart's wp proof by the kit; Ψ records the order fact of one view fact):
  `hWW/hWWc` (fence w / COH), `hRR/hRRc` (fence r / coherence floor), `hRW/hRWc`, `hWR/hWRc`, `hW`, `hLW`; writer
  and outcome lemmas of their Ψ's; `writer_cases`.
- Rows closed in the logic (axioms of each: propext, Classical.choice, Quot.sound):
  8 `lit_mpFF`, 8′ `lit_mpFFrr` (CoreLitMP.lean); 13 `lit_sbFF`, 21′ `lit_w22F` (needs both harts finished,
  A0 (i)), 24 `lit_isa2F`, `lit_wrcF`, 25 `lit_iriwF` (CoreLitF.lean); 22 `lit_coWW` (H0 finished ⇒ x = 2),
  `lit_coWR0`, `lit_coWR`, `lit_coRW1`, `lit_coRW2` (H1 finished), `lit_coRR`, `lit_coRR2` (CoreLitCo.lean; each
  states the row's coherence-violating outcome, see the file header for the map to the repository conditions);
  9 `lit_mpFAddr` (CoreLitMP.lean, address dependency through `xor; add`); 10 `lit_mpAmoRlAq`, 11 `lit_mpFAmo`,
  11b `lit_amoStorePart`, 28 `lit_mpAmoData`, 28c `lit_mpAmoCtrl` (CoreLitA.lean, the fused AMO's view facts);
  37 `lit_lrScSc` (final registers of the finished hart, A0 (i), value map `litFin`), 32 `lit_mixSca` (M9 single
  read point) (CoreLitM.lean); 38 `lit_mpPtr` (CoreLitP.lean: faulting front end `litStepF acc` = `litStep` plus a
  load-access fault event `LSilent` at an address outside the PMA set `acc`; protocol "p ∈ {&x, &z}" byte-wise;
  the doomed branch's fault step is proved from `⟦|M|⟧False`; A0 (ii) + (iv): no valid run has a fault);
  18 `lit_addrpo` (CoreLitAd.lean, rule 13 through a loaded pointer; a misaligned loaded address is stuck);
  23 `lit_parInc` (CoreLitPI.lean, `exclOk` atomicity window; both harts finished, A0 (i)); 16 `lit_datarfi`
  (CoreLitDR.lean, rule 12 through the forward bank: `fwdView_ge_of`).
- Outcome forms: load outcomes via `run.obsLoad` (no termination needed); final-memory outcomes via `finalMem` of
  `M` plus `run.done` of the storing harts (A0 (i): a finished hart's stores are in `M`, `wwDone`/`wDone`/`piDone`);
  row 37's register outcome via the value map `litFin` (a finished hart's final registers).
- Row 38's front end `litStepF acc` is the one extension (new definitions only; Machine.lean / MachCert.lean
  untouched).  Not modelled (needs the Sail-level front end): trap side effects / handler, misaligned and
  store/fetch faults.

## fwdMono for Zalasr release/acquire stores (settled, CoreFwdRel.lean)
- The forwarded-read RULE needs no side condition: `fwdRead` gives `⟦pv_f⟧ proto(M[t_f])` at the forwarding store's
  own pre-view for EVERY store (FK holds of release/acquire stores too).
- The dischargeability lemma depends on the kinds: plain/exclusive forwarder → any consumer covering the forward
  view (`fwdMono`, `fwdMono_bound`); release forwarder → release consumer (`fwdMono_rel`, proved); release
  forwarder → plain consumer FAILS (`fwdMono_rel_fails`, a concrete counterexample).  This is RVWMO's verdict, not
  a machine artefact: in `ld z; sw.rl 1,(x); lw b,(x); sw b,(y)` nothing orders `ld z` before `sw y` (rule 6 stops
  at the `sw.rl`; the rfi is not ppo; rule 12 needs a dependency into the `sw.rl`).  So the knowledge cannot be
  re-indexed; FK's `isRelAcq` disjunct is exactly this exception, not a weakening.

## Open items
- Rows 46, 48 (BOOT-sfence, A-lost): need walks / A/D (machine v2 extension points, [OWN.P3]); not attempted.
  Row 50 negative lemma skipped (translation deferred, [OWN.P3]).
- Not attempted (variants outside the §8 S2 list): 18r `addrpoR`, 26 mixed-size subrows (S3c), 52–61.
- `devFreeProg` is a premise of A0 as stated but unused by the proof (the per-hart wp is over every fabric value).
