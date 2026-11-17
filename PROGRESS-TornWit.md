# PROGRESS — TornWit (fidelity check, review-R2 F3)

## Status: DONE — CLAIM CONFIRMED (green, 2026-11-17)

`lake build Weak.Prom.MachTornWit` green (47 jobs). New file only: `Weak/Prom/MachTornWit.lean` (62 lines).
No existing file edited; not imported from the `Weak` root (no root edits; coordinator decides).

## Theorems (Weak/Prom/MachTornWit.lean)
* `tornT` (:32) — hart 0 `sw a1,0(a2); lw a0,0(a2)` [a1 = 0x01010101, a2 = X]; hart 1 `sw a1,0(a2)`
  [a1 = 0x02020202]; image 0; cond `r 0 10 0x02020201`.
* `mach_torn : allowedMach tornT` (:50) — `certOk_sound _ cert_torn (by decide +kernel)`. Run: hart 0 promises
  ts 1, hart 1 ts 2, both fulfil; hart 0's `lw` answers `[(1,01),(2,02),(2,02),(2,02)]`. Byte 0 is `fwdHit`
  (Machine.lean:293–296) so its floor is `max vpre (coh X) = 1`; bytes 1–3 have floor `nonFwdMax = 2`
  (Machine.lean:326–333); no write lies in `(1,1]` or `(2,2]`.
* `ref_torn : forbiddenRef tornT` (:53) — `forbid_sound`.
* `ref_torn_exec : allowedRef (anyOutcome tornT)` (:56) — non-vacuity.
* Axioms (all three): `[propext, Classical.choice, Quot.sound]`.

## Answers
* OWN store only: YES. `fwdHit` needs `get? ws.wFwd a = some (t, _)`, and `wFwd` is written only by
  `storeBytes` (Machine.lean:409–412) in the storing hart's own `PState`, and it keeps only that hart's LATEST
  store to the byte. The tear only goes one way: the forwarded byte is OLDER than the others. If the own store
  were coherence-later, the non-forwarded bytes' floor `coh` would cover it, which `writesIn` blocks.
* Do existing proofs assume untorn loads? NO. No hypothesis anywhere restricts to untorn runs (grep
  `untorn` finds nothing). The Core*/Own* `lit_` theorems quantify over ALL machine runs, torn ones included, so
  they stay valid; the tear only makes them harder to prove. The forwarded-byte rule `fwdRead` (CoreRules.lean:156)
  already handles the exemption. `rvwmo_complete` (CmpMain.lean:90, Ref ⊆ Mach) builds untorn answers
  (`uniTvs`, `nonFwdMax_uni_le` CmpStep.lean:52) and is unaffected, and so are `refFromLit`/`forbid_of_lit`
  (CmpLit.lean). What does fail is any claim of Mach ⊆ Ref (machine soundness, or the mini plan's E2b).
  `tornT` is a counterexample to that claim. A fix (applying the common read point to forwarded bytes when every byte is
  forwarded from the same aligned same-size store, or always) is the owner's call. It strengthens the machine, and
  proofs that unfold `loadOk` (for example OwnMPDefs.lean:355, CoreKitV.lean:260) would need to be re-checked.
