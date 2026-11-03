/-
Weak/Prom: **`fwdMono` for release/acquire forwarders: what holds** (stage S2; plan rev 7 §2 "Forwarded reads"
[R1.5]: "plain RISC-V stores have no rl (Zalasr is out of scope, NA-10)"; machine v2 has Zalasr `s*.rl`/`s*.aqrl`
labels (`LStore aq rl …`, FIX S0P2-D3), so the open caveat of PROGRESS-S2.md is settled here).

THE FORWARDED-READ RULE NEEDS NO SIDE CONDITION.  `fwdRead` (CoreRules.lean) gives, for a byte forwarded from the
hart's own store `t_f`, the knowledge recorded at that store's fulfil at the store's OWN pre-view,
`⟦pv_f⟧ proto(M[t_f])` with `pv_f < t_f`.  It is proved from the forward-bank invariant FK (CoreFwd.lean), which
holds of every store, release and acquire included; the rule is sound as stated.  What depends on the store's kind
is only the dischargeability lemma `fwdMono` — whether `⟦pv_f⟧` is below a LATER fulfil's pre-view:
* plain and exclusive forwarders (`fwdMono`, `fwdMono_bound`, CoreRules.lean): `pv_f ≤ v_f ⊔ plainFloor`, so every
  later fulfil whose address or data view covers the forward view `v_f` discharges it;
* RELEASE forwarders, RELEASE consumers (`fwdMono_rel` below): the release pre-view adds `vrOld ⊔ vwOld`, and a later
  release fulfil's pre-view contains the later (larger) `vrOld ⊔ vwOld`: it discharges `⟦pv_f⟧`;
* RELEASE forwarder, PLAIN consumer: `fwdMono` FAILS (`fwdMono_rel_fails`: a concrete pair of states with the floors
  and coverage of `fwdMono` and a strictly smaller consumer pre-view).  This is RVWMO, not a machine artefact:
  `ld a,(z); sw.rl 1,(x); lw b,(x); sw b,(y)` — rule 6 orders `ld z` before `sw.rl`, but the read-from-own-store
  `sw.rl →rfi lw x` is not in ppo and rule 12 needs an address/data dependency into the `sw.rl` (its data is a
  constant), so `ld z` is NOT ordered before `sw y`; knowledge guarded by `ld z`'s source cannot be re-indexed to
  `sw y`'s pre-view.  A client forwarding from a release store into a plain store must justify the plain store's
  protocol fact at the plain store's own pre-view (e.g. from the data's own provenance), exactly as without
  forwarding.  FK's second disjunct (`isRelAcq`) records precisely this exception; nothing was weakened.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreKitV

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom
open PLabel

/-- **`fwdMono` for a release forwarder and a release consumer**: a release store at `ws_f` (no fetch view) with
forward view `v_f = va_f ⊔ vd_f`; at a later state `ws''` whose floors and old views are at least `ws_f`'s, a release
fulfil covering `v_f` has a pre-view at least the forwarder's. -/
theorem fwdMono_rel {wsf ws'' : PState} {vaf vdf va'' vd'' : Nat} (aq'' : Bool) (hif : wsf.wIfv = 0)
    (hfl : stFloor wsf ≤ stFloor ws'') (hro : wsf.wVrOld ≤ ws''.wVrOld) (hwo : wsf.wVwOld ≤ ws''.wVwOld)
    (hcov : max vaf vdf ≤ max va'' vd'') :
    stPreA wsf false true vaf vdf ≤ stPreA ws'' aq'' true va'' vd'' := by
  unfold stFloor at hfl
  have hup : stPreA wsf false true vaf vdf ≤
      max (max vaf vdf) (max (max wsf.wVcap wsf.wVwNew) (max wsf.wVrOld wsf.wVwOld)) := by
    show max (max vaf (max vdf (max wsf.wIfv (max wsf.wVcap (max wsf.wVwNew (max wsf.wVrOld wsf.wVwOld)))))) 0 ≤ _
    rw [hif]; omega
  have g := stPreA_ge ws'' aq'' true va'' vd''
  have g5 := g.2.2.2.2 rfl
  have hcap := g.2.2.1
  have hnew := g.2.2.2.1
  have hva := g.1
  have hvd := g.2.1
  omega

/-- **`fwdMono` fails for a release forwarder and a plain consumer**: the hypotheses of `fwdMono` (no fetch view,
monotone floors, the consumer covers the forward view) hold, and the consumer's pre-view is below the forwarder's
(the forwarder's `vrOld = 5`, from a po-earlier load, is in its release pre-view only). -/
theorem fwdMono_rel_fails : ∃ (wsf ws'' : PState) (vaf vdf va'' vd'' : Nat),
    wsf.wIfv = 0 ∧ stFloor wsf ≤ stFloor ws'' ∧ wsf.wVrOld ≤ ws''.wVrOld ∧ wsf.wVwOld ≤ ws''.wVwOld ∧
    max vaf vdf ≤ max va'' vd'' ∧ stPreA ws'' false false va'' vd'' < stPreA wsf false true vaf vdf := by
  refine ⟨{ psInit with wVrOld := 5 }, { psInit with wVrOld := 5 }, 0, 0, 0, 0, rfl, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, ?_⟩
  simp [stPreA, stPre, psInit]

end Weak.Prom.PF

#print axioms Weak.Prom.PF.fwdMono_rel
#print axioms Weak.Prom.PF.fwdMono_rel_fails
