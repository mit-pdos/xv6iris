/-
Weak: **the branch leaves and the REAL-SHAPE acquire loop** (M4-prep item
(iii)): the one-instruction leaf for an instruction with no weak-memory effect
of its own (branch, jump, ALU), its certificate-discharged forms, and xv6's
acquire loop over its real two-instruction shape.

Rocq: `iris/WeakBranch.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  `WeakAcquire`'s spin loop abstracts its RETRY
EDGE: xv6's acquire is

    1:  amoswap.w.aq  a5, a4, (s1)
        bnez          a5, 1b

and only the first instruction had a weak leaf, so the branch back was a
premise of the loop lemma.  This file supplies the missing leaf and closes the
loop over the real shape.

WHY A BRANCH IS NOT `wQ_none`: a leaf has to give the state interpretation back
at the successor, and `wmstateInterp σ'`'s `wlatInterp` conjunct says every
latest-write element is still the latest write -- unprovable if the step might
have appended a message.  So the branch's `Q` is `WeakEff.wQPure` (image and
log unchanged, views only grew), which `WeakEff.wcertNowrite` proves for any
write-free effect trace; a branch's trace is the fetch read alone.

§1 the leaf (`wwpBranchStep`) and its certificate-discharged forms;
§2 the composed real-shape acquire loop (`wwpAcquireLoopReal`) -- one
   `amoswap.w.aq` at `pca` and one branch at `pcb`, the retry edge a PROOF.

**Deviations from Rocq.**
1. NAMES / VOCABULARY as `Weak/WeakAcquire.lean` deviation 1 (ambient
   `GenId`/`CpuId` are the explicit `gen`/`cpu`; `WWP Loop` is
   `wwpTriv ⊤ (WExpr.loop gen cpu)`; `fin_to_nat cpu_id` is `cpu.val`;
   `register_lookup PC (wm_regs σ)` is `σ.wmRegs .PC`; `mstate` is `ExecSt`;
   `n : N` is `n : Nat`).  None of this file's names is in the
   duplicated-name table.
2. STATEMENT SHAPES (WeakInstr deviation 3): Rocq `A -∗ B -∗ C` is
   `A ⊢ B -∗ C`; `wbrCb` takes `gen`/`cpu` explicitly.
3. O2, THE TEXT PIN (WeakInstr deviation 4): `wbrCb` hands over
   `pinnedRead σ (accAddr pc j) ∧ fetchPinned σ (accAddr pc j)` per text byte
   (Rocq: `pinned_read` only), as `wpWinstr` requires.
4. O2, THE CERTIFICATE FORMS.  The branch callbacks (`wwpBranchStepCert`,
   the branch premise of `wwpAcquireLoopRealCert`) are at Lean's `wPEff`
   (Rocq `wP_eff`; Lean's carries the O2 `fetchPin`, WeakCert deviation 4),
   exactly as `WeakEff.wcertNowrite` states it -- the downstream Rocq user
   `WeakLeafAmo4Leaf.wwp_amo4_acquire_loop` passes `wcert_nowrite` at that
   form.  The ATTEMPT callback of `wwpAcquireLoopRealCert` is at
   `WeakAcquire.wPEffText` (Rocq `wP_eff` verbatim), as in
   `WeakAcquire.wwpAcquireLoopCert`: its fetch obligation is supplied from
   the Rocq fetch-footprint premise via `wstepCertText`.  Rocq's
   `ak_coh aka = false` is `aka.akIfetch = false` (WeakCert/WeakAcquire).

**Rocq → Lean name map.**  `nowrite_trace_read` `nowriteTraceRead`, `wbr_cb`
`wbrCb`, `wwp_branch_step` `wwpBranchStep`, `wlat_interp_wQ_pure`
`wlatInterpWQPure`, `wwp_branch_step_cert` `wwpBranchStepCert`,
`wwp_branch_step_quiet` `wwpBranchStepQuiet`, `wwp_acquire_loop_real`
`wwpAcquireLoopReal`, `wwp_acquire_loop_real_cert` `wwpAcquireLoopRealCert`.

**Dropped:** nothing -- 8 Rocq declarations, 8 Lean.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakAcquire
import Weak.WeakEff

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- A branch's whole effect trace is the fetch read. -/
theorem nowriteTraceRead (ak : AkInfo) (pa : PAddr) (n : Nat) :
    nowriteTrace [.WEread ak pa n] := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  trivial

/-! ## 1. THE LEAF

Identical to `WeakAcquire.wwpFenceStep` except for the `Q`: a branch, a jump or
an ALU instruction has no weak-memory effect of its own. -/

section branch

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The leaf's callback, generic in `Q`: ONE rule serves the branch (`wQPure`,
or `wQQuiet`), the jump, and any ALU instruction. -/
def wbrCb (gen : Nat) (cpu : CPU) (pc : BitVec 64) (P : Wmstate → Prop)
    (Q : Wmstate → Wmstate → Prop) : IProp GF :=
  iprop(∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
    ⌜σ.wmRegs .PC = pc⌝ ∗
    ⌜∀ j : Nat, j < 4 →
      pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
    ⌜P σ⌝ ∗
    ∃ t0 t1 : ExecSt,
      ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
      ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
      ▷ (∀ (tick : Bool) (σ' : Wmstate),
          ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
          ⌜Q σ σ'⌝ ={∅,⊤}=∗
            wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))

theorem wwpBranchStep (gen : Nat) (cpu : CPU) (pc : BitVec 64) (P : Wmstate → Prop)
    (Q : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    wstepCert cpu.val pc P Q →
    wbrCb (hlc := hlc) (GF := GF) gen cpu pc P Q ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hcert
  unfold wbrCb
  exact wpWinstr gen cpu pc P Q hgen haccpc hcert

/-- The latest-write authority crosses a `wQPure` step untouched. -/
theorem wlatInterpWQPure (σ σ' : Wmstate) :
    wQPure σ σ' →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢ wlatInterp σ'.wmImg σ'.wmLog := by
  rintro ⟨hi, hl, -⟩
  rw [hi, hl]

/-- ... and the certificate, DISCHARGED (`WeakEff.wcertNowrite`): the trace is
the fetch read and nothing else. -/
theorem wwpBranchStepCert (gen : Nat) (cpu : CPU) (pc : BitVec 64)
    (akf : AkInfo) (pf : PAddr) (nf : Nat) :
    gen = 0 →
    accWf pc 4 →
    wbrCb (hlc := hlc) (GF := GF) gen cpu pc (wPEff (some cpu.val) [.WEread akf pf nf]) wQPure ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := fun hgen haccpc =>
  wwpBranchStep gen cpu pc _ _ hgen haccpc
    (wcertNowrite cpu.val pc [.WEread akf pf nf] (nowriteTraceRead akf pf nf))

/-- The same at the QUIET altitude (`WeakEff.wcertQuiet`). -/
theorem wwpBranchStepQuiet (gen : Nat) (cpu : CPU) (pc : BitVec 64) (es : List Weff) :
    gen = 0 →
    accWf pc 4 →
    quietTrace es →
    wbrCb (hlc := hlc) (GF := GF) gen cpu pc (wPEff (some cpu.val) es) wQQuiet ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := fun hgen haccpc hq =>
  wwpBranchStep gen cpu pc _ _ hgen haccpc (wcertQuiet cpu.val pc es hq)

end branch

/-! ## 2. THE REAL-SHAPE ACQUIRE LOOP

    1:  amoswap.w.aq  a5, a4, (s1)     -- at `pca`
        bnez          a5, 1b           -- at `pcb`

THE ATTEMPT: from the loop head's `K`, one `wacqCb` at `pca`, whose FAILURE arm
hands back `Kb` (the head one instruction later).  THE RETRY EDGE: from `Kb`,
one branch step at `pcb`, back to `K`.  The Löb induction is `wwpSpinLoop`'s;
its ▷ is stripped inside the AMO's continuation, where the branch runs. -/

section loop

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

theorem wwpAcquireLoopReal (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pca pcb : BitVec 64) (Pa Pb : Wmstate → Prop) (Qb : Wmstate → Wmstate → Prop)
    (K Kb : IProp GF) (esa : List Weff) :
    gen = 0 →
    accWf pca 4 →
    accWf pcb 4 →
    accWf lk 4 →
    (∀ a : Int, weffsTouch esa a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pca j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j)) →
    wstepCert cpu.val pca Pa (wQFr (wQAmoAq (some cpu.val) lk lockOne) (some cpu.val) esa) →
    wstepCert cpu.val pcb Pb Qb →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      □ (K -∗ ▷ (Kb -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk R pca Pa) -∗
        □ (Kb -∗ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
            wbrCb (hlc := hlc) (GF := GF) gen cpu pcb Pb Qb) -∗
          K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hacca haccb hacclk hfoot hcerta hcertb
  iintro #Hinv #Hatt #Hbr HK
  iapply wwpSpinLoop gen cpu K $$ [] HK
  imodintro
  iintro HK Hrec
  iapply wwpAcquireSwap gen cpu γ lk R pca Pa esa hgen hacca hacclk hfoot hcerta $$ Hinv
  ispecialize Hatt $$ HK
  iapply Hatt
  -- the retry edge, under the AMO's own later
  inext
  iintro HKb
  iapply wwpBranchStep gen cpu pcb Pb Qb hgen haccb hcertb
  iapply Hbr $$ HKb Hrec

/-- ... and the same with BOTH certificates discharged (deviation 4). -/
theorem wwpAcquireLoopRealCert (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pca pcb : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo)
    (akf2 : AkInfo) (pf2 : PAddr) (nf2 : Nat) (K Kb : IProp GF) :
    gen = 0 →
    accWf pca 4 →
    accWf pcb 4 →
    accWf lk 4 →
    aka.akIfetch = false →
    aka.akSync = true →
    akw.akLatest = true →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pca j) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      □ (K -∗ ▷ (Kb -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk R pca
            (wPEffText (some cpu.val)
              [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne])) -∗
        □ (Kb -∗ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
            wbrCb (hlc := hlc) (GF := GF) gen cpu pcb
              (wPEff (some cpu.val) [.WEread akf2 pf2 nf2]) wQPure) -∗
          K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hacca haccb hacclk hcoh hsync hlat hfetch
  refine wwpAcquireLoopReal gen cpu γ lk R pca pcb _ _ _ K Kb
    [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne]
    hgen hacca haccb hacclk ?_ ?_
    (wcertNowrite cpu.val pcb [.WEread akf2 pf2 nf2] (nowriteTraceRead akf2 pf2 nf2))
  · intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · right
      rcases weffsTouchCons _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j := ha
        exact ⟨j, hj, rfl⟩
      · exact weffsTouchWrite1 _ lk _ _ a ha
  · exact wstepCertText _ pca _ _ (fetchInWindowAmo pca akf pf nf aka akw lk lockOne hcoh hfetch)
      (fetchFreshAmo akf pf nf aka akw lk lockOne)
      (wstepCertFr _ pca _ _ (wcertAmoAq cpu.val pca akf pf nf aka akw lk lockOne hcoh hsync hlat))

end loop

end Weak
