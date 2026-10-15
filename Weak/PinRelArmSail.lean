/-
Weak: **W11-C2′ (a3) relArmed — a base instruction's whole cycle under `amB`**
(`PROGRESS-relArmed.md`).  Lean-only.

`amSailOf`: at a kernel-text pc holding a 4-byte, non-AMO word that decodes (`decS`) to `a`,
every cycle `riscvStep tick` started with an empty log and no AMO bit satisfies `amB` with the
post "armed if `rA`", given the execute stage's fact (`uxaExecAs a` retires with that post or
traps).  The prelude, dispatch and retire tail are `zfB` footprints (the flag never lowered);
an interrupt, a fetch fault, an execute trap and a landing-pad fault end at the trap handler's
cause write (a stop); the fetch is `amFetch` (the arm of the log, so the word is the kernel's);
the decoder is `runRead drefS`.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmCyc

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

/-- The execute stage's post: retired with the AMO bit clear and the flag armed if `rA`, or a
trap. -/
def execPostAm (rA : Bool) (r : ExecutionResult) (st : AmSt) : Prop :=
  (r = RETIRE_SUCCESS ∧ st.amo = false ∧ (rA = true → st.armed = true)) ∨
  ((∃ x, r = .Trap x) ∧ st.amo = false)

theorem amAnnBind {Y : Type} {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}
    (Q : Y → AmSt → Prop) {n : Nat} (w : BitVec n) (f : Unit → SailM Y) (st : AmSt)
    (h : amB A Aa Q (f ()) { st with amo := WbPrimed.ibAmo (ibAnn (ibOfBvn w)) }) :
    amB A Aa Q (instr_announce w >>= f) st :=
  fun u => by cases u; exact h

theorem amBindF {X Y : Type} {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}
    (Q : X → AmSt → Prop) (P : Y → AmSt → Prop) (m : SailM X) (f : X → SailM Y) (st : AmSt)
    (hm : amB A Aa Q m st) (hf : ∀ x st', Q x st' → amB A Aa P (f x) st') :
    amB A Aa P (FreeM.bind m f) st :=
  amBind Q P m f st hm hf

set_option maxHeartbeats 40000000 in
/-- **A BASE INSTRUCTION'S CYCLE** (header). -/
theorem amSailOf (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hrvc : wIsRvc (kw pc) = false)
    (hamo : WbPrimed.ibAmo (ibAnn (ibOfBvn (kword pc))) = false) (a0 rA : Bool)
    (hexec : ∀ st : AmSt, st.amo = false → (a0 = true → st.armed = true) →
      amB kA (kAa pc) (execPostAm rA) (uxaExecAs a) st)
    (tick : Bool) (st : AmSt) (hfe : st.fe = []) (ha : st.amo = false)
    (h0 : a0 = true → st.armed = true) :
    amB kA (kAa pc) (fun _ st' => rA = true → st'.armed = true) (riscvStep tick) st := by
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  unfold ucPrelude
  simp only [bind_assoc]
  refine amReadBind _ _ _ _ (fun v _ _ => ?_)
  refine amBind (fun _ st' => st'.fe = st.fe ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
    _ _ _ _ (amOfZf _ _ _ _ (zfShouldIncMinstret v) ha
      (fun _ st' _ e1 e2 e3 => ⟨e1, e2, fun h => e3 (h0 h)⟩)) (fun b st1 h1 => ?_)
  refine amWriteBind _ _ _ _ _ trivial rfl ?_
  refine amReadBind _ _ _ _ (fun hs _ hg => ?_)
  obtain rfl : hs = HartState.HART_ACTIVE () := hg _ rfl
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  unfold ucDispatch
  simp only [bind_assoc]
  refine amReadBind _ _ _ _ (fun v2 _ _ => ?_)
  refine amBind (fun _ st' => st'.fe = st.fe ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
    _ _ _ _ (amOfZf _ _ _ _ (zfDispatchInterrupt v2) h1.2.1
      (fun _ st' _ e1 e2 e3 => ⟨e1.trans h1.1, e2, fun h => e3 (h1.2.2 h)⟩)) (fun o st2 h2 => ?_)
  cases o with
  | some ip =>
    refine amPureBind _ _ _ _ ?_
    exact amFinishIntr kA (kAa pc) _ ip tick st2 h2.2.1
  | none =>
    simp only [bind_assoc]
    refine amBind (fetchPostAm pc st2) _ _ _ st2 (amFetch pc st2 (h2.1.trans hfe) h2.2.1)
      (fun fr st3 h3 => ?_)
    obtain ⟨hsh3, hamo3, harm3, hkA3⟩ := h3
    have ha3 : st3.amo = false := hamo3.trans h2.2.1
    have h03 : a0 = true → st3.armed = true := fun h => harm3 (h2.2.2 h)
    cases fr with
    | F_Ext_Error e => exact hsh3.elim
    | F_Error p =>
      obtain ⟨e, addr⟩ := p
      simp only [ucAfterFetch, ext_fetch_hook]
      refine amPureBind _ _ _ _ ?_
      exact amFinishFetchFail kA (kAa pc) _ (virtaddr.Virtaddr addr, e) tick st3 ha3
    | F_RVC h =>
      obtain ⟨-, hr, -⟩ := PinCycRun.rvcFacts pc htext h st3.fe hkA3 hsh3
      rw [hrvc] at hr; cases hr
    | F_Base w =>
      obtain ⟨hw, -, -, -⟩ := PinCycRun.baseFacts pc htext w st3.fe hkA3 hsh3
      simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
      refine amAnnBind _ w _ st3 ?_
      have ha4 : WbPrimed.ibAmo (ibAnn (ibOfBvn w)) = false := by rw [hw]; exact hamo
      obtain ⟨bb, hrr⟩ := PinCycRun.decBase pc a hdec hrvc
      have hrr' : runRead drefS (ext_decode w) = some (a, bb) := by rw [hw]; exact hrr
      refine amBind (fun i st' => i = a ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
        _ _ _ _ (amOfRunRead kA (kAa pc) _ _ _ _ a bb hrr' (SailCycleOrderFp.fpDecodeS _)
          (fun st' e1 e2 e3 => ⟨rfl, e2.trans ha4, fun h => e3 (h03 h)⟩)) (fun i st5 h5 => ?_)
      obtain ⟨rfl, ha5, h05⟩ := h5
      unfold is_landing_pad_expected
      simp only [bind_assoc]
      refine amReadBind _ _ _ _ (fun ev _ _ => ?_)
      refine amPureBind _ _ _ _ ?_
      split
      · simp only [trap, bind_assoc]
        refine amReadBind _ _ _ _ (fun p1 _ _ => ?_)
        refine amReadBind _ _ _ _ (fun p2 _ _ => ?_)
        simp only [pure_bind]
        exact amFinishTrap kA (kAa pc) _ _ _ tick st5 ha5
      · refine amReadBind _ _ _ _ (fun pcv _ _ => ?_)
        refine amWriteBind _ _ _ _ _ trivial rfl ?_
        refine amBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend w) ∧
          execPostAm rA r st') _ _ _ st5 ?_ (fun s st6 hs => ?_)
        · exact amBind (execPostAm rA) _ _ _ st5 (hexec st5 ha5 h05) (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h6⟩ := hs
        rcases h6 with ⟨rfl, ha6, h6⟩ | ⟨⟨x, rfl⟩, ha6⟩
        · exact amOfZf _ _ _ _ (zfFinishRetire _ tick) ha6 (fun _ st' _ _ _ e3 h => e3 (h6 h))
        · exact amFinishTrap kA (kAa pc) _ _ _ tick st6 ha6

set_option maxHeartbeats 40000000 in
/-- **A COMPRESSED INSTRUCTION'S CYCLE** (header): the twin of `amSailOf` for a halfword. -/
theorem amSailOfC (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hrvc : wIsRvc (kw pc) = true)
    (hamo : WbPrimed.ibAmo (ibAnn (ibOfBvn (BitVec.ofNat 16 (kw pc)))) = false) (a0 rA : Bool)
    (hexec : ∀ st : AmSt, st.amo = false → (a0 = true → st.armed = true) →
      amB kA (kAa pc) (execPostAm rA) (uxaExecAs a) st)
    (tick : Bool) (st : AmSt) (hfe : st.fe = []) (ha : st.amo = false)
    (h0 : a0 = true → st.armed = true) :
    amB kA (kAa pc) (fun _ st' => rA = true → st'.armed = true) (riscvStep tick) st := by
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  unfold ucPrelude
  simp only [bind_assoc]
  refine amReadBind _ _ _ _ (fun v _ _ => ?_)
  refine amBind (fun _ st' => st'.fe = st.fe ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
    _ _ _ _ (amOfZf _ _ _ _ (zfShouldIncMinstret v) ha
      (fun _ st' _ e1 e2 e3 => ⟨e1, e2, fun h => e3 (h0 h)⟩)) (fun b st1 h1 => ?_)
  refine amWriteBind _ _ _ _ _ trivial rfl ?_
  refine amReadBind _ _ _ _ (fun hs _ hg => ?_)
  obtain rfl : hs = HartState.HART_ACTIVE () := hg _ rfl
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  unfold ucDispatch
  simp only [bind_assoc]
  refine amReadBind _ _ _ _ (fun v2 _ _ => ?_)
  refine amBind (fun _ st' => st'.fe = st.fe ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
    _ _ _ _ (amOfZf _ _ _ _ (zfDispatchInterrupt v2) h1.2.1
      (fun _ st' _ e1 e2 e3 => ⟨e1.trans h1.1, e2, fun h => e3 (h1.2.2 h)⟩)) (fun o st2 h2 => ?_)
  cases o with
  | some ip =>
    refine amPureBind _ _ _ _ ?_
    exact amFinishIntr kA (kAa pc) _ ip tick st2 h2.2.1
  | none =>
    simp only [bind_assoc]
    refine amBind (fetchPostAm pc st2) _ _ _ st2 (amFetch pc st2 (h2.1.trans hfe) h2.2.1)
      (fun fr st3 h3 => ?_)
    obtain ⟨hsh3, hamo3, harm3, hkA3⟩ := h3
    have ha3 : st3.amo = false := hamo3.trans h2.2.1
    have h03 : a0 = true → st3.armed = true := fun h => harm3 (h2.2.2 h)
    cases fr with
    | F_Ext_Error e => exact hsh3.elim
    | F_Error p =>
      obtain ⟨e, addr⟩ := p
      simp only [ucAfterFetch, ext_fetch_hook]
      refine amPureBind _ _ _ _ ?_
      exact amFinishFetchFail kA (kAa pc) _ (virtaddr.Virtaddr addr, e) tick st3 ha3
    | F_Base w =>
      obtain ⟨-, hr, -⟩ := PinCycRun.baseFacts pc htext w st3.fe hkA3 hsh3
      rw [hrvc] at hr; cases hr
    | F_RVC h =>
      obtain ⟨hw, -, -, -⟩ := PinCycRun.rvcFacts pc htext h st3.fe hkA3 hsh3
      simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
      refine amAnnBind _ h _ st3 ?_
      have ha4 : WbPrimed.ibAmo (ibAnn (ibOfBvn h)) = false := by rw [hw]; exact hamo
      obtain ⟨bb, hrr⟩ := PinCycRun.decRvc pc a hdec hrvc
      have hrr' : runRead drefS (ext_decode_compressed h) = some (a, bb) := by rw [hw]; exact hrr
      refine amBind (fun i st' => i = a ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
        _ _ _ _ (amOfRunRead kA (kAa pc) _ _ _ _ a bb hrr' (SailCycleOrderFp.fpDecodeC _)
          (fun st' e1 e2 e3 => ⟨rfl, e2.trans ha4, fun h => e3 (h03 h)⟩)) (fun i st5 h5 => ?_)
      obtain ⟨rfl, ha5, h05⟩ := h5
      unfold is_landing_pad_expected
      simp only [bind_assoc]
      refine amReadBind _ _ _ _ (fun ev _ _ => ?_)
      refine amPureBind _ _ _ _ ?_
      split
      · simp only [trap, bind_assoc]
        refine amReadBind _ _ _ _ (fun p1 _ _ => ?_)
        refine amReadBind _ _ _ _ (fun p2 _ _ => ?_)
        simp only [pure_bind]
        exact amFinishTrap kA (kAa pc) _ _ _ tick st5 ha5
      · refine amBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend h) ∧
          execPostAm rA r st') _ _ _ st5 ?_ (fun s st7 hs => ?_)
        · refine amBind (fun z st' => z = true ∧ st'.amo = false ∧ (a0 = true → st'.armed = true))
            _ _ _ _ (amOfRunRead kA (kAa pc) _ _ _ _ true true PinCycRun.zcaOn
              (SailCycleOrderFp.fpCurrentlyEnabled _)
              (fun st' e1 e2 e3 => ⟨rfl, e2.trans ha5, fun h => e3 (h05 h)⟩)) (fun z st6 h6 => ?_)
          obtain ⟨rfl, ha6, h06⟩ := h6
          simp only [↓reduceIte]
          refine amReadBind _ _ _ _ (fun pcv _ _ => ?_)
          refine amWriteBind _ _ _ _ _ trivial rfl ?_
          exact amBind (execPostAm rA) _ _ _ st6 (hexec st6 ha6 h06) (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h7⟩ := hs
        rcases h7 with ⟨rfl, ha7, h7⟩ | ⟨⟨x, rfl⟩, ha7⟩
        · exact amOfZf _ _ _ _ (zfFinishRetire _ tick) ha7 (fun _ st' _ _ _ e3 h => e3 (h7 h))
        · exact amFinishTrap kA (kAa pc) _ _ _ tick st7 ha7

end PinRelArm
end Weak
