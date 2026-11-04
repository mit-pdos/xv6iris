/-
Weak: **W11-F row 6d (the DATA half), part 1 — THE CYCLE IN SUPERVISOR MODE**: along a walk cycle
from the kernel configuration, every EXCEPTION's cause write (`scause`/`mcause`, bit 63 clear) is made
while the hart's register mirror is in Supervisor mode (`PROGRESS-6d.md` §0 (2)).  Lean-only, no Rocq
twin.

Why: [OWN.115]'s stuck instrument (`MachCSL.kExcWrite`, `MachCSL/Lang.lean:1337`) refuses a cause write
with bit 63 clear made FROM SUPERVISOR MODE; to refute a realized exception at a walk cycle the consumer
(`Weak/CapDataOk.lean`) needs the hart in Supervisor mode AT that write.  Sail: `cur_privilege` is
written only by the trap handler AFTER its first cause write and by xRET; at a walk cycle the fetch keeps
every protected register (`fetchPostCy`), the execute stage keeps them but `nextPC` (`execPost`), the
trap handler writes only `mstatus`/`elp` before the cause (`trap_handler`, Zicfilp), and an interrupt's
tail writes no exception cause (`PinDataOk.cyDFinishIntr`).

* §1 the trap tails, re-walked to REPORT the mirror's `cur_privilege` at the stop (the merged
  `PinCycRun.cyTrapHandler` / `cyExcHandler` / `cyFinishTrap` / `cyFinishFetchFail`,
  `Weak/PinCycRunCyc.lean:227`, `Weak/PinCycRunCyc2.lean:186-224`, report only the log and the flag);
* §2 **`CapDataTrap.cyPSailOf`** — `PinDataOk.cyDSailOf` (`Weak/PinDataOkSail.lean:56`) re-assembled
  with the boot register filter `gB`, the trivial answer filter `dT` and the stop post `privS`, WITHOUT
  the data-access product (the execute stage may trap: its trap tail is §1's).

Spec: FAITHFUL (a theorem about the Sail text: `riscvStep`, `trap_handler`, `exception_handler`).
Every name is `Weak.CapDataTrap.*`.
-/
import Weak.PinDataOkSail

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace CapDataTrap
open SailCycleOrderK PinCycRun PinDataflow PinDataOk
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-! ## 0. The stop post and the filters -/

/-- **The stop post**: the mirror is in Supervisor mode. -/
def privS (st : CySt) (_r : Register) (_v : RegisterType _r) : Prop :=
  st.rv .cur_privilege = Privilege.Supervisor

/-- The stop post `cyB` stretches are lifted at (an exception's cause, in Supervisor mode). -/
def pStop0 (st : CySt) (r : Register) (v : RegisterType r) : Prop :=
  causeBit r v = false ∧ privS st r v

/-- The register filter: the boot filter only. -/
def gB (r : Register) (v : RegisterType r) : Prop := Rboot r v

/-- The answer filter: none. -/
def dT (_pa : BitVec 64) (n : Nat) (_w : BitVec (8 * n)) : Prop := True

/-! ## 1. The trap tails, reporting `cur_privilege` -/

section tail
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
  (T : CySt → (r : Register) → RegisterType r → Prop)

/-- **The trap handler up to its first cause write**, with the mirror's `cur_privilege` kept
(`PinCycRun.cyTrapHandler` + the privilege: the writes before the cause are `mstatus`/`elp`). -/
theorem trapHandlerP {Y : Type} (Q : Y → CySt → Prop) (del : Privilege) (c : TrapCause)
    (pc : BitVec 64) (info : Option (BitVec 64)) (ext : Option Unit) (f : BitVec 64 → SailM Y)
    (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r),
      st'.rv .cur_privilege = st.rv .cur_privilege →
      cyS r = true → causeBit r v = trapCause_is_interrupt c → T st' r v) :
    cyB A Aa cyS T Q (trap_handler del c pc info ext >>= f) st := by
  unfold trap_handler
  simp only [get_config_print_exception, get_config_print_interrupt, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, pure_bind]
  -- since 2026-11-04 no Zicfilp: the trap neither banks nor resets `elp`
  have hz : hartSupports extension.Ext_Zicfilp = false := by
    simp [hartSupports]
  rw [if_neg (by simp [hz])]
  try simp only [pure_bind]
  cases del with
  | Machine =>
    simp only [bind_assoc]
    refine cyReadBind _ _ _ _ (fun v3 _ => ?_)
    refine cyStopBind A Aa T _ _ _ _ _ (by decide) ?_
    refine hT _ _ _ ?_ (by decide) ?_
    · simp (disch := decide) only [cyRd, cyWr, RegFile.set_other]
    · exact PinCycRun.causeBitUpd _ _
  | Supervisor =>
    simp only [bind_assoc]
    refine cyBBind (fun b st' => st'.rv .cur_privilege = st.rv .cur_privilege) _ _ _ _ ?_
      (fun b st1 hpr => ?_)
    · refine cyOfPf A Aa cyS T ?_ _ _ _ _ (pfCurrentlyEnabled _) ?_
        (fun _ st' _ hf => (hf.1 .cur_privilege (by decide)).trans ?_)
      · intro r hr
        simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with rfl | rfl <;> rfl
      · exact hrb
      · simp (disch := decide) only [cyRd, cyWr, RegFile.set_other]
    · refine cyAssertBind A Aa T _ _ _ _ _ (fun _ => ?_)
      refine cyReadBind _ _ _ _ (fun v3 _ => ?_)
      refine cyStopBind A Aa T _ _ _ _ _ (by decide) ?_
      refine hT _ _ _ hpr (by decide) ?_
      exact PinCycRun.causeBitUpd _ _
  | User => exact trivial
  | VirtualUser => exact trivial
  | VirtualSupervisor => exact trivial

/-- **The exception handler**, reporting `cur_privilege` (`PinCycRun.cyExcHandler` + the
privilege: the delegation is a footprint). -/
theorem excHandlerP {Y : Type} (Q : Y → CySt → Prop) (priv : Privilege) (exc : sync_exception)
    (pc : BitVec 64) (f : BitVec 64 → SailM Y) (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r),
      st'.rv .cur_privilege = st.rv .cur_privilege →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (exception_handler priv exc pc >>= f) st := by
  unfold exception_handler
  simp only [get_config_print_exception, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine cyBBind (fun _ st' => cyFrame st st') _ _ _ st ?_ (fun del st1 hf => ?_)
  · refine cyOfPf A Aa cyS T ?_ _ _ _ _ (pfExceptionDelegatee _ _) hrb (fun _ st' _ h => h)
    intro r hr
    simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  · refine trapHandlerP A Aa T _ _ _ _ _ _ _ st1 hf.2.1 (fun st' r v h1 h2 h3 => ?_)
    exact hT st' r v (h1.trans (hf.1 .cur_privilege (by decide))) h2 h3

/-- **An execute trap's tail**, reporting `cur_privilege`. -/
theorem finishTrapP (Q : Unit → CySt → Prop) (x : Privilege × sync_exception × BitVec 64)
    (ib : BitVec 32) (tick : Bool) (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r),
      st'.rv .cur_privilege = st.rv .cur_privilege →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (ucFinish (.Step_Execute (.Trap x, ib)) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨priv, exc, pc⟩ := x
  simp only [ucFinish, ucArm, bind_assoc]
  exact excHandlerP A Aa T _ _ _ _ _ st hrb hT

/-- **A fetch failure's tail**, reporting `cur_privilege`. -/
theorem finishFetchFailP (Q : Unit → CySt → Prop) (p : virtaddr × ExceptionType) (tick : Bool)
    (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r),
      st'.rv .cur_privilege = st.rv .cur_privilege →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (ucFinish (.Step_Fetch_Failure p) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨va, e⟩ := p
  simp only [ucFinish, ucArm, handle_exception, bind_assoc]
  refine cyReadBind _ _ _ _ (fun v1 _ => ?_)
  refine cyReadBind _ _ _ _ (fun v2 _ => ?_)
  exact excHandlerP A Aa T _ _ _ _ _ _ hrb (fun st' r v h1 h2 h3 => hT st' r v h1 h2 h3)

end tail

/-! ## 2. The cycle -/

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **THE CYCLE IN SUPERVISOR MODE** (header): at a walk pc (the decoded instruction, the two
per-instruction facts, the role's `dfNwRole`), every cycle `riscvStep tick` from the kernel
configuration satisfies `cyDB` at the boot filter with the stop post `privS` — every exception's
cause write is made in Supervisor mode; an interrupt's tail never stops. -/
theorem cyPSailOf (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hfetch : fetchCyR1 pc) (hexec : execCyAt pc)
    (hnw : dfNwRole (krole pc)) :
    ∀ (tick : Bool) (st : CySt), cyInit pc st →
      cyDB gB dT kA (kAa pc) privS (fun _ _ => True) (riscvStep tick) st := by
  intro tick st hinit
  obtain ⟨⟨hpc, hcfg, hrb⟩, hfe, han, hd⟩ := hinit
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  have hpre0 : preInv st st := ⟨cyFrameRefl st hrb, by rw [hd], by rw [hd], by rw [hd]⟩
  -- the prelude
  have hP := cyPrelude kA (kAa pc) pStop0 (fun hs st' => hs = st.rv .hart_state ∧ preInv st st') pure st st
    hpre0 (fun st' h => ⟨rfl, h⟩)
  rw [bindPureR] at hP
  refine cyDBind _ _ _ _ st (cyDOfCyB _ _ _ hP) (fun hs st1 h1 => ?_)
  obtain ⟨rfl, h1⟩ := h1
  rw [hcfg.2.2.2.2.1]
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  -- the dispatch
  have hD := cyDispatch kA (kAa pc) pStop0 (fun o st' => preInv st st') pure st st1 h1 (fun o st' h => h)
  rw [bindPureR] at hD
  refine cyDBind _ _ _ _ st1 (cyDOfCyB _ _ _ hD) (fun o st2 h2 => ?_)
  have han2 : st2.an = false := h2.1.2.2.2.trans han
  cases o with
  | some ip =>
    refine cyDPureBind _ _ _ _ ?_
    exact cyDFinishIntr (fun _ _ h => h) ip tick st2
  | none =>
    simp only [bind_assoc]
    have hF := hfetch pStop0 st2 (h2.1.2.2.1.trans hfe) han2
      (by rw [h2.1.1 .PC (by decide)]; exact hpc)
      (PinCycRun.kCfgProt _ _ (fun r hr _ _ => h2.1.1 r hr) hcfg) h2.1.2.1 h2.2.1
    refine cyDBind (fetchPostCy pc st2) _ _ _ st2 (cyDOfCyB _ _ _ hF) (fun fr st3 h3 => ?_)
    obtain ⟨hp3, hrb3, han3, hro3, hn3, hok3, hkA3, hsh3⟩ := h3
    have han3' : st3.an = false := han3.trans han2
    cases fr with
    | F_Ext_Error e => exact hsh3.elim
    | F_Error p =>
      obtain ⟨e, addr⟩ := p
      simp only [ucAfterFetch, ext_fetch_hook]
      refine cyDPureBind _ _ _ _ ?_
      exact cyDOfCyB _ _ _ (finishFetchFailP kA (kAa pc) pStop0 _ (virtaddr.Virtaddr addr, e) tick st3 hrb3
        (fun st' r v hpr _ hcb => ⟨hcb, by
          show st'.rv .cur_privilege = Privilege.Supervisor
          rw [hpr, hp3 .cur_privilege (by decide), h2.1.1 .cur_privilege (by decide)]; exact hcfg.1⟩))
    | F_RVC h =>
      obtain ⟨hw, hrvc, hrole, fa, hfa, hfaR⟩ := PinCycRun.rvcFacts pc htext h st3.fe hkA3 hsh3
      simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
      refine cyDAnnBind _ h _ st3 han3' ?_
      have hp4 : ∀ r, pfProt r = true → (cyAnn st3 16 h).rv r = st.rv r := fun r hr =>
        (hp3 r hr).trans (h2.1.1 r hr)
      have hcfg4 : kCfg (cyAnn st3 16 h).rv :=
        PinCycRun.kCfgProt _ _ (fun r hr _ _ => hp4 r hr) hcfg
      obtain ⟨b, hrr⟩ := PinCycRun.decRvc pc a hdec hrvc
      have hrr' : runRead drefS (ext_decode_compressed h) = some (a, b) := by rw [hw]; exact hrr
      refine cyDBind (fun i' st' => i' = a ∧ st'.rv = (cyAnn st3 16 h).rv ∧
        st'.fe = st3.fe ∧ st'.an = true ∧ st'.d.ro = krole pc ∧ st'.d.n = 0 ∧
        st'.d.ok = true) _ _ _ _ (cyDOfCyB _ _ _ ?_) (fun i' st5 h5 => ?_)
      · refine cyOfRunRead kA (kAa pc) cyS pStop0 drefS _ _ _ _ a b hrr'
          (SailCycleOrderFp.fpDecodeC _) (PinCycRun.drefAgree _ hcfg4) hrb3
          (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, ?_, ?_, ?_⟩)
        · rw [e4]; exact hrole
        · rw [e5]; exact hn3.trans h2.2.2.1
        · rw [e6]; exact hok3.trans h2.2.2.2
      · obtain ⟨hia, e1, e2, e3, e4, e5, e6⟩ := h5
        subst i'
        unfold is_landing_pad_expected
        simp only [bind_assoc]
        refine cyDReadBind _ _ _ _ (fun ev hev _ => ?_)
        have hev' : ev = 0#1 := by
          rw [PinCycRun.rdMirror _ _ _ (by decide) hev, e1]; exact hcfg4.2.2.2.2.2.2
        subst hev'
        refine cyDPureBind _ _ _ _ ?_
        simp only [landing_pad_bits_backwards]
        rw [if_neg (by decide)]
        simp only [bind_assoc]
        refine cyDBind (fun z st' => z = true ∧ st'.rv = (cyRd st5 .elp).rv ∧
          st'.fe = st5.fe ∧ st'.an = st5.an ∧ st'.d.ro = st5.d.ro ∧ st'.d.n = st5.d.n ∧
          st'.d.ok = st5.d.ok) _ _ _ _ (cyDOfCyB _ _ _ ?_) (fun z st5' h5' => ?_)
        · refine cyOfRunRead kA (kAa pc) cyS pStop0 drefS _ _ _ _ true true PinCycRun.zcaOn
            (SailCycleOrderFp.fpCurrentlyEnabled _) ?_ ?_
            (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, e4, e5, e6⟩)
          · show ∀ r v, drefS r = some v → wireReg r = false ∧ st5.rv r = v
            rw [e1]; exact PinCycRun.drefAgree _ hcfg4
          · show RbootAll st5.rv
            rw [e1]; exact hrb3
        obtain ⟨rfl, f1, f2, f3, f4, f5, f6⟩ := h5'
        simp only [↓reduceIte]
        refine cyDReadBind _ _ _ _ (fun pcv hpcv _ => ?_)
        have hpcv' : pcv = BitVec.ofInt 64 pc := by
          rw [PinCycRun.rdMirror _ _ _ (by decide) hpcv, f1]
          show st5.rv .PC = _
          rw [e1]; exact (hp4 .PC (by decide)).trans hpc
        subst hpcv'
        refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
        have hW := PinCycRun.dfWrNextPC (cyRd st5' .PC).d
        have hsz : wSize (kw pc) = 2 := by simp [wSize, hrvc]
        have hnpc : BitVec.addInt (BitVec.ofInt 64 pc) 2 = BitVec.ofInt 64 (pc + wSize (kw pc)) := by
          rw [hsz, BitVec.addInt, BitVec.ofInt_add]
        let st6 := cyWr (cyRd st5' .PC) .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 2)
        have hp6 : ∀ r, pfProt r = true → r ≠ .nextPC → st6.rv r = st.rv r := by
          intro r hr hne
          show (st5'.rv.set .nextPC _) r = _
          rw [RegFile.set_other _ _ _ _ hne, f1]
          show st5.rv r = _
          rw [e1]; exact hp4 r hr
        have hpre6 : execPre pc st6 := by
          refine ⟨?_, ?_, rbootAllSet _ _ _ ?_ trivial, ?_, f3.trans e3, ?_, ?_, ?_⟩
          · rw [hp6 .PC (by decide) (by decide)]; exact hpc
          · exact PinCycRun.kCfgProt st.rv st6.rv (fun r hr _ hne => hp6 r hr hne) hcfg
          · show RbootAll st5'.rv
            rw [f1]
            show RbootAll st5.rv
            rw [e1]; exact hrb3
          · show (st5'.rv.set .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 2)) .nextPC = _
            rw [RegFile.set_same]; exact hnpc
          · exact hW.2.2.trans (f4.trans e4)
          · exact hW.1.trans (f5.trans e5)
          · exact hW.2.1.trans (f6.trans e6)
        simp only [FreeMLemmas.bind_pure]
        refine cyDBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend h) ∧
          execPost pc st6 r st') _ _ _ st6 ?_ (fun s st7 hs => ?_)
        · exact cyDBind _ _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec pStop0 st6 hpre6))
            (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h7⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        rcases hres with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
        · exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) pStop0 _ _ tick st7
            (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
            (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))
        · exact cyDOfCyB _ _ _ (finishTrapP kA (kAa pc) pStop0 _ x _ tick st7 hrb7
            (fun st' r v hpr _ hcb => ⟨hcb, by
              show st'.rv .cur_privilege = Privilege.Supervisor
              rw [hpr, hp7' .cur_privilege (by decide) (by decide)]; exact hcfg.1⟩))
    | F_Base w =>
      obtain ⟨hw, hrvc, hrole, fa, hfa, hfaR⟩ := PinCycRun.baseFacts pc htext w st3.fe hkA3 hsh3
      simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
      refine cyDAnnBind _ w _ st3 han3' ?_
      have hp4 : ∀ r, pfProt r = true → (cyAnn st3 32 w).rv r = st.rv r := fun r hr =>
        (hp3 r hr).trans (h2.1.1 r hr)
      have hcfg4 : kCfg (cyAnn st3 32 w).rv :=
        PinCycRun.kCfgProt _ _ (fun r hr _ _ => hp4 r hr) hcfg
      obtain ⟨b, hrr⟩ := PinCycRun.decBase pc a hdec hrvc
      have hrr' : runRead drefS (ext_decode w) = some (a, b) := by rw [hw]; exact hrr
      refine cyDBind (fun i' st' => i' = a ∧ st'.rv = (cyAnn st3 32 w).rv ∧
        st'.fe = st3.fe ∧ st'.an = true ∧ st'.d.ro = krole pc ∧ st'.d.n = 0 ∧
        st'.d.ok = true) _ _ _ _ (cyDOfCyB _ _ _ ?_) (fun i' st5 h5 => ?_)
      · refine cyOfRunRead kA (kAa pc) cyS pStop0 drefS _ _ _ _ a b hrr'
          (SailCycleOrderFp.fpDecodeS _) (PinCycRun.drefAgree _ hcfg4) hrb3
          (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, ?_, ?_, ?_⟩)
        · rw [e4]; exact hrole
        · rw [e5]; exact hn3.trans h2.2.2.1
        · rw [e6]; exact hok3.trans h2.2.2.2
      · obtain ⟨hia, e1, e2, e3, e4, e5, e6⟩ := h5
        subst i'
        unfold is_landing_pad_expected
        simp only [bind_assoc]
        refine cyDReadBind _ _ _ _ (fun ev hev _ => ?_)
        have hev' : ev = 0#1 := by
          rw [PinCycRun.rdMirror _ _ _ (by decide) hev, e1]; exact hcfg4.2.2.2.2.2.2
        subst hev'
        refine cyDPureBind _ _ _ _ ?_
        simp only [landing_pad_bits_backwards]
        refine cyDReadBind _ _ _ _ (fun pcv hpcv _ => ?_)
        have hpcv' : pcv = BitVec.ofInt 64 pc := by
          rw [PinCycRun.rdMirror _ _ _ (by decide) hpcv]
          show st5.rv .PC = _
          rw [e1]; exact (hp4 .PC (by decide)).trans hpc
        subst hpcv'
        refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
        have hW := PinCycRun.dfWrNextPC (cyRd (cyRd st5 .elp) .PC).d
        have hsz : wSize (kw pc) = 4 := by simp [wSize, hrvc]
        have hnpc : BitVec.addInt (BitVec.ofInt 64 pc) 4 = BitVec.ofInt 64 (pc + wSize (kw pc)) := by
          rw [hsz, BitVec.addInt, BitVec.ofInt_add]
        let st6 := cyWr (cyRd (cyRd st5 .elp) .PC) .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 4)
        have hp6 : ∀ r, pfProt r = true → r ≠ .nextPC → st6.rv r = st.rv r := by
          intro r hr hne
          show (st5.rv.set .nextPC _) r = _
          rw [RegFile.set_other _ _ _ _ hne, e1]; exact hp4 r hr
        have hpre6 : execPre pc st6 := by
          refine ⟨?_, ?_, rbootAllSet _ _ _ ?_ trivial, ?_, e3, ?_, ?_, ?_⟩
          · rw [hp6 .PC (by decide) (by decide)]; exact hpc
          · exact PinCycRun.kCfgProt st.rv st6.rv (fun r hr _ hne => hp6 r hr hne) hcfg
          · show RbootAll st5.rv
            rw [e1]; exact hrb3
          · show (st5.rv.set .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 4)) .nextPC = _
            rw [RegFile.set_same]; exact hnpc
          · exact hW.2.2.trans e4
          · exact hW.1.trans e5
          · exact hW.2.1.trans e6
        simp only [FreeMLemmas.bind_pure]
        refine cyDBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend w) ∧
          execPost pc st6 r st') _ _ _ st6 ?_ (fun s st7 hs => ?_)
        · exact cyDBind _ _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec pStop0 st6 hpre6))
            (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h7⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        rcases hres with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
        · exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) pStop0 _ _ tick st7
            (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
            (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))
        · exact cyDOfCyB _ _ _ (finishTrapP kA (kAa pc) pStop0 _ x _ tick st7 hrb7
            (fun st' r v hpr _ hcb => ⟨hcb, by
              show st'.rv .cur_privilege = Privilege.Supervisor
              rw [hpr, hp7' .cur_privilege (by decide) (by decide)]; exact hcfg.1⟩))

end CapDataTrap
end Weak
