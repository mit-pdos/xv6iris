/-
Weak: **`dataOkR` (4d) — THE FILTERED CYCLE at a walk load/store** (`PROGRESS-dataOk.md`).
Lean-only.

`cyDSailOf`: at a walk pc whose instruction is a load/store with an access the interface
describes (`dAccOk pc c`, the walk's pages in RAM), every cycle `riscvStep tick` from the kernel
configuration satisfies `cyDB` at the interface's filters (`dG c`, `dAns c`) with the stop post
`dStopPost` — an EXCEPTION's cause write happens only BEFORE the instruction's announce (a fetch
failure).  The proof is w1's `PinCycRun.cySailOf` (`Weak/PinCycRunCyc3.lean:298`) re-assembled in
`cyDB`: every `cyB` stretch is lifted (`cyDOfCyB`, its continuation-passing lemmas instantiated at
`pure`); an interrupt's tail is `cyDFinishIntr`; the execute stage is w1's `execCyAt` × the data
access `dkExecWalkAcc` (`cyDAndDk`), so its trap branch is empty.  Every helper is
`Weak.PinDataOk.*`.
-/
import Weak.PinDataOkIntr
import Weak.PinCycRunCyc3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace PinDataOk
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-- The stop post: an exception's cause write only before the announce. -/
def dStopPost (st : CySt) (_r : Register) (_v : RegisterType _r) : Prop := st.an = false

/-- The stop post `cyB` stretches are lifted at. -/
def dStop0 (st : CySt) (r : Register) (v : RegisterType r) : Prop := causeBit r v = false ∧ dStopPost st r v

theorem bindPureR {X : Type} (m : SailM X) : (m >>= pure) = m := FreeMLemmas.bind_pure_right m

theorem cyDAnnBind {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
    {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {T : CySt → (r : Register) → RegisterType r → Prop}
    {Y : Type} (Q : Y → CySt → Prop) {n : Nat} (w : BitVec n) (f : Unit → SailM Y)
    (st : CySt) (han : st.an = false) (h : cyDB G D A Aa T Q (f ()) (cyAnn st n w)) :
    cyDB G D A Aa T Q (instr_announce w >>= f) st :=
  ⟨han, fun u => by cases u; exact h⟩

theorem cyDBindF {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
    {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {T : CySt → (r : Register) → RegisterType r → Prop}
    {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) (st : CySt) (hm : cyDB G D A Aa T Q m st)
    (hf : ∀ x st', Q x st' → cyDB G D A Aa T P (f x) st') : cyDB G D A Aa T P (FreeM.bind m f) st :=
  cyDBind Q P m f st hm hf

theorem dGRboot (c : DCfg) : ∀ r v, dG c r v → Rboot r v := fun _ _ h => h.1

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **THE FILTERED CYCLE** (header). -/
theorem cyDSailOf (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hfetch : fetchCyR1 pc) (hexec : execCyAt pc)
    (hnw : dfNwRole (krole pc)) (c : DCfg) (hr : c.ram) (hacc : dAccOk pc c) :
    ∀ (tick : Bool) (st : CySt), cyInit pc st →
      cyDB (dG c) (dAns c) kA (kAa pc) dStopPost (fun _ _ => True) (riscvStep tick) st := by
  intro tick st hinit
  obtain ⟨⟨hpc, hcfg, hrb⟩, hfe, han, hd⟩ := hinit
  obtain ⟨a', hdec', hdk⟩ := dkExecWalkAcc pc c hr hacc
  rw [hdec] at hdec'
  injection hdec' with hdec'
  subst hdec'
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  have hpre0 : preInv st st := ⟨cyFrameRefl st hrb, by rw [hd], by rw [hd], by rw [hd]⟩
  -- the prelude
  have hP := cyPrelude kA (kAa pc) dStop0 (fun hs st' => hs = st.rv .hart_state ∧ preInv st st') pure st st
    hpre0 (fun st' h => ⟨rfl, h⟩)
  rw [bindPureR] at hP
  refine cyDBind _ _ _ _ st (cyDOfCyB _ _ _ hP) (fun hs st1 h1 => ?_)
  obtain ⟨rfl, h1⟩ := h1
  rw [hcfg.2.2.2.2.1]
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  -- the dispatch
  have hD := cyDispatch kA (kAa pc) dStop0 (fun o st' => preInv st st') pure st st1 h1 (fun o st' h => h)
  rw [bindPureR] at hD
  refine cyDBind _ _ _ _ st1 (cyDOfCyB _ _ _ hD) (fun o st2 h2 => ?_)
  have han2 : st2.an = false := h2.1.2.2.2.trans han
  cases o with
  | some ip =>
    refine cyDPureBind _ _ _ _ ?_
    exact cyDFinishIntr (dGRboot c) ip tick st2
  | none =>
    simp only [bind_assoc]
    have hF := hfetch dStop0 st2 (h2.1.2.2.1.trans hfe) han2
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
      exact cyDOfCyB _ _ _ (cyFinishFetchFail kA (kAa pc) dStop0 _ (virtaddr.Virtaddr addr, e) tick st3 hrb3
        (fun st' r v _ han' _ hcb => ⟨hcb, by show st'.an = false; rw [han', han3']⟩))
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
      · refine cyOfRunRead kA (kAa pc) cyS dStop0 drefS _ _ _ _ a b hrr'
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
        · refine cyOfRunRead kA (kAa pc) cyS dStop0 drefS _ _ _ _ true true PinCycRun.zcaOn
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
          execPost pc st6 r st' ∧ r = RETIRE_SUCCESS) _ _ _ st6 ?_ (fun s st7 hs => ?_)
        · exact cyDBind _ _ _ _ st6 (cyDAndDk c _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec dStop0 st6 hpre6)) hdk)
            (fun r st' h => ⟨r, rfl, h.1, h.2⟩)
        obtain ⟨r, rfl, h7, rfl⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) dStop0 _ _ tick st7
          (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
          (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))
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
      · refine cyOfRunRead kA (kAa pc) cyS dStop0 drefS _ _ _ _ a b hrr'
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
          execPost pc st6 r st' ∧ r = RETIRE_SUCCESS) _ _ _ st6 ?_ (fun s st7 hs => ?_)
        · exact cyDBind _ _ _ _ st6 (cyDAndDk c _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec dStop0 st6 hpre6)) hdk)
            (fun r st' h => ⟨r, rfl, h.1, h.2⟩)
        obtain ⟨r, rfl, h7, rfl⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) dStop0 _ _ tick st7
          (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
          (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))

end PinDataOk
end Weak
