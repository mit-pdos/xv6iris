/-
Weak: **r2 glue (ii) — THE NO-FETCH-FAULT CYCLE at a walk pc** (`PROGRESS-r2glue.md`).
Lean-only.

`cyESailOf`: at a walk pc (even, kernel text, decoded), with fetch configurations `c1` (`PC`) and
`c2` (`PC + 2`) — `R|X` identity leaves, pages in RAM — every cycle `riscvStep tick` from the kernel
configuration satisfies `cyDB` at the two configurations' filters with the stop post `eStopPost`:
an EXCEPTION's cause write happens only AFTER the instruction's announce.  The proof is
`PinDataOk.cyDSailOf`'s re-assembly of w1's `cySailOf` with the fetch replaced by the three-way
product `cyEFetch` (w1's `fetchCyR1` lifted × `dkFetchOk` × w1's frame `pfFetch`, the `PC` / `misa`
reads justified by the mirror), so its `F_Error` arm is empty; the execute stage's trap goes to
w1's `cyFinishTrap` (after the announce).  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkIF2
import Weak.PinDataOkSail
import Weak.PinCycRunFetch

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace PinDataOk
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-- The two fetch configurations' register filter (per read, the interface's). -/
def eG (c1 c2 : DCfg) (r : Register) (v : RegisterType r) : Prop := dG c1 r v ∧ dG c2 r v

/-- The two fetch configurations' answer filter. -/
def eD (c1 c2 : DCfg) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  dAns c1 pa n w ∧ dAns c2 pa n w

theorem eGRboot (c1 c2 : DCfg) : ∀ r v, eG c1 c2 r v → Rboot r v := fun _ _ h => h.1.1

/-- The fetch configurations at `pc`: identity `R|X` leaves for `PC` and `PC + 2`, pages in RAM. -/
def fCfgOk (pc : Int) (c1 c2 : DCfg) : Prop :=
  c1.ram ∧ c1.perm = .rx ∧ c1.vpn = vpnOf (BitVec.ofInt 64 pc) ∧
  c2.ram ∧ c2.perm = .rx ∧ c2.vpn = vpnOf (BitVec.addInt (BitVec.ofInt 64 pc) 2)

/-- The stop post: an exception's cause write only after the announce. -/
def eStopPost (st : CySt) (_r : Register) (_v : RegisterType _r) : Prop := st.an = true

/-- The stop post `cyB` stretches are lifted at. -/
def eStop0 (st : CySt) (r : Register) (v : RegisterType r) : Prop := causeBit r v = false ∧ eStopPost st r v

set_option maxHeartbeats 4000000 in
/-- **THE FETCH'S THREE-WAY PRODUCT** (header): a `cyDB` fact of the fetch, the fetch-Ok fact at the
two configurations, and w1's frame footprint: along the product the mirror keeps `PC` and `misa`
(protected), which answers `dk2B`'s `PC` / `misa` reads. -/
theorem cyEFetch (c1 c2 : DCfg) (pc : Int) {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}
    {T : CySt → (r : Register) → RegisterType r → Prop} {X : Type} (Q : X → CySt → Prop) (R : X → Prop)
    (S : X → Prop) :
    ∀ (m : SailM X) (st : CySt), cyDB (eG c1 c2) (eD c1 c2) A Aa T Q m st → dk2B c1 c2 pc R m →
      pfB true S m → st.rv .PC = BitVec.ofInt 64 pc → st.rv .misa = kMisa →
      cyDB (eG c1 c2) (eD c1 c2) A Aa T (fun x st' => Q x st' ∧ R x) m st := by
  intro m
  induction m with
  | pure y => exact fun st h1 h2 _ _ _ => ⟨h1, h2⟩
  | impure call k ih =>
    intro st h1 h2 hp hpc hmi
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv hg
        have hd : dG2 c1 c2 pc r v := by
          refine ⟨hg.1, hg.2, fun h => ?_, fun h => ?_⟩
          · subst h; rw [hv (by decide)]; exact hpc
          · subst h; rw [hv (by decide)]; exact hmi
        exact ih v _ (h1 v hv hg) (h2 v hd) (hp v hg.1.1) hpc hmi
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hk⟩ := hp
        have hpf : pfProt r = false := by simpa [pfRegOk] using hok
        refine ⟨h1.1, fun h => ⟨(h1.2 h).1, fun u => ih u _ ((h1.2 h).2 u) (h2 u) (hk u) ?_ ?_⟩⟩
        · have e : Register.PC ≠ r := by rintro rfl; cases hpf
          show (st.rv.set r v) .PC = _
          rw [RegFile.set_other _ _ _ _ e]; exact hpc
        · have e : Register.misa ≠ r := by rintro rfl; cases hpf
          show (st.rv.set r v) .misa = _
          rw [RegFile.set_other _ _ _ _ e]; exact hmi
      case memRead =>
        exact ⟨fun a1 a2 a3 w hw hd => ih _ _ (h1.1 a1 a2 a3 w hw hd) (h2 w hd.1 hd.2) (hp.2 _) hpc hmi,
          fun a w hd => ih _ _ (h1.2 a w hd) (h2 w hd.1 hd.2) (hp.2 _) hpc hmi⟩
      case instrAnnounce => exact hp.elim
      case memWrite => exact ih _ _ h1 h2 (hp _) hpc hmi
      case getCycleCount => exact ih _ _ h1 (h2 _) (hp _) hpc hmi
      case barrier => exact fun v => ih v _ (h1 v) (h2 v) hp.2 hpc hmi
      all_goals exact fun v => ih v _ (h1 v) (h2 v) (hp v) hpc hmi

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **THE NO-FETCH-FAULT CYCLE** (header). -/
theorem cyESailOf (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (hev : pc % 2 = 0) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hfetch : fetchCyR1 pc) (hexec : execCyAt pc)
    (hnw : dfNwRole (krole pc)) (c1 c2 : DCfg) (hc : fCfgOk pc c1 c2) :
    ∀ (tick : Bool) (st : CySt), cyInit pc st →
      cyDB (eG c1 c2) (eD c1 c2) kA (kAa pc) eStopPost (fun _ _ => True) (riscvStep tick) st := by
  intro tick st hinit
  obtain ⟨⟨hpc, hcfg, hrb⟩, hfe, han, hd⟩ := hinit
  obtain ⟨hr1, hp1, hv1, hr2, hp2, hv2⟩ := hc
  have hpc0 : 0 ≤ pc := by have := htext.1; simp only [textLo] at this; omega
  have hpc38 : pc + 2 < 2 ^ 38 := by have := htext.2; simp only [textHi] at this; omega
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  have hpre0 : preInv st st := ⟨cyFrameRefl st hrb, by rw [hd], by rw [hd], by rw [hd]⟩
  -- the prelude
  have hP := cyPrelude kA (kAa pc) eStop0 (fun hs st' => hs = st.rv .hart_state ∧ preInv st st') pure st st
    hpre0 (fun st' h => ⟨rfl, h⟩)
  rw [bindPureR] at hP
  refine cyDBind _ _ _ _ st (cyDOfCyB _ _ _ hP) (fun hs st1 h1 => ?_)
  obtain ⟨rfl, h1⟩ := h1
  rw [hcfg.2.2.2.2.1]
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  -- the dispatch
  have hD := cyDispatch kA (kAa pc) eStop0 (fun o st' => preInv st st') pure st st1 h1 (fun o st' h => h)
  rw [bindPureR] at hD
  refine cyDBind _ _ _ _ st1 (cyDOfCyB _ _ _ hD) (fun o st2 h2 => ?_)
  have han2 : st2.an = false := h2.1.2.2.2.trans han
  cases o with
  | some ip =>
    refine cyDPureBind _ _ _ _ ?_
    exact cyDFinishIntr (eGRboot c1 c2) ip tick st2
  | none =>
    simp only [bind_assoc]
    have hF := hfetch eStop0 st2 (h2.1.2.2.1.trans hfe) han2
      (by rw [h2.1.1 .PC (by decide)]; exact hpc)
      (PinCycRun.kCfgProt _ _ (fun r hr _ _ => h2.1.1 r hr) hcfg) h2.1.2.1 h2.2.1
    have hpc2 : st2.rv .PC = BitVec.ofInt 64 pc := by rw [h2.1.1 .PC (by decide)]; exact hpc
    have hmisa2 : st2.rv .misa = kMisa := by rw [h2.1.1 .misa (by decide)]; exact hcfg.2.1
    refine cyDBind (fun fr st' => fetchPostCy pc st2 fr st' ∧ frNoFault fr) _ _ _ st2
      (cyEFetch c1 c2 pc _ _ _ (fetch ()) st2 (cyDOfCyB _ _ _ hF)
        (dkFetchOk c1 c2 pc hpc0 hpc38 hev hr1 hp1 hv1 hr2 hp2 hv2)
        PinCycRunFp.PinCycRunFetch.pfFetch hpc2 hmisa2) (fun fr st3 h3 => ?_)
    obtain ⟨⟨hp3, hrb3, han3, hro3, hn3, hok3, hkA3, hsh3⟩, hnf⟩ := h3
    have han3' : st3.an = false := han3.trans han2
    cases fr with
    | F_Ext_Error e => exact hsh3.elim
    | F_Error p => exact hnf.elim
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
      · refine cyOfRunRead kA (kAa pc) cyS eStop0 drefS _ _ _ _ a b hrr'
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
        · refine cyOfRunRead kA (kAa pc) cyS eStop0 drefS _ _ _ _ true true PinCycRun.zcaOn
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
        · exact cyDBind _ _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec eStop0 st6 hpre6))
            (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h7⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        have han7' : st7.an = true := han7.trans hpre6.2.2.2.2.1
        rcases hres with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
        · exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) eStop0 _ _ tick st7
            (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
            (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))
        · exact cyDOfCyB _ _ _ (cyFinishTrap kA (kAa pc) eStop0 _ x _ tick st7 hrb7
            (fun st' r v _ h2 _ hcb => ⟨hcb, h2.trans han7'⟩))
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
      · refine cyOfRunRead kA (kAa pc) cyS eStop0 drefS _ _ _ _ a b hrr'
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
        · exact cyDBind _ _ _ _ st6 (cyDOfCyB _ _ _ (hexec a hdec eStop0 st6 hpre6))
            (fun r st' h => ⟨r, rfl, h⟩)
        obtain ⟨r, rfl, h7⟩ := hs
        obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
        have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
          (hp7 r hr hne).trans (hp6 r hr hne)
        have han7' : st7.an = true := han7.trans hpre6.2.2.2.2.1
        rcases hres with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
        · exact cyDOfCyB _ _ _ (cyFinishRetire kA (kAa pc) eStop0 _ _ tick st7
            (by rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1) hrb7
            (by rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw) (fun _ _ => trivial))
        · exact cyDOfCyB _ _ _ (cyFinishTrap kA (kAa pc) eStop0 _ x _ tick st7 hrb7
            (fun st' r v _ h2 _ hcb => ⟨hcb, h2.trans han7'⟩))

end PinDataOk
end Weak
