/-
Weak: **the 4-byte `AxCert.Cert` SPINE over the TLB-FRAMED execute certificate**
`AxDataX4.CertXT` (`spineCertXT`, the port of `AxCert4.spineCertX`: the execute may fill the
TLB).

Rocq: `iris/AxDataX5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`spineCertXT`: over `SpineOkT` + `SpineFetch4T` at budget `BInf`, given the decode fact of the
fetched word and a `CertXT` for `execute ins` (from every state of the regime at this pc, the
execute ends in `wrOpt ow t0` for SOME `t0` that is a TLB frame of the start state and keeps the
regime), `riscvStep tick` (both ticks) is a `Cert` ending in `PX ∧ GoodC … none ow` (PC + 4,
GPRs by `ow`, control state in the regime).  (The Rocq header also announces the 4-byte
load/store leaves; the Rocq file contains only the spine — the leaves are not in it.)

## Deviations from Rocq

1. Q7 (as `AxCert4` deviation 1): the 4-byte arm announces the 32-bit word, so `spineCertXT`
   takes `Hsf : sfAnnB 32 w = false` right after `textAt4 pc w`.
2. Types / registers as `AxCert4` deviation 3: `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`, `register_lookup r t.(sregs)` ↦ `t.regs r`,
   `add_vec_int` ↦ `BitVec.addInt`, `CS d BInf r` ↦ `⟨d, .BInf, r⟩`, `cs_b` ↦ `csB`.
3. Section variables `img dok kind` are explicit arguments (in the section order).

**Rocq → Lean name map.**  `spine_certXT` `spineCertXT` (not in the duplicated-name table).

**Dropped:** nothing (Rocq 1 lemma; Lean 1).  **Not ported:** the section notations `CM` / `EvM`
and the Ltac `lk` (`RegFile` rewrites instead).
-/
import Weak.AxDataX4
import Weak.AxCert4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `spine_certXT`. -/
theorem spineCertXT (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
    (rs : RegFile) (pc : BitVec 64) (w : BitVec 32) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (d : Cdata) (r : Bool) (PX : Cst → Prop) :
    ctrlOk rs → rs .PC = pc → textAt4 pc w → sfAnnB 32 w = false →
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t) →
    (∀ s, PX s → owOk (ow s)) → (∀ s, PX s → s.csB = .BInf) →
    CertXT img dok kind ctrlOk rs pc ins ow ⟨d, .BInf, r⟩ PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s _ t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs)
        ⟨d, .BInf, r⟩ (riscvStep tick) t := by
  intro Hct HPC Htx Hsf Hdec How HPX Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hf4 _ pc w Hct_a HPC_a Htx
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 4)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc 4)).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .nextPC =
      BitVec.addInt pc 4 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag
  have Hrun := CertHartActiveBaseT img dok kind _ t1 w ins pc d r
    (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 4)) t0 ∧
      ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0) Hsf
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1) (Hsp.sptLpad _ Hct1) HPC_1 Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine CertRiscvStep img dok kind tick ⟨d, .BInf, r⟩ t
    (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs) _ ?_ ?_
  · have HT := CertTryStepActive img dok kind t b (zero_extend (m := 32) w) d r
      (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 4)) t0 ∧
        ctrlOk t0.regs ∧ t' = wrOpt (ow s) t0)
      (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs) Hb
      (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono img dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨HP, t0, Hfr0, Hc0, rfl⟩
      have Hct_x := wrNpcCtrl img ctrlOk textAt Hsp (ow s) none _ Hc0
      have How' := How s HP
      rw [show wrOpt (ow s) t0 = wrOpt (ow s) (npcOpt none t0) from rfl]
      refine ⟨?_, ?_, HP, ?_, ?_, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · unfold tfinal
        cases b
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC, tlbFrameLookup _ _ _ Hfr0 (by decide)]
        exact Hnpc_pc
      · intro r Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        refine gprPostAgree _ _ _ _ ?_ Hr
        intro r1 Hr1
        rw [AxSpineOk5.tlbFrameXget _ _ Hfr0]
        exact Hgag r1 Hr1
  · rintro s' t' ⟨HP, HG⟩
    cases tick with
    | false => exact ⟨HP, HG⟩
    | true =>
      obtain ⟨d', b', r'⟩ := s'
      have Hb' : b' = .BInf := HPX _ HP
      subst Hb'
      refine CertMono img dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertEvA img dok kind _ _ d' r' t' (Hsp.sptTick t' HG.1))
      rintro _ _ t'' ⟨rfl, Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨HP, Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end Weak
