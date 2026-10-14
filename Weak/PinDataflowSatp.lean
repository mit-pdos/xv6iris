/-
Weak: **W9a (B) B5 — the PURE CSR READ clause (`csrr rd, satp`, `rdtime rd`)** (plan
`notes/weak-allocproc-plan.md` rev 52 §C "W9a (B)" (B5); B1's per-instruction dataflow,
`Weak/PinDataflowCsr.lean`, extended WITHOUT editing the merged file).  Lean-only.

B5's generated per-state checks (`Weak/PinWalkTab.lean`) found exactly TWO instructions that B1's
per-word check (`dfInstrOkAll`) rejects:
  * `prepare_return+0x32` (`0x80002592`, `csrr a4,satp`) — a walk state of the certifying row
    `prepare_return+0x30` (`ld a5,88(a0)`, `PDep` at `+0x36`): B1's CSR table `csrDfReg` has no
    `satp` ("boot code");
  * `clockintr+0xe` (`0x800025e2`, `rdtime a5`) — a state of B2's fence-free census (path (c)):
    `time` IS in B1's table, but B1's role check `dfCsrRoleOk` rejects the CSR's pseudo-register
    `p = TIME` in every access mode — a restriction needed where `p` is a DESTINATION (`dfNwRole`),
    vacuous for a pure read, where `p` is a source only.
This file proves the PURE READ (`CSRReg` with a `CSRRead` access: `csrrs`/`csrrc rd, csr, x0`) at
`satp` and at every CSR of B1's table:
  * `dfReadSatp`, `dfDoCsrSatp`, `dfExecCsrRegSatp` — `doCSR` at `satp` is B1's `dfDoCsr` text at
    the one CSR, with the read arm `read_CSR 0x180 = readReg satp` (`ZicsrInsts.lean`);
  * `dfCsrReadRoleOk` (the read role check: ONE destination `rd`, sources among the CSR's
    pseudo-register and `rs1`), `dfNwRoleOfReadCheck`, `dfCsrReadDone` (B1's `dfCsrDone`, the
    `CSRRead` case);
  * the per-word check `dfCsrReadOk` and the instruction-level headline `dfInstrCsrRead`; the
    combined check `dfInstrOkB5 = dfInstrOkAll || dfCsrReadOk` and headline `dfInstrB5` (post
    `dfDone`, as `dfInstrAll`).
The decoded role of `csrr rd, satp` is `ORalu rd [SATP]` (DEC-5, `Weak/WeakDeps.lean`); of
`rdtime rd`, `ORalu rd [TIME]`.

Spec: Sail `doCSR`/`read_CSR`/`check_CSR_result` (`ZicsrInsts.lean`); no trusted text.  FAITHFUL.
Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflowCsr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataflow
open SailCycleOrderK

set_option maxHeartbeats 4000000 in
/-- `read_CSR` at `satp` reads the register `satp` once. -/
theorem dfReadSatp (st : DfSt) : dfB (dfRdPost st .satp) (read_CSR 0x180#12) st :=
  fun _ _ => dfExtRefl _

set_option maxHeartbeats 8000000 in
/-- **`doCSR` at `satp`, a pure read** (B1's `dfDoCsr` at the one CSR). -/
theorem dfDoCsrSatp (v : BitVec 64) (rd : BitVec 5) (op : csrop) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfCsrPost st .satp rd .CSRRead) (doCSR 0x180#12 v (regidx.Regidx rd) op .CSRRead) st := by
  have h344 : (0x180#12 : BitVec 12) ≠ 836#12 := by decide
  have h144 : (0x180#12 : BitVec 12) ≠ 324#12 := by decide
  unfold doCSR
  refine dfNwBind false _ _ _ _ st hro (nwReadReg _) (fun p st0 _ h0 => ?_)
  refine dfNwBind false _ _ _ _ st0 (dfNwRoleExt _ _ h0 hro) (nwCheckCSRResult _ _ _)
    (fun cr st1 _ h1 => ?_)
  have h01 := dfExtTrans _ _ _ h0 h1
  cases cr with
  | CSR_Illegal u => exact Or.inl rfl
  | CSR_Virtual u => exact Or.inl rfl
  | CSR_Check_OK u =>
    cases u
    refine dfNwBind false _ _ _ _ st1 (dfNwRoleExt _ _ h01 hro) (nwReadReg _)
      (fun p2 st2 _ h2 => ?_)
    have h02 := dfExtTrans _ _ _ h01 h2
    rw [if_neg (by simp [ext_check_CSR, Functions.not])]
    refine dfBBind (fun _ st' => dfExt st2 st' ∧
        (CSRAccessType.CSRRead ≠ .CSRWrite → ∀ k, eregNum Register.satp = some k → k ∈ st'.rds))
        _ _ _ st2 ?_ ?_
    · split
      · refine dfBMono _ _ (fun _ st' h => ⟨dfExtTrans _ _ _ (dfExtRd _ _) h, fun _ k hk =>
          dfExtMem _ _ _ h (dfRdMem st2 .satp k hk)⟩) _ _ (dfReadSatp st2)
      · rename_i hne
        exact absurd hne (by decide)
    · rintro rv st3 ⟨h3, hm3⟩
      have h03 := dfExtTrans _ _ _ h02 h3
      split
      · first | exact absurd rfl h344 | exact absurd ‹_› h344
      · first | exact absurd rfl h144 | exact absurd ‹_› h144
      · refine dfBPureBind _ _ _ _ ?_
        split
        · refine dfNwBind false _ _ _ _ st3 (dfNwRoleExt _ _ h03 hro) (nwCsrIdReadCallback _ _)
            (fun _ st4 _ h4 => ?_)
          have h04 := dfExtTrans _ _ _ h03 h4
          refine dfWXBind _ _ _ _ _ (dfNwRoleExt _ _ h04 hro) (fun _ st5 h5 => ?_)
          refine Or.inr ⟨rfl, st4, st4, h04, fun ha k hk => dfExtMem _ _ _ h4 (hm3 ha k hk),
            fun _ => rfl, fun ha => absurd rfl ha, h5⟩
        · rename_i hr
          exact absurd hr (by decide)

/-- The `CSRReg` clause at `satp`, for a pure-read access. -/
theorem dfExecCsrRegSatp (rs1 rd : BitVec 5) (op : csrop)
    (hacc : csr_access_type op (regidx.Regidx rd == zreg) (regidx.Regidx rs1 == zreg) = .CSRRead)
    (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfCsrPost (dfGprRd st rs1) .satp rd .CSRRead)
      (execute_CSRReg 0x180#12 (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_CSRReg
  rw [hacc]
  exact dfRXBind _ _ _ _ (fun v => dfDoCsrSatp v rd op _ hro)

/-- **THE ROLE CHECK OF A PURE CSR READ** (header): the role's ONE destination is `rd`, its
decoded sources among what was read (the CSR's pseudo-register `p` and `rs1`).  B1's
`dfCsrRoleOk` also requires `p` not to be `mip`/`mtime` — needed where `p` is a DESTINATION; in a
pure read `p` is a source only, so `rdtime` (`p = TIME`) passes here. -/
def dfCsrReadRoleOk (ro : OpRoles) (p : Nat) (rd : BitVec 5) (reads : List Nat) : Bool :=
  match depsRd ro, depsRd2 ro with
  | some (k, dec), none => gprNum rd == some k && dfCov dec (p :: reads)
  | _, _ => false

/-- A pure read's role names no `mip`/`mtime` destination. -/
theorem dfNwRoleOfReadCheck (ro : OpRoles) (p : Nat) (rd : BitVec 5) (reads : List Nat)
    (h : dfCsrReadRoleOk ro p rd reads = true) : dfNwRole ro := by
  unfold dfCsrReadRoleOk at h
  intro q hq
  split at h
  · rename_i k dec hd1 hd2
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.mem_singleton] at hq
    subst hq
    have := gprNumLt rd k h.1
    exact ⟨by simp only [wcsr, MIP]; omega, by simp only [wcsr, TIME]; omega⟩
  · exact absurd h Bool.false_ne_true

/-- **The `doCSR` post of a pure read gives the instruction-level post** (B1's `dfCsrDone`, the
`CSRRead` case, under the read role check). -/
theorem dfCsrReadDone (st0 st : DfSt) (reg : Register) (p : Nat) (rd : BitVec 5)
    (reads : List Nat) (hp : eregNum reg = some p) (hext : dfExt st st0)
    (hreads : ∀ r, r ∈ reads → r ∈ st0.rds) (hn : st.n = 0) (hok : st.ok = true)
    (hchk : dfCsrReadRoleOk st.ro p rd reads = true) (r : ExecutionResult) (st' : DfSt)
    (h : dfCsrPost st0 reg rd .CSRRead r st') : dfDone r st' := by
  rcases h with h | ⟨-, st1, st2, h01, hrd1, hR, -, h2'⟩
  · exact Or.inl h
  have hst1 := dfExtTrans _ _ _ hext h01
  have hr1 : ∀ r, r ∈ reads → r ∈ st1.rds := fun r h => dfExtMem _ _ _ h01 (hreads r h)
  refine Or.inr ?_
  unfold dfCsrReadRoleOk at hchk
  split at hchk
  · rename_i k dec hd1 hd2
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨hk, hcv⟩ := hchk
    have e2 : st2 = st1 := hR rfl
    subst e2
    obtain ⟨f1, f2, f3⟩ := dfGprWrFill st2 rd k dec hk (hst1.1 ▸ hd1) (hst1.1 ▸ hd2)
      (hst1.2.1.trans hn) (dfCovCons dec p reads st2 hcv (hrd1 (by intro e; cases e) p hp) hr1)
    refine ⟨by rw [h2'.2.2.1, f2, hst1.2.2.1, hok], ?_⟩
    rw [h2'.2.1, f1, h2'.1, f3, hst1.1]
    simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.length_singleton]
  · exact absurd hchk Bool.false_ne_true

/-- The CSR a pure read reads: `satp` (this file) or one of B1's (`csrDfReg`). -/
def csrReadReg (c : BitVec 12) : Option Register :=
  if c == 0x180#12 then some .satp else csrDfReg c

/-- **THE PER-WORD CHECK, pure CSR reads** (header): a `CSRReg` with a `CSRRead` access at
`satp` or at a CSR of B1's table (`time` included), whose role passes the read role check. -/
def dfCsrReadOk (ro : OpRoles) (i : instruction) : Bool :=
  match i with
  | .CSRReg (c, rs1, rd, op) =>
      csr_access_type op (rd == zreg) (rs1 == zreg) == .CSRRead &&
        match csrReadReg c with
        | some reg =>
            match eregNum reg with
            | some p => dfCsrReadRoleOk ro p (uxaIdx rd) (gprNum (uxaIdx rs1)).toList
            | none => false
        | none => false
  | _ => false

theorem satpNum : eregNum Register.satp = some (wcsr SATP) := rfl

/-- **B1 at a pure CSR read** (header): the execute stage of `csrr rd, csr` is `dfDone`. -/
theorem dfInstrCsrRead (c : instruction) (st : DfSt) (hn : st.n = 0) (hok : st.ok = true)
    (h : dfCsrReadOk st.ro c = true) : dfB dfDone (uxaExecAs c) st := by
  cases c
  all_goals first | (simp only [dfCsrReadOk, reduceCtorEq] at h) | skip
  case CSRReg a =>
    obtain ⟨csr, ⟨rs1⟩, ⟨rd⟩, op⟩ := a
    simp only [uxaIdx, Bool.and_eq_true] at h
    obtain ⟨hacc, h⟩ := h
    have hacc' := accBeqRT _ hacc
    split at h
    · rename_i reg hreg
      split at h
      · rename_i p hp
        have hro := dfNwRoleOfReadCheck _ _ _ _ h
        have hrd : ∀ r, r ∈ (gprNum rs1).toList → r ∈ (dfGprRd st rs1).rds := by
          intro r hr
          cases hg : gprNum rs1 with
          | none => rw [hg] at hr; cases hr
          | some k =>
            rw [hg] at hr
            simp only [Option.toList, List.mem_singleton] at hr
            subst hr
            simp only [dfGprRd, hg, dfRdsAdd]
            exact List.mem_append_right _ (List.mem_singleton.2 rfl)
        have hdone := fun r st' h' =>
          dfCsrReadDone (dfGprRd st rs1) st reg p rd (gprNum rs1).toList hp (dfExtGprRd st rs1)
            hrd hn hok h r st' h'
        unfold csrReadReg at hreg
        split at hreg
        · rename_i hc
          have hc' : csr = 0x180#12 := beq_iff_eq.mp hc
          subst hc'
          simp only [Option.some.injEq] at hreg
          subst hreg
          exact dfBMono _ _ hdone _ _
            (dfExecAsOf _ _ st (dfCsrPostRes _ _ _ _) (dfExecCsrRegSatp rs1 rd op hacc' st hro))
        · have hx := dfExecCsrReg csr rs1 rd op reg hreg (fun _ => hacc') st hro
          rw [hacc'] at hx
          exact dfBMono _ _ hdone _ _ (dfExecAsOf _ _ st (dfCsrPostRes _ _ _ _) hx)
      · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true

/-- **The per-word check, every covered class** (B1's `dfInstrOkAll` or a pure CSR read). -/
def dfInstrOkB5 (ro : OpRoles) (c : instruction) : Bool := dfInstrOkAll ro c || dfCsrReadOk ro c

/-- **B1 + the pure CSR reads: the execute stage of ONE instruction** (header). -/
theorem dfInstrB5 (c : instruction) (st : DfSt) (hn : st.n = 0) (hok : st.ok = true)
    (h : dfInstrOkB5 st.ro c = true) : dfB dfDone (uxaExecAs c) st := by
  unfold dfInstrOkB5 at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact dfInstrAll c st hn hok h
  · exact dfInstrCsrRead c st hn hok h

/-- Non-vacuity: the check holds at the real words `0x18002773` (`csrr a4,satp`,
`prepare_return+0x32`) and `0xc01027f3` (`rdtime a5`, `clockintr+0xe`). -/
theorem dfCsrReadOkSatp :
    dfCsrReadOk (depsOfBits (BitVec.ofNat 32 0x18002773))
      (instruction.CSRReg (0x180#12, regidx.Regidx 0#5, regidx.Regidx 14#5, csrop.CSRRS)) = true := by
  decide +kernel

theorem dfCsrReadOkRdtime :
    dfCsrReadOk (depsOfBits (BitVec.ofNat 32 0xc01027f3))
      (instruction.CSRReg (0xC01#12, regidx.Regidx 0#5, regidx.Regidx 15#5, csrop.CSRRS)) = true := by
  decide +kernel

end PinDataflow
end Weak
