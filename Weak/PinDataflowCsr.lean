/-
Weak: **W9a (B) B1 — the Zicsr clauses** (plan `notes/weak-allocproc-plan.md` rev 49 §C "W9a (B)"
(B1): `CSRReg` among the base clauses, and the trap paths' CSR writes; spike `notes/W9aB-spike.md`
§4).  Lean-only.

`csrr`/`csrw`/`csrrw`/`csrrs`/`csrrc` and their immediate forms run `doCSR csr v rd op acc`: the
access checks (`check_CSR_result`, register reads only), the CSR READ unless the access is a pure
write (`read_CSR csr`), the CSR WRITE unless it is a pure read (`write_CSR csr v`), then the GPR
write of `rd` (`wX_bits`, nothing for `x0`).  The decoded role (`WeakDeps` DEC-5/6) names the
CSR's pseudo-register `p` as a destination (`ORcsr p srcs rd`: slot 0 the CSR, slot 1 `rd`) or,
for a pure read, as the source of `rd` (`ORalu rd [p]`).

* For the CSRs of the kernel's trap paths and certified walks (`csrDfReg`: `sstatus` (the model
  reads and writes `mstatus`), `sie` (`mie`), `stvec`, `sscratch`, `sepc`, `scause`, `stval`,
  `stimecmp`, and `time` (`mtime`, read only)), `read_CSR` reads the CSR's register and `write_CSR`
  writes it ONCE (`dfReadCsr`, `dfWriteCsr`; each by the model's own arm, reached by computation at
  the literal CSR number).  `stimecmp`'s write also runs `clint_dispatch`, which writes `mip` -- a
  different pseudo-register, neutral at every role but a `mip` one (`dfNwRole`).
* `dfDoCsr`: `doCSR` at such a CSR, along every path: a failure, or a retirement whose state went
  through the CSR read (if any), then ONE write of the CSR's register (if any), then the `rd` write
  (`dfCsrPost`).
* `dfExecCsrReg` / `dfExecCsrImm` with the per-word role check `dfCsrRoleOk` give the
  instruction-level post `dfDone` (`dfInstrCsr`).

Not covered: `satp` and the M-mode CSRs (boot code), `sip`/`mip`/`time` WRITES (no xv6 kernel text
writes them in S-mode).

Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflowExec2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataflow
open SailCycleOrderK

/-! ## 1. `nwB` pieces -/

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[nw_reg] theorem nwCheckCSRResult (csr : BitVec 12) (p : Privilege) (acc : CSRAccessType) :
    nwT (check_CSR_result csr p acc) := by
  nw_walk

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwCsrIdReadCallback (csr : BitVec 12) (v : BitVec 64) :
    nwT (csr_id_read_callback csr v) := by
  nw_walk

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwCsrIdWriteCallback (csr : BitVec 12) (v : BitVec 64) :
    nwT (csr_id_write_callback csr v) := by
  nw_walk

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwAlignPc (a : BitVec 64) : nwT (align_pc a) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwLegalizeSstatus (m v : BitVec 64) : nwT (legalize_sstatus m v) := by
  nw_walk

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwLegalizeTvec (o v : BitVec 64) (a : Bool) (b : Nat) (c : Bool) (d : Nat) :
    nwT (legalize_tvec o v a b c d) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwClintDispatch (b : Bool) : nwT (clint_dispatch b) := by
  nw_walk

/-! ## 2. The CSRs: read and write -/

/-- The register the model reads and writes for a CSR (the table of the header). -/
def csrDfReg (c : BitVec 12) : Option Register :=
  match c.toNat with
  | 0x100 => some .mstatus
  | 0x104 => some .mie
  | 0x105 => some .stvec
  | 0x140 => some .sscratch
  | 0x141 => some .sepc
  | 0x142 => some .scause
  | 0x143 => some .stval
  | 0x14D => some .stimecmp
  | 0xC01 => some .mtime
  | _ => none

/-- The read post: the CSR's register was read. -/
def dfRdPost (st : DfSt) (reg : Register) (_v : BitVec 64) (st' : DfSt) : Prop :=
  dfExt (dfRd st reg) st'

/-- The write post: ONE write of the CSR's register (after reads, before reads). -/
def dfWrPost {X : Type} (st : DfSt) (reg : Register) (_r : X) (st' : DfSt) : Prop :=
  ∃ st1, dfExt st st1 ∧ dfExt (dfWr st1 reg) st'

theorem dfWrPostOf {X : Type} (st st1 st' : DfSt) (reg : Register) (r : X) (h1 : dfExt st st1)
    (h : dfExt (dfWr st1 reg) st') : dfWrPost st reg r st' := ⟨st1, h1, h⟩

set_option maxHeartbeats 4000000 in
theorem dfReadCsr (c : BitVec 12) (reg : Register) (h : csrDfReg c = some reg) (st : DfSt)
    (hro : dfNwRole st.ro) : dfB (dfRdPost st reg) (read_CSR c) st := by
  have hc : ∀ k : Nat, c.toNat = k → k < 4096 → c = BitVec.ofNat 12 k := by
    intro k hk _; apply BitVec.eq_of_toNat_eq; rw [hk, BitVec.toNat_ofNat]; omega
  unfold csrDfReg at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ _ _ => dfExtRd _ _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]
    exact fun v _ => dfBMono _ _ (fun _ _ h => h.2) _ _
      (dfOfNw false _ _ _ hro (nwAlignPc v))
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _
  · rw [hc _ ‹_› (by omega)]; exact fun _ _ => dfExtRefl _

theorem dfSetStvec (v : BitVec 64) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfWrPost st .stvec) (set_stvec v) st := by
  unfold set_stvec
  intro o _
  refine dfBPureBind _ _ _ _ ?_
  refine dfNwBind false _ _ _ _ _ hro (nwLegalizeTvec _ _ _ _ _ _) (fun x st1 _ h1 => ?_)
  exact ⟨trivial, fun _ _ _ => dfWrPostOf _ st1 _ _ _ (dfExtTrans _ _ _ (dfExtRd _ _) h1)
    (dfExtRd _ _)⟩

set_option maxHeartbeats 4000000 in
theorem dfWriteCsr (c : BitVec 12) (reg : Register) (h : csrDfReg c = some reg) (hm : c.toNat ≠ 0xC01)
    (v : BitVec 64) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfWrPost st reg) (write_CSR c v) st := by
  have hc : ∀ k : Nat, c.toNat = k → k < 4096 → c = BitVec.ofNat 12 k := by
    intro k hk _; apply BitVec.eq_of_toNat_eq; rw [hk, BitVec.toNat_ofNat]; omega
  unfold csrDfReg at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · -- sstatus: read `mstatus`, legalize, write it, read it
    rw [hc _ ‹_› (by omega)]
    intro m _
    refine dfBPureBind _ _ _ _ ?_
    refine dfNwBind false _ _ _ _ _ hro (nwLegalizeSstatus _ _) (fun x st1 _ h1 => ?_)
    exact ⟨trivial, fun _ _ _ => dfWrPostOf _ st1 _ _ _ (dfExtTrans _ _ _ (dfExtRd _ _) h1)
      (dfExtRd _ _)⟩
  · -- sie: read `mie`, `mideleg`, write `mie`, read both
    rw [hc _ ‹_› (by omega)]
    exact fun _ _ _ _ => ⟨trivial, fun _ _ _ _ _ => dfWrPostOf _ _ _ _ _
      (dfExtTrans _ _ _ (dfExtRd _ _) (dfExtRd _ _))
      (dfExtTrans _ _ _ (dfExtRd _ _) (dfExtRd _ _))⟩
  · -- stvec: `set_stvec`
    rw [hc _ ‹_› (by omega)]
    show dfB _ (set_stvec v >>= fun x => pure (Ok x)) st
    exact dfBBind _ _ _ _ st (dfSetStvec v st hro) (fun _ _ h => h)
  · rw [hc _ ‹_› (by omega)]
    exact ⟨trivial, fun _ _ _ => dfWrPostOf _ _ _ _ _ (dfExtRefl _) (dfExtRd _ _)⟩
  · rw [hc _ ‹_› (by omega)]
    exact ⟨trivial, fun _ => dfWrPostOf _ _ _ _ _ (dfExtRefl _) (dfExtRefl _)⟩
  · rw [hc _ ‹_› (by omega)]
    exact ⟨trivial, fun _ _ _ => dfWrPostOf _ _ _ _ _ (dfExtRefl _) (dfExtRd _ _)⟩
  · rw [hc _ ‹_› (by omega)]
    exact ⟨trivial, fun _ _ _ => dfWrPostOf _ _ _ _ _ (dfExtRefl _) (dfExtRd _ _)⟩
  · -- stimecmp: read, write, `clint_dispatch` (writes `mip`), read
    rw [hc _ ‹_› (by omega)]
    intro _ _
    refine ⟨trivial, fun _ => ?_⟩
    have hro' : dfNwRole (dfWr (dfRd st Register.stimecmp) Register.stimecmp).ro := hro
    refine dfBPureBind _ _ _ _ ?_
    refine dfNwBind false _ _ _ _ _ hro' (nwClintDispatch false) (fun _ st1 _ h1 => ?_)
    exact fun _ _ => dfWrPostOf _ _ _ _ _ (dfExtRd _ _) (dfExtTrans _ _ _ h1 (dfExtRd _ _))
  · exact absurd ‹_› hm

/-! ## 3. `doCSR` -/

theorem accBneW (a : CSRAccessType) (h : (a != .CSRWrite) = false) : a = .CSRWrite := by
  cases a <;> first | rfl | cases h

theorem accBeqRT (a : CSRAccessType) (h : (a == .CSRRead) = true) : a = .CSRRead := by
  cases a <;> first | rfl | cases h

theorem accBeqRF (a : CSRAccessType) (h : (a == .CSRRead) = false) : a ≠ .CSRRead := by
  cases a <;> first | exact absurd h (by decide) | (intro e; cases e)

theorem dfGprWrRo (st : DfSt) (i : BitVec 5) : (dfGprWr st i).ro = st.ro := by
  unfold dfGprWr; split <;> rfl

theorem dfWrRo (st : DfSt) (r : Register) : (dfWr st r).ro = st.ro := rfl

theorem dfRdMem (st : DfSt) (r : Register) (k : Nat) (hk : eregNum r = some k) :
    k ∈ (dfRd st r).rds := by
  simp only [dfRd, dfRdsAdd, hk]
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- **The `doCSR` post** (header). -/
def dfCsrPost (st : DfSt) (reg : Register) (rd : BitVec 5) (acc : CSRAccessType)
    (r : ExecutionResult) (st' : DfSt) : Prop :=
  failRes r = true ∨
  (r = RETIRE_SUCCESS ∧ ∃ st1 st2, dfExt st st1 ∧
    (acc ≠ .CSRWrite → ∀ k, eregNum reg = some k → k ∈ st1.rds) ∧
    (acc = .CSRRead → st2 = st1) ∧
    (acc ≠ .CSRRead → ∃ st1', dfExt st1 st1' ∧ dfExt (dfWr st1' reg) st2) ∧
    dfExt (dfGprWr st2 rd) st')

theorem dfDoCsr (c : BitVec 12) (reg : Register) (hreg : csrDfReg c = some reg)
    (v : BitVec 64) (rd : BitVec 5) (op : csrop)
    (acc : CSRAccessType) (hacc : c.toNat = 0xC01 → acc = .CSRRead) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfCsrPost st reg rd acc) (doCSR c v (regidx.Regidx rd) op acc) st := by
  have h344 : c ≠ 836#12 := by
    rintro rfl; simp [csrDfReg] at hreg
  have h144 : c ≠ 324#12 := by
    rintro rfl; simp [csrDfReg] at hreg
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
        (acc ≠ .CSRWrite → ∀ k, eregNum reg = some k → k ∈ st'.rds)) _ _ _ st2 ?_ ?_
    · split
      · refine dfBMono _ _ (fun _ st' h => ⟨dfExtTrans _ _ _ (dfExtRd _ _) h, fun _ k hk =>
          dfExtMem _ _ _ h (dfRdMem st2 reg k hk)⟩) _ _
          (dfReadCsr c reg hreg st2 (dfNwRoleExt _ _ h02 hro))
      · rename_i hne
        exact ⟨dfExtRefl _, fun hw' => absurd (accBneW acc (by simpa using hne)) hw'⟩
    · rintro rv st3 ⟨h3, hm3⟩
      have h03 := dfExtTrans _ _ _ h02 h3
      split
      · first | exact absurd rfl h344 | exact absurd ‹_› h344
      · first | exact absurd rfl h144 | exact absurd ‹_› h144
      · refine dfBPureBind _ _ _ _ ?_
        split
        · rename_i hr
          have hr' : acc = .CSRRead := accBeqRT acc (by simpa using hr)
          refine dfNwBind false _ _ _ _ st3 (dfNwRoleExt _ _ h03 hro) (nwCsrIdReadCallback _ _)
            (fun _ st4 _ h4 => ?_)
          have h04 := dfExtTrans _ _ _ h03 h4
          refine dfWXBind _ _ _ _ _ (dfNwRoleExt _ _ h04 hro) (fun _ st5 h5 => ?_)
          refine Or.inr ⟨rfl, st4, st4, h04, fun ha k hk => dfExtMem _ _ _ h4 (hm3 ha k hk),
            fun _ => rfl, fun ha => absurd hr' ha, h5⟩
        · rename_i hr
          have hr' : acc ≠ .CSRRead := accBeqRF acc (by simpa using hr)
          dsimp only
          refine dfBBind _ _ _ _ st3 (dfWriteCsr c reg hreg (fun e => hr' (hacc e)) _ st3
            (dfNwRoleExt _ _ h03 hro)) (fun res st4 h4 => ?_)
          obtain ⟨st1', h1', h4'⟩ := h4
          cases res with
          | Ok fv =>
            have hro4 : dfNwRole st4.ro := by
              rw [h4'.1, dfWrRo]; exact dfNwRoleExt _ _ h1' (dfNwRoleExt _ _ h03 hro)
            refine dfWXBind _ _ _ _ _ hro4 (fun _ st5 h5 => ?_)
            have hro5 : dfNwRole st5.ro := by rw [h5.1, dfGprWrRo]; exact hro4
            refine dfNwBind false _ _ _ _ st5 hro5 (nwCsrIdWriteCallback _ _) (fun _ st6 _ h6 => ?_)
            exact Or.inr ⟨rfl, st3, st4, h03, hm3, fun ha => absurd ha hr',
              fun _ => ⟨st1', h1', h4'⟩, dfExtTrans _ _ _ h5 h6⟩
          | Err u => exact Or.inl rfl

/-! ## 4. The clauses -/

theorem dfExecCsrReg (c : BitVec 12) (rs1 rd : BitVec 5) (op : csrop) (reg : Register)
    (hreg : csrDfReg c = some reg)
    (hacc : c.toNat = 0xC01 → csr_access_type op (regidx.Regidx rd == zreg)
      (regidx.Regidx rs1 == zreg) = .CSRRead)
    (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfCsrPost (dfGprRd st rs1) reg rd
        (csr_access_type op (regidx.Regidx rd == zreg) (regidx.Regidx rs1 == zreg)))
      (execute_CSRReg c (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_CSRReg
  exact dfRXBind _ _ _ _ (fun v => dfDoCsr c reg hreg v rd op _ hacc _ hro)

theorem dfExecCsrImm (c : BitVec 12) (imm : BitVec 5) (rd : BitVec 5) (op : csrop) (reg : Register)
    (hreg : csrDfReg c = some reg)
    (hacc : c.toNat = 0xC01 → csr_access_type op (regidx.Regidx rd == zreg)
      (imm == zeros (n := 5)) = .CSRRead)
    (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfCsrPost st reg rd (csr_access_type op (regidx.Regidx rd == zreg) (imm == zeros (n := 5))))
      (execute_CSRImm c imm (regidx.Regidx rd) op) st := by
  unfold execute_CSRImm
  exact dfDoCsr c reg hreg _ rd op _ hacc st hro

/-! ## 5. The role check and the slots -/

/-- The decoded sources lie in a register-number list (`DLdRes` never). -/
def dfCov (dec : List Dsrc) (rs : List Nat) : Bool :=
  dec.all (fun x =>
    match x with
    | .DReg r => rs.contains r
    | .DLdRes => false)

theorem dfCovMem (dec : List Dsrc) (rs : List Nat) (h : dfCov dec rs = true) (r : Nat)
    (hr : Dsrc.DReg r ∈ dec) : r ∈ rs := by
  have := List.all_eq_true.1 h _ hr
  simpa using this

/-- **THE PER-WORD CHECK, Zicsr** (header): the role's destinations are what `doCSR` writes, in
order -- the CSR's pseudo-register `p` (≥ 32, not `mip`/`mtime`) unless the access is a pure read,
then `rd` -- each with its decoded sources among what was read before (`p` unless a pure write,
and `rs1`). -/
def dfCsrRoleOk (ro : OpRoles) (p : Nat) (rd : BitVec 5) (reads : List Nat)
    (acc : CSRAccessType) : Bool :=
  (p != wcsr MIP && p != wcsr TIME && decide (32 ≤ p)) &&
  match acc with
  | .CSRRead =>
      match depsRd ro, depsRd2 ro with
      | some (k, dec), none => gprNum rd == some k && dfCov dec (p :: reads)
      | _, _ => false
  | .CSRWrite =>
      match depsRd ro, depsRd2 ro with
      | some (k, dec), none => k == p && dfCov dec reads && gprNum rd == none
      | _, _ => false
  | .CSRReadWrite =>
      match depsRd ro with
      | some (k, dec) =>
          k == p && dfCov dec (p :: reads) &&
            (match gprNum rd, depsRd2 ro with
             | none, none => true
             | some k2, some (k2', dec2) => k2 == k2' && dfCov dec2 (p :: reads)
             | _, _ => false)
      | none => false

/-- The CSR write fills slot 0. -/
theorem dfWrFill (st : DfSt) (reg : Register) (p : Nat) (dec : List Dsrc)
    (hreg : eregNum reg = some p) (hnx : reg ≠ .nextPC) (hrd : depsRd st.ro = some (p, dec))
    (hn : st.n = 0) (hcov : ∀ r, Dsrc.DReg r ∈ dec → r ∈ st.rds) :
    (dfWr st reg).n = 1 ∧ (dfWr st reg).ok = st.ok := by
  have hs : slotOk st.ro 0 p (erwSrcs dec st.rds) = true := by
    simp only [slotOk, dfDests, hrd, Option.toList, List.singleton_append,
      List.getElem?_cons_zero, Nat.beq_refl, Bool.true_and]
    exact dsubbCovers dec st.rds hcov
  have he : erwOf st.ro st.rds reg = .ERWreg p (erwSrcs dec st.rds) := by
    simp only [erwOf, hnx, ↓reduceIte, hrd, erwDest, hreg]
  simp only [dfWr, he, erwLabel, dfLab, hn, hs, ↓reduceIte]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

/-- The `rd` write after the CSR write fills slot 1. -/
theorem dfGprWrFill2 (st : DfSt) (rd : BitVec 5) (k p : Nat) (dec1 dec2 : List Dsrc)
    (hk : gprNum rd = some k) (hkp : k ≠ p) (h1 : depsRd st.ro = some (p, dec1))
    (h2 : depsRd2 st.ro = some (k, dec2)) (hn : st.n = 1)
    (hcov : ∀ r, Dsrc.DReg r ∈ dec2 → r ∈ st.rds) :
    (dfGprWr st rd).n = 2 ∧ (dfGprWr st rd).ok = st.ok := by
  have hs : slotOk st.ro 1 k (erwSrcs dec2 st.rds) = true := by
    simp only [slotOk, dfDests, h1, h2, Option.toList, List.singleton_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.beq_refl, Bool.true_and]
    exact dsubbCovers dec2 st.rds hcov
  have he : erwOfNum st.ro st.rds (some k) = .ERWreg k (erwSrcs dec2 st.rds) := by
    simp only [erwOfNum, h1, h2, hkp, ↓reduceIte]
  simp only [dfGprWr, hk, he, erwLabel, dfLab, hn, hs, ↓reduceIte]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

theorem dfGprWrNone (st : DfSt) (rd : BitVec 5) (h : gprNum rd = none) : dfGprWr st rd = st := by
  simp only [dfGprWr, h]

theorem dfCovCons (dec : List Dsrc) (p : Nat) (reads : List Nat) (st : DfSt)
    (h : dfCov dec (p :: reads) = true) (hp : p ∈ st.rds) (hr : ∀ r, r ∈ reads → r ∈ st.rds) :
    ∀ r, Dsrc.DReg r ∈ dec → r ∈ st.rds := by
  intro r hd
  rcases List.mem_cons.1 (dfCovMem dec _ h r hd) with rfl | h'
  · exact hp
  · exact hr r h'

theorem gprNotCsr (rd : BitVec 5) (k p : Nat) (hk : gprNum rd = some k) (hp : 32 ≤ p) : k ≠ p := by
  have := gprNumLt rd k hk; omega

/-- **The `doCSR` post gives the instruction-level post** under the role check (header). -/
theorem dfCsrDone (st0 st : DfSt) (reg : Register) (p : Nat) (rd : BitVec 5) (reads : List Nat)
    (acc : CSRAccessType) (hp : eregNum reg = some p) (hnx : reg ≠ .nextPC) (hext : dfExt st st0)
    (hreads : ∀ r, r ∈ reads → r ∈ st0.rds) (hn : st.n = 0) (hok : st.ok = true)
    (hchk : dfCsrRoleOk st.ro p rd reads acc = true) (r : ExecutionResult) (st' : DfSt)
    (h : dfCsrPost st0 reg rd acc r st') : dfDone r st' := by
  rcases h with h | ⟨-, st1, st2, h01, hrd1, hR, hW, h2'⟩
  · exact Or.inl h
  unfold dfCsrRoleOk at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨hpb, hchk⟩ := hchk
  have hp32 : 32 ≤ p := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpb; exact hpb.2
  have hst1 := dfExtTrans _ _ _ hext h01
  have hr1 : ∀ r, r ∈ reads → r ∈ st1.rds := fun r h => dfExtMem _ _ _ h01 (hreads r h)
  refine Or.inr ?_
  cases acc with
  | CSRRead =>
    dsimp only at hchk
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
  | CSRWrite =>
    dsimp only at hchk
    split at hchk
    · rename_i k dec hd1 hd2
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨rfl, hcv⟩, hrd0⟩ := hchk
      obtain ⟨st1', h11', hw2⟩ := hW (by intro e; cases e)
      have hst1' := dfExtTrans _ _ _ hst1 h11'
      obtain ⟨f1, f2⟩ := dfWrFill st1' reg k dec hp hnx (hst1'.1 ▸ hd1) (hst1'.2.1.trans hn)
        (fun r hd => dfExtMem _ _ _ h11' (hr1 r (dfCovMem dec reads hcv r hd)))
      rw [dfGprWrNone st2 rd hrd0] at h2'
      refine ⟨by rw [h2'.2.2.1, hw2.2.2.1, f2, hst1'.2.2.1, hok], ?_⟩
      rw [h2'.2.1, hw2.2.1, f1, h2'.1, hw2.1, dfWrRo, hst1'.1]
      simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.length_singleton]
    · exact absurd hchk Bool.false_ne_true
  | CSRReadWrite =>
    dsimp only at hchk
    split at hchk
    · rename_i k dec hd1
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨rfl, hcv⟩, hrest⟩ := hchk
      obtain ⟨st1', h11', hw2⟩ := hW (by intro e; cases e)
      have hst1' := dfExtTrans _ _ _ hst1 h11'
      have hp1 : k ∈ st1'.rds := dfExtMem _ _ _ h11' (hrd1 (by intro e; cases e) k hp)
      have hr1' : ∀ r, r ∈ reads → r ∈ st1'.rds := fun r h => dfExtMem _ _ _ h11' (hr1 r h)
      obtain ⟨f1, f2⟩ := dfWrFill st1' reg k dec hp hnx (hst1'.1 ▸ hd1) (hst1'.2.1.trans hn)
        (dfCovCons dec k reads st1' hcv hp1 hr1')
      have hst2ro : st2.ro = st.ro := by rw [hw2.1, dfWrRo, hst1'.1]
      have hst2n : st2.n = 1 := by rw [hw2.2.1, f1]
      have hst2ok : st2.ok = true := by rw [hw2.2.2.1, f2, hst1'.2.2.1, hok]
      split at hrest
      · rename_i hg hd2
        rw [dfGprWrNone st2 rd hg] at h2'
        refine ⟨by rw [h2'.2.2.1, hst2ok], ?_⟩
        rw [h2'.2.1, hst2n, h2'.1, hst2ro]
        simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.length_singleton]
      · rename_i k2 k2' dec2 hg hd2
        simp only [Bool.and_eq_true, beq_iff_eq] at hrest
        obtain ⟨rfl, hcv2⟩ := hrest
        obtain ⟨g1, g2⟩ := dfGprWrFill2 st2 rd k2 k dec dec2 hg (gprNotCsr rd k2 k hg hp32)
          (hst2ro ▸ hd1) (hst2ro ▸ hd2) hst2n
          (dfCovCons dec2 k reads st2 hcv2 (dfExtMem _ _ _ hw2 (by
              simp only [dfWr]; exact hp1))
            (fun r h => dfExtMem _ _ _ hw2 (hr1' r h)))
        refine ⟨by rw [h2'.2.2.1, g2, hst2ok], ?_⟩
        rw [h2'.2.1, g1, h2'.1, dfGprWrRo, hst2ro]
        simp only [dfDests, hd1, hd2, Option.toList, List.singleton_append, List.length_cons,
          List.length_nil]
      · exact absurd hrest Bool.false_ne_true
    · exact absurd hchk Bool.false_ne_true

/-! ## 6. The headline, Zicsr -/

theorem csrDfRegNext (c : BitVec 12) (reg : Register) (h : csrDfReg c = some reg) :
    reg ≠ .nextPC := by
  unfold csrDfReg at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

theorem dfNwRoleOfCheck (ro : OpRoles) (p : Nat) (rd : BitVec 5) (reads : List Nat)
    (acc : CSRAccessType) (h : dfCsrRoleOk ro p rd reads acc = true) : dfNwRole ro := by
  unfold dfCsrRoleOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpb, h⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hpb
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hpb
  have gpr : ∀ k, gprNum rd = some k → k ≠ wcsr MIP ∧ k ≠ wcsr TIME := by
    intro k hk
    have := gprNumLt rd k hk
    exact ⟨by simp only [wcsr, MIP]; omega, by simp only [wcsr, TIME]; omega⟩
  intro q hq
  cases acc with
  | CSRRead =>
    dsimp only at h
    split at h
    · rename_i k dec hd1 hd2
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.mem_singleton] at hq
      subst hq
      exact gpr k h.1
    · exact absurd h Bool.false_ne_true
  | CSRWrite =>
    dsimp only at h
    split at h
    · rename_i k dec hd1 hd2
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.mem_singleton] at hq
      subst hq
      exact ⟨hp1, hp2⟩
    · exact absurd h Bool.false_ne_true
  | CSRReadWrite =>
    dsimp only at h
    split at h
    · rename_i k dec hd1
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, -⟩, hrest⟩ := h
      split at hrest
      · rename_i hg hd2
        simp only [dfDests, hd1, hd2, Option.toList, List.append_nil, List.mem_singleton] at hq
        subst hq
        exact ⟨hp1, hp2⟩
      · rename_i k2 k2' dec2 hg hd2
        simp only [Bool.and_eq_true, beq_iff_eq] at hrest
        obtain ⟨rfl, -⟩ := hrest
        simp only [dfDests, hd1, hd2, Option.toList, List.singleton_append, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨hp1, hp2⟩
        · exact gpr k2 hg
      · exact absurd hrest Bool.false_ne_true
    · exact absurd h Bool.false_ne_true

/-- A post that only admits failures and retirements survives the redirect stage. -/
theorem dfExecAsOf (i : instruction) (Q : ExecutionResult → DfSt → Prop) (st : DfSt)
    (hQ : ∀ r st', Q r st' → failRes r = true ∨ r = RETIRE_SUCCESS)
    (h : dfB Q (execute i) st) : dfB Q (uxaExecAs i) st := by
  unfold uxaExecAs
  refine dfBBind _ _ _ _ st h (fun r st1 hr => ?_)
  rcases hQ r st1 hr with hf | rfl
  · cases r <;> first | exact hr | (simp only [failRes] at hf; exact absurd hf (by decide))
  · exact hr

theorem dfCsrPostRes (st : DfSt) (reg : Register) (rd : BitVec 5) (acc : CSRAccessType)
    (r : ExecutionResult) (st' : DfSt) (h : dfCsrPost st reg rd acc r st') :
    failRes r = true ∨ r = RETIRE_SUCCESS := by
  rcases h with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **THE PER-WORD CHECK, Zicsr instruction** (header). -/
def dfCsrOk (ro : OpRoles) (i : instruction) : Bool :=
  match i with
  | .CSRReg (c, rs1, rd, op) =>
      match csrDfReg c with
      | some reg =>
          match eregNum reg with
          | some p =>
              (c.toNat != 0xC01 || csr_access_type op (rd == zreg) (rs1 == zreg) == .CSRRead) &&
                dfCsrRoleOk ro p (uxaIdx rd) (gprNum (uxaIdx rs1)).toList
                  (csr_access_type op (rd == zreg) (rs1 == zreg))
          | none => false
      | none => false
  | .CSRImm (c, imm, rd, op) =>
      match csrDfReg c with
      | some reg =>
          match eregNum reg with
          | some p =>
              (c.toNat != 0xC01 ||
                  csr_access_type op (rd == zreg) (imm == zeros (n := 5)) == .CSRRead) &&
                dfCsrRoleOk ro p (uxaIdx rd) [] (csr_access_type op (rd == zreg) (imm == zeros (n := 5)))
          | none => false
      | none => false
  | _ => false

theorem accRead (c : BitVec 12) (a : CSRAccessType)
    (h : (c.toNat != 0xC01 || a == .CSRRead) = true) : c.toNat = 0xC01 → a = .CSRRead := by
  intro hc
  rw [hc] at h
  simp only [bne_self_eq_false, Bool.false_or] at h
  exact accBeqRT a h

/-- **B1, the execute stage of ONE Zicsr instruction** (header). -/
theorem dfInstrCsr (c : instruction) (st : DfSt) (hn : st.n = 0) (hok : st.ok = true)
    (h : dfCsrOk st.ro c = true) : dfB dfDone (uxaExecAs c) st := by
  cases c
  all_goals first | (simp only [dfCsrOk, reduceCtorEq] at h) | skip
  case CSRReg a =>
    obtain ⟨csr, ⟨rs1⟩, ⟨rd⟩, op⟩ := a
    simp only [uxaIdx] at h
    split at h
    · rename_i reg hreg
      split at h
      · rename_i p hp
        rw [Bool.and_eq_true] at h
        obtain ⟨hacc, hchk⟩ := h
        have hro := dfNwRoleOfCheck _ _ _ _ _ hchk
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
        exact dfBMono _ _
          (fun r st' h' => dfCsrDone (dfGprRd st rs1) st reg p rd (gprNum rs1).toList _ hp
            (csrDfRegNext csr reg hreg) (dfExtGprRd st rs1) hrd hn hok hchk r st' h') _ _
          (dfExecAsOf _ _ st (dfCsrPostRes _ _ _ _)
            (dfExecCsrReg csr rs1 rd op reg hreg (accRead csr _ hacc) st hro))
      · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true
  case CSRImm a =>
    obtain ⟨csr, imm, ⟨rd⟩, op⟩ := a
    simp only [uxaIdx] at h
    split at h
    · rename_i reg hreg
      split at h
      · rename_i p hp
        rw [Bool.and_eq_true] at h
        obtain ⟨hacc, hchk⟩ := h
        have hro := dfNwRoleOfCheck _ _ _ _ _ hchk
        exact dfBMono _ _
          (fun r st' h' => dfCsrDone st st reg p rd [] _ hp (csrDfRegNext csr reg hreg)
            (dfExtRefl st) (fun r h => absurd h List.not_mem_nil) hn hok hchk r st' h') _ _
          (dfExecAsOf _ _ st (dfCsrPostRes _ _ _ _)
            (dfExecCsrImm csr imm rd op reg hreg (accRead csr _ hacc) st hro))
      · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true

/-! ## 7. The headline, every class -/

/-- **THE PER-WORD CHECK** (header): Exec2's check or the Zicsr one. -/
def dfInstrOkAll (ro : OpRoles) (c : instruction) : Bool := dfInstrOk ro c || dfCsrOk ro c

/-- **B1: the execute stage of ONE instruction** (header). -/
theorem dfInstrAll (c : instruction) (st : DfSt) (hn : st.n = 0) (hok : st.ok = true)
    (h : dfInstrOkAll st.ro c = true) : dfB dfDone (uxaExecAs c) st := by
  unfold dfInstrOkAll at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact dfInstr c st hn hok h
  · exact dfInstrCsr c st hn hok h

/-! Non-vacuity: the check holds at real decoder outputs of the kernel image (the words and
`MachCSL` decode facts of `Weak/KernelSites.lean`): the racy load `main+0x16` (`c.lw a5,0(a4)`, a
compressed load through its `ExecuteAs` target), the release store `release+0x1a`
(`sw zero,0(s1)`, a destination-free role) and kerneltrap's `csrr a5,scause` (`0x142027f3`). -/

theorem dfInstrOkCLw :
    dfInstrOkAll (depsOfBits (BitVec.ofNat 32 0x431c))
      (instruction.C_LW (0#5, cregidx.Cregidx 6#3, cregidx.Cregidx 7#3)) = true := by
  decide +kernel

theorem dfInstrOkSw :
    dfInstrOkAll (depsOfBits (BitVec.ofNat 32 0x0004a023))
      (instruction.STORE (0#12, regidx.Regidx 0#5, regidx.Regidx 9#5, 4)) = true := by
  decide +kernel

theorem dfInstrOkCsrrScause :
    dfInstrOkAll (depsOfBits (BitVec.ofNat 32 0x142027f3))
      (instruction.CSRReg (0x142#12, regidx.Regidx 0#5, regidx.Regidx 15#5, csrop.CSRRS)) = true := by
  decide +kernel

end PinDataflow
end Weak
