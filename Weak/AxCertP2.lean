/-
Weak: **THE WINDOW-BOUNDED `Cert` bridge** — the no-RMW / no-split premises of the data read
restricted to the instruction's window.

Rocq: `iris/AxCertP2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `wpdOfCertK` (AxSpinE4) passes the whole-row `HnoRmw` / `HnoSplit` to every data-read
node, because a single `Cert` cannot bound where its data read happens: `cEnd` (a plain read at
budget `BFin 0`, no continuation) lets a path run past the instruction's window, so a `cDrd` node
whose subtree ends only in `cEnd` may sit at any row position.  `wpdDrdNodeP` / `wpdXrdNodeP`
(AxCertP) need the premise only at the node's own position: what is missing is a POSITION BOUND.

HOW (no new `Cert` variant, no re-derivation of the spine).  The `Cert` facts the leaves use hold
for EVERY final budget.  A FAMILY `FamP P m t a c` = "for every shift `j`, some `Cert` of `m` at
budget `a + j` whose `Ret`s end at budget `c + j` (and not in an RMW-half state)".  Row
consumption is labelling-independent, so
- `FamBound` (budget monotonicity): a family has `c ≤ a` — a path that would hit `cEnd` at shift
  `j` keeps going at shift `j + 1`; induction on the PROGRAM (not on one derivation) closes it;
- `FamRBound`: from an RMW-half state (`CRmwR`) `c + 1 ≤ a`.
The bridge `AxCertP2.wpdOfCertP` walks the REAL derivation (as `wpdOfCertK`) and carries the
family as an invariant `PF` while no data event has happened (`csD = CPend`); at the data read
`cDrd` (budget `a' + 1`) `FamDrd` gives `c ≤ a'`, at the exclusive read `cXrd` (budget `a`)
`FamXrd` gives `c < a`; with `bpos` the node's position `kk` satisfies `kk + c < length`.  So the
bridge's premises `HnoRmwW` / `HnoSplitW` are stated only for positions `k0 ≤ k` with
`k + c < (grow GD i).length`.  The family inversions use a SMALL INVERSION `AxCertP2.cinv` into
`CInv` (computed from the program).

§1 `CInvO` / `CInv` / `AxCertP2.cinv`; §2 families, `FamBound`, `FamRBound`, `FamDrd`, `FamXrd`,
the `PF` invariant and its step lemmas; §3 the bridge `AxCertP2.wpdOfCertP` and the instruction
wrapper `AxCertP2.wpdInstrOfCertP`.

## Deviations from Rocq

1. O2 STAGE C (as `AxCert` deviation 1): Lean's `Cert` has the extra constructor `cIf` (an image
   FETCH, `akIfetch = true`, keeps the budget and the state).  `CInvO`'s `memRead` arm gains the
   corresponding disjunct (second), and the plain-read disjuncts (`cMrd` / `cEnd` / `cDrd`)
   record `akIfetch = false`.  `rdCons`, `FamDrd` and `PFMrd` take `Hnf : akIfetch = false`
   after the `akLatest` premise.  `FamBound` / `FamRBound` split a non-latest read on `akIfetch`
   (a fetch keeps the budget).  Lean-only, file-qualified: `AxCertP2.rdIf` (the fetch inversion)
   and `AxCertP2.PFIf` (the `PF` step at a fetch, used by the bridge's `cIf` arm).  Rocq's section
   premise `Hntext` is DROPPED (AxCert2 deviation 1).
2. LEAN-SAIL OUTCOMES (AxCert deviation 4/5): the program is a `SailM X` (`FreeM`), `CInvO` is a
   match on `Eff RegisterType exception` (`.error e ↦ QE`, Rocq's `ExtraOutcome`); outcomes with
   no `Cert` constructor (`readRam`, `writeRam`, `choose`) give `False`.  Write answers are
   `.Ok (some true)`, read answers `.Ok (wordOfBytes n vs, none)`.  The register pins are
   `AxRunClose.pinReg` (Rocq `seip_reg`).  `v0` pads with `0` (Rocq `inhabitant`).
3. TYPES as AxCert2 deviation 4: `[InvGS_gen hlc GF]` (any `hlc`), `Mc` = `rvwmoCatConsistent`,
   `Interface.Ret tt` ↦ `.pure ()`, `MState rs ∅ dev0_state` ↦ `⟨rs, fun _ => none, testDevs⟩`,
   `S n` ↦ `n + 1`.  Section variables are explicit arguments: the §1–§2 lemmas take
   `img dok kind` first (as Rocq's section); the bridge takes
   `img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc Out k0 c HnoRmwW HnoSplitW`.
   `AxCertP2.cinv` takes `QE Q s m t` implicitly.
4. The Ltac `silent_psP` is replaced by inline inversions (as `wpdOfCertK`).
5. Q19 (provisional, as `AxCert.Cert.cSf`): the SFENCE.VMA announce is one row item.  `CInvO`'s
   `instrAnnounce` arm is a disjunction — non-sfence (`sfAnnB n w = false`, state kept) or sfence
   (`sfAnnB n w = true`, budget `bsucc b'` consumed, data/release kept).  `FamBound` / `FamRBound`
   split an announce on `sfAnnB` (the sfence arm consumes like a fence).  The bridge gains a `cSf`
   arm via `AxCert2.wpdSfNodeM` (no pin refutation: `CResK` carries no pin).  Lean-only,
   file-qualified: `AxCertP2.annCons` (the announce inversion) and `AxCertP2.PFSf` (the `PF` step).
6. (Lean-only, Theorem 2 / P4; AxCert deviation 11) `Cert.cWrEnd` (a plain write at `BFin 0`, the
   row end): `CInvO`'s `memWrite` arm is a disjunction — the consuming write (`cDwr`/`cXwr`, as
   before) or the stuck write (`csB = BFin 0`, `akLatest = false`).  `wrCons` therefore takes
   `0 < b` (STATEMENT CHANGE; its only users are `FamBound` / `FamRBound` here), and `FamBound` /
   `FamRBound` split a write on the budget (at `a = 0` the shift `FamStepP0`, as a read).  The
   bridge's `cWrEnd` arm is `AxCert2.wpdStuckWriteM`.

**Rocq → Lean name map.**  `CInvO` `CInvO`, `CInv` `CInv`, `cinv` `AxCertP2.cinv` (`Weak.cinv`
exists in WeakRvwmoCert3), `Qc` `Qc`, `FamP` `FamP`, `isR` `AxCertP2.isR` (`Weak.isR` exists in WeakAxiomatic), `v0` `v0`, `img_bytes_len`
`imgBytesLen`, `v0_len` `v0Len`, `v0_img` `v0Img`, `rd_cons` `rdCons`, `rd_x` `rdX`, `wr_cons`
`wrCons`, `fence_cons` `fenceCons`, `Fam_stepP` `FamStepP`, `Fam_stepP0` `FamStepP0`,
`Fam_bound` `FamBound`, `FamR_bound` `FamRBound`, `Fam_drd` `FamDrd`, `Fam_xrd` `FamXrd`, `PF`
`PF`, `PF_step` `PFStep`, `PF_sil` `PFSil`, `PF_sil'` `PFSil'`, `PF_rds` `PFRds`, `PF_rdn`
`PFRdn`, `PF_wr` `PFWr`, `PF_mrd` `PFMrd`, `PF_fence` `PFFence`, `wpd_of_CertP`
`AxCertP2.wpdOfCertP`, `wpd_instr_of_CertP` `AxCertP2.wpdInstrOfCertP` (both duplicated with
AxCondM2).

**Dropped:** nothing (Rocq 31 definitions/lemmas; Lean 31 + 4 Lean-only).  **Not ported:** the
Ltac `silent_psP` (deviation 4), the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCertP
import Weak.AxSpinE4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. Small inversion of `Cert` -/

section famP
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- The small inversion at a node `.impure o k` (deviations 1–2). -/
def CInvO {X : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (s : Cst) (t : ExecSt) :
    (o : Eff RegisterType exception) → (Sail.ArchSem.Effect.ret o → SailM X) → Prop
  | .ok (.regRead r), k =>
      (AxRunClose.pinReg r → ∀ v, AxCert.Cert img dok kind QE Q s (k v) t) ∧
      (¬ AxRunClose.pinReg r → AxCert.Cert img dok kind QE Q s (k (t.regs r)) t)
  | .ok (.regWrite r v), k => AxCert.Cert img dok kind QE Q s (k PUnit.unit) (t.setReg r v)
  | .ok (.memRead n _ req), k =>
      (∃ b' vi, s.csB = bsucc b' ∧ (classify req.access_kind).akLatest = false ∧
         (classify req.access_kind).akIfetch = false ∧
         imgBytes img (paZ req.pa) n = some vi ∧
         AxCert.Cert img dok kind QE Q ⟨s.csD, b', s.csR⟩ (k (.Ok (wordOfBytes n vi, none))) t)
      ∨ ((classify req.access_kind).akLatest = false ∧ (classify req.access_kind).akIfetch = true ∧
         ∃ vi, imgBytes img (paZ req.pa) n = some vi ∧
           AxCert.Cert img dok kind QE Q s (k (.Ok (wordOfBytes n vi, none))) t)
      ∨ (s.csB = .BFin 0 ∧ (classify req.access_kind).akLatest = false ∧
         (classify req.access_kind).akIfetch = false)
      ∨ (∃ b', s.csB = bsucc b' ∧ s.csD = .CPend ∧ (classify req.access_kind).akLatest = false ∧
         (classify req.access_kind).akIfetch = false ∧
         ∀ vs : List (BitVec 8), vs.length = n →
           AxCert.Cert img dok kind QE Q ⟨.CLd vs, b', s.csR⟩ (k (.Ok (wordOfBytes n vs, none))) t)
      ∨ (s.csD = .CPend ∧ (classify req.access_kind).akLatest = true ∧
         ∀ vs : List (BitVec 8), vs.length = n →
           ∃ aq, AxCert.Cert img dok kind QE Q ⟨.CRmwR aq vs, s.csB, s.csR⟩
             (k (.Ok (wordOfBytes n vs, none))) t)
  | .ok (.memWrite _ _ req), k =>
      (∃ b' d', s.csB = bsucc b' ∧ AxCert.Cert img dok kind QE Q ⟨d', b', false⟩ (k (.Ok (some true))) t)
      ∨ (s.csB = .BFin 0 ∧ (classify req.access_kind).akLatest = false)
  | .ok (.readRam _ _ _), _ => False
  | .ok (.writeRam _ _ _ _), _ => False
  | .ok (.barrier bk), k =>
      ∃ b', s.csB = bsucc b' ∧
        AxCert.Cert img dok kind QE Q ⟨s.csD, b', relpUpd (ebarLabel bk) s.csR⟩ (k ()) t
  | .ok (.cacheOp _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.tlbi _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.translationStart _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.translationEnd _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.takeException _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.returnException _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok .cycleCount, k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok .getCycleCount, k => AxCert.Cert img dok kind QE Q s (k (0 : Nat)) t
  | .ok (.message _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .ok (.choose _), _ => False
  | .ok (.instrAnnounce n w), k =>
      (sfAnnB n w = false ∧ AxCert.Cert img dok kind QE Q s (k ()) t)
      ∨ (sfAnnB n w = true ∧ ∃ b', s.csB = bsucc b' ∧
           AxCert.Cert img dok kind QE Q ⟨s.csD, b', s.csR⟩ (k ()) t)
  | .ok (.branchAnnounce _ _), k => AxCert.Cert img dok kind QE Q s (k ()) t
  | .error e, _ => QE s e t

def CInv {X : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (s : Cst) (m : SailM X) (t : ExecSt) : Prop :=
  match m with
  | .pure x => Q s x t
  | .impure o k => CInvO img dok kind QE Q s t o k

theorem AxCertP2.cinv {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {s : Cst} {m : SailM X} {t : ExecSt}
    (h : AxCert.Cert img dok kind QE Q s m t) : CInv img dok kind QE Q s m t := by
  cases h with
  | cRet s x t h => exact h
  | cRd s r k t hs hn => exact ⟨hs, hn⟩
  | cWr s r v k t _ h => exact h
  | cMrd d b r n va req k t vs _ h2 h3 h4 h => exact Or.inl ⟨b, vs, rfl, h2, h3, h4, h⟩
  | cIf s n va req k t vs _ h2 h3 h4 h => exact Or.inr (Or.inl ⟨h2, h3, vs, h4, h⟩)
  | cEnd d r n va req k t _ h2 h3 => exact Or.inr (Or.inr (Or.inl ⟨rfl, h2, h3⟩))
  | cDrd b r n va req k t _ _ h2 h3 _ h =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b, rfl, rfl, h2, h3, h⟩)))
  | cDwr b r n va req k t v _ _ _ _ _ h => exact Or.inl ⟨b, _, rfl, h⟩
  | cFence d b r bk k t _ h => exact ⟨b, rfl, h⟩
  | cXrd b r n va req k t _ _ h2 _ h =>
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h2, fun vs hl => ⟨_, h vs hl⟩⟩)))
  | cXwr aq rvs b r n va req k t v _ _ _ _ _ h => exact Or.inl ⟨b, _, rfl, h⟩
  | cWrEnd d r n va req k t _ h2 => exact Or.inr ⟨rfl, h2⟩
  | cIa s n w k t hs h => exact Or.inl ⟨hs, h⟩
  | cSf d b r n w k t hs h => exact Or.inr ⟨hs, b, rfl, h⟩
  | cBa s _ _ k t h => exact h
  | cCo s _ k t h => exact h
  | cTl s _ k t h => exact h
  | cTe s _ k t h => exact h
  | cRx s _ k t h => exact h
  | cTs s _ k t h => exact h
  | cTx s _ k t h => exact h
  | cCc s k t h => exact h
  | cMsg s _ k t h => exact h
  | cGcc s k t h => exact h
  | cExt s e k t h => exact h

/-! # 2. Families and the budget bound -/

def Qc {X : Type} (n : Nat) : Cst → X → ExecSt → Prop :=
  fun s _ _ => s.csB = .BFin n ∧ ∀ aq vs, s.csD ≠ .CRmwR aq vs

/-- For every shift `j`, a certificate at budget `a + j` ending at `c + j`. -/
def FamP {X : Type} (P : Cdata → Prop) (m : SailM X) (t : ExecSt) (a c : Nat) : Prop :=
  ∀ j : Nat, ∃ d r, P d ∧
    AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d, .BFin (a + j), r⟩ m t

def AxCertP2.isR (d : Cdata) : Prop := ∃ aq vs, d = .CRmwR aq vs

def v0 (base : Int) (n : Nat) : List (BitVec 8) :=
  match imgBytes img base n with
  | some vs => vs
  | none => List.replicate n 0

theorem imgBytesLen (base : Int) (n : Nat) (vs : List (BitVec 8)) :
    imgBytes img base n = some vs → vs.length = n :=
  fun h => (imgBytesSpec img base n vs h).1

theorem v0Len (base : Int) (n : Nat) : (v0 img base n).length = n := by
  unfold v0
  cases h : imgBytes img base n with
  | some vs => exact imgBytesLen img base n vs h
  | none => exact List.length_replicate

theorem v0Img {base : Int} {n : Nat} {vi : List (BitVec 8)} :
    imgBytes img base n = some vi → v0 img base n = vi := by
  intro h
  unfold v0
  rw [h]

theorem rdCons {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {d : Cdata} {b : Nat} {r : Bool} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {t : ExecSt} :
    (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false →
    AxCert.Cert img dok kind QE Q ⟨d, .BFin (b + 1), r⟩ (.impure (.ok (.memRead n va req)) k) t →
    ∃ d' r', (d' = d ∨ d = .CPend) ∧
      AxCert.Cert img dok kind QE Q ⟨d', .BFin b, r'⟩
        (k (.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t := by
  intro Hl Hf H
  have H' := AxCertP2.cinv img dok kind H
  rcases H' with ⟨b', vi, Hb, -, -, Hi, H⟩ | ⟨-, Hf', -⟩ | ⟨Hb, -⟩ | ⟨b', Hb, Hd, -, -, H⟩ |
    ⟨-, Hl', -⟩
  · cases b' with
    | BInf => cases Hb
    | BFin b' =>
      simp only [bsucc, Bud.BFin.injEq, Nat.add_right_cancel_iff] at Hb
      subst Hb
      rw [v0Img img Hi]
      exact ⟨d, r, Or.inl rfl, H⟩
  · rw [Hf] at Hf'
    cases Hf'
  · cases Hb
  · cases b' with
    | BInf => cases Hb
    | BFin b' =>
      simp only [bsucc, Bud.BFin.injEq, Nat.add_right_cancel_iff] at Hb
      subst Hb
      exact ⟨_, r, Or.inr Hd, H _ (v0Len img _ _)⟩
  · rw [Hl] at Hl'
    cases Hl'

/-- (Lean-only, deviation 1) A non-latest FETCH keeps the certificate state. -/
theorem AxCertP2.rdIf {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {s : Cst} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {t : ExecSt} :
    (classify req.access_kind).akIfetch = true →
    AxCert.Cert img dok kind QE Q s (.impure (.ok (.memRead n va req)) k) t →
    AxCert.Cert img dok kind QE Q s (k (.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t := by
  intro Hf H
  have H' := AxCertP2.cinv img dok kind H
  rcases H' with ⟨-, -, -, -, Hf', -, -⟩ | ⟨-, -, vi, Hi, H⟩ | ⟨-, -, Hf'⟩ | ⟨-, -, -, -, Hf', -⟩ |
    ⟨-, Hl', -⟩
  · rw [Hf] at Hf'
    cases Hf'
  · rw [v0Img img Hi]
    exact H
  · rw [Hf] at Hf'
    cases Hf'
  · rw [Hf] at Hf'
    cases Hf'
  · rw [AxCert2.nfOfLatest _ Hl'] at Hf
    cases Hf

theorem rdX {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {d : Cdata} {b : Bud} {r : Bool} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {t : ExecSt} :
    (classify req.access_kind).akLatest = true →
    AxCert.Cert img dok kind QE Q ⟨d, b, r⟩ (.impure (.ok (.memRead n va req)) k) t →
    d = .CPend ∧ ∃ aq, AxCert.Cert img dok kind QE Q ⟨.CRmwR aq (v0 img (paZ req.pa) n), b, r⟩
      (k (.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t := by
  intro Hl H
  have H' := AxCertP2.cinv img dok kind H
  rcases H' with ⟨-, -, -, Hl', -⟩ | ⟨Hl', -⟩ | ⟨-, Hl', -⟩ | ⟨-, -, -, Hl', -⟩ | ⟨Hd, -, H⟩
  · rw [Hl] at Hl'
    cases Hl'
  · rw [Hl] at Hl'
    cases Hl'
  · rw [Hl] at Hl'
    cases Hl'
  · rw [Hl] at Hl'
    cases Hl'
  · exact ⟨Hd, H _ (v0Len img _ _)⟩

theorem wrCons {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {d : Cdata} {b : Nat} {r : Bool} {n va : Nat}
    {req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (Option Bool) Arch.abort → SailM X} {t : ExecSt} :
    AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (.impure (.ok (.memWrite n va req)) k) t →
    0 < b →
    ∃ b' d', b = b' + 1 ∧ AxCert.Cert img dok kind QE Q ⟨d', .BFin b', false⟩ (k (.Ok (some true))) t := by
  intro H Hb0
  obtain ⟨b', d', Hb, H⟩ | ⟨Hb, -⟩ := AxCertP2.cinv img dok kind H
  case inr =>
    simp only [Bud.BFin.injEq] at Hb
    omega
  cases b' with
  | BInf => cases Hb
  | BFin b' =>
    simp only [bsucc, Bud.BFin.injEq] at Hb
    exact ⟨b', d', Hb, H⟩

theorem fenceCons {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {d : Cdata} {b : Nat} {r : Bool} {bk : barrier_kind}
    {k : Unit → SailM X} {t : ExecSt} :
    AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (.impure (.ok (.barrier bk)) k) t →
    ∃ b', b = b' + 1 ∧
      AxCert.Cert img dok kind QE Q ⟨d, .BFin b', relpUpd (ebarLabel bk) r⟩ (k ()) t := by
  intro H
  obtain ⟨b', Hb, H⟩ := AxCertP2.cinv img dok kind H
  cases b' with
  | BInf => cases Hb
  | BFin b' =>
    simp only [bsucc, Bud.BFin.injEq] at Hb
    exact ⟨b', Hb, H⟩

/-- (Lean-only, deviation 5) The announce inversion: a non-sfence announce keeps the state, an
sfence announce consumes one budget unit. -/
theorem AxCertP2.annCons {X : Type} {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → X → ExecSt → Prop} {d : Cdata} {b : Nat} {r : Bool} {n : Nat} {w : BitVec n}
    {k : Unit → SailM X} {t : ExecSt} :
    AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (.impure (.ok (.instrAnnounce n w)) k) t →
    (sfAnnB n w = false ∧ AxCert.Cert img dok kind QE Q ⟨d, .BFin b, r⟩ (k ()) t) ∨
    (sfAnnB n w = true ∧ ∃ b', b = b' + 1 ∧ AxCert.Cert img dok kind QE Q ⟨d, .BFin b', r⟩ (k ()) t) := by
  intro H
  rcases AxCertP2.cinv img dok kind H with ⟨Hs, H⟩ | ⟨Hs, b', Hb, H⟩
  · exact Or.inl ⟨Hs, H⟩
  · cases b' with
    | BInf => cases Hb
    | BFin b' =>
      simp only [bsucc, Bud.BFin.injEq] at Hb
      exact Or.inr ⟨Hs, b', Hb, H⟩

theorem FamStepP {X : Type} (P P' : Cdata → Prop) (m m' : SailM X) (t t' : ExecSt) (a a' c : Nat)
    (H : ∀ d r j, P d →
      AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d, .BFin (a + j), r⟩ m t →
      ∃ d' r', P' d' ∧
        AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d', .BFin (a' + j), r'⟩ m' t') :
    FamP img dok kind P m t a c → FamP img dok kind P' m' t' a' c := by
  intro HF j
  obtain ⟨d, r, Hd, Hc⟩ := HF j
  exact H d r j Hd Hc

/-- The shift: at budget 0, use the family member `j + 1`. -/
theorem FamStepP0 {X : Type} (P P' : Cdata → Prop) (m m' : SailM X) (t t' : ExecSt) (c : Nat)
    (H : ∀ d r j, P d →
      AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + (j + 1))) ⟨d, .BFin (j + 1), r⟩ m t →
      ∃ d' r', P' d' ∧
        AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + (j + 1))) ⟨d', .BFin j, r'⟩ m' t') :
    FamP img dok kind P m t 0 c → FamP img dok kind P' m' t' 0 (c + 1) := by
  intro HF j
  obtain ⟨d, r, Hd, Hc⟩ := HF (j + 1)
  rw [Nat.zero_add] at Hc
  rw [show c + 1 + j = c + (j + 1) by omega, Nat.zero_add]
  exact H d r j Hd Hc

/-- BUDGET MONOTONICITY: a family never ends above its start. -/
theorem FamBound {X : Type} (m : SailM X) :
    ∀ t a c, FamP img dok kind (fun _ => True) m t a c → c ≤ a := by
  induction m with
  | pure x =>
    intro t a c HF
    obtain ⟨d, r, -, Hc⟩ := HF 0
    obtain ⟨Hb, -⟩ := AxCertP2.cinv img dok kind Hc
    simp only [Bud.BFin.injEq] at Hb
    omega
  | impure o k IH =>
    intro t a c HF
    cases o with
    | error e =>
      obtain ⟨d, r, -, Hc⟩ := HF 0
      exact (AxCertP2.cinv img dok kind Hc).elim
    | ok o =>
      cases o
      case regRead r =>
        refine IH (t.regs r) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
        intro d rr j _ Hc
        have Hc' := AxCertP2.cinv img dok kind Hc
        refine ⟨d, rr, trivial, ?_⟩
        by_cases Hs : AxRunClose.pinReg r
        · exact Hc'.1 Hs _
        · exact Hc'.2 Hs
      case regWrite r v =>
        refine IH PUnit.unit (t.setReg r v) a c (FamStepP img dok kind _ _ _ _ t _ a a c ?_ HF)
        intro d rr j _ Hc
        exact ⟨d, rr, trivial, AxCertP2.cinv img dok kind Hc⟩
      case memRead n va req =>
        cases Hl : (classify req.access_kind).akLatest with
        | true =>
          refine IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
          intro d rr j _ Hc
          obtain ⟨-, aq, H⟩ := rdX img dok kind Hl Hc
          exact ⟨_, rr, trivial, H⟩
        | false =>
          cases Hf : (classify req.access_kind).akIfetch with
          | true =>
            refine IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
            intro d rr j _ Hc
            exact ⟨d, rr, trivial, AxCertP2.rdIf img dok kind Hf Hc⟩
          | false =>
            cases a with
            | zero =>
              exfalso
              have := IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t 0 (c + 1) (FamStepP0 img dok kind _ _ _ _ t t c (by
                intro d rr j _ Hc
                obtain ⟨d', r', -, H⟩ := rdCons img dok kind Hl Hf Hc
                exact ⟨d', r', trivial, H⟩) HF)
              omega
            | succ a =>
              have := IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t a c (FamStepP img dok kind _ _ _ _ t t (a + 1) a c (by
                intro d rr j _ Hc
                rw [show a + 1 + j = (a + j) + 1 by omega] at Hc
                obtain ⟨d', r', -, H⟩ := rdCons img dok kind Hl Hf Hc
                exact ⟨d', r', trivial, H⟩) HF)
              omega
      case memWrite n va req =>
        cases a with
        | zero =>
          exfalso
          have := IH (Result.Ok (some true)) t 0 (c + 1) (FamStepP0 img dok kind _ _ _ _ t t c (by
            intro d rr j _ Hc
            obtain ⟨b', d', Hb, H⟩ := wrCons img dok kind Hc (Nat.succ_pos j)
            obtain rfl : b' = j := by omega
            exact ⟨d', false, trivial, H⟩) HF)
          omega
        | succ a' =>
          have := IH (Result.Ok (some true)) t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
            intro d rr j _ Hc
            obtain ⟨b', d', Hb, H⟩ := wrCons img dok kind Hc (by omega)
            obtain rfl : b' = a' + j := by omega
            exact ⟨d', false, trivial, H⟩) HF)
          omega
      case barrier bk =>
        obtain ⟨d0, r0, -, Hc0⟩ := HF 0
        obtain ⟨a', Ha, -⟩ := fenceCons img dok kind Hc0
        obtain rfl : a = a' + 1 := by omega
        have := IH () t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
          intro d rr j _ Hc
          obtain ⟨b', Hb, H⟩ := fenceCons img dok kind Hc
          obtain rfl : b' = a' + j := by omega
          exact ⟨d, _, trivial, H⟩) HF)
        omega
      case instrAnnounce n w =>
        cases Hs : sfAnnB n w with
        | false =>
          refine IH () t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
          intro d rr j Hd Hc
          rcases AxCertP2.annCons img dok kind Hc with ⟨-, H⟩ | ⟨Hs', -⟩
          · exact ⟨d, rr, trivial, H⟩
          · rw [Hs] at Hs'
            cases Hs'
        | true =>
          obtain ⟨d0, r0, -, Hc0⟩ := HF 0
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
            rcases AxCertP2.annCons img dok kind Hc0 with ⟨Hs', -⟩ | ⟨-, a', Ha, -⟩
            · rw [Hs] at Hs'
              cases Hs'
            · exact ⟨a', by omega⟩
          have := IH () t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
            intro d rr j Hd Hc
            rcases AxCertP2.annCons img dok kind Hc with ⟨Hs', -⟩ | ⟨-, b', Hb, H⟩
            · rw [Hs] at Hs'
              cases Hs'
            · obtain rfl : b' = a' + j := by omega
              exact ⟨d, rr, trivial, H⟩) HF)
          omega
      all_goals first
        | (exfalso
           obtain ⟨d, rr, -, Hc⟩ := HF 0
           exact AxCertP2.cinv img dok kind Hc)
        | (refine IH () t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
           intro d rr j _ Hc
           exact ⟨d, rr, trivial, AxCertP2.cinv img dok kind Hc⟩)
        | (refine IH (0 : Nat) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
           intro d rr j _ Hc
           exact ⟨d, rr, trivial, AxCertP2.cinv img dok kind Hc⟩)

/-- From an RMW-half state the write half still consumes: `c < a`. -/
theorem FamRBound {X : Type} (m : SailM X) :
    ∀ t a c, FamP img dok kind AxCertP2.isR m t a c → c + 1 ≤ a := by
  induction m with
  | pure x =>
    intro t a c HF
    exfalso
    obtain ⟨d, r, ⟨aq, vs, rfl⟩, Hc⟩ := HF 0
    obtain ⟨-, Hn⟩ := AxCertP2.cinv img dok kind Hc
    exact Hn aq vs rfl
  | impure o k IH =>
    intro t a c HF
    cases o with
    | error e =>
      obtain ⟨d, r, -, Hc⟩ := HF 0
      exact (AxCertP2.cinv img dok kind Hc).elim
    | ok o =>
      cases o
      case regRead r =>
        refine IH (t.regs r) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
        intro d rr j Hd Hc
        have Hc' := AxCertP2.cinv img dok kind Hc
        refine ⟨d, rr, Hd, ?_⟩
        by_cases Hs : AxRunClose.pinReg r
        · exact Hc'.1 Hs _
        · exact Hc'.2 Hs
      case regWrite r v =>
        refine IH PUnit.unit (t.setReg r v) a c (FamStepP img dok kind _ _ _ _ t _ a a c ?_ HF)
        intro d rr j Hd Hc
        exact ⟨d, rr, Hd, AxCertP2.cinv img dok kind Hc⟩
      case memRead n va req =>
        cases Hl : (classify req.access_kind).akLatest with
        | true =>
          exfalso
          obtain ⟨d, rr, ⟨aq, vs, rfl⟩, Hc⟩ := HF 0
          obtain ⟨Hd, -⟩ := rdX img dok kind Hl Hc
          cases Hd
        | false =>
          cases Hf : (classify req.access_kind).akIfetch with
          | true =>
            refine IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
            intro d rr j Hd Hc
            exact ⟨d, rr, Hd, AxCertP2.rdIf img dok kind Hf Hc⟩
          | false =>
            have hstep : ∀ (d : Cdata) (rr : Bool) (j b : Nat), AxCertP2.isR d →
                AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d, .BFin (b + 1), rr⟩
                  (.impure (.ok (.memRead n va req)) k) t →
                ∃ d' r', AxCertP2.isR d' ∧ AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j))
                  ⟨d', .BFin b, r'⟩ (k (.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t := by
              intro d rr j b Hd Hc
              obtain ⟨d', r', Hdd, H⟩ := rdCons img dok kind Hl Hf Hc
              refine ⟨d', r', ?_, H⟩
              rcases Hdd with Hq | Hq
              · rw [Hq]
                exact Hd
              · rw [Hq] at Hd
                obtain ⟨_, _, Hq2⟩ := Hd
                cases Hq2
            cases a with
            | zero =>
              exfalso
              have := IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t 0 (c + 1) (FamStepP0 img dok kind _ _ _ _ t t c (by
                intro d rr j Hd Hc
                exact hstep d rr (j + 1) j Hd Hc) HF)
              omega
            | succ a =>
              have := IH (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none)) t a c (FamStepP img dok kind _ _ _ _ t t (a + 1) a c (by
                intro d rr j Hd Hc
                rw [show a + 1 + j = (a + j) + 1 by omega] at Hc
                exact hstep d rr j (a + j) Hd Hc) HF)
              omega
      case memWrite n va req =>
        cases a with
        | zero =>
          exfalso
          have := (fun x => FamBound img dok kind (k x)) (Result.Ok (some true)) t 0 (c + 1) (FamStepP0 img dok kind _ _ _ _ t t c (by
            intro d rr j _ Hc
            obtain ⟨b', d', Hb, H⟩ := wrCons img dok kind Hc (Nat.succ_pos j)
            obtain rfl : b' = j := by omega
            exact ⟨d', false, trivial, H⟩) HF)
          omega
        | succ a' =>
          have := (fun x => FamBound img dok kind (k x)) (Result.Ok (some true)) t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
            intro d rr j _ Hc
            obtain ⟨b', d', Hb, H⟩ := wrCons img dok kind Hc (by omega)
            obtain rfl : b' = a' + j := by omega
            exact ⟨d', false, trivial, H⟩) HF)
          omega
      case barrier bk =>
        obtain ⟨d0, r0, -, Hc0⟩ := HF 0
        obtain ⟨a', Ha, -⟩ := fenceCons img dok kind Hc0
        obtain rfl : a = a' + 1 := by omega
        have := IH () t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
          intro d rr j Hd Hc
          obtain ⟨b', Hb, H⟩ := fenceCons img dok kind Hc
          obtain rfl : b' = a' + j := by omega
          exact ⟨d, _, Hd, H⟩) HF)
        omega
      case instrAnnounce n w =>
        cases Hs : sfAnnB n w with
        | false =>
          refine IH () t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
          intro d rr j Hd Hc
          rcases AxCertP2.annCons img dok kind Hc with ⟨-, H⟩ | ⟨Hs', -⟩
          · exact ⟨d, rr, Hd, H⟩
          · rw [Hs] at Hs'
            cases Hs'
        | true =>
          obtain ⟨d0, r0, -, Hc0⟩ := HF 0
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
            rcases AxCertP2.annCons img dok kind Hc0 with ⟨Hs', -⟩ | ⟨-, a', Ha, -⟩
            · rw [Hs] at Hs'
              cases Hs'
            · exact ⟨a', by omega⟩
          have := IH () t a' c (FamStepP img dok kind _ _ _ _ t t (a' + 1) a' c (by
            intro d rr j Hd Hc
            rcases AxCertP2.annCons img dok kind Hc with ⟨Hs', -⟩ | ⟨-, b', Hb, H⟩
            · rw [Hs] at Hs'
              cases Hs'
            · obtain rfl : b' = a' + j := by omega
              exact ⟨d, rr, Hd, H⟩) HF)
          omega
      all_goals first
        | (exfalso
           obtain ⟨d, rr, -, Hc⟩ := HF 0
           exact AxCertP2.cinv img dok kind Hc)
        | (refine IH () t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
           intro d rr j Hd Hc
           exact ⟨d, rr, Hd, AxCertP2.cinv img dok kind Hc⟩)
        | (refine IH (0 : Nat) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
           intro d rr j Hd Hc
           exact ⟨d, rr, Hd, AxCertP2.cinv img dok kind Hc⟩)

/-- The data read at budget `a + 1` sits strictly inside the window: `c ≤ a` (deviation 1:
`Hnf`). -/
theorem FamDrd {X : Type} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {t : ExecSt} {a c : Nat} :
    FamP img dok kind (fun _ => True) (.impure (.ok (.memRead n va req)) k) t (a + 1) c →
    (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false → c ≤ a := by
  intro HF Hl Hf
  refine FamBound img dok kind (k (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t a c (FamStepP img dok kind _ _ _ _ t t (a + 1) a c ?_ HF)
  intro d r j _ Hc
  rw [show a + 1 + j = (a + j) + 1 by omega] at Hc
  obtain ⟨d', r', -, H⟩ := rdCons img dok kind Hl Hf Hc
  exact ⟨d', r', trivial, H⟩

/-- The exclusive read at budget `a`: `c < a`. -/
theorem FamXrd {X : Type} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {t : ExecSt} {a c : Nat} :
    FamP img dok kind (fun _ => True) (.impure (.ok (.memRead n va req)) k) t a c →
    (classify req.access_kind).akLatest = true → c + 1 ≤ a := by
  intro HF Hl
  refine FamRBound img dok kind (k (Result.Ok (wordOfBytes n (v0 img (paZ req.pa) n), none))) t a c (FamStepP img dok kind _ _ _ _ t t a a c ?_ HF)
  intro d r j _ Hc
  obtain ⟨-, aq, H⟩ := rdX img dok kind Hl Hc
  exact ⟨_, r, ⟨aq, _, rfl⟩, H⟩

/-- THE BRIDGE INVARIANT: before the data event, a family at the current budget. -/
def PF {X : Type} (c : Nat) (s : Cst) (m : SailM X) (t : ExecSt) : Prop :=
  s.csD = .CPend → ∃ a, s.csB = .BFin a ∧ FamP img dok kind (fun _ => True) m t a c

theorem PFStep {X : Type} (c : Nat) (s s' : Cst) (m m' : SailM X) (t t' : ExecSt)
    (Hd : s'.csD = .CPend → s.csD = .CPend)
    (H : ∀ a, s.csB = .BFin a → s'.csD = .CPend → ∃ a', s'.csB = .BFin a' ∧
      ∀ d r j,
        AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d, .BFin (a + j), r⟩ m t →
        ∃ d' r',
          AxCert.Cert img dok kind (fun _ _ _ => False) (Qc (c + j)) ⟨d', .BFin (a' + j), r'⟩ m' t') :
    PF img dok kind c s m t → PF img dok kind c s' m' t' := by
  intro HP Hd'
  obtain ⟨a, Ha, HF⟩ := HP (Hd Hd')
  obtain ⟨a', Ha', Hs⟩ := H a Ha Hd'
  refine ⟨a', Ha', fun j => ?_⟩
  obtain ⟨d, r, -, Hc⟩ := HF j
  obtain ⟨d', r', Hc'⟩ := Hs d r j Hc
  exact ⟨d', r', trivial, Hc'⟩

theorem PFSil {X : Type} {o : Eff RegisterType exception}
    {k : Sail.ArchSem.Effect.ret o → SailM X} {v : Sail.ArchSem.Effect.ret o} {c : Nat} {s : Cst}
    {t : ExecSt} :
    (∀ (Q : Cst → X → ExecSt → Prop) (s1 : Cst), CInvO img dok kind (fun _ _ _ => False) Q s1 t o k →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s1 (k v) t) →
    PF img dok kind c s (.impure o k) t → PF img dok kind c s (k v) t := by
  intro Hi
  apply PFStep img dok kind c s s _ _ t t id
  intro a Ha _
  exact ⟨a, Ha, fun d r j Hc => ⟨d, r, Hi _ _ (AxCertP2.cinv img dok kind Hc)⟩⟩

theorem PFSil' {X : Type} {o : Eff RegisterType exception}
    {k : Sail.ArchSem.Effect.ret o → SailM X} {v : Sail.ArchSem.Effect.ret o} {c : Nat} {s : Cst}
    {t : ExecSt} :
    PF img dok kind c s (.impure o k) t →
    (∀ (Q : Cst → X → ExecSt → Prop) (s1 : Cst), CInvO img dok kind (fun _ _ _ => False) Q s1 t o k →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s1 (k v) t) →
    PF img dok kind c s (k v) t :=
  fun HP Hi => PFSil img dok kind Hi HP

theorem PFRds {X : Type} {r : Register} {k : RegisterType r → SailM X} {c : Nat} {s : Cst}
    {t : ExecSt} (v : RegisterType r) :
    AxRunClose.pinReg r → PF img dok kind c s (.impure (.ok (.regRead r)) k) t →
    PF img dok kind c s (k v) t := by
  intro Hs
  exact PFSil img dok kind (fun _ _ Hc => Hc.1 Hs v)

theorem PFRdn {X : Type} {r : Register} {k : RegisterType r → SailM X} {c : Nat} {s : Cst}
    {t : ExecSt} :
    ¬ AxRunClose.pinReg r → PF img dok kind c s (.impure (.ok (.regRead r)) k) t →
    PF img dok kind c s (k (t.regs r)) t := by
  intro Hs
  exact PFSil img dok kind (fun _ _ Hc => Hc.2 Hs)

theorem PFWr {X : Type} {r : Register} {v : RegisterType r} {k : PUnit → SailM X} {c : Nat}
    {s : Cst} {t : ExecSt} :
    PF img dok kind c s (.impure (.ok (.regWrite r v)) k) t →
    PF img dok kind c s (k PUnit.unit) (t.setReg r v) := by
  apply PFStep img dok kind c s s _ _ t _ id
  intro a Ha _
  exact ⟨a, Ha, fun d rr j Hc => ⟨d, rr, AxCertP2.cinv img dok kind Hc⟩⟩

theorem PFMrd {X : Type} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak} {vs : List (BitVec 8)}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {c : Nat} {d : Cdata}
    {b : Bud} {r : Bool} {t : ExecSt} :
    (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false →
    imgBytes img (paZ req.pa) n = some vs →
    PF img dok kind c ⟨d, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t →
    PF img dok kind c ⟨d, b, r⟩ (k (.Ok (wordOfBytes n vs, none))) t := by
  intro Hl Hf Hv
  apply PFStep img dok kind c ⟨d, bsucc b, r⟩ ⟨d, b, r⟩ _ _ t t (fun h => h)
  intro a Ha _
  cases b with
  | BInf => cases Ha
  | BFin b =>
    simp only [bsucc, Bud.BFin.injEq] at Ha
    subst Ha
    refine ⟨b, rfl, fun d0 r0 j Hc => ?_⟩
    rw [show b + 1 + j = (b + j) + 1 by omega] at Hc
    obtain ⟨d', r', -, H⟩ := rdCons img dok kind Hl Hf Hc
    rw [v0Img img Hv] at H
    exact ⟨d', r', H⟩

/-- (Lean-only, deviation 1) The `PF` step at an image FETCH (same state). -/
theorem AxCertP2.PFIf {X : Type} {n va : Nat}
    {req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak} {vs : List (BitVec 8)}
    {k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X} {c : Nat} {s : Cst}
    {t : ExecSt} :
    (classify req.access_kind).akIfetch = true →
    imgBytes img (paZ req.pa) n = some vs →
    PF img dok kind c s (.impure (.ok (.memRead n va req)) k) t →
    PF img dok kind c s (k (.Ok (wordOfBytes n vs, none))) t := by
  intro Hf Hv
  apply PFStep img dok kind c _ _ _ _ t t id
  intro a Ha _
  refine ⟨a, Ha, fun d0 r0 j Hc => ?_⟩
  have H := AxCertP2.rdIf img dok kind Hf Hc
  rw [v0Img img Hv] at H
  exact ⟨d0, r0, H⟩

theorem PFFence {X : Type} {bk : barrier_kind} {k : Unit → SailM X} {c : Nat} {d : Cdata}
    {b : Bud} {r : Bool} {t : ExecSt} :
    PF img dok kind c ⟨d, bsucc b, r⟩ (.impure (.ok (.barrier bk)) k) t →
    PF img dok kind c ⟨d, b, relpUpd (ebarLabel bk) r⟩ (k ()) t := by
  apply PFStep img dok kind c ⟨d, bsucc b, r⟩ ⟨d, b, relpUpd (ebarLabel bk) r⟩ _ _ t t (fun h => h)
  intro a Ha _
  cases b with
  | BInf => cases Ha
  | BFin b =>
    simp only [bsucc, Bud.BFin.injEq] at Ha
    subst Ha
    refine ⟨b, rfl, fun d0 r0 j Hc => ?_⟩
    obtain ⟨b', Hb, H⟩ := fenceCons img dok kind Hc
    obtain rfl : b' = b + j := by omega
    exact ⟨d0, _, H⟩

/-- (Lean-only, deviation 5) The `PF` step at an SFENCE.VMA announce (twin of `PFFence`). -/
theorem AxCertP2.PFSf {X : Type} {n : Nat} {w : BitVec n} {k : Unit → SailM X} {c : Nat}
    {d : Cdata} {b : Bud} {r : Bool} {t : ExecSt} :
    sfAnnB n w = true →
    PF img dok kind c ⟨d, bsucc b, r⟩ (.impure (.ok (.instrAnnounce n w)) k) t →
    PF img dok kind c ⟨d, b, r⟩ (k ()) t := by
  intro Hs
  apply PFStep img dok kind c ⟨d, bsucc b, r⟩ ⟨d, b, r⟩ _ _ t t (fun h => h)
  intro a Ha _
  cases b with
  | BInf => cases Ha
  | BFin b =>
    simp only [bsucc, Bud.BFin.injEq] at Ha
    subst Ha
    refine ⟨b, rfl, fun d0 r0 j Hc => ?_⟩
    rw [show b + 1 + j = (b + j) + 1 by omega] at Hc
    rcases AxCertP2.annCons img dok kind Hc with ⟨Hs', -⟩ | ⟨-, b', Hb, H⟩
    · rw [Hs] at Hs'
      cases Hs'
    · obtain rfl : b' = b + j := by omega
      exact ⟨d0, r0, H⟩

end famP

/-! # 3. The window-bounded bridge -/

section bridgeP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
variable (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (Out : Nat → List (BitVec 8) → IProp GF) (k0 c : Nat)
/- THE WINDOW PREMISES: only positions `k0 ≤ k < length − c`. -/
variable (HnoRmwW : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k0 ≤ k →
    k + c < (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplitW : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k0 ≤ k →
    k + c < (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include HG Hmid Htext Hflow Hloc HnoRmwW HnoSplitW in
theorem AxCertP2.wpdOfCertP (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst)
    (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t → PF img dok kind c s m t →
    ∀ rs ib kk, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i kk s.csB → k0 ≤ kk →
    ⊢ CResK dok kind i Out k0 s.csD kk -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ ⌜k0 ≤ k'⌝ -∗ CResK dok kind i Out k0 s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro H
  induction H with
  | cRet s x t HQ =>
    intro _ rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply C $$ %s %t %rs %ib %kk %HQ %Hag %Hb %Hk0 Hd
  | cExt s e k t he => exact he.elim
  | cRd s r k t _ _ IHs IHn =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdAdminNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) (PFRds img dok kind (rs1 r) Hs HPF) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
      · have h := IHn Hs (PFRdn img dok kind Hs HPF) rs1 ib1 kk HA1 Hb Hk0
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | cWr s r v k t Hr _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdAdminNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (PFWr img dok kind HPF) (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb
        Hk0) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgRead3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow n va
      req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH (PFMrd img dok kind Hlat Hnf Hvs HPF) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)
      (by omega)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext n va req k
      ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH (AxCertP2.PFIf img dok kind Hfe Hvs HPF) rs' ib kk HA' Hb Hk0) $$ Hd C
  | cEnd d r n va req k t Hdev Hlat Hnf =>
    intro _ rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (wpdStuckReadM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req
      k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | cWrEnd d r n va req k t Hdev Hlat =>
    intro _ rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (AxCert2.wpdStuckWriteM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat rs Hag)
  | cDrd b r n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    -- THE DATA READ: positioned inside the window
    intro HPF rs ib kk Hag Hb Hk0
    obtain ⟨a, Ha, HF⟩ := HPF rfl
    obtain ⟨b', rfl⟩ : ∃ b', b = .BFin b' := by
      cases b with
      | BInf => cases Ha
      | BFin b' => exact ⟨b', rfl⟩
    simp only [bsucc, Bud.BFin.injEq] at Ha
    subst Ha
    have Hca := FamDrd img dok kind HF Hlat Hnf
    have HnoRmwK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (n' : Nat),
          (AxOpsem.grow GD i)[kk]? = some lb → aident lb = .IRmw aq rl base n' → ¬ dok base n'⌝ := by
      intro GD Hc
      refine (BI.and_intro (HG GD Hc) (HnoRmwW Hkd GD Hc)).trans ?_
      iintro ⟨%HGD, %Hw⟩
      ipureintro
      intro lb aq rl base n' Hlb Hid
      have E : (AxOpsem.grow GD i).length = kk + (b' + 1) := Hb GD HGD
      exact Hw kk lb aq rl base n' Hk0 (by omega) Hlb Hid
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢ FldM rvwmoCatConsistent dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodeP rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) HnoRmwK Hdev Hlat Hnf Hdok) $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd vs) ⊢
        CResK dok kind i Out k0 (.CLd vs) (kk + 1) := .rfl
    iapply (IH vs Hlen (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk (.BFin b') Hb)
      (by omega)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cDwr b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro _ rs ib kk Hag Hb Hk0
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢ FstM rvwmoCatConsistent dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResK dok kind i Out k0 (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r))
          (kk + 1) := .rfl
    iapply (IH (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cFence d b r bk k t Hpark _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdFenceNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc bk k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH (PFFence img dok kind HPF) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    -- THE EXCLUSIVE READ: positioned inside the window
    intro HPF rs ib kk Hag Hb Hk0
    obtain ⟨a, Ha, HF⟩ := HPF rfl
    simp only at Ha
    subst Ha
    have Hca := FamXrd img dok kind HF Hlat
    have HnoSplitK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
          (AxOpsem.grow GD i)[kk]? = some lb → aident lb = .IRead aq base n' → ¬ dok base n'⌝ := by
      intro GD Hc
      refine (BI.and_intro (HG GD Hc) (HnoSplitW Hkd GD Hc)).trans ?_
      iintro ⟨%HGD, %Hw⟩
      ipureintro
      intro lb aq base n' Hlb Hid
      have E : (AxOpsem.grow GD i).length = kk + a := Hb GD HGD
      exact Hw kk lb aq base n' Hk0 (by omega) Hlb Hid
    iintro Hd C
    iapply (wpdXrdNodeP rvwmoCatConsistent dok i Φ cpu G HG Hmid n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) HnoSplitK Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA'
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢
        CResK dok kind i Out k0 (.CRmwR (classify req.access_kind).akSync vs) kk := by
      subst Hkd
      exact .rfl
    ihave Hd := hconv $$ Hd
    iapply (IH vs Hlen (fun h => by cases h) rs' ib kk HA' Hb Hk0) $$ Hd C
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro _ rs ib kk Hag Hb Hk0
    have hconv : CResK dok kind i Out k0 (.CRmwR aq rvs) kk ⊢
        FstM rvwmoCatConsistent dok i Out := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdXwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResK dok kind i Out k0 (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cIa s n w k t Hsf _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH (PFSil' img dok kind HPF (fun _ _ H => Or.elim H And.right
        (fun h => absurd (Hsf.symm.trans h.1) Bool.false_ne_true))) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
  | cSf d b r n w k t Hsf _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxCert2.wpdSfNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc n w k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
    iintro %rs' %ib' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH (AxCertP2.PFSf img dok kind Hsf HPF) rs' ib' (kk + 1) HA' (bposSucc G i kk b Hb)
      (by omega)) $$ Hd C
  | cBa s _ _ k t _ IH | cCo s _ k t _ IH | cTl s _ k t _ IH | cTe s _ k t _ IH
  | cRx s _ k t _ IH | cTs s _ k t _ IH | cTx s _ k t _ IH | cCc s k t _ IH
  | cMsg s _ k t _ IH | cGcc s k t _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ _ ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH (PFSil' img dok kind HPF (fun _ _ H => H)) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C

include HG Hmid Htext Hflow Hloc HnoRmwW HnoSplitW in
theorem AxCertP2.wpdInstrOfCertP (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile)
    (s : Athread) (Hs : RetX cpu rs k0 s)
    (Hbp : AxCert2.bpos G i k0 s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k0 s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s0 (riscvStep tick) t)
    (HPF : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       PF img dok kind c s0 (riscvStep tick) t) :
    ⊢ CResK dok kind i Out k0 s0.csD k0 -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResK dok kind i Out k0 s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M rvwmoCatConsistent i Φ cpu G HG rs k0 s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (AxCertP2.wpdOfCertP img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc Out k0 c HnoRmwW
    HnoSplitW Q _ s0 ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag))
    (HPF tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k0
    (regsAgreeRefl _ _) Hbp (Nat.le_refl _)) $$ Hd
  iintro %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' %_ Hd
  iapply C $$ %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' Hd

end bridgeP

end Weak
