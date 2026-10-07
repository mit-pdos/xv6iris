/-
Weak: the second half of the `AxLdgSeal` validation (Lean-only split of
`iris/AxLdgSealArith.v`: one file elaborated in ~260 s): and / or, addiw, slt, the
full-seal add, the tick = true and three-symbol addi ledgers, and the WPds.  Header, deviations
and name map: `Weak.AxLdgSealArith`.
-/
import Weak.AxLdgSealArith

namespace Weak
open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

set_option maxHeartbeats 4000000 in
theorem ldgAnd : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vsAnd
    (PRegs [⟨.x7, rfl⟩]) (postRr (· &&& ·)) := by
  ax_ldg_seal_solve (unfold postRr execute_RTYPE) (ax_ldg_seal_alu)

set_option maxHeartbeats 4000000 in
theorem ldgOr : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vsOr
    (PRegs [⟨.x7, rfl⟩]) (postRr (· ||| ·)) := by
  ax_ldg_seal_solve (unfold postRr execute_RTYPE) (ax_ldg_seal_alu)

/-! # Coverage beyond the target set: addiw (32-bit wrap + sign extension of a symbolic result)
and slt (a data-only comparison), with `ax_ldg_seal_all`. -/

/-- addiw x6,x5,7 -/
def vsAddiw : List (BitVec 8) := [0x1B#8, 0x83#8, 0x72#8, 0x00#8]
/-- slt x7,x5,x6 -/
def vsSlt : List (BitVec 8) := [0xB3#8, 0xA3#8, 0x62#8, 0x00#8]

def postAddiw : List (BitVec 64) → RegFile → Bool
  | [x] => ldgPost (pcA + 4)
      [(⟨.x6, rfl⟩, ((sign_extend (m := 64)
          (Sail.BitVec.extractLsb (x + sign_extend (m := 64) (imm12 7)) 31 0)).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgAddiw : LdgFacts probeMem baseA [⟨.x5, rfl⟩] (AOf baseA pcA vsAddiw) DrLdg DwLdg DLdg
    pcA vsAddiw (PRegs [⟨.x6, rfl⟩]) postAddiw := by
  ax_ldg_seal_solve (unfold postAddiw execute_ADDIW) (ax_ldg_seal_all)

def postSlt : List (BitVec 64) → RegFile → Bool
  | [x, y] => ldgPost (pcA + 4)
      [(⟨.x7, rfl⟩, ((zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgSlt : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vsSlt
    (PRegs [⟨.x7, rfl⟩]) postSlt := by
  ax_ldg_seal_solve (unfold postSlt execute_RTYPE) (ax_ldg_seal_all)

set_option maxHeartbeats 4000000 in
/-- The full seal set also closes the target class (add shown). -/
theorem ldgAddAll : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA
    vsAdd (PRegs [⟨.x7, rfl⟩]) (postRr (· + ·)) := by
  ax_ldg_seal_solve (unfold postRr execute_RTYPE) (ax_ldg_seal_all)

/-! # tick = true, with the retire/timer counters also symbolic -/

noncomputable def AAddiT : List Register := AOfT true baseA pcA vsAddi

def postAddi3 : List (BitVec 64) → RegFile → Bool
  | [x, _, _] => ldgPost (pcA + 4) [(⟨.x6, rfl⟩, ((x + sx 7).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgAddiTick : LdgFactsT probeMem baseA [⟨.x5, rfl⟩, ⟨.minstret, rfl⟩, ⟨.mcycle, rfl⟩]
    AAddiT DrLdg DwLdg DLdg pcA vsAddi (PRegs [⟨.x6, rfl⟩]) postAddi3 := by
  ax_ldg_seal_solve_tick (unfold postAddi3 execute_ITYPE) (ax_ldg_seal_alu)

set_option maxHeartbeats 4000000 in
/-- tick = false with `minstret`/`mip` symbolic too (the caller then need not match the
counters, cf. `AxEpiCjrFrame.tFrame`). -/
theorem ldgAddi3 : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.minstret, rfl⟩, ⟨.mip, rfl⟩] AAddi
    DrLdg DwLdg DLdg pcA vsAddi (PRegs [⟨.x6, rfl⟩]) postAddi3 := by
  ax_ldg_seal_solve (unfold postAddi3 execute_ITYPE) (ax_ldg_seal_alu)

theorem postAddi3Local (xs : List (BitVec 64)) : postLocal (PRegs [⟨.x6, rfl⟩]) (postAddi3 xs) := by
  match xs with
  | [] => exact postLocalFalse _
  | [_] => exact postLocalFalse _
  | [_, _] => exact postLocalFalse _
  | [_, _, _] => exact ldgPostLocal _ [(_, _)]
  | _ :: _ :: _ :: _ :: _ => exact postLocalFalse _

theorem postAddi3Spec (x a b : BitVec 64) (rs : RegFile) :
    postAddi3 [x, a, b] rs = true ↔
      obs64 AxLdgSeal.pcR rs = pcA + 4 ∧
        obs64 ⟨.x6, rfl⟩ rs = ((x.toNat : Int) + 7) % 2 ^ 64 := by
  simp only [postAddi3, ldgPostSpec, List.mem_singleton, forall_eq, addVecUnsigned,
    AxLdgSealArith.sx7]

/-! # The WPds -/

section wpd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- addi x6,x5,7 for EVERY value of x5 (= the caller's own `rs .x5`): PC = pc+4 ∧
x6 = (x5 + 7) mod 2^64 (`postAddiSpec`). -/
theorem wpdAddiSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsAddi⌝)
    (rs : RegFile)
    (Hag : agreeOn (AAddi.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postAddi [rs .x5]) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsAddi cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdLdg i Φ cpu ib kk probeMem baseA [⟨.x5, rfl⟩] _ _ _ _ _ _ _ postAddi ldgAddi postAddiLocal
    Hgd rs Hag

/-- addi, tick = true, counters free. -/
theorem wpdAddiSymTick (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsAddi⌝)
    (rs : RegFile)
    (Hag : agreeOn (AAddiT.filter fun r =>
      !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.minstret, rfl⟩, ⟨.mcycle, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 =>
            postAddi3 (lookups rs [⟨.x5, rfl⟩, ⟨.minstret, rfl⟩, ⟨.mcycle, rfl⟩]) rs3 = true)
            kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerCjrtInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsAddi cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ :=
  wpdLdgTick i Φ cpu ib kk probeMem baseA _ _ _ _ _ _ _ _ postAddi3 ldgAddiTick postAddi3Local
    Hgd rs Hag

/-- add / sub / and / or x7,x5,x6: `f` is the model's operation. -/
theorem wpdRrSym (f : BitVec 64 → BitVec 64 → BitVec 64) (vs : List (BitVec 8))
    (F : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vs
      (PRegs [⟨.x7, rfl⟩]) (postRr f))
    (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vs⌝)
    (rs : RegFile)
    (Hag : agreeOn (ARr.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postRr f (lookups rs [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdLdg i Φ cpu ib kk probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] _ _ _ _ _ _ _ (postRr f) F
    (postRrLocal f) Hgd rs Hag

/-- Rocq `wpd_add_sym` (deviation 3). -/
theorem wpdAddSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsAdd⌝)
    (rs : RegFile)
    (Hag : agreeOn (ARr.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postRr (· + ·) (lookups rs [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsAdd cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdRrSym _ vsAdd ldgAdd i Φ cpu ib kk Hgd rs Hag

/-- Rocq `wpd_sub_sym` (deviation 3). -/
theorem wpdSubSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsSub⌝)
    (rs : RegFile)
    (Hag : agreeOn (ARr.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postRr (· - ·) (lookups rs [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsSub cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdRrSym _ vsSub ldgSub i Φ cpu ib kk Hgd rs Hag

/-- Rocq `wpd_and_sym` (deviation 3). -/
theorem wpdAndSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsAnd⌝)
    (rs : RegFile)
    (Hag : agreeOn (ARr.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postRr (· &&& ·) (lookups rs [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsAnd cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdRrSym _ vsAnd ldgAnd i Φ cpu ib kk Hgd rs Hag

/-- Rocq `wpd_or_sym` (deviation 3). -/
theorem wpdOrSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsOr⌝)
    (rs : RegFile)
    (Hag : agreeOn (ARr.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postRr (· ||| ·) (lookups rs [⟨.x5, rfl⟩, ⟨.x6, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsOr cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdRrSym _ vsOr ldgOr i Φ cpu ib kk Hgd rs Hag

theorem wpdCaddiSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcC vsCaddi⌝)
    (rs : RegFile)
    (Hag : agreeOn (ACaddi.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩])) rs baseC) :
    ⊢ ((∀ s', ⌜RetS cpu (postCaddi (lookups rs [⟨.x5, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsCaddi cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdLdg i Φ cpu ib kk probeMem baseC [⟨.x5, rfl⟩] _ _ _ _ _ _ _ postCaddi ldgCaddi
    postCaddiLocal Hgd rs Hag

theorem wpdSlliSym (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pcA vsSlli⌝)
    (rs : RegFile)
    (Hag : agreeOn (AAddi.filter fun r => !decide (r ∈ syms [⟨.x5, rfl⟩])) rs baseA) :
    ⊢ ((∀ s', ⌜RetS cpu (postSlli (lookups rs [⟨.x5, rfl⟩])) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ DrLdg DwLdg DLdg vsSlli cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdLdg i Φ cpu ib kk probeMem baseA [⟨.x5, rfl⟩] _ _ _ _ _ _ _ postSlli ldgSlli
    postSlliLocal Hgd rs Hag

end wpd

end Weak