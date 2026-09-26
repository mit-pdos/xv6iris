/-
**THE KEYED TRUNC COMMIT AND ITS PERMITS** (Rocq `SysOpenDefs.v` §2b'/2b'',
`/shared/xv6rocq/iris/SysOpenDefs.v` at `1900b8a43`, lanes F-OPEN-2/3/6 and
TRUNC-PERMIT): the part of that family that does NOT change the landed
`openTruncPiece`.

Rocq's section note, abridged: the trunc commit used to be NOT keyed at the
opened inum, because no inum exists to name at SUPPLY time.  That is true
of the supply and false of the FIRE: a constraining application cannot step
a truncate at an inum it cannot identify.  So the piece arrives KEYED, on
`aunarmOfArm`'s mould: a PERMIT naming the inum goes in, the commit AT THAT
INUM comes out, and whatever the application parked in the permit rides
into the fire.  `atruncCommitI` is `atruncCommitAt` with `i` an INDEX,
`atruncOfPermit` the keyed family.  The plain surface pays its walk's
TERMINAL cursor (`truncTermAt`/`truncTermArg`); the O_CREATE surface pays
the walk's TIE (`truncTieAt`/`truncTieArg`: the last element of the path is
`nm`, the parent cursor is at `d`) beside the DISJUNCTION create's two arms
pay from (`truncPermitOf`; the EXISTS branch alone is `truncPermitEx`).
Once the inum is known the piece travels as `openTruncAt`, and the permit
is recoverable from its refund side (`creFtKept`).

A NEW FILE (not appended to `SysOpenDefs`): the family is self-contained,
and Rocq's `SysOpenDefs.v` places it between definitions this port keeps
in `SysOpenDefs.lean` only because Rocq has one file per module.

## Deviations from Rocq

1. Vocabulary as `SysOpenDefs` deviations 2 and 7: inums `Nat`,
   `Γ.top ↪●MAP{½} I`, `RegMapF FsNode`; the image and pointer of the
   syscall-tier readings are `ArgPath`'s (`M : Nat → List (BitVec 8)`,
   `pv : Nat`).  `list_basics.last` is `List.getLast?`; `MkPfam r f` is
   `⟨r, f⟩`.
2. Names: camel head, Rocq's snake tail (`atrunc_commit_i` →
   `atruncCommitI`, `atrunc_commit_i_of_at` → `atruncCommitI_of_at`,
   `trunc_term_arg_of_at` → `truncTermArg_of_at`, `trunc_permit_of_ex` →
   `truncPermitOf_ex`, `open_trunc_at_kept_mono` → `openTruncAt_kept_mono`,
   `cre_ft_kept` → `creFtKept`, …).

## Deferred (not dropped): the keyed `open_trunc_piece` (lane K6)

Rocq's `open_trunc_piece Γ vom Kt Ft` takes the permit family `Kt`
(TRUNC-PERMIT / F-OPEN-3); the landed `SysOpenDefs.openTruncPiece Γ vom Ft`
predates it and is threaded through `SpecSysOpen` and the sys_open proof.
So `open_trunc_piece_of_all`, `_mono`, `_arg_to_at`, `_at_to_arg`,
`_term_arg_to_at`, `_term_at_to_arg`, `open_trunc_at_of_permit`,
`open_trunc_at_of_permit_at` (and the `_true`/`_false`/`_none` restatements
at `Kt`) land with that re-spec.

## Dropped/simplified vs Rocq

Nothing.
-/
import Xv6.SysOpenDefs
import Xv6.SysMknodDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

section TruncPermit
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsTopG GF] [Appcfg GF]

/-! ## The keyed commit -/

/-- Rocq `atrunc_commit_i`: `atruncCommitAt` with `i` an INDEX. -/
def atruncCommitI (Γ : FsViewNames GF) (E : CoPset) (i : Nat)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (I : RegMapF FsNode) (bs0 : List (BitVec 8)) (nl : Nat),
    ⌜arowAt (absView I) i ⟨.AFile bs0, nl⟩⌝ -∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ={E}=∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ∗
      appStep i I (deltaTrunc i (absView I)) ∗
      (∀ I' : RegMapF FsNode,
        ⌜absView I' = deltaTrunc i (absView I)⌝ -∗
        (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I') ={E}=∗
        (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I') ∗ Φ (absView I) i bs0))

/-- Rocq `atrunc_commit_i_of_at`. -/
theorem atruncCommitI_of_at (Γ : FsViewNames GF) (E : CoPset) (i : Nat)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) :
    atruncCommitAt Γ E Φ ⊢ atruncCommitI Γ E i Φ := by
  unfold atruncCommitAt atruncCommitI
  iintro H %I %bs0 %nl %hpre Hka
  iapply H $$ %I %i %bs0 %nl %hpre Hka

/-- Rocq `atrunc_commit_at_of_i`. -/
theorem atruncCommitAt_of_i (Γ : FsViewNames GF) (E : CoPset)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) :
    iprop(∀ i : Nat, atruncCommitI Γ E i Φ) ⊢ atruncCommitAt Γ E Φ := by
  unfold atruncCommitAt atruncCommitI
  iintro H %I %i %bs0 %nl %hpre Hka
  iapply H $$ %i %I %bs0 %nl %hpre Hka

/-- Rocq `atrunc_of_permit`: THE KEYED PIECE, on `aunarmOfArm`'s mould. -/
def atruncOfPermit (Γ : FsViewNames GF) (E : CoPset) (Kt : Nat → IProp GF)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ i : Nat, Kt i -∗ atruncCommitI Γ E i Φ)

/-- Rocq `atrunc_of_permit_of_all`: a caller that can answer at EVERY file
row answers at the permitted one and drops the permit. -/
theorem atruncOfPermit_of_all (Γ : FsViewNames GF) (E : CoPset) (Kt : Nat → IProp GF)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) :
    atruncCommitAt Γ E Φ ⊢ atruncOfPermit Γ E Kt Φ := by
  unfold atruncOfPermit
  iintro H %i _
  iapply (atruncCommitI_of_at Γ E i Φ) $$ H

/-- Rocq `atrunc_of_permit_unit` (at any `Γ`, `SysOpenDefs` deviation 3). -/
theorem atruncOfPermit_unit (Γ : FsViewNames GF) (E : CoPset) (Kt : Nat → IProp GF) :
    appSup (GF := GF) ⊢ atruncOfPermit Γ E Kt (fun _ _ _ => iprop(True)) := by
  iintro #Hsup
  iapply (atruncOfPermit_of_all Γ E Kt _)
  iapply (atruncCommitAt_unit Γ E) $$ Hsup

/-- Rocq `trunc_permit_cre`: THE CREATE'S OWN RECEIPT, AS A PERMIT. -/
def truncPermitCre (Fok : Pfam GF (Aview → Nat → Fname → Nat → IProp GF)) (i : Nat) :
    IProp GF :=
  iprop(∃ (d : Nat) (nm : Fname), creAcreFired Fok d nm i (.AFile []))

end TruncPermit

/-! ## The cursor permits (plain surface: the terminal; O_CREATE: the tie) -/

section TruncCursor
variable {GF : BundledGFunctors}

/-- Rocq `trunc_term_at`: the walk's terminal cursor, bare at the ONE-PATH
tier. -/
def truncTermAt (pl : List (BitVec 8)) (P : Nat → Nat → IProp GF) (i : Nat) : IProp GF :=
  P (pathElems pl).length i

/-- Rocq `trunc_term_arg`: ...and under the reading of argument 0. -/
def truncTermArg (M : Nat → List (BitVec 8)) (pv : Nat) (P : Nat → Nat → IProp GF) (i : Nat) :
    IProp GF :=
  iprop(∀ pl : List (BitVec 8), ⌜argPathOf M pv pl⌝ -∗ P (pathElems pl).length i)

/-- Rocq `trunc_term_arg_of_at`. -/
theorem truncTermArg_of_at (M : Nat → List (BitVec 8)) (pv : Nat) (pl : List (BitVec 8))
    (P : Nat → Nat → IProp GF) (i : Nat) (hpl : argPathOf M pv pl) :
    truncTermAt pl P i ⊢ truncTermArg M pv P i := by
  unfold truncTermAt truncTermArg
  iintro HP %pl' %hpl'
  rw [argPathOf_uniq M pv pl' pl hpl' hpl]
  iexact HP

/-- Rocq `trunc_term_at_of_arg`. -/
theorem truncTermAt_of_arg (M : Nat → List (BitVec 8)) (pv : Nat) (pl : List (BitVec 8))
    (P : Nat → Nat → IProp GF) (i : Nat) (hpl : argPathOf M pv pl) :
    truncTermArg M pv P i ⊢ truncTermAt pl P i := by
  unfold truncTermAt truncTermArg
  iintro H
  iapply H $$ %pl %hpl

/-- Rocq `trunc_tie_at`: the tie at the ONE-PATH tier. -/
def truncTieAt (pl : List (BitVec 8)) (P : Nat → Nat → IProp GF) (d : Nat) (nm : Fname) :
    IProp GF :=
  iprop(⌜(pathElems pl).getLast? = some nm⌝ ∗ P (nparElems pl).length d)

/-- Rocq `trunc_tie_arg`: ...and at the SYSCALL tier. -/
def truncTieArg (M : Nat → List (BitVec 8)) (pv : Nat) (P : Nat → Nat → IProp GF) (d : Nat)
    (nm : Fname) : IProp GF :=
  iprop((∀ pl : List (BitVec 8), ⌜argPathOf M pv pl⌝ -∗ ⌜(pathElems pl).getLast? = some nm⌝) ∗
    nparCur M pv P d)

/-- Rocq `trunc_tie_arg_of_at`. -/
theorem truncTieArg_of_at (M : Nat → List (BitVec 8)) (pv : Nat) (pl : List (BitVec 8))
    (P : Nat → Nat → IProp GF) (d : Nat) (nm : Fname) (hpl : argPathOf M pv pl) :
    truncTieAt pl P d nm ⊢ truncTieArg M pv P d nm := by
  unfold truncTieAt truncTieArg
  iintro ⟨%hlast, HP⟩
  isplitr
  · iintro %pl' %hpl'
    rw [argPathOf_uniq M pv pl' pl hpl' hpl]
    ipureintro
    exact hlast
  · iapply (nparCur_intro M pv pl P d hpl) $$ HP

/-- Rocq `trunc_tie_at_of_arg`. -/
theorem truncTieAt_of_arg (M : Nat → List (BitVec 8)) (pv : Nat) (pl : List (BitVec 8))
    (P : Nat → Nat → IProp GF) (d : Nat) (nm : Fname) (hpl : argPathOf M pv pl) :
    truncTieArg M pv P d nm ⊢ truncTieAt pl P d nm := by
  unfold truncTieAt truncTieArg
  iintro ⟨Hl, HP⟩
  isplitl [Hl]
  · iapply Hl $$ %pl %hpl
  · iapply (nparCur_elim M pv pl P d hpl) $$ HP

end TruncCursor

/-! ## The O_CREATE surface's permit -/

section TruncPermitOf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsTopG GF] [Appcfg GF]

/-- Rocq `trunc_permit_of`: the tie beside the DISJUNCTION create's two arms
pay from -- the FRESH run's fired create receipt, or the EXISTS run's fired
observation BESIDE the unfired arm piece. -/
def truncPermitOf (Γ : FsViewNames GF) (T : Nat → Fname → IProp GF)
    (Farm : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF)) (i : Nat) : IProp GF :=
  iprop(∃ (d : Nat) (nm : Fname), T d nm ∗
    (creAcreFired Fok d nm i (.AFile []) ∨
      (creExFired Fex d nm i ∗ pfAt (aarmCommitAt (hlc := hlc) Γ appE (.AFile [])) Farm)))

/-- Rocq `trunc_permit_of_mono`: the permit moves with its tie. -/
theorem truncPermitOf_mono (Γ : FsViewNames GF) (T T' : Nat → Fname → IProp GF)
    (Farm : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF)) (i : Nat) :
    ⊢ iprop(□ (∀ (d : Nat) (nm : Fname), T d nm -∗ T' d nm)) -∗
      truncPermitOf (hlc := hlc) Γ T Farm Fok Fex i -∗
      truncPermitOf (hlc := hlc) Γ T' Farm Fok Fex i := by
  unfold truncPermitOf
  iintro #Hmv ⟨%d, %nm, HT, Hrest⟩
  iexists d, nm
  isplitl [HT]
  · iapply Hmv $$ %d %nm HT
  · iexact Hrest

/-- Rocq `trunc_permit_ex`: THE EXISTS BRANCH ALONE (lane F-OPEN-6). -/
def truncPermitEx (Γ : FsViewNames GF) (T : Nat → Fname → IProp GF)
    (Farm : Pfam GF (Aview → Nat → IProp GF))
    (Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF)) (i : Nat) : IProp GF :=
  iprop(∃ (d : Nat) (nm : Fname), T d nm ∗ creExFired Fex d nm i ∗
    pfAt (aarmCommitAt (hlc := hlc) Γ appE (.AFile [])) Farm)

/-- Rocq `trunc_permit_of_ex`: the branch-specific permit IS a permit. -/
theorem truncPermitOf_ex (Γ : FsViewNames GF) (T : Nat → Fname → IProp GF)
    (Farm : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF)) (i : Nat) :
    truncPermitEx (hlc := hlc) Γ T Farm Fex i ⊢ truncPermitOf (hlc := hlc) Γ T Farm Fok Fex i := by
  unfold truncPermitEx truncPermitOf
  iintro ⟨%d, %nm, HT, Hex, Harm⟩
  iexists d, nm
  iframe HT
  iright
  iframe Hex Harm

/-! ## The piece once the inum is known -/

/-- Rocq `open_trunc_at`: the trunc piece KEYED at the inum the call
reached, owed only when the code truncates. -/
def openTruncAt (Γ : FsViewNames GF) (vom : BitVec 64) (i : Nat)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  if omTrunc vom then pfAt (atruncCommitI (hlc := hlc) Γ appE i) Ft else iprop(emp)

/-- Rocq `cre_ft_kept`: the permit is RECOVERABLE from the keyed piece's
refund side. -/
def creFtKept (Kt : Nat → IProp GF) (i : Nat)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF) :=
  ⟨Ft.pfRecv, iprop(Ft.pfRefund ∗ Kt i)⟩

/-- Rocq `open_trunc_at_true`. -/
theorem openTruncAt_true (Γ : FsViewNames GF) (vom : BitVec 64) (i : Nat)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = true) :
    openTruncAt (hlc := hlc) Γ vom i Ft ⊣⊢ pfAt (atruncCommitI (hlc := hlc) Γ appE i) Ft := by
  unfold openTruncAt; rw [if_pos hv]; exact .rfl

/-- Rocq `open_trunc_at_false`. -/
theorem openTruncAt_false (Γ : FsViewNames GF) (vom : BitVec 64) (i : Nat)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = false) :
    openTruncAt (hlc := hlc) Γ vom i Ft ⊣⊢ iprop(emp) := by
  unfold openTruncAt; rw [if_neg (by simp [hv])]; exact .rfl

/-- Rocq `open_trunc_at_none`. -/
theorem openTruncAt_none (Γ : FsViewNames GF) (vom : BitVec 64) (i : Nat)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = false) :
    ⊢ openTruncAt (hlc := hlc) Γ vom i Ft := by
  unfold openTruncAt; rw [if_neg (by simp [hv])]; exact .rfl

/-- Rocq `open_trunc_at_kept_mono`: the keyed piece is MONOTONE IN THE
PERMIT IT REFUNDS. -/
theorem openTruncAt_kept_mono (Γ : FsViewNames GF) (vom : BitVec 64) (Kt Kt' : Nat → IProp GF)
    (i : Nat) (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢ (Kt' i -∗ Kt i) -∗ openTruncAt (hlc := hlc) Γ vom i (creFtKept Kt' i Ft) -∗
      openTruncAt (hlc := hlc) Γ vom i (creFtKept Kt i Ft) := by
  unfold openTruncAt
  by_cases hv : omTrunc vom = true
  · simp only [if_pos hv]
    unfold pfAt creFtKept
    dsimp only
    iintro Hmv H
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, ⟨Hr, Hk⟩⟩
      iframe Hr
      iapply Hmv $$ Hk
  · simp only [if_neg hv]
    iintro _ H
    iexact H

/-- Rocq `open_trunc_at_kept_forget`: a consumer that does not fire the
commit may drop the permit its refund carries. -/
theorem openTruncAt_kept_forget (Γ : FsViewNames GF) (vom : BitVec 64) (Kt : Nat → IProp GF)
    (i : Nat) (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    openTruncAt (hlc := hlc) Γ vom i (creFtKept Kt i Ft) ⊢ openTruncAt (hlc := hlc) Γ vom i Ft := by
  unfold openTruncAt
  by_cases hv : omTrunc vom = true
  · simp only [if_pos hv]
    unfold pfAt creFtKept
    dsimp only
    iintro H
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, ⟨Hr, -⟩⟩
      iexact Hr
  · simp only [if_neg hv]
    exact .rfl

/-- Rocq `open_trunc_at_kept_intro`: a keyed piece takes a permit onto its
refund side for nothing. -/
theorem openTruncAt_kept_intro (Γ : FsViewNames GF) (vom : BitVec 64) (Kt : Nat → IProp GF)
    (i : Nat) (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢ openTruncAt (hlc := hlc) Γ vom i Ft -∗ (if omTrunc vom then Kt i else iprop(emp)) -∗
      openTruncAt (hlc := hlc) Γ vom i (creFtKept Kt i Ft) := by
  unfold openTruncAt
  by_cases hv : omTrunc vom = true
  · simp only [if_pos hv]
    unfold pfAt creFtKept
    dsimp only
    iintro H Hk
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, H⟩
      iframe H Hk
  · simp only [if_neg hv]
    iintro H _
    iexact H

end TruncPermitOf

end Xv6
