/-
**THE OPEN FAMILY'S STATEMENT LEAF (partial): the omode readings, the two
abstract-state commits sys_open fires, the trunc piece's guard, the era
walk package and the AU bundles, and the descriptor receipt.**  A PARTIAL
port of Rocq `SysOpenDefs.v` (`/shared/xv6rocq/iris/SysOpenDefs.v`, 777
lines).  Definitions and small
structural lemmas only -- no arms, no frame, no contract.

## What is here, and what is DEFERRED (wave-7b brief §5.4, batch 7b-0 item O-B)

PORTED:
* section 1 WHOLE: `om_arg` and the four bit readings, the two mode
  booleans, `om_arg_range`, `om_rdonly_modes`, `om_rdwr_modes`,
  `om_rdwr_plain`, and the mint justification `delta_write_no_shrink`
  (`delta_trunc` itself was hoisted to `FsAbsDelta`, as in Rocq);
* 2a `aopen_commit_at` + `aopen_commit_at_unit`;
* 2b `atrunc_commit_at` + `atrunc_commit_at_unit`;
* 2b' `open_trunc_piece` + `_true` / `_false` / `_none`;
* 2c `namei_walk_pre_era` / `namei_walk_dead_era` (APPENDED by worktree
  W-A of wave 7b, after `FsAbsEra` and `FsAbsMknodFire` §5-6 landed);
* 2d / 2d' the four AU bundles `open_au_pre_plain/create`,
  `open_au_plain_at/create_at`, their `_inst` and `_of_all` lemmas (W-A);
* from 2e', the PURE receipt `open_fd_rcpt`.

DEFERRED (appended later by a worktree agent -- rule 1 of the brief; the
FsAbsOpenFire precedent):
* `aopen_commit_at_pinned`, `atrunc_commit_at_pinned`: they read FsAbs.v's
  iProp half (`nview`, `mkf_auth_nview`), deferred by D15.  Consumers
  (grep of /shared/xv6rocq/iris, comments stripped): the stable add-ons
  only (`SpecSysMknod` / FsAbsInvFire's pinned families); no kernel proof.
* 2e `open_fd_frags_any`, `open_fd_ok`, and 2e' `open_fd_ok_split`: they
  state Rocq's whole `proc_priv` block and `fd_frags (pv_fdg ..)` --
  C0's P2 block (brief rule 5 / D16).  **Process-layer: flagged, not
  ported.**  `open_fd_rcpt` (the pure half) IS ported, so the split lands
  as a one-liner beside `open_fd_ok` after C0.

## Deviations from Rocq

1. **`om_arg` is `Nat`** (`v.toNat % 2 ^ 32`) and the bit readings are
   `Nat.testBit` (Rocq: `Z.testbit` of the `Z` reading).  Same values: the
   argument is non-negative.
2. The commits are over the landed Lean vocabulary: `Γ.top ↪●MAP{½} I`
   for `ghost_map_auth (γtop Γ) (1/2) I`, `RegMapF FsNode` for
   `gmap Z fs_node`, inums are `Nat` (FsAbsDefs deviation 1), `appStep` /
   `appStep_acc` / `appE` / `pfAt` / `Pfam` from AppInv / PieceFam.  The
   shapes follow the landed `FsAbsReadFire.areadCommitAt` /
   `FsAbsWriteFire.awriteFullAt`.
3. **`atruncCommitAt_unit` is stated at ANY `Γ`** where Rocq states it at
   `fs_gamma_L γfs`: the proof never reads `Γ` (it pays the step out of
   the supply), so the generic form is the same proof and implies Rocq's.
4. **No `` `{XI : CurCtx} `` binder** anywhere (Rocq's own header says the
   commits must not carry one); `aopen_commit_at_unit`'s unused `XI` is
   dropped with it.
5. `open_fd_rcpt`: `mword_of_int (Z.of_nat fd)` is `BitVec.ofNat 64 fd`,
   `sts !! fd = Some FdClosed` is `sts[fd]? = some .closed`, and the list
   insert `<[fd := FdOpen rb wb t]> sts` is `sts.set fd (.open rb wb t)`
   (stdpp's list insert is a no-op out of range, as `List.set` is).
6. Names camelCased (`om_arg` → `omArg`, `aopen_commit_at` →
   `aopenCommitAt`, `open_trunc_piece` → `openTruncPiece`,
   `namei_walk_pre_era` → `nameiWalkPreEra`, `open_au_pre_plain` →
   `openAuPrePlain`, `open_au_plain_at_inst` → `openAuPlainAt_inst`,
   `open_fd_rcpt` → `openFdRcpt`); lemma names camel head, Rocq snake tail.
7. **2d': the image and the pointer are `ArgPath`'s.**  Rocq's
   `open_au_plain_at`/`_create_at` take `M : gmap Z (bv 8)` and
   `pv : mword 64`; here `M : Nat → List (BitVec 8)` (the per-page user view)
   and `pv : Nat`, because that is what the landed `argPathOf` reads
   (`Xv6/ArgPath.lean` deviations 1-2).  The syscall tier passes the
   trapframe word's `.toNat`.  `cw` (the cwd inum) is `Nat`; `vom` stays
   `BitVec 64`.
8. **2d: `open_au_*_of_all`'s inline walk step is one helper.**  Rocq's
   four `_of_all` proofs each re-do `rewrite /ex_start /namei_walk_pre_era;
   iMod ("Hw" $! pl r …)`.  Here the plain pair calls the private
   `openWalk_start` (the statement of `FsAbsOpenFire.opfStart_of_open`,
   which cannot be called from here: that file imports this one) and the
   create pair calls `FsAbsMknodFire.npStart_of_mknod`.

## Dropped/simplified vs Rocq

Nothing dropped; everything not listed as ported is DEFERRED above.
-/
import Xv6.SysWriteDefs
import Xv6.AppInv
import Xv6.PieceFam
import Xv6.FileDefs
import Xv6.FsAbsMknodFire
import Xv6.ArgPath

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

/-! ## 1.  The omode readings and the trunc delta (pure) -/

/-- The mode-flag reading of syscall argument 1 (Rocq's `om_arg`): argint
keeps the low int, and the C's bit tests read that int's bits -- O_WRONLY =
1, O_RDWR = 2, O_CREATE = 0x200 (bit 9), O_TRUNC = 0x400 (bit 10). -/
def omArg (v : BitVec 64) : Nat := v.toNat % 2 ^ 32

def omWronly (v : BitVec 64) : Bool := (omArg v).testBit 0
def omRdwr (v : BitVec 64) : Bool := (omArg v).testBit 1
def omCreate (v : BitVec 64) : Bool := (omArg v).testBit 9
def omTrunc (v : BitVec 64) : Bool := (omArg v).testBit 10

/-- the two mode booleans the walk stores into the new file, read straight
off the C: `f->readable = !(omode & O_WRONLY)`,
`f->writable = (omode & O_WRONLY) || (omode & O_RDWR)` -/
def omReadable (v : BitVec 64) : Bool := !omWronly v
def omWritable (v : BitVec 64) : Bool := omWronly v || omRdwr v

theorem omArg_range (v : BitVec 64) : omArg v < 2 ^ 32 :=
  Nat.mod_lt _ (by decide)

/-- the dir arm's key is the WHOLE-int equality `omode = O_RDONLY = 0`;
under it the stored modes are read-only-read-write-not (Rocq's
`om_rdonly_modes`) -/
theorem omRdonly_modes (v : BitVec 64) (h : omArg v = 0) :
    omReadable v = true ∧ omWritable v = false := by
  simp only [omReadable, omWritable, omWronly, omRdwr, h]
  decide

/-- init's omode, decoded (Rocq's `om_rdwr_modes`) -/
theorem omRdwr_modes (v : BitVec 64) (h : omArg v = 2) :
    omReadable v = true ∧ omWritable v = true := by
  simp only [omReadable, omWritable, omWronly, omRdwr, h]
  decide

/-- Rocq's `om_rdwr_plain` -/
theorem omRdwr_plain (v : BitVec 64) (h : omArg v = 2) :
    omCreate v = false ∧ omTrunc v = false := by
  simp only [omCreate, omTrunc, h]
  decide

/-- THE MINT JUSTIFICATION (Rocq's `delta_write_no_shrink`): the write delta
cannot express truncation -- a splice never shrinks the file -- so the
trunc delta (`FsAbsDelta.deltaTrunc`) is a NEW total function in
`deltaWrite`'s mold, not a reuse refused. -/
theorem deltaWrite_no_shrink (av : Aview) (i off : Nat) (new bs0 : List (BitVec 8)) (nl : Nat)
    (hi : PartialMap.get? av i = some ⟨.AFile bs0, nl⟩) (hoff : off ≤ bs0.length) :
    ∃ bs1, PartialMap.get? (deltaWrite i off new av) i = some ⟨.AFile bs1, nl⟩ ∧
      bs0.length ≤ bs1.length :=
  ⟨blkSplice off new bs0, deltaWrite_lookup av i off new bs0 nl hi, by
    rw [blkSplice_length_grow off new bs0 hoff]; omega⟩

/-! ## 2.  The commits -/

section OpenDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsTopG GF]

/-! ### 2a.  The observation commit (single-phase, read-only, at the map) -/

/-- THE TERMINAL OBSERVATION (Rocq's `aopen_commit_at`), the single-phase
read-only mold at the WHOLE `Anode`: open without O_CREATE mutates nothing,
so the caller hands the very same authority back and no row obligation
arises.  Fired once, inside the opened node's lock window.  `E` for reuse;
the machine contract instantiates `appE`. -/
def aopenCommitAt (Γ : FsViewNames GF) (E : CoPset) (Φ : Aview → Nat → Anode → IProp GF) :
    IProp GF :=
  iprop(∀ (I : RegMapF FsNode) (i : Nat) (a : Anode),
    ⌜arowAt (absView I) i a⌝ -∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ={E}=∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ∗ Φ (absView I) i a)

/-- satisfiability: the seal cannot be vacuously blocked on the caller
(Rocq's `aopen_commit_at_unit`) -/
theorem aopenCommitAt_unit (Γ : FsViewNames GF) (E : CoPset) :
    ⊢ aopenCommitAt Γ E (fun _ _ _ => iprop(True)) := by
  unfold aopenCommitAt
  iintro %I %i %a %_ Ha
  imodintro
  iframe Ha

/-! ### 2b.  The trunc commit (two-phase, at the map) -/

/-- `acre_commit_at`'s two-phase mold at `deltaTrunc` (Rocq's
`atrunc_commit_at`): phase 1 lends the pre-state (the row IS a file, at the
bytes the receipt names) and hands back THE CALLER'S STEP at the RAW insert
the mover performs; phase 2 is quantified over the post map and constrained
by its READING alone, so the caller witnesses exactly "the row is empty
now" and nothing about the record the mover chose. -/
def atruncCommitAt [Appcfg GF] (Γ : FsViewNames GF) (E : CoPset)
    (Φ : Aview → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (I : RegMapF FsNode) (i : Nat) (bs0 : List (BitVec 8)) (nl : Nat),
    ⌜arowAt (absView I) i ⟨.AFile bs0, nl⟩⌝ -∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ={E}=∗
    (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I) ∗
      appStep i I (deltaTrunc i (absView I)) ∗
      (∀ I' : RegMapF FsNode,
        ⌜absView I' = deltaTrunc i (absView I)⌝ -∗
        (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I') ={E}=∗
        (Γ.top ↪●MAP{DFrac.own (1 : Qp).half} I') ∗ Φ (absView I) i bs0))

/-- satisfiability (Rocq's `atrunc_commit_at_unit`; deviation 3): a
write-kind shape owes the caller's step, which a client that answers for no
abstract state pays out of the SUPPLY (`appStep_acc`). -/
theorem atruncCommitAt_unit [Appcfg GF] (Γ : FsViewNames GF) (E : CoPset) :
    appSup (GF := GF) ⊢ atruncCommitAt Γ E (fun _ _ _ => iprop(True)) := by
  unfold atruncCommitAt
  iintro #Hsup %I %i %bs0 %nl %_ Ha
  ihave Hstep := appStep_acc i I (deltaTrunc i (absView I)) $$ Hsup
  imodintro
  iframe Ha Hstep
  iintro %I' %_ Ha'
  imodintro
  iframe Ha'

/-! ### 2b'.  The trunc piece is owed only when the code truncates -/

/-- sys_open truncates iff `(omode & O_TRUNC) && ip->type == T_FILE`, and the
mode half of that test is decided by the caller's own omode before the walk
runs; so the trunc commit rides the guard `omTrunc vom` (Rocq's
`open_trunc_piece`).  An open without O_TRUNC owes NOTHING here.  THE
COMMIT IS NOT KEYED AT THE OPENED INUM, and that is forced: the bundle is
handed in before argstr runs, and the O_CREATE fresh arm fires it at a
child that went through no hop (Rocq's header, kept). -/
def openTruncPiece [Appcfg GF] (Γ : FsViewNames GF) (vom : BitVec 64)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  if omTrunc vom then pfAt (atruncCommitAt Γ appE) Ft else iprop(emp)

/-- Rocq's `open_trunc_piece_true` -/
theorem openTruncPiece_true [Appcfg GF] (Γ : FsViewNames GF) (vom : BitVec 64)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = true) :
    openTruncPiece Γ vom Ft ⊣⊢ pfAt (atruncCommitAt Γ appE) Ft := by
  unfold openTruncPiece; rw [if_pos hv]; exact .rfl

/-- Rocq's `open_trunc_piece_false` -/
theorem openTruncPiece_false [Appcfg GF] (Γ : FsViewNames GF) (vom : BitVec 64)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = false) :
    openTruncPiece Γ vom Ft ⊣⊢ iprop(emp) := by
  unfold openTruncPiece; rw [if_neg (by simp [hv])]; exact .rfl

/-- ...and the free one (Rocq's `open_trunc_piece_none`): at
`omTrunc vom = false` nothing is owed, so the piece is available out of thin
air -- the whole content of the tightening for init's
`open("console", O_RDWR)`. -/
theorem openTruncPiece_none [Appcfg GF] (Γ : FsViewNames GF) (vom : BitVec 64)
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hv : omTrunc vom = false) :
    ⊢ openTruncPiece Γ vom Ft := by
  unfold openTruncPiece; rw [if_neg (by simp [hv])]; exact .rfl

end OpenDefs

/-! ## 2c.  The walk package (full path; the era hops; quantified start) -/

section OpenWalk
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [FsTopG GF] [FsBytesG GF]

/-- ONE SHOT, instantiated by the walk at the string argstr fetched and at
the inum it starts from (Rocq's `namei_walk_pre_era`):
`FsAbsMknodFire.nparWalkPreEra`'s shape over the FULL element list (open
resolves via namei, not nameiparent).  The start is namex's rule
(`FsAbsEra.umStartOf`): an absolute fetch pins ROOTINO, a relative one
starts at `cw`, the calling process's cwd inum. -/
def nameiWalkPreEra (γfs : FsNames) (cw : Nat) (P Pmiss : Nat → Nat → IProp GF) : IProp GF :=
  iprop(∀ (pl : List (BitVec 8)) (r : Nat), ⌜r = umStartOf cw pl⌝ ={⊤}=∗
    P 0 r ∗ axHopsFrom (elend (fsGammaL γfs)) P Pmiss (pathElems pl) 0)

/-- the walk's death receipt, the era refund shape verbatim (Rocq's
`namei_walk_dead_era`): either hop `k` never fired (non-directory cursor,
or namex's nlink guard) and the cursor comes back with hops from `k`, or it
fired and missed and the miss receipt comes back with hops from `k + 1`.
No context binder: it is what open's and chdir's RECEIPTS carry, read at a
U-mode key (Rocq's note). -/
def nameiWalkDeadEra (γfs : FsNames) (P Pmiss : Nat → Nat → IProp GF) (pl : List (BitVec 8)) :
    IProp GF :=
  iprop(∃ (k d : Nat), ⌜k < (pathElems pl).length⌝ ∗
    ((P k d ∗ axHopsFrom (elend (fsGammaL γfs)) P Pmiss (pathElems pl) k) ∨
     (Pmiss k d ∗ axHopsFrom (elend (fsGammaL γfs)) P Pmiss (pathElems pl) (k + 1))))

/-! ## 2d.  The AU bundles, at ONE path

Everything the caller hands in AT THE PATH IT PASSED.  Each one-shot piece
arrives as its AU conjoined with its own refund (`PieceFam.pfAt`); the
walk's cursor pair `P`/`Pmiss` stays BARE.  THE WALK IS AT ONE PATH
(`FsAbsEra.exStart` at `pl`), not at every path: a caller whose cursor is
PINNED -- a pin is sound at one path -- can hand this in; the `∀ pl` form it
could not.  `FsAbsOpenFire.opfStart_of_open` and `openAuPrePlain_of_all`
below are the one-line bridges from the `∀ pl` form. -/

variable [Appcfg GF]

/-- the PLAIN caller's bundle (Rocq's `open_au_pre_plain`). -/
def openAuPrePlain (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (pl : List (BitVec 8))
    (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  iprop(exStart (hlc := hlc) γfs cw P Pmiss pl ∗
    pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∗ openTruncPiece (hlc := hlc) Γ vom Ft)

/-- ...and the O_CREATE caller's (Rocq's `open_au_pre_create`): the
parent-prefix one-shot at that same path (`FsAbsEra.epStart`), create's
fused delta at the child `AFile []`, the exists observation, open's own two
commits, and create's CHILD legs. -/
def openAuPreCreate (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (pl : List (BitVec 8))
    (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  iprop(epStart (hlc := hlc) γfs cw P Pmiss pl ∗
    pfAt (acreCommitAt (hlc := hlc) Γ appE (.AFile []) Farm) Fok ∗
    pfAt (dlookupCommitAt (hlc := hlc) Γ appE) Fex ∗
    pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∗
    openTruncPiece (hlc := hlc) Γ vom Ft ∗
    creChildUnfired (hlc := hlc) Γ (.AFile []) Farm Fun)

/-! ## 2d'.  The syscall tier: the same bundle under the reading of the
caller's argument 0

sys_open `argstr`s trapframe argument 0 and walks THAT string, so the WALK
PIECE is owed at whatever the image holds there:
`∀ pl, ⌜argPathOf M pv pl⌝ -∗ exStart … pl`.  It is ONE walk -- the reading
is a function of `(M, pv)` (`ArgPath.argPathOf_uniq`).  THE COMMITS STAY
OUTSIDE THE WAND, and that is forced: argstr can fail, and then NO `pl`
satisfies the reading, so a consumer of the failure fold's "nothing
happened" arm could never open a whole-bundle wand to get its commits back
(Rocq's header, kept). -/

/-- Rocq's `open_au_plain_at` (deviation 7 for `M`/`pv`). -/
def openAuPlainAt (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (M : Nat → List (BitVec 8))
    (pv : Nat) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  iprop((∀ pl : List (BitVec 8), ⌜argPathOf M pv pl⌝ -∗ exStart (hlc := hlc) γfs cw P Pmiss pl) ∗
    pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∗ openTruncPiece (hlc := hlc) Γ vom Ft)

/-- Rocq's `open_au_create_at`. -/
def openAuCreateAt (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (M : Nat → List (BitVec 8))
    (pv : Nat) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) : IProp GF :=
  iprop((∀ pl : List (BitVec 8), ⌜argPathOf M pv pl⌝ -∗ epStart (hlc := hlc) γfs cw P Pmiss pl) ∗
    pfAt (acreCommitAt (hlc := hlc) Γ appE (.AFile []) Farm) Fok ∗
    pfAt (dlookupCommitAt (hlc := hlc) Γ appE) Fex ∗
    pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∗
    openTruncPiece (hlc := hlc) Γ vom Ft ∗
    creChildUnfired (hlc := hlc) Γ (.AFile []) Farm Fun)

/-- THE INSTANCE: at the path the syscall actually read, the walk wand
fires and the bundle is the one-path one (Rocq's `open_au_plain_at_inst`). -/
theorem openAuPlainAt_inst (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (M : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64) (pl : List (BitVec 8))
    (P Pmiss : Nat → Nat → IProp GF) (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hpl : argPathOf M pv pl) :
    openAuPlainAt (hlc := hlc) Γ γfs cw M pv vom P Pmiss Fo Ft ⊢
      openAuPrePlain (hlc := hlc) Γ γfs cw pl vom P Pmiss Fo Ft := by
  unfold openAuPlainAt openAuPrePlain
  iintro ⟨Hw, Ho, Ht⟩
  isplitl [Hw]
  · iapply Hw $$ %pl %hpl
  · isplitl [Ho]
    · iexact Ho
    · iexact Ht

/-- Rocq's `open_au_create_at_inst`. -/
theorem openAuCreateAt_inst (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (M : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64) (pl : List (BitVec 8))
    (P Pmiss : Nat → Nat → IProp GF) (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hpl : argPathOf M pv pl) :
    openAuCreateAt (hlc := hlc) Γ γfs cw M pv vom P Pmiss Farm Fun Fok Fex Fo Ft ⊢
      openAuPreCreate (hlc := hlc) Γ γfs cw pl vom P Pmiss Farm Fun Fok Fex Fo Ft := by
  unfold openAuCreateAt openAuPreCreate
  iintro ⟨Hw, Hrest⟩
  isplitl [Hw]
  · iapply Hw $$ %pl %hpl
  · iexact Hrest

omit [Appcfg GF] in
/-- the `∀ pl` walk premise specialised at one path: `exStart` there
(the body `FsAbsOpenFire.opfStart_of_open` states; restated privately
because `FsAbsOpenFire` imports this file). -/
private theorem openWalk_start (γfs : FsNames) (cw : Nat) (P Pmiss : Nat → Nat → IProp GF)
    (pl : List (BitVec 8)) :
    nameiWalkPreEra (hlc := hlc) γfs cw P Pmiss ⊢ exStart (hlc := hlc) γfs cw P Pmiss pl := by
  unfold nameiWalkPreEra exStart
  rw [exHops_is_axHops]
  iintro Hw %r %hr
  iapply Hw $$ %pl %r %hr

/-- THE GENERIC SUPPLIER'S ONE LINE (Rocq's `open_au_plain_at_of_all`): a
family that tracks nothing owes the walk at EVERY string, and that form
instantiates to the one-path bundle. -/
theorem openAuPlainAt_of_all (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (M : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢@{IProp GF} nameiWalkPreEra (hlc := hlc) γfs cw P Pmiss -∗
      pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo -∗ openTruncPiece (hlc := hlc) Γ vom Ft -∗
      openAuPlainAt (hlc := hlc) Γ γfs cw M pv vom P Pmiss Fo Ft := by
  unfold openAuPlainAt
  iintro Hw Ho Ht
  isplitl [Hw]
  · iintro %pl _
    iapply (openWalk_start γfs cw P Pmiss pl) $$ Hw
  · isplitl [Ho]
    · iexact Ho
    · iexact Ht

/-- Rocq's `open_au_create_at_of_all` (the walk leg is
`FsAbsMknodFire.npStart_of_mknod`). -/
theorem openAuCreateAt_of_all (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (M : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢@{IProp GF} nparWalkPreEra (hlc := hlc) γfs cw P Pmiss -∗
      pfAt (acreCommitAt (hlc := hlc) Γ appE (.AFile []) Farm) Fok -∗
      pfAt (dlookupCommitAt (hlc := hlc) Γ appE) Fex -∗
      pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo -∗
      openTruncPiece (hlc := hlc) Γ vom Ft -∗
      creChildUnfired (hlc := hlc) Γ (.AFile []) Farm Fun -∗
      openAuCreateAt (hlc := hlc) Γ γfs cw M pv vom P Pmiss Farm Fun Fok Fex Fo Ft := by
  unfold openAuCreateAt
  iintro Hw Hok Hex Ho Ht Hch
  isplitl [Hw]
  · iintro %pl _
    iapply (npStart_of_mknod γfs cw P Pmiss pl) $$ Hw
  · iframe Hok Hex Ho Ht Hch

/-- Rocq's `open_au_pre_plain_of_all`. -/
theorem openAuPrePlain_of_all (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (pl : List (BitVec 8)) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢@{IProp GF} nameiWalkPreEra (hlc := hlc) γfs cw P Pmiss -∗
      pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo -∗ openTruncPiece (hlc := hlc) Γ vom Ft -∗
      openAuPrePlain (hlc := hlc) Γ γfs cw pl vom P Pmiss Fo Ft := by
  unfold openAuPrePlain
  iintro Hw Ho Ht
  isplitl [Hw]
  · iapply (openWalk_start γfs cw P Pmiss pl) $$ Hw
  · isplitl [Ho]
    · iexact Ho
    · iexact Ht

/-- Rocq's `open_au_pre_create_of_all`. -/
theorem openAuPreCreate_of_all (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat)
    (pl : List (BitVec 8)) (vom : BitVec 64) (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) :
    ⊢@{IProp GF} nparWalkPreEra (hlc := hlc) γfs cw P Pmiss -∗
      pfAt (acreCommitAt (hlc := hlc) Γ appE (.AFile []) Farm) Fok -∗
      pfAt (dlookupCommitAt (hlc := hlc) Γ appE) Fex -∗
      pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo -∗
      openTruncPiece (hlc := hlc) Γ vom Ft -∗
      creChildUnfired (hlc := hlc) Γ (.AFile []) Farm Fun -∗
      openAuPreCreate (hlc := hlc) Γ γfs cw pl vom P Pmiss Farm Fun Fok Fex Fo Ft := by
  unfold openAuPreCreate
  iintro Hw Hok Hex Ho Ht Hch
  isplitl [Hw]
  · iapply (npStart_of_mknod γfs cw P Pmiss pl) $$ Hw
  · iframe Hok Hex Ho Ht Hch

end OpenWalk

/-! ## 2e'.  The descriptor receipt (pure) -/

/-- THE RECEIPT: what open's success is worth to the PROCESS (Rocq's
`open_fd_rcpt`).  It names WHICH descriptor came back (`r`), that the
caller's table had it closed, and that the table it resumes at is the
caller's with that one row retyped at the caller's own mode bits and the
node the walk reached.  The kernel's half (`open_fd_ok`, `proc_priv` at
`us_ofile` and the `fd_frags` bundle) waits on C0's block (header). -/
def openFdRcpt (rb wb : Bool) (t : FdType) (sts : List FdState) (r : BitVec 64)
    (fdv' : List FdState) : Prop :=
  ∃ fd : Nat, r = BitVec.ofNat 64 fd ∧ sts[fd]? = some .closed ∧
    fdv' = sts.set fd (.open rb wb t)

end Xv6
