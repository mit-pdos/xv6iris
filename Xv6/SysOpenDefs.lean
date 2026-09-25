/-
**THE OPEN FAMILY'S STATEMENT LEAF (partial): the omode readings, the two
abstract-state commits sys_open fires, the trunc piece's guard, and the
descriptor receipt.**  A PARTIAL port of Rocq `SysOpenDefs.v`
(`/shared/xv6rocq/iris/SysOpenDefs.v`, 777 lines).  Definitions and small
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
* from 2e', the PURE receipt `open_fd_rcpt`.

DEFERRED (appended later by a worktree agent -- rule 1 of the brief; the
FsAbsOpenFire precedent):
* `aopen_commit_at_pinned`, `atrunc_commit_at_pinned`: they read FsAbs.v's
  iProp half (`nview`, `mkf_auth_nview`), deferred by D15.  Consumers
  (grep of /shared/xv6rocq/iris, comments stripped): the stable add-ons
  only (`SpecSysMknod` / FsAbsInvFire's pinned families); no kernel proof.
* 2c `namei_walk_pre_era` / `namei_walk_dead_era`: need `FsAbsEra`
  (`elend`, `ax_hops_from`, `um_start_of`) -- after E0.
* 2d / 2d' the four AU bundles `open_au_pre_plain/create`,
  `open_au_plain_at/create_at` and their `_inst` / `_of_all` lemmas: need
  `FsAbsEra` (`ex_start`/`ep_start`), `FsAbsMknodFire`
  (`acre_commit_at`, `dlookup_commit_at`), `FsAbsCreateFire`
  (`cre_child_unfired`) and `ArgPath` -- after E0 / C-A (and E1 for
  `ep_start`).
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
   `open_fd_rcpt` → `openFdRcpt`); lemma names camel head, Rocq snake tail.

## Dropped/simplified vs Rocq

Nothing dropped; everything not listed as ported is DEFERRED above.
-/
import Xv6.SysWriteDefs
import Xv6.AppInv
import Xv6.PieceFam
import Xv6.FileDefs

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
