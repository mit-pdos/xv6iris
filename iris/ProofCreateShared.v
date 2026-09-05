(* ProofCreate.v -- the walk of xv6's create (fs.c): the FOUND half and the
   ALLOCATE half's C-OK-FILE / A-FAIL arms.

     static struct inode*
     create(char *path, short type, short major, short minor)

   332 bytes.  The CFG is [SpecCreate.v]'s header and
   claude-notes/projects/fs-sysfile.md's verified listing; every immediate
   below is taken from [CodeCreate.v]'s own lemma statements and from
   nowhere else.

   ---- WHAT THIS FILE PROVES, AND WHAT IT PARKS -------------------------

   [cr_found_half] is create's contract on the FOUND half: the prologue,
   [nameiparent], ARM N, [ilock(dp)], the [dp->nlink == 0] guard and its
   ARM G, [dirlookup], and the two found arms F-BAD and F-OK -- with the
   whole ALLOCATE half (+0xa2 onward, reached by the [c.beqz] at +0x4c
   being TAKEN) parked behind ONE HYPOTHESIS, [cr_alloc_body].  That
   hypothesis is a PREMISE of the lemma, not an axiom and not an [admit]:
   [Print Assumptions cr_found_half] shows the standing platform six and
   nothing else, and the parked half appears in the STATEMENT.

   The cut is at +0x4c rather than at the failure family because the
   family's ARM FAIL is reached only through ialloc / ilock(ip) / three
   [sh]s / iupdate / dirlink -- i.e. through more code than everything
   before it.  The found half is the increment that stands alone.

   [cr_alloc_half] is the OTHER half, and it discharges [cr_alloc_body]:
   the eighth save at +0xa2, the fresh-type gate span (+0xa4..+0xb0,
   [ProofCreateFreshTy]), ARM A-FAIL (+0xec), the three metadata [sh]s, the
   LINK MINT at +0xc4 ([SpecIupdate.wp_iupdate_link]), the T_DIR branch at
   +0xca, the [dirlink(dp,name)] at +0xd8 and ARM C-OK-FILE (+0xe0..+0xea).
   Two of its branches leave through a PREMISE of their own -- the whole
   T_DIR sub-branch through [cr_mkdir_body] and the failing [dirlink]
   through [cr_fail_body] -- so its [Print Assumptions] is the standing six
   and nothing else.  Its conclusion is
   [wp_next]-wrapped for the reason stated at the lemma: the parked bodies
   and the contract's own continuation are anchored at the SECTION hart,
   and the allocate half runs at whatever hart the +0x4c [c.beqz] rebound
   to, so the entry hart's chain link IS the [wp_next] guard.

   ---- THE PIECES ------------------------------------------------------

   [cr_tail_body]  -- the epilogue funnel at +0x70 ([mv a0,s2], the seven
   restores, the pop, [c.ret]).  FOUR arms of this half reach it (N, G,
   F-BAD, F-OK) and two more will (C-OK, A-FAIL, FAIL), so it is
   [□]-persistent with an ABSTRACT continuation -- ProofDirlookup's shape --
   and speaks only of [cr_tregs] and the ten frame slots.

   [cr_alloc_body] -- the parked gate.  It takes the register file, the pc,
   the parent's [dn]/[bm]/[data] and the ledger triple as ARGUMENTS and
   the contract's own continuation as its last premise (ProofDirlink's
   [dl_after_body] shape), so the allocate half will discharge it as an
   ordinary block lemma and this file hands it [Hcont] unretargeted.

   NO LOOP, so no [∀ fuel] anywhere: create is the first fs whole-function
   walk that is straight-line-with-branches, which is why ProofDirlink and
   not ProofNamex is the model for everything except the guard.

   ---- THE ONE LEDGER SUBTLETY (ARM G) ---------------------------------

   [crz] is UNAVAILABLE ON ARM G BY CONSTRUCTION.  It buys itrunc's
   tail-flush unit with [InodeRegion.nlz_obs], which is minted only at an
   observation that the record's nlink is NONZERO -- and ARM G is the guard
   TAKEN, i.e. [di_nlink dn = 0] observed.  So its [iunlockput(dp)] runs at
   [crb = cru = crz = false] and spends [SpecIput.ip_spend_w w false false
   = ip_bm w + 1 <= 2].  It closes with room because nothing has been
   logged before the guard: the count is [CreateBudget.cr_uw w >= 9]
   against [iput_units = 3], which is [cr_budget_found_w]'s first two
   conjuncts.  The same figure covers ARM F-BAD's two uncredited
   [iunlockput]s.

   ---- SEAM NOTE (GR-2c FINDING 5) -------------------------------------

   Every [iunlockput] on this half reports its credited bound at
   [ip_spend_w w false false], which is STRONGER than the [iput_units = 3]
   the ledger cites.  Each seam weakens once, KEEPING the hypothesis name,
   exactly as ProofDirlink's found arm does.                            *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelText.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioDefs.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DirentEnc.
Require Import BvShift.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import AppInv.       (* [appN], [app_inv]: the suspended child's movers open the application's invariant *)
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecBmap SpecWritei.
Require Import SpecIput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNamex.
Require Import SpecCreate.
(* THE FRESH-TYPE SPAN: the four instructions +0xa4..+0xb0 that pin
   [di_type dn = ty] across [ialloc]/[ilock].  It is a stretch of create's
   OWN body rather than a callee, so it is NOT a functor argument -- the
   statement ([create_fresh_ty_body], spliced verbatim below), the span's
   register contract ([cr_cs_but_s3]) and the proof all live in
   [ProofCreateFreshTy.v], and this file applies [create_fresh_ty] directly,
   handing it [IA]/[IL] for its two callee hypotheses. *)
Require Import ProofCreateFreshTy.
Require Import CodeCreate.
Require Import ProofDirlookupParts ProofNamexParts ProofCreateParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows] / [off_rows_dep] / [off_rows_to_dep] -- the inode's off rows (items 35/36) *)

(* claude-notes/optimization.md "Register maps": the leaves' premises are
   stated over [rget] (see e.g. [cri_*]'s consumers below), so with these
   three transparent every register-chain [iApply]'s unifier walks
   [rget -> tp_pin -> rf_upd] down the whole chain, and [Qed] re-walks it.
   ProofPipewrite.v is the measured instance (its own header): sealing all
   three is a net win on a file of this shape, PROVIDED no site hands a
   leaf a premise spelled with [!!!] where the leaf's statement says
   [rget] -- those used to bridge for free by delta and regress once the
   three are opaque.  Re-measure after sealing; restate any regressed
   premise in the [rget] spelling with [rget_ne] (HartTp.v) right before
   its [iApply], as ProofPipewrite's own three recoveries did. *)
Local Strategy opaque [rget].
Local Strategy opaque [tp_pin].
Local Strategy opaque [rf_upd].

(* claude-notes/durable-notes.md: a syscall-altitude goal carries
   [ProcInv.tf_page]'s 4096-conjunct big-op, and printing it turns a
   one-line mistake into a forty-minute non-answer. *)
Set Printing Depth 40.
(* ==================================================================== *)
(*  ProofCreateShared.v -- create's functor-free vocabulary. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)


Notation CK := KernelSyms.create (only parsing).
Notation Rra := (mword_of_int 1 : mword 5).
Notation Rz := (mword_of_int 0 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).

(* ===================================================================== *)
(*  1.  THE REGISTER BUNDLES                                              *)
(* ===================================================================== *)

(* create writes SEVEN callee-saved registers on this half (sp s0 s1 s2 s4
   s5 s6) and s3 on the allocate half only, so ONE agreement predicate
   covers the whole found half.  Stated POSITIVELY on the pinned ones and
   by exception only on the rest (durable-notes: an "everything except"
   premise over [is_cs_idx] would demand [sp] and [s0] agree with the
   caller's, which the prologue makes false). *)
Definition cr_thr (m : regfile) (Mx : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
    Mx !!! Regidx c = m !!! Regidx c.

(* what the epilogue funnel at +0x70 needs, and what all four arms have *)
Definition cr_tregs (m : regfile) (sp0 : mword 64) (Mt : regfile) : Prop :=
  Mt !!! Regidx csp_rs1 = pa_stk sp0 10 /\ cr_thr m Mt.

(* the walk's bundle: [dpv] is s1 and [ansv] is s2, both as parameters
   because both are written mid-walk ([mv s1,a0] at +0x20, [mv s2,a0] at
   +0x4a, [li s2,0] at +0x8a / +0x9e / the [mv s2,a0] at +0x160). *)
Definition cr_regs (m : regfile) (sp0 dpv ansv : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) : Prop :=
  Mx !!! Regidx csp_rs1 = pa_stk sp0 10
  /\ Mx !!! Regidx Rs0 = sp0
  /\ Mx !!! Regidx Rs1 = dpv
  /\ Mx !!! Regidx Rs2 = ansv
  /\ Mx !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64)
  /\ Mx !!! Regidx Rs5 = (sign_extend' 64 mj : mword 64)
  /\ Mx !!! Regidx Rs6 = (sign_extend' 64 mn : mword 64)
  /\ cr_thr m Mx.

Lemma cr_thr_caller (m Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> cr_thr m Mx -> cr_thr m (<[Regidx r := v]> Mx).
Proof.
  intros Hr H c Hc N2 N8 N9 N18 N20 N21 N22.
  rewrite upd_ne; [exact (H c Hc N2 N8 N9 N18 N20 N21 N22) | dlk_rne2 Hr Hc].
Qed.

Lemma cr_thr_cs (m Mx My : regfile) :
  callee_saved Mx My -> cr_thr m Mx -> cr_thr m My.
Proof.
  intros Hcs H c Hc N2 N8 N9 N18 N20 N21 N22.
  rewrite (callee_saved_lookup Hcs c Hc).
  exact (H c Hc N2 N8 N9 N18 N20 N21 N22).
Qed.

Lemma cr_regs_caller (m : regfile) (sp0 dpv ansv : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> cr_regs m sp0 dpv ansv ty mj mn Mx ->
  cr_regs m sp0 dpv ansv ty mj mn (<[Regidx r := v]> Mx).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H20 & H21 & H22 & Hthr).
  unfold cr_regs. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H9 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H18 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H20 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - exact (cr_thr_caller m Mx r v Hr Hthr).
Qed.

Lemma cr_regs_cs (m : regfile) (sp0 dpv ansv : mword 64)
    (ty mj mn : mword 16) (Mx My : regfile) :
  callee_saved Mx My -> cr_regs m sp0 dpv ansv ty mj mn Mx ->
  cr_regs m sp0 dpv ansv ty mj mn My.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H20 & H21 & H22 & Hthr).
  unfold cr_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs Rs4 ltac:(vm_compute; reflexivity)). exact H20.
  - rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)). exact H22.
  - exact (cr_thr_cs m Mx My Hcs Hthr).
Qed.

(* the [mv s1,a0] at +0x20 *)
Lemma cr_regs_s1 (m : regfile) (sp0 dpv dpv' ansv : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (v : mword 64) :
  v = dpv' -> cr_regs m sp0 dpv ansv ty mj mn Mx ->
  cr_regs m sp0 dpv' ansv ty mj mn (<[Regidx Rs1 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H20 & H21 & H22 & Hthr).
  unfold cr_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N20 N21 N22.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18 N20 N21 N22) | dlk_xne N9].
Qed.

(* the three writes of s2: [mv s2,a0] at +0x4a and +0x160, [li s2,0] at
   +0x8a / +0x9e *)
Lemma cr_regs_s2 (m : regfile) (sp0 dpv ansv ansv' : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (v : mword 64) :
  v = ansv' -> cr_regs m sp0 dpv ansv ty mj mn Mx ->
  cr_regs m sp0 dpv ansv' ty mj mn (<[Regidx Rs2 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H20 & H21 & H22 & Hthr).
  unfold cr_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H9 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N20 N21 N22.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18 N20 N21 N22) | dlk_xne N18].
Qed.

Lemma cr_tregs_of_regs (m : regfile) (sp0 dpv ansv : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) :
  cr_regs m sp0 dpv ansv ty mj mn Mx -> cr_tregs m sp0 Mx.
Proof. intros (H2 & _ & _ & _ & _ & _ & _ & Hthr). split; assumption. Qed.

(* ---- ...AND THE SAME BUNDLE ON THE ALLOCATE HALF, WHERE s3 IS LIVE ----

   The [c.mv s3,a0] at +0xac (inside the gate span) writes the EIGHTH
   callee-saved register, so [cr_thr]'s claim "s3 still holds the caller's
   value" is false from +0xac until the [c.ldsp s3,40(sp)] at +0xe8 /
   +0xf4 puts it back.  [cr_thr3] is [cr_thr] with s3 removed from the
   agreeing set and [cr_regs3] pins the live value in its place -- stated
   POSITIVELY, exactly as [cr_regs] is, so that no premise anywhere is a
   claim about a set the reader has to go and look up (durable-notes).

   Two lemmas bracket the s3 epoch and nothing else needs to know about it:
   [cr_regs3_of_span] is the ENTRY (the span's own register contract is
   [ProofCreateFreshTy.cr_cs_but_s3], i.e. "callee-saved everywhere but s3",
   and the [c.mv] gives its value), and [cr_tregs_of_regs3] is the EXIT
   (the reload restores [m]'s own s3, which is exactly what [cr_thr] was
   missing).  The three propagation lemmas beside them mirror
   [cr_regs_caller] / [cr_regs_cs] / [cr_regs_s2] one-for-one. *)
Definition cr_thr3 (m : regfile) (Mx : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
    Mx !!! Regidx c = m !!! Regidx c.

Definition cr_regs3 (m : regfile) (sp0 dpv ansv s3v : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) : Prop :=
  Mx !!! Regidx csp_rs1 = pa_stk sp0 10
  /\ Mx !!! Regidx Rs0 = sp0
  /\ Mx !!! Regidx Rs1 = dpv
  /\ Mx !!! Regidx Rs2 = ansv
  /\ Mx !!! Regidx Rs3 = s3v
  /\ Mx !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64)
  /\ Mx !!! Regidx Rs5 = (sign_extend' 64 mj : mword 64)
  /\ Mx !!! Regidx Rs6 = (sign_extend' 64 mn : mword 64)
  /\ cr_thr3 m Mx.

Lemma cr_thr3_caller (m Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> cr_thr3 m Mx -> cr_thr3 m (<[Regidx r := v]> Mx).
Proof.
  intros Hr H c Hc N2 N8 N9 N18 N19 N20 N21 N22.
  rewrite upd_ne; [exact (H c Hc N2 N8 N9 N18 N19 N20 N21 N22)
                  | dlk_rne2 Hr Hc].
Qed.

Lemma cr_regs3_caller (m : regfile) (sp0 dpv ansv s3v : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> cr_regs3 m sp0 dpv ansv s3v ty mj mn Mx ->
  cr_regs3 m sp0 dpv ansv s3v ty mj mn (<[Regidx r := v]> Mx).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold cr_regs3. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H9 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H18 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H19 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H20 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - exact (cr_thr3_caller m Mx r v Hr Hthr).
Qed.

Lemma cr_regs3_cs (m : regfile) (sp0 dpv ansv s3v : mword 64)
    (ty mj mn : mword 16) (Mx My : regfile) :
  callee_saved Mx My -> cr_regs3 m sp0 dpv ansv s3v ty mj mn Mx ->
  cr_regs3 m sp0 dpv ansv s3v ty mj mn My.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold cr_regs3. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs Rs3 ltac:(vm_compute; reflexivity)). exact H19.
  - rewrite (callee_saved_lookup Hcs Rs4 ltac:(vm_compute; reflexivity)). exact H20.
  - rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)). exact H22.
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
    rewrite (callee_saved_lookup Hcs c Hc).
    exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22).
Qed.

(* the [c.mv s2,s3] at +0xe6 (ARM C-OK) and +0xf2 (ARM A-FAIL) *)
Lemma cr_regs3_s2 (m : regfile) (sp0 dpv ansv ansv' s3v : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (v : mword 64) :
  v = ansv' -> cr_regs3 m sp0 dpv ansv s3v ty mj mn Mx ->
  cr_regs3 m sp0 dpv ansv' s3v ty mj mn (<[Regidx Rs2 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold cr_regs3. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H9 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H19 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22)
                    | dlk_xne N18].
Qed.

(* the [c.ldsp s3,40(sp)] at +0xe8 / +0xf4 *)
Lemma cr_regs3_s3 (m : regfile) (sp0 dpv ansv s3v s3w : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) (v : mword 64) :
  v = s3w -> cr_regs3 m sp0 dpv ansv s3v ty mj mn Mx ->
  cr_regs3 m sp0 dpv ansv s3w ty mj mn (<[Regidx Rs3 := v]> Mx).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold cr_regs3. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H9 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
    rewrite upd_ne; [exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22)
                    | dlk_xne N19].
Qed.

(* ENTRY: the gate span promises [callee_saved] EVERYWHERE BUT s3 and
   reports s3's own value per arm, so [cr_regs] in gives [cr_regs3] out. *)
Lemma cr_regs3_of_span `{XI : CurCtx} (m : regfile) (sp0 dpv ansv s3v : mword 64)
    (ty mj mn : mword 16) (Ma Mo : regfile) :
  cr_cs_but_s3 Ma Mo ->
  (Mo !!! Regidx Rs3 : mword 64) = s3v ->
  cr_regs m sp0 dpv ansv ty mj mn Ma ->
  cr_regs3 m sp0 dpv ansv s3v ty mj mn Mo.
Proof.
  intros Hsp Hs3 (H2 & H8 & H9 & H18 & H20 & H21 & H22 & Hthr).
  unfold cr_regs3. split_and!.
  - rewrite (Hsp csp_rs1 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H2.
  - rewrite (Hsp Rs0 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H8.
  - rewrite (Hsp Rs1 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H9.
  - rewrite (Hsp Rs2 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H18.
  - exact Hs3.
  - rewrite (Hsp Rs4 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H20.
  - rewrite (Hsp Rs5 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H21.
  - rewrite (Hsp Rs6 ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate)). exact H22.
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
    rewrite (Hsp c Hc N19).
    exact (Hthr c Hc N2 N8 N9 N18 N20 N21 N22).
Qed.

(* EXIT: once the reload has put [m]'s own s3 back, the s3 exception is
   gone and the funnel's [cr_tregs] is available again. *)
Lemma cr_tregs_of_regs3 (m : regfile) (sp0 dpv ansv : mword 64)
    (ty mj mn : mword 16) (Mx : regfile) :
  cr_regs3 m sp0 dpv ansv (m !!! Regidx Rs3 : mword 64) ty mj mn Mx ->
  cr_tregs m sp0 Mx.
Proof.
  intros (H2 & _ & _ & _ & H19 & _ & _ & _ & Hthr).
  split; [exact H2 |].
  intros c Hc N2 N8 N9 N18 N20 N21 N22.
  destruct (Z.eq_dec (bv_unsigned c) 19) as [Heq | Hne].
  - assert (Hc3 : c = Rs3)
      by (apply bv_eq; rewrite Heq; vm_compute; reflexivity).
    rewrite Hc3. exact H19.
  - refine (Hthr c Hc N2 N8 N9 N18 _ N20 N21 N22).
    intro Hc3. apply Hne. rewrite Hc3. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  1b.  THE LEDGER READINGS, over plain [nat]                            *)
(*                                                                        *)
(*  create begins at [create_units = MAXOPBLOCKS = 10] and the whole found *)
(*  half spends at most two units per uncredited [iunlockput], so every    *)
(*  budget premise on this half is one of these four.  They are            *)
(*  [CreateBudget.cr_budget_found_w] read at the two figures the           *)
(*  contracts actually state ([SpecNamex.walk_spend] in,                   *)
(*  [SpecIput.ip_spend_w _ false false] out).                              *)
(* ===================================================================== *)

Lemma cr_walk_need (L n : nat) :
  (create_units <= n)%nat -> (SpecNamex.walk_need L <= n)%nat.
Proof.
  intro H. rewrite create_units_value in H.
  unfold SpecNamex.walk_need, iput_units. destruct L; lia.
Qed.

(* nameiparent's success arm leaves [cr_uw w >= 9] -- the row
   [CreateBudget.cr_budget_found_w] is stated at. *)
Lemma cr_n1_lo (u n1 : nat) (w : bool) :
  (create_units <= u)%nat ->
  ((u - (SpecNamex.walk_spend w + 0))%nat <= n1)%nat -> (9 <= n1)%nat.
Proof.
  intros Hu Hn. rewrite create_units_value in Hu.
  unfold SpecNamex.walk_spend in Hn. destruct w; lia.
Qed.

Lemma cr_ip_of9 (n : nat) : (9 <= n)%nat -> (iput_units <= n)%nat.
Proof. unfold iput_units. lia. Qed.

(* ...and after ONE uncredited [iunlockput] there are still seven, which is
   what lets ARM F-BAD call a second one. *)
Lemma cr_after_ip (n n' : nat) (w : bool) :
  (9 <= n)%nat -> ((n - ip_spend_w w false false)%nat <= n')%nat ->
  (iput_units <= n')%nat /\ (7 <= n')%nat.
Proof.
  intros Hn Hn'. unfold ip_spend_w, ip_bm, iput_units in *.
  destruct w; cbn in Hn' |- *; lia.
Qed.

Lemma cr_after_ip7 (n n' : nat) (w : bool) :
  (7 <= n)%nat -> ((n - ip_spend_w w false false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hn Hn'. unfold ip_spend_w, ip_bm, iput_units in *.
  destruct w; cbn in Hn' |- *; lia.
Qed.

(* ---- THE CLOSING ARITHMETIC, AS NAMED LEMMAS RATHER THAN TACTICS ----
   fs-sysfile's S3l trap, paid again here: [set_solver] IS QUADRATIC IN THE
   PROOF CONTEXT, and a syscall-altitude Iris context is enormous -- ONE
   [split; [set_solver | lia]] bullet measured **147.8 s** in this file.
   Every arm's two closing bullets are pure facts about a [gset Z] and a
   [nat], so they are proven ONCE up here, where the context is empty, and
   the call sites are [exact] terms with no search at all.  The same goes
   for the bare [lia]s: they are cheap in isolation and not in there. *)

Lemma cr_sub2 (A B C : gset Z) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. intros H1 H2. exact (transitivity H1 H2). Qed.

Lemma cr_sub3 (A B C D : gset Z) : A ⊆ B -> B ⊆ C -> C ⊆ D -> A ⊆ D.
Proof. intros H1 H2 H3. exact (transitivity H1 (transitivity H2 H3)). Qed.

Lemma cr_le2 (a b c : nat) : (a <= b)%nat -> (b <= c)%nat -> (a <= c)%nat.
Proof. lia. Qed.

Lemma cr_le3 (a b c d : nat) :
  (a <= b)%nat -> (b <= c)%nat -> (c <= d)%nat -> (a <= d)%nat.
Proof. lia. Qed.

(* the four slot figures the halves hand back, against [create_slots]:
   ARM N / ARM G return the ledger WHOLE, F-OK keeps one out for the inode
   it returns, F-BAD's second [iunlockput] gives that one back too.  Each
   states its figure EXACTLY -- the contract used to take an interval and
   these lemmas weakened into it, which is what stopped sys_mkdir and
   sys_mknod from showing they end where they started. *)
Lemma cr_slots_ns (ok : bool) (ns : nat) :
  ok = false -> (create_slots <= ns)%nat ->
  (if ok then (S ns = ns)%nat else ns = ns).
Proof. intros -> Hns. reflexivity. Qed.

Lemma cr_slots_1 (ok : bool) (ns : nat) :
  ok = true -> (create_slots <= ns)%nat ->
  (if ok then (S (1 + (ns - 2))%nat = ns)%nat else (1 + (ns - 2))%nat = ns).
Proof. intros -> Hns. unfold create_slots in *. lia. Qed.

Lemma cr_slots_2 (ok : bool) (ns : nat) :
  ok = false -> (create_slots <= ns)%nat ->
  (if ok then (S (1 + (1 + (ns - 2)))%nat = ns)%nat
   else (1 + (1 + (ns - 2)))%nat = ns).
Proof. intros -> Hns. unfold create_slots in *. lia. Qed.

Lemma cr_ns_split (ns : nat) : (create_slots <= ns)%nat -> ns = (2 + (ns - 2))%nat.
Proof. unfold create_slots. lia. Qed.

Lemma cr_ns_1 (ns : nat) : (create_slots <= ns)%nat ->
  (1 + (ns - 2))%nat = (ns - 1)%nat.
Proof. unfold create_slots. lia. Qed.

(* a live directory record's inum is nonzero, as a [Z] fact *)
Lemma cr_pos_of_nz (x : Z) : 0 <= x -> x <> 0 -> 0 < x.
Proof. lia. Qed.

(* ===================================================================== *)
(*  1c.  THE ALLOCATE HALF'S OWN PURE CLUSTER                             *)
(*                                                                        *)
(*  Three things the walk from +0xa2 to +0xea needs and nothing else in   *)
(*  the tree has: the HALFWORD BRIDGE at +0xce, the record identity the   *)
(*  three [sh]s produce, and the arm's ledger readings.                    *)
(* ===================================================================== *)

(* ---- (i) THE HALFWORD BRIDGE.  The [lw a2,4(s3)] at +0xce loads the
   child's inum as a SIGN-extended 32-bit cell; [SpecDirlink]'s a2 premise
   is a ZERO-extended SIXTEEN-bit one, because the [sh s6,-80(s0)] inside
   dirlink stores exactly sixteen bits.  The two agree below 2^16, and
   what bounds the inum there is the ruled premise
   [16 * Z.of_nat nib <= 2^16] -- mkfs's own [ushort] geometry, carried as
   a premise of the alloc-half lemma (D0-a, the eleventh stop's item-2
   ruling) rather than as a slot widening. *)
Lemma cr_zext64_16_unsigned (h : mword 16) :
  bv_unsigned (zero_extend' 64 h : mword 64) = bv_unsigned h.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned; [ reflexivity | cbn; lia ].
Qed.

(* ...and the 32-bit widening the region's movers want: [DirView.dir_inum]
   is a [bv 16] and the region is stated at its own [bv 32] inum, so the
   T_DIR [fail:] sibling crosses the two here. *)
Lemma cr_bzext32_16 (h : bv 16) :
  bv_unsigned (bv_zero_extend 32 h) = bv_unsigned h.
Proof. rewrite bv_zero_extend_unsigned; [ reflexivity | cbn; lia ]. Qed.

Definition cr_low16 (v : mword 32) : mword 16 := mword_of_int (bv_unsigned v).

Lemma cr_moi16_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 16) = bv_wrap 16 z.
Proof.
  unfold mword_of_int, SailStdpp.Values.mword_of_int,
         MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 16) with 16%N. reflexivity.
Qed.

Lemma cr_low16_unsigned (v : mword 32) :
  bv_unsigned v < 2 ^ 16 -> bv_unsigned (cr_low16 v) = bv_unsigned v.
Proof.
  intro Hv. pose proof (bv_unsigned_in_range _ v) as Hlo.
  unfold cr_low16. rewrite cr_moi16_unsigned.
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 16)%Z with (2^16)%Z. lia.
Qed.

Lemma cr_sext64_32_unsigned (v : mword 32) :
  bv_unsigned v < 2 ^ 31 ->
  bv_unsigned (sign_extend' 64 v : mword 64) = bv_unsigned v.
Proof.
  intro Hv.
  pose proof (bv_unsigned_in_range _ v) as Hlo.
  (* the [change] MUST NOT be done before the [bv_swrap_small] rewrite: it
     also rewrites the implicit width inside [@bv_unsigned (Z_idx 32) v],
     after which a hand-instantiated rewrite finds no subterm. *)
  assert (Hhm32 : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2^31)
    by reflexivity.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed.
  rewrite bv_swrap_small; [ apply bvw64_small; lia | rewrite Hhm32; lia ].
Qed.

Lemma cr_a2_halfword (v : mword 32) (h : mword 16) :
  bv_unsigned v = bv_unsigned h ->
  (sign_extend' 64 v : mword 64) = (zero_extend' 64 h : mword 64).
Proof.
  intro Hvh.
  pose proof (bv_unsigned_in_range _ h) as Hh. unfold bv_modulus in Hh.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16)) with 65536 in Hh.
  apply bv_eq.
  rewrite cr_zext64_16_unsigned.
  rewrite (cr_sext64_32_unsigned v ltac:(rewrite Hvh; lia)).
  exact Hvh.
Qed.

Lemma cr_a2_low16 (v : mword 32) :
  bv_unsigned v < 2 ^ 16 ->
  (sign_extend' 64 v : mword 64) = (zero_extend' 64 (cr_low16 v) : mword 64).
Proof.
  intro Hv. apply cr_a2_halfword. rewrite (cr_low16_unsigned v Hv). reflexivity.
Qed.

(* the [c.li a4,1] at +0xbc stores a SIXTEEN-bit one through the [sh] at
   +0xbe: [trunc16] of the 64-bit literal. *)
Lemma cr_trunc16_one :
  trunc16 (mword_of_int 1 : mword 64) = (mword_of_int 1 : mword 16).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- (ii) THE RECORD THE THREE [sh]s LEAVE.  [ProofCreateParts.
   cr_made_setf] is this identity at [ialloc_fresh ty]; what the walk
   actually holds after [ilock] is an ARBITRARY record with
   [fresh_shape] and the gate's [di_type dn = ty], which is exactly as
   much as [create_made] needs. *)
Lemma cr_setf_fresh_made (dn : dinode) (ty mj mn : mword 16) :
  fresh_shape dn -> di_type dn = ty ->
  cr_setf dn mj mn (mword_of_int 1 : mword 16) = create_made ty mj mn.
Proof.
  intros (_ & Hsz & Hadd & _) Hty.
  unfold cr_setf, create_made.
  rewrite Hty Hadd. f_equal.
  apply bv_eq. rewrite Hsz. reflexivity.
Qed.

(* ---- (iii) THE ARM'S LEDGER READINGS.  [CreateBudget.cr_budget_file]
   is the theorem; these are it at the figures the CONTRACTS state,
   exactly as [cr_n1_lo] / [cr_after_ip] are for the found half.  The
   walk reaches its [dirlink] with [q1 >= 8] ([cr_uw w - ia_spend -
   iu_spend true] is 8 or 7... at [w = false] it is nine minus one), and
   [dl_need] is at most six, [wi16_spend] at most five.
   ONE spend reading serves BOTH exits of that [dirlink]: since the
   [dl16_post] collapse the failing append reports the same credit-aware
   [wi16_spend] as the succeeding one, so the [bltz]-taken branch needs no
   [tot]-split and no constant-shaped twin ([cr_alloc_ip0], retired). *)
Lemma cr_alloc_dlneed (nc : nat) (crb ind : bool) :
  (8 <= nc)%nat -> (SpecDirlink.dl_need crb ind <= nc)%nat.
Proof.
  intro Hnc.
  unfold SpecDirlink.dl_need, wi16_need, SpecBmap.bmap_need, iput_units.
  destruct crb, ind; simpl; lia.
Qed.

Lemma cr_alloc_ip (nc n' : nat) (crb crd cru al ind : bool) :
  (8 <= nc)%nat ->
  ((nc - wi16_spend crb crd cru al ind)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hnc Hn'.
  unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crb, crd, cru, al, ind; simpl in *; lia.
Qed.

(* ...AND THE SAME READING ONE UNIT SHARPER, which is what the [fail:] arm's
   SECOND [iunlockput] needs (D0-c).  [wi16_spend] never exceeds four
   ([CreateBudget.cr_wi16_spend_max] is the witness that four is attained),
   so the eight the walk carries into its first [dirlink] leave FOUR however
   the append went -- and four is [iput_units] plus the bitmap unit the fail
   tail's uncredited freeing iput may report. *)
Lemma cr_alloc_ip4 (nc n' : nat) (crb crd cru al ind : bool) :
  (8 <= nc)%nat ->
  ((nc - wi16_spend crb crd cru al ind)%nat <= n')%nat ->
  (S iput_units <= n')%nat.
Proof.
  intros Hnc Hn'.
  unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crb, crd, cru, al, ind; simpl in *; lia.
Qed.

(* THE FAIL TAIL'S TWO READINGS, one per disjunct of the body's own ledger
   premise.  [ip_spend_w w cru crz] is [ip_bm w + (if cru || crz then 0 else
   1)]: create claims [cru] (its own [ialloc]/[iupdate] logged the child's
   inode block, and the [fail:] flush unions it in again), so the only term
   left is the bitmap report. *)
Lemma cr_fail_ip_left (n4 n' : nat) (w : bool) :
  (S iput_units <= n4)%nat ->
  ((n4 - ip_spend_w w true false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros H4 Hn'. unfold ip_spend_w, ip_bm, iput_units in *.
  destruct w; simpl in *; lia.
Qed.

(* ...and with the bitmap block already in the op's set the report is pinned
   [false] (fs-log.md §G.25's [crb = true -> w = false]), so the freeing iput
   is free and the landed [iput_units <= n4] is enough. *)
Lemma cr_fail_ip_right (n4 n' : nat) :
  (iput_units <= n4)%nat ->
  ((n4 - ip_spend_w false true false)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros H3 Hn'. unfold ip_spend_w, ip_bm, iput_units in *.
  simpl in *. lia.
Qed.

(* THE HONEST [crb], BOTH READINGS.  The fail arm enters its freeing
   [iunlockput] at [crb := bool_decide (bmapstart ∈ Sb)] -- the claim it can
   always make -- so the two directions of that decision are what the call's
   honesty premise and the ledger step below need.  Stated here rather than
   inlined: an [ltac:(... bool_decide_eq_true_1 ...)] in argument position
   has to guess [P] from an expected type that is still an evar, and the
   failure is an uninferable placeholder naming a [bool_decide] of the
   IMPLICATION rather than of the membership. *)
Lemma cr_crb_honest (S : gset Z) (x : Z) :
  bool_decide (x ∈ S) = true -> x ∈ S.
Proof. intro H. apply bool_decide_eq_true_1 in H. exact H. Qed.

Lemma cr_crb_claim (S : gset Z) (x : Z) :
  x ∈ S -> bool_decide (x ∈ S) = true.
Proof. intro H. apply bool_decide_eq_true_2. exact H. Qed.

(* the [sh zero,74(s3)] at +0x146: [trunc16] of x0's word *)
Lemma cr_trunc16_zero :
  trunc16 (zero_reg : mword 64) = (mword_of_int 0 : mword 16).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- (iv) THE T_DIR DECISION AT +0xca, WHICH IS A [beq] AND NOT A [bne].
   [ProofNamexParts.nx_tdir_eq]/[_ne] answer at [neq_vec], because namex
   spells the same test as a [bne]; [WpSconfBtype.wp_beq_*_s_sconf] wants an
   [eq_vec].  [neq_vec] IS [negb (eq_vec ..)], so the bridge is one
   destruct -- stated once here rather than inlined at the two branch
   arms. *)
Lemma cr_tdir_eq (t : mword 16) : t = SpecDirlookup.T_DIR ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = true.
Proof.
  intro Ht. pose proof (nx_tdir_eq t Ht) as H. unfold neq_vec in H.
  destruct (eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64));
    [reflexivity | discriminate H].
Qed.

Lemma cr_tdir_ne (t : mword 16) : t <> SpecDirlookup.T_DIR ->
  eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64) = false.
Proof.
  intro Ht. pose proof (nx_tdir_ne t Ht) as H. unfold neq_vec in H.
  destruct (eq_vec (sign_extend' 64 t : mword 64) (mword_of_int 1 : mword 64));
    [discriminate H | reflexivity].
Qed.

(* THE REGISTER VALUE THE FILL CHOOSES, and how many fragments it mints
   (lane G5).  At a DIRECTORY the child's value is [TDir dp] -- which is
   what lets [dp]'s own name record for the child assert "my target's
   parent is me" -- and the multiplicity crosses [0 -> 2]: the name in the
   parent, and the child's own ["."].  At a file it is [TFile] and one. *)
Definition cr_ity (ty : mword 16) (dpv : Z) : ity :=
  if decide (ty = SpecDirlookup.T_DIR) then TDir dpv else TFile.

Definition cr_delta (ty : mword 16) : nat :=
  if decide (ty = SpecDirlookup.T_DIR) then 2%nat else 1%nat.

(* the FILL's premise at create's own record: the claim box stands at
   multiplicity zero (its count is zero, [fresh_shape_nlink]), and the
   chosen value matches the type the fill writes. *)
Lemma cr_fill_choice_ok (ty : mword 16) (major minor : mword 16)
    (dnc : dinode) (dind : mword 32) :
  bv_unsigned (di_nlink dnc) = 0 ->
  di_type dnc = ty ->
  forall v : ity,
    Some (cr_ity ty (bv_unsigned dind)) = Some v ->
    InodeRegion.ireg_mult dnc = 0%nat
    /\ InodeRegion.ireg_reg_ok
         (bv_unsigned (di_type (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16)))) v.
Proof.
  intros Hnl Hty v Hv. injection Hv as <-.
  split; [exact (InodeRegion.ireg_mult_zero dnc Hnl) |].
  rewrite cr_setf_type Hty /InodeRegion.ireg_reg_ok /cr_ity.
  assert (Hdty : InodeRegion.ireg_dir_ty = bv_unsigned SpecDirlookup.T_DIR)
    by (vm_compute; reflexivity).
  destruct (decide (ty = SpecDirlookup.T_DIR)) as [-> | Hne].
  - rewrite Hdty //.
  - rewrite Hdty. intros Hc. apply Hne. apply bv_eq. exact Hc.
Qed.

(* the fail arm's [ip->nlink = 0] retires exactly what the fill minted:
   the record it writes has count zero, so [ireg_dot_delta] is TWO at a
   directory and ONE at a file -- [cr_delta] on the nose. *)
Lemma cr_delta_eq (ty major minor : mword 16) (dnc : dinode) (nl : mword 16) :
  di_type dnc = ty -> bv_unsigned nl = 0 ->
  InodeRegion.ireg_dot_delta
    (bv_unsigned (di_type (cr_setf dnc major minor nl)))
    (bv_unsigned (di_nlink (cr_setf dnc major minor nl))) = cr_delta ty.
Proof.
  intros Hty Hz.
  rewrite cr_setf_type cr_setf_nlink Hty Hz
    /InodeRegion.ireg_dot_delta /cr_delta
    (bool_decide_eq_true_2 (0 = 0) eq_refl) andb_true_r.
  assert (Hdty : InodeRegion.ireg_dir_ty = bv_unsigned SpecDirlookup.T_DIR)
    by (vm_compute; reflexivity).
  rewrite Hdty.
  destruct (decide (ty = SpecDirlookup.T_DIR)) as [-> | Hne].
  - rewrite (bool_decide_eq_true_2 _ eq_refl) //.
  - rewrite (bool_decide_eq_false_2
               (bv_unsigned ty = bv_unsigned SpecDirlookup.T_DIR)
               ltac:(intros Hc; apply Hne; by apply bv_eq)) //.
Qed.

Lemma cr_ity_dir (ty : mword 16) (dpv : Z) :
  ty = SpecDirlookup.T_DIR -> cr_ity ty dpv = TDir dpv.
Proof. intro H. rewrite /cr_ity decide_True; [reflexivity | exact H]. Qed.

Lemma cr_ity_file (ty : mword 16) (dpv : Z) :
  ty <> SpecDirlookup.T_DIR -> cr_ity ty dpv = TFile.
Proof. intro H. rewrite /cr_ity decide_False; [reflexivity | exact H]. Qed.

Lemma cr_delta_dir (ty : mword 16) :
  ty = SpecDirlookup.T_DIR -> cr_delta ty = 2%nat.
Proof. intro H. rewrite /cr_delta decide_True; [reflexivity | exact H]. Qed.

Lemma cr_delta_file (ty : mword 16) :
  ty <> SpecDirlookup.T_DIR -> cr_delta ty = 1%nat.
Proof. intro H. rewrite /cr_delta decide_False; [reflexivity | exact H]. Qed.

(* ---- (iv-bis) THE NLINK_MAX GATE AT +0x30..+0x3c (xv6 117c0e7).
   [c.lui a4,0xffff8] then [c.addi a4,a4,1] put -32767 in a4, [c.add
   a5,a5,a4] leaves [nlink - NLINK_MAX] in a5, and the [c.bnez] at +0x36
   jumps over the type test whenever that is nonzero.  Falling through it,
   [addi a5,s4,-1] leaves [ty - T_DIR] and the [c.beqz] at +0x3c takes the
   guard's own exit block at +0x8e.  Both decisions are "this sum is zero",
   so one cancellation lemma serves both: [d] is [c]'s additive inverse,
   checked by [vm_compute] at each use. *)
Lemma cr_add_inv (x c d : mword 64) :
  (bv_unsigned c + bv_unsigned d = 18446744073709551616)%Z ->
  add_vec x c = (zero_reg : mword 64) -> x = d.
Proof.
  intros Hcd H.
  apply (f_equal bv_unsigned) in H.
  rewrite add_vec64_unsigned in H.
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z in H.
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z) by (vm_compute; reflexivity).
  unfold bv_wrap in H. rewrite Hm in H.
  assert (Hmz : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616%Z)
    by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ x) as [Hx0 Hx1]. rewrite Hmz in Hx1.
  pose proof (bv_unsigned_in_range _ d) as [Hd0 Hd1]. rewrite Hmz in Hd1.
  apply Z.mod_divide in H; [| lia].
  destruct H as [k Hk].
  apply bv_eq. lia.
Qed.

(* +0x36, the nlink test.  [nx_sext16_inj] is what turns "the sum is zero"
   back into a fact about the halfword the [lh] read. *)
Lemma cr_nlmax_eq (h : mword 16) : h = (mword_of_int 32767 : mword 16) ->
  neq_vec (add_vec (sign_extend' 64 h : mword 64)
             (mword_of_int (-32767) : mword 64)) (zero_reg : mword 64) = false.
Proof.
  intros ->. unfold neq_vec.
  rewrite (proj2 (eq_vec_true_iff _ _)); [reflexivity |].
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma cr_nlmax_ne (h : mword 16) : h <> (mword_of_int 32767 : mword 16) ->
  neq_vec (add_vec (sign_extend' 64 h : mword 64)
             (mword_of_int (-32767) : mword 64)) (zero_reg : mword 64) = true.
Proof.
  intro Hne. unfold neq_vec.
  rewrite (proj2 (eq_vec_false_iff _ _)); [reflexivity |].
  intro Hc. apply Hne. apply nx_sext16_inj.
  assert (Hinv : (bv_unsigned (mword_of_int (-32767) : mword 64)
                  + bv_unsigned (mword_of_int 32767 : mword 64)
                  = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite (cr_add_inv _ _ _ Hinv Hc).
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* +0x3c, the type test.  [sign_extend' 64 (4095 : mword 12)] is -1. *)
Lemma cr_tym1_eq (t : mword 16) : t = SpecDirlookup.T_DIR ->
  eq_vec (add_vec (sign_extend' 64 t : mword 64)
            (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64))
         (zero_reg : mword 64) = true.
Proof.
  intros ->. apply (proj2 (eq_vec_true_iff _ _)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma cr_tym1_ne (t : mword 16) : t <> SpecDirlookup.T_DIR ->
  eq_vec (add_vec (sign_extend' 64 t : mword 64)
            (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64))
         (zero_reg : mword 64) = false.
Proof.
  intro Ht. apply (proj2 (eq_vec_false_iff _ _)).
  intro Hc. apply Ht. apply nx_sext16_inj.
  assert (Hinv : (bv_unsigned (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                  + bv_unsigned (mword_of_int 1 : mword 64)
                  = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite (cr_add_inv _ _ _ Hinv Hc).
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- (v) THE [bltz a0] AT +0xdc, AT dirlink's TWO BRANCHLESS ANSWERS.
   [SpecDirlink]'s append arm returns 0 exactly when all sixteen bytes went
   in and -1 otherwise, so the branch is decided by which disjunct holds and
   never by any arithmetic of this walk's. *)
Lemma cr_bltz_zero :
  zopz0zI_s (mword_of_int 0 : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cr_bltz_m1 :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- (vi) writei's RECORD AT THE SIZE [DirView.dir_ok_dirlink] ASKS
   FOR.  [SpecWritei.wi_dinode] installs [max(size, off+tot)] as a 32-bit
   literal; the re-park lemma wants it read back over [Z].  The side condition is the only place the walk has to
   know that the append slot is inside the file. *)
Lemma cr_wi_size_max (dn : dinode) (bm' : blkmap) (off tot : nat) :
  (Z.of_nat (off + tot) < 2 ^ 32)%Z ->
  bv_unsigned (di_size (wi_dinode dn bm' off tot))
  = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (off + tot)).
Proof.
  intro Hlt. rewrite /wi_dinode. cbn [di_size].
  case_decide as Hd.
  - rewrite (moi32_small (Z.of_nat (off + tot))
               (conj (Nat2Z.is_nonneg (off + tot)) Hlt)). lia.
  - lia.
Qed.

(* ---- (vii) THE ALLOCATE HALF'S SLOT LEDGER.  [cr_slots_2] above is ARM
   A-FAIL's (the gate hands the slot back and [iunlockput] returns one); ARM
   C-OK keeps the child's slot out and gets one back from [dirlink]'s net
   zero and one from its [iunlockput(dp)]. *)
Lemma cr_slots_3 (ok : bool) (ns : nat) :
  ok = true -> (create_slots <= ns)%nat ->
  (if ok then (S (1 + (1 + (ns - 3)))%nat = ns)%nat
   else (1 + (1 + (ns - 3)))%nat = ns).
Proof. intros -> Hns. unfold create_slots in *. lia. Qed.

Lemma cr_ns_2 (ns : nat) : (create_slots <= ns)%nat ->
  (1 + (ns - 3))%nat = (ns - 2)%nat.
Proof. unfold create_slots. lia. Qed.

(* the two set facts the mint's membership premise needs, proven where the
   proof context is EMPTY (the file's standing [set_solver] rule) *)
Lemma cr_in_union_sing (S : gset Z) (x : Z) : x ∈ S ∪ {[x]}.
Proof. apply elem_of_union_r, elem_of_singleton. reflexivity. Qed.

Lemma cr_sub_union_sing (S : gset Z) (x : Z) : S ⊆ S ∪ {[x]}.
Proof. apply union_subseteq_l. Qed.

(* ===================================================================== *)
(*  (viii) THE mkdir SUB-BRANCH (+0xf8 .. +0x144), D0-b step 1            *)
(*                                                                        *)
(*  Three groups and nothing else: the sixteen-bit [++] at +0x134..+0x13a, *)
(*  the DIRECTORY-VIEW readings the two interior [dirlink]s need, and the  *)
(*  arm's ledger, which closes at EXACTLY [iput_units].                    *)
(* ===================================================================== *)

(* ---- (a) THE [++].  The [lhu] at +0x134 zero-extends, the [c.addiw] at
   +0x138 wraps at 32 and sign-extends to 64, and the [sh] at +0x13a
   commits [trunc16] of that -- which IS [add_vec h 1] at sixteen bits.
   [ProofCreateParts.cr_inner]'s pattern verbatim: name the 32-bit
   intermediate, and the whole Sail cast layer collapses by conversion.
   [BvShift.swrap_low_32_16] crosses the sign extension without a case
   split on the sign. *)
Definition cr_ninner (h : mword 16) : bv 32 :=
  bv_extract 0 32 (bv_add (bv_zero_extend 64 h)
      (bv_sign_extend 64 (bv_sign_extend 12 (mword_of_int 1 : mword 6)))).

Lemma cr_ninner_unsigned (h : mword 16) :
  bv_unsigned (cr_ninner h) = (bv_unsigned h + 1) `mod` 4294967296.
Proof.
  unfold cr_ninner.
  rewrite bv_extract_unsigned bv_add_unsigned.
  rewrite (bv_zero_extend_unsigned 64 h ltac:(vm_compute; discriminate)).
  assert (Hc : bv_unsigned (bv_sign_extend 64
                  (bv_sign_extend 12 (mword_of_int 1 : mword 6)) : bv 64) = 1)
    by (vm_compute; reflexivity).
  rewrite Hc.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296.
  rewrite mod_2_64_32. reflexivity.
Qed.

Lemma cr_nbump_bv (h : mword 16) :
  bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
         : mword 64)) 31 0)))
  = bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (cr_ninner h))).
Proof. reflexivity. Qed.

Lemma cr_nbump_unsigned (h : mword 16) :
  bv_unsigned (bv_extract 0 16 (bv_sign_extend 64 (cr_ninner h)))
  = (bv_unsigned h + 1) `mod` 65536.
Proof.
  rewrite bv_extract_unsigned bv_sign_extend_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296.
  change (2 ^ Z.of_N 16) with 65536.
  rewrite mod_2_64_16 swrap_low_32_16 cr_ninner_unsigned mod_2_32_16.
  reflexivity.
Qed.

Lemma cr_nlink_incr (h : mword 16) :
  trunc16 (sign_extend' 64 (subrange_vec_dec
     (add_vec (zero_extend' 64 h : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
         : mword 64)) 31 0))
  = add_vec h (mword_of_int 1 : mword 16).
Proof.
  apply bv_eq. rewrite cr_nbump_bv cr_nbump_unsigned.
  rewrite add_vec_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
    by (vm_compute; reflexivity).
  rewrite H1. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16)) with 65536.
  reflexivity.
Qed.

(* ---- (b) THE DIRECTORY-VIEW READINGS.  The child is EMPTY when the arm
   starts, so the first link's slot is zero and its dirlookup cannot hit;
   after it, slot zero is LIVE at the child's own inum (which is what makes
   the second link's free-slot scan settle on slot one) and its canonical
   name is ["."] (which is what makes the second link's dirlookup MISS,
   [".."] being a different list). *)
Lemma cr_nrec_0 : dir_nrec 0 = 0%nat.
Proof. reflexivity. Qed.

Lemma cr_nrec_16 : dir_nrec 16 = 1%nat.
Proof. reflexivity. Qed.

Lemma cr_slot_0 (data : nat -> list (bv 8)) : dir_slot data 0 = 0%nat.
Proof. unfold dir_slot, dir_free_first. rewrite dfirst_0. reflexivity. Qed.

Lemma cr_first_0 (data : nat -> list (bv 8)) (s : list (bv 8)) :
  dir_first data 0 s = None.
Proof. apply dir_first_None. intros j Hj. exfalso. lia. Qed.

(* ---- THE NOP ARM'S UNIQUENESS CLAUSE, and why it is stated here.
   [FsTree.dir_uniq_dirlink] takes dirlink's APPEND GUARD
   ([dir_first data nrec s = None]) because at [tot = 16] that guard is
   the whole argument.  At [tot = 0] nothing was written, and this arm --
   [cr_fail_body]'s, whose block lemma carries the dirlink RESULT but not
   the guard -- has no supplier for it.  So the [tot = 0] case is proved
   on its own here, where the range clause alone does the work: the window
   is EMPTY, so [data'] agrees with [data] on every record, and the size
   cannot have moved past [nrec] because the slot is at or below it. *)
Lemma cr_uniq_nop (dn dn' : dinode) (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : list (bv 8)) (nrec k0 : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  di_type dn' = di_type dn ->
  bv_unsigned (di_size dn')
    = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + 0)) ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + 0)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_uniq dn data -> dir_uniq dn' data'.
Proof.
  intros Hnrec Hk0 Hty Hsz Hrng H Hd'.
  assert (Hd : bv_unsigned (di_type dn) = T_DIR_z)
    by (rewrite <- Hty; exact Hd').
  specialize (H Hd).
  assert (Hagr : forall q : nat, dir_win_agree data data' q).
  { intros q jj Hjj. rewrite (Hrng (16 * q + jj)%nat).
    rewrite decide_False; [reflexivity |]. lia. }
  assert (Hk0le : (k0 <= nrec)%nat) by (rewrite Hk0; apply dir_slot_le).
  assert (Hsznn : 0 <= bv_unsigned (di_size dn))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
  destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 Hnr2].
  rewrite <- Hnrec in Hnr1, Hnr2.
  assert (Hmax : Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + 0))
                 = bv_unsigned (di_size dn)).
  { assert (Hle : Z.of_nat (16 * k0 + 0)%nat <= Z.of_nat (16 * nrec)%nat)
      by lia.
    lia. }
  assert (Hnr : dir_nrec (bv_unsigned (di_size dn')) = nrec)
    by (rewrite Hsz Hmax; symmetry; exact Hnrec).
  rewrite Hnr. rewrite <- Hnrec in H.
  intros j k Hj Hk Hlj Hlk Heq.
  apply (H j k Hj Hk).
  - unfold dir_live. rewrite <- (dir_inum_agree data data' j (Hagr j)).
    exact Hlj.
  - unfold dir_live. rewrite <- (dir_inum_agree data data' k (Hagr k)).
    exact Hlk.
  - unfold dir_bname.
    rewrite <- (dir_bname_agree data data' j (Hagr j)).
    rewrite <- (dir_bname_agree data data' k (Hagr k)). exact Heq.
Qed.

Lemma cr_slot_1 (data : nat -> list (bv 8)) :
  dir_inum data 0 <> bv_0 16 -> dir_slot data 1 = 1%nat.
Proof.
  intro Hlive. apply dir_slot_char; [lia | | left; reflexivity].
  intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j. exact Hlive.
Qed.

Lemma cr_dot_record (data : nat -> list (bv 8)) (i : bv 16) :
  (forall j, (j < 16)%nat ->
     file_byte data (16 * 0 + j)%nat
     = dirent_bytes (de_of_name i (bname 14 cr_dot_f)) !!! j) ->
  dir_inum data 0 = i /\ bname 14 (dir_name data 0) = [Z_to_bv 8 0x2e].
Proof.
  intro Hb.
  destruct (dir_record_of_name data 0 i (bname 14 cr_dot_f)
              (bname_length_le 14 cr_dot_f)
              (cut_nul_nonul (bview 14 cr_dot_f)) Hb) as [Hi Hn].
  split; [exact Hi | rewrite Hn; exact cr_dot_name].
Qed.

(* the index-1 analogue, and what ESTABLISHES the [".."] half of
   [DirView.dir_dots_ix]: [dirlink(ip, "..", dp->inum)] writes record 1
   whole, so its inum is the parent's and its name is [".."]. *)
Lemma cr_dotdot_record (data : nat -> list (bv 8)) (i : bv 16) :
  (forall j, (j < 16)%nat ->
     file_byte data (16 * 1 + j)%nat
     = dirent_bytes (de_of_name i (bname 14 cr_dotdot_f)) !!! j) ->
  dir_inum data 1 = i /\ bname 14 (dir_name data 1) = dotdot_name.
Proof.
  intro Hb.
  destruct (dir_record_of_name data 1 i (bname 14 cr_dotdot_f)
              (bname_length_le 14 cr_dotdot_f)
              (cut_nul_nonul (bview 14 cr_dotdot_f)) Hb) as [Hi Hn].
  split; [exact Hi | rewrite Hn; exact cr_dotdot_name].
Qed.

(* ---- THE COMPLEMENT DOT CLAUSE AT A LIVE RECORD.  create's parent is
   live at every one of its re-parks (the guard at +0x2a), and
   [DirView.dir_orphan_clean] says nothing above [nlink = 0] -- so all six
   parent sites are this one line, with the count carried across a dirlink
   by the callee's own [di_nlink] equation. *)
Lemma cr_nl0z (d : dinode) :
  di_nlink d <> (mword_of_int 0 : mword 16) -> bv_unsigned (di_nlink d) <> 0.
Proof.
  intros Hne Hc. apply Hne. apply bv_eq. rewrite Hc. vm_compute. reflexivity.
Qed.

Lemma cr_doc_of_live (d d' : dinode) (data : nat -> list (bv 8)) :
  di_nlink d' = di_nlink d ->
  di_nlink d <> (mword_of_int 0 : mword 16) -> dir_orphan_clean d' data.
Proof.
  intros Heq Hne. apply dir_orphan_clean_live. rewrite Heq.
  exact (cr_nl0z d Hne).
Qed.

Lemma cr_first_miss_dotdot (data : nat -> list (bv 8)) (i : bv 16) :
  (forall j, (j < 16)%nat ->
     file_byte data (16 * 0 + j)%nat
     = dirent_bytes (de_of_name i (bname 14 cr_dot_f)) !!! j) ->
  dir_first data 1 (bname 14 cr_dotdot_f) = None.
Proof.
  intro Hb. apply dir_first_None. intros j Hj.
  assert (Hj0 : j = 0%nat) by lia. subst j.
  intros [_ Hn].
  destruct (cr_dot_record data i Hb) as [_ Hnm].
  rewrite Hnm cr_dotdot_name in Hn. discriminate.
Qed.

(* ---- (c) THE FIRST LINK ALWAYS ALLOCATES.  The fresh child's cell zero
   is zero ([fresh_shape]'s all-zero [addrs] through [inode_ok]'s
   [di_addrs = bm_cells]) and the sixteen bytes that went in make the
   file's first block COVERED, so [SpecBmap.bmap_ad] fires.  That is what
   pins [crb] at [true] for both later links -- an allocating writei
   reports [bmapstart ∈ Sb'] -- and the whole arm's ledger rests on it. *)
Lemma cr_fresh_cell0 (bm : blkmap) :
  bm_cells bm = replicate 13 (bv_0 32) ->
  length (bm_dir bm) = NDIRECT ->
  bv_unsigned (blkmap_get bm 0) = 0.
Proof.
  intros Hc Hlen.
  rewrite blkmap_get_dir; [| unfold NDIRECT; lia ].
  unfold bm_cells in Hc.
  assert (H0 : (bm_dir bm ++ [bm_ind bm])%list !! 0%nat = Some (bv_0 32))
    by (rewrite Hc; reflexivity).
  assert (Hl : (bm_dir bm ++ [bm_ind bm])%list !! 0%nat = bm_dir bm !! 0%nat)
    by (apply lookup_app_l; unfold NDIRECT in Hlen; lia).
  rewrite Hl in H0.
  rewrite (list_lookup_total_correct _ _ _ H0).
  vm_compute. reflexivity.
Qed.

Lemma cr_alloced_first (bm bm' : blkmap) :
  bv_unsigned (blkmap_get bm 0) = 0 ->
  bv_unsigned (blkmap_get bm' 0) <> 0 ->
  SpecBmap.bmap_alloced bm bm' 0 = true.
Proof.
  intros H0 H1.
  exact (SpecBmap.bmap_alloced_of_ad bm bm' 0%nat
           (SpecBmap.bmap_ad_true bm bm' 0%nat H0 H1)).
Qed.

(* ---- (d) THE ARM'S LEDGER.  Three facts feed it and every one is read
   off the walk rather than assumed: [al1 = true] (above), the walk's own
   correlation [crb1 = false -> 9 <= n3] (at [w = true] nameiparent paid
   the bitmap block and it is in the set, at [w = false] it did not pay and
   the count is one higher -- which is why [cr_mkdir_body] carries the
   disjunction), and [dl16_post]'s "an allocating writei reports the bitmap
   block".  WITHOUT THE CORRELATION THE CHAIN BUSTS BY EXACTLY ONE UNIT at
   the corner [crb1 = false], [n3 = 8]. *)
Lemma cr_u_ge10 (u : nat) : (create_units <= u)%nat -> (10 <= u)%nat.
Proof. unfold create_units, MAXOPBLOCKS. lia. Qed.

Lemma cr_n3_lo (u q2 : nat) (w : bool) :
  (create_units <= u)%nat ->
  ((u - (SpecNamex.walk_spend w + 0))%nat <= S (S q2))%nat ->
  w = false -> (9 <= S q2)%nat.
Proof.
  intros Hu Hn Hw. rewrite Hw in Hn.
  pose proof (cr_u_ge10 u Hu) as H10.
  unfold SpecNamex.walk_spend in Hn. lia.
Qed.

(* the FIRST interior link's spend, at the two unknown booleans: [cru] is
   true (create's own ialloc/iupdate put the child's inode block in the
   set) and the window is DIRECT (slot 0 of a fresh child), so it is at
   most two -- which is what leaves the second link its four. *)
Lemma cr_mkdir_dl1 (nc n' : nat) (crb crd al : bool) :
  ((nc - wi16_spend crb crd true al false)%nat <= n')%nat ->
  ((nc - 2)%nat <= n')%nat.
Proof.
  intro H. unfold wi16_spend, SpecBmap.bmap_cost in *.
  destruct crb, crd, al; simpl in *; lia.
Qed.

Lemma cr_mkdir_dl3_need (n3 n4 n5 : nat)
    (crb1 crd1 crb2 crd2 al2 crb3 ind3 : bool) :
  (8 <= n3)%nat ->
  (crb1 = false -> (9 <= n3)%nat) ->
  ((n3 - wi16_spend crb1 crd1 true true false)%nat <= n4)%nat ->
  ((n4 - wi16_spend crb2 crd2 true al2 false)%nat <= n5)%nat ->
  crb2 = true -> crb3 = true ->
  (SpecDirlink.dl_need crb3 ind3 <= n5)%nat.
Proof.
  intros H3 Hw H4 H5 -> ->.
  unfold wi16_spend, SpecBmap.bmap_cost, SpecDirlink.dl_need,
         wi16_need, SpecBmap.bmap_need in *.
  destruct crb1; [| pose proof (Hw eq_refl) ];
    destruct crd1, crd2, al2, ind3; simpl in *; lia.
Qed.

Lemma cr_mkdir_ip (n3 n4 n5 n6 : nat)
    (crb1 crd1 crb2 crd2 al2 crb3 crd3 cru3 al3 ind3 : bool) :
  (8 <= n3)%nat ->
  (crb1 = false -> (9 <= n3)%nat) ->
  ((n3 - wi16_spend crb1 crd1 true true false)%nat <= n4)%nat ->
  ((n4 - wi16_spend crb2 crd2 true al2 false)%nat <= n5)%nat ->
  ((n5 - wi16_spend crb3 crd3 cru3 al3 ind3)%nat <= n6)%nat ->
  crb2 = true -> crb3 = true ->
  (iput_units <= n6)%nat /\ (1 <= n6)%nat.
Proof.
  intros H3 Hw H4 H5 H6 -> ->.
  unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crb1; [| pose proof (Hw eq_refl) ];
    destruct crd1, crd2, al2, crd3, cru3, al3, ind3; simpl in *; lia.
Qed.

Lemma cr_mkdir_n5 (n3 n4 n5 : nat) (crb1 crd1 crb2 crd2 al2 : bool) :
  (8 <= n3)%nat ->
  (crb1 = false -> (9 <= n3)%nat) ->
  ((n3 - wi16_spend crb1 crd1 true true false)%nat <= n4)%nat ->
  ((n4 - wi16_spend crb2 crd2 true al2 false)%nat <= n5)%nat ->
  crb2 = true -> (6 <= n5)%nat.
Proof.
  intros H3 Hw H4 H5 ->.
  unfold wi16_spend, SpecBmap.bmap_cost in *.
  destruct crb1; [| pose proof (Hw eq_refl) ];
    destruct crd1, crd2, al2; simpl in *; lia.
Qed.

(* ...and the three FAIL exits' readings.  The first two entries discharge
   [cr_fail_mkdir_body]'s LEFT disjunct outright ([8 <= n3] and a spend of
   at most two, twice); only the third needs
   [CreateBudget.cr_fail_mkdir_closes] / [_closes_ind], and it has
   [bmapstart ∈ Sb4] as well. *)
Lemma cr_mkdir_fail1 (n3 n' : nat) (crb crd al : bool) :
  (8 <= n3)%nat ->
  ((n3 - wi16_spend crb crd true al false)%nat <= n')%nat ->
  (iput_units <= n')%nat /\ (S iput_units <= n')%nat.
Proof.
  intros H3 H. unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crb, crd, al; simpl in *; lia.
Qed.

Lemma cr_mkdir_fail2 (n3 n4 n' : nat) (crb1 crd1 crb2 crd2 al2 : bool) :
  (8 <= n3)%nat ->
  ((n3 - wi16_spend crb1 crd1 true true false)%nat <= n4)%nat ->
  ((n4 - wi16_spend crb2 crd2 true al2 false)%nat <= n')%nat ->
  crb2 = true ->
  (iput_units <= n')%nat /\ (S iput_units <= n')%nat.
Proof.
  intros H3 H4 H5 ->.
  unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crb1, crd1, crd2, al2; simpl in *; lia.
Qed.

Lemma cr_mkdir_fail3 (n5 n' : nat) (crb3 crd3 cru3 al3 ind3 : bool) :
  (6 <= n5)%nat -> crb3 = true ->
  ((n5 - wi16_spend crb3 crd3 cru3 al3 ind3)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros H5 -> H.
  unfold wi16_spend, SpecBmap.bmap_cost, iput_units in *.
  destruct crd3, cru3, al3, ind3; simpl in *; lia.
Qed.

(* the slot ledger for the mkdir arm: three [dirlink]s, each net zero, so
   the count never leaves [ns - 2] except while a call holds its unit. *)
Lemma cr_ns_3 (ns : nat) : (create_slots <= ns)%nat ->
  (1 + (ns - 3))%nat = (ns - 2)%nat.
Proof. unfold create_slots. lia. Qed.

(* ===================================================================== *)
(*  2.  THE PROOF                                                         *)
(* ===================================================================== *)

Section ProofCreateMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* THE GENERATION-NAMED SHED.  [IcacheRef.inode_ref_shed] loses the
     generation, and the whole point of [nameiparent]'s
     [inode_held_ty] payout is that the share handed to ilock names the
     SAME generation as the type one-shot beside it.  Pure resource
     algebra, exactly [inode_ref_carve]'s proof with [live_frac_split]
     replaced by [live_gen_split].  ITS HOME IS [IcacheRef.v] -- it is
     stated here only because that file's rebuild cone is the whole tree
     and this increment has no other reason to pay it. *)
  Lemma cr_carve_gen (k : nat) (q s : Qp) (inum : mword 32) (g : gname) :
    inode_ref_gen k (q + s)%Qp icfg_dev inum g ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q icfg_dev inum g ∗ inode_shr_gen k s icfg_dev inum g.
  Proof. apply inode_ref_carve_gen. Qed.

  Lemma cr_shed_gen (k : nat) (q : Qp) (inum : mword 32) (g : gname) :
    inode_ref_gen k q icfg_dev inum g ⊣⊢
    inode_ref_short_gen k (q/2 + q/2)%Qp (q/2)%Qp icfg_dev inum g ∗
    inode_shr_gen k (q/2)%Qp icfg_dev inum g.
  Proof.
    pose proof (cr_carve_gen k (q/2)%Qp (q/2)%Qp inum g) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

  (* A6.145: the lo-exposed shed *)
  Lemma cr_shed_genlo (k : nat) (q : Qp) (dev inum : mword 32) (g : gname)
      (lo : nat) :
    IcacheRef.inode_ref_genlo k q dev inum g lo ⊣⊢
    IcacheRef.inode_ref_short_genlo k (q/2 + q/2)%Qp (q/2)%Qp dev inum g lo ∗
    IcacheRef.inode_shr_genlo k (q/2)%Qp dev inum g lo.
  Proof. apply IcacheRef.inode_ref_genlo_shed. Qed.

  (* the two frame slots [name[DIRSIZ]] occupies (10 and 9), carved into
     sixteen named bytes and put back.  ProofDirlink's [de] record
     verbatim -- same two slots, same alignment obligation. *)
  Lemma cr_slots_bytes (sp0 : Arch.pa) (w1 w2 : bv 64) :
    (pa_stk sp0 10) ↦₈[KT1] w1 -∗ (pa_stk sp0 9) ↦₈[KT1] w2 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true⌝ ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 10) 16.
  Proof.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "H1 H2".
    iDestruct (slot_bytes_own (KTR := KT1) with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own (KTR := KT1) with "H2") as "[%Ha2 B2]".
    iSplitR; [done |].
    change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iSplitL "B1"; [iExact "B1" | iExact "B2"].
  Qed.

  Lemma cr_bytes_slots (sp0 : Arch.pa) :
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 10) 16 ⊢
    ∃ w1 w2 : bv 64, (pa_stk sp0 10) ↦₈[KT1] w1 ∗ (pa_stk sp0 9) ↦₈[KT1] w2.
  Proof.
    intros Ha1 Ha2.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "B". change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iDestruct "B" as "[B1 B2]".
    iDestruct (bytes_own_slot (KTR := KT1) _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot (KTR := KT1) _ Ha2 with "B2") as (w2) "H2".
    iExists w1, w2. iFrame.
  Qed.

  (* the sixteen-byte local is FOURTEEN bytes of [name] and two of slack;
     [nameiparent] and [dirlookup] both want exactly the fourteen. *)
  Lemma cr_split14 (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] f j) ⊣⊢
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] f j) ∗
    ([∗ list] j ∈ seq 14 2, pa_add a j ↦ₘ[KT1] f j).
  Proof.
    change 16%nat with (14 + 2)%nat. rewrite seq_app big_sepL_app.
    reflexivity.
  Qed.

  (* ...and back: the fourteen bytes and the two of slack rejoin into the
     sixteen the frame slots are.  The two halves carry DIFFERENT byte
     functions ([nameiparent] rewrote only the fourteen), so the join has to
     produce the pointwise splice rather than reuse either. *)
  Lemma cr_join14 (a : Arch.pa) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 14 2, pa_add a j ↦ₘ[KT1] g j) -∗
    ∃ h : nat -> bv 8, ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] h j).
  Proof.
    iIntros "H1 H2".
    iExists (fun j => if decide (j < 14)%nat then f j else g j).
    rewrite cr_split14. iSplitL "H1".
    - iApply (big_sepL_impl with "H1"). iIntros "!>" (k jj Hk) "H".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      case_decide as Hd; [iExact "H" | lia].
    - iApply (big_sepL_impl with "H2"). iIntros "!>" (k jj Hk) "H".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      case_decide as Hd; [lia | iExact "H"].
  Qed.

  (* the escrow-family accessor, at create's own persistent bundles.  The
     sleeplock family's is [IcacheEscrow.ic_sleeplocks_lookup]. *)
    Lemma cr_esc_acc
      (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows /ic_boxes_all /ic_escrow.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma cr_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* the p->cwd the walk lends and gets back untouched *)
  (* NAMED, not spliced: an inline [ltac:(vm_compute; lia)] in argument
     position runs before the conclusion is unified, so its goal still has
     the [nl] evar in it and [vm_compute] does not come back
     (durable-notes' inline-[ltac:] trap). *)
  Lemma cr_nl_short_1 : bv_unsigned (mword_of_int 1 : mword 16) <= 32767.
  Proof.
    assert (H : bv_unsigned (mword_of_int 1 : mword 16) = 1)
      by (vm_compute; reflexivity).
    rewrite H. clear H. lia.
  Qed.

  Lemma cr_nl_short_0 : bv_unsigned (mword_of_int 0 : mword 16) <= 32767.
  Proof.
    assert (H : bv_unsigned (mword_of_int 0 : mword 16) = 0)
      by (vm_compute; reflexivity).
    rewrite H. clear H. lia.
  Qed.

  (* mkdir's [++] on the PARENT's count stays short, and the guard the
     walk already carries -- [di_nlink <> 32767] -- is exactly what says
     so (durable-disk 2b-inode-3). *)
  Lemma cr_nl_bump_short (x : Z) :
    x <= 32767 -> x <> 32767 -> x + 1 <= 32767.
  Proof. lia. Qed.

  Lemma cr_nl_ne_32767 (d : mword 16) :
    d <> (mword_of_int 32767 : mword 16) -> bv_unsigned d <> 32767.
  Proof.
    intros Hne Hc. apply Hne. apply bv_eq. rewrite Hc.
    vm_compute. reflexivity.
  Qed.

  (* [cr_setf] moves only major/minor/nlink, so the type and the size ride
     and only the new count has to be bounded (durable-disk 2b-inode-3). *)
  Lemma cr_setf_rec_local (dn : dinode) (mj mn nl : mword 16) :
    inode_rec_local dn -> bv_unsigned nl <= 32767 ->
    inode_rec_local (cr_setf dn mj mn nl).
  Proof.
    intros Hrl Hnl.
    apply (inode_rec_local_same_type dn _ Hrl (cr_setf_type dn mj mn nl)).
    - rewrite cr_setf_nlink. exact Hnl.
    - rewrite cr_setf_type cr_setf_size. exact (proj2 (proj2 Hrl)).
  Qed.

  (* a MAX of two multiples of sixteen is one (durable-disk 2b-inode-3:
     dirlink's size growth, at [inode_rec_local]'s granularity clause) *)
  Lemma cr_max_div16 (a b : Z) : (16 | a) -> (16 | b) -> (16 | Z.max a b).
  Proof.
    intros Ha Hb. destruct (Z.max_spec a b) as [[_ ->] | [_ ->]];
      [exact Hb | exact Ha].
  Qed.

  Lemma cr_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
  Proof. destruct V; reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE THREE NAMED BODIES (optimization.md, RULE ONE)                   *)
  (* ------------------------------------------------------------------- *)

  (* THE CONTRACT'S OWN CONTINUATION, named once so that the walk lemma's
     statement and the parked gate both speak of ONE term.  It is
     [SpecCreate.wp_create_sconf_body]'s [wp_next] callback verbatim; the
     seal (with the allocate half) closes by [iApply] straight through it. *)
  (* THE CHILD'S ROW IS SUSPENDED (durable-disk lane A, plan section 4b).
     Between create's [ip->nlink = 1] flush and its two interior dot
     entries a mkdir's child is a directory with a link count and no dots,
     which [FsStateInode.inode_local] rules out; the registry's receipt is
     what carries that window across the calls in between.  The transaction
     id is EXISTENTIAL: no arm of this function ever compares one -- what
     matters is only that the id belongs to a transaction that is still
     open, and the registry parks its token to say so. *)
  (* THE ARM ID IS EXISTENTIAL, THE TRANSACTION ID IS NOT (durable-disk
     B''-tx2).  B''-arm re-keyed the registry by arm id, so the arm needs no
     freshness and may park ANY positive share -- and create needs that,
     because by the time it arms, its parent and its fresh child are BOTH
     write-locked and each escrow holds a quarter of the transaction's
     element ([IcacheEscrow.ic_tx_dep_at] at [1/4]).  What is left is the
     HALF this registry entry parks, and it must be at the SAME [t] as the
     two arms or the three never rejoin into the whole element
     [LogInv.log_tx] closes -- so the id rides in the index, exactly as it
     does in the escrow's own [_at] form, and create's stage statements bind
     it once. *)
  Definition cr_dirty (t : nat) (i : Z) : iProp Σ :=
    (∃ k : nat, ireg_armed k t (1/2) {[i]})%I.

  (* THE THREE MOVES A SUSPENDED CHILD NEEDS, so that no arm of create
     spells the registry dance out.  ARM: hand the transaction token over
     and retag to the half-built node in one step.  RETAG under the receipt:
     the row says nothing about an armed inum, so the new node may be
     anything.  CLEAR: retag, disarm at the node that is well-formed again,
     and hand the transaction token back -- create's four exits (the FILE
     arm, the two mkdir failures, the mkdir success) each take exactly one
     of these. *)
  (* ...EACH A NON-AU MOVE of the suspended child (app-instances.md section
     7): the application's parked license pays it ([ireg_top_retag_armed_auto],
     [top_move] being everything in round A) until round E gives create's
     directory child its AU form. *)
  Lemma cr_dirty_arm (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    ftop_inv fsc_fs -∗ app_inv fsc_fs -∗ t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      cr_dirty t i ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE) "#Hi #Hai Htx Hf".
    iMod (ireg_arm E fsc_fs i t (1/2)%Qp (ftopN_sub_app E HE) with "Hi Htx")
      as (k) "Harm".
    iMod (ireg_top_retag_armed_auto E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) Logic.I with "Hi Hai Harm Hf")
      as "[Harm Hf]".
    iModIntro. iFrame "Hf". rewrite /cr_dirty. iExists k. iExact "Harm".
  Qed.

  Lemma cr_dirty_retag (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    ftop_inv fsc_fs -∗ app_inv fsc_fs -∗ cr_dirty t i -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      cr_dirty t i ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE) "#Hi #Hai Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed_auto E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) Logic.I with "Hi Hai Harm Hf")
      as "[Harm Hf]".
    iModIntro. iFrame "Hf". iExists k. iExact "Harm".
  Qed.

  Lemma cr_dirty_clear (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i n' ->
    ftop_inv fsc_fs -∗ app_inv fsc_fs -∗ cr_dirty t i -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      t ↪[ln_tx icfg_log]{#(1/2)} tt ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE Hloc) "#Hi #Hai Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed_auto E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) Logic.I with "Hi Hai Harm Hf")
      as "[Harm Hf]".
    iMod (ireg_disarm E fsc_fs k t (1/2)%Qp {[i]} i n' (ftopN_sub_app E HE) Hloc
            with "Hi Harm Hf") as "[Harm Hf]".
    iEval (rewrite difference_diag_L) in "Harm".
    iMod (ireg_release E fsc_fs k t (1/2)%Qp (ftopN_sub_app E HE) with "Hi Harm")
      as "Htx".
    iModIntro. iFrame "Htx Hf".
  Qed.

  (* ...AND THE VIEW-PRESERVING TWINS (app-instances.md section 7, round
     E1): a retag whose reading is unchanged ([FsAbsDefs.abs_of n =
     FsAbsDefs.abs_of n']) owes the application nothing, so it rides
     [InodeRegion.ireg_top_retag_armed_same] and the parked license is not
     consulted.  The FILE arm's disarm (the node does not move at all) and
     mkdir's failing-["."] arm (a bare directory at count 1 either side)
     take these; the byte-moving arms stay on the [_auto] forms above until
     round E2 gives them their AU steps. *)
  Lemma cr_dirty_retag_same (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    FsAbsDefs.abs_of n = FsAbsDefs.abs_of n' ->
    ftop_inv fsc_fs -∗ app_inv fsc_fs -∗ cr_dirty t i -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      cr_dirty t i ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE Habs) "#Hi #Hai Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed_same E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) Habs with "Hi Hai Harm Hf")
      as "[Harm Hf]".
    iModIntro. iFrame "Hf". iExists k. iExact "Harm".
  Qed.

  Lemma cr_dirty_clear_same (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    FsAbsDefs.abs_of n = FsAbsDefs.abs_of n' ->
    inode_local i n' ->
    ftop_inv fsc_fs -∗ app_inv fsc_fs -∗ cr_dirty t i -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      t ↪[ln_tx icfg_log]{#(1/2)} tt ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE Habs Hloc) "#Hi #Hai Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed_same E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) Habs with "Hi Hai Harm Hf")
      as "[Harm Hf]".
    iMod (ireg_disarm E fsc_fs k t (1/2)%Qp {[i]} i n' (ftopN_sub_app E HE) Hloc
            with "Hi Harm Hf") as "[Harm Hf]".
    iEval (rewrite difference_diag_L) in "Harm".
    iMod (ireg_release E fsc_fs k t (1/2)%Qp (ftopN_sub_app E HE) with "Hi Harm")
      as "Htx".
    iModIntro. iFrame "Htx Hf".
  Qed.

  Definition cr_cont_body
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (j : nat) (ret_tgt : mword 64)
      (CIDc : CpuId) : iProp Σ :=
    (∀ (mf : regfile) (ok made : bool)
       (k : nat) (qi s : Qp) (g : gname) (inum : mword 32)
       (dn : dinode) (bm : blkmap)
       (u' : nat) (Sb' : gset Z) (ns' : nat),
       ⌜callee_saved m mf⌝ -∗
       sie_cap_gpr KT1 mf K b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) b lks -∗
       pc_is ret_tgt -∗
       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       proc_priv γf (proc_addr j) pidv U -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       ⌜if ok then (S ns' = ns)%nat else ns' = ns⌝ -∗
       iref_slots ns' -∗
       ⌜Sb ⊆ Sb' /\ (u' <= u)%nat
         /\ (ok = true -> (iput_units <= u')%nat)⌝ -∗
       log_opS icfg_log u' Sb' -∗
       (* THE TRANSACTION TOKEN GOES WITH THE ANSWER (durable-disk B''-tx2).
          On the SUCCESS arm create returns with the child still write-locked
          and its escrow holding the arm, so the token is inside
          [SpecCreate.create_locked]'s [IcacheEscrow.ic_tx_dep] and there is
          nothing to hand back beside it; on the FAILURE arm no inode is
          locked and the whole token comes home. *)
       (if ok
        then ⌜mf !!! Regidx Ra0 = ientry k
              /\ (k < NINODE)%nat
              /\ 0 < bv_unsigned inum < 16 * Z.of_nat icfg_nib
              /\ (if made
                  then di_type dn = ty
                       /\ di_major dn = major
                       /\ di_minor dn = minor
                       /\ bv_unsigned (di_nlink dn) = 1
                       /\ (ty <> SpecDirlookup.T_DIR ->
                           dn = create_made ty major minor)
                  else ty = T_FILE
                       /\ (di_type dn = T_FILE \/ di_type dn = T_DEVICE))⌝ ∗
          create_locked pidv k qi s g inum dn bm
        else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗ log_tx icfg_log) -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE EPILOGUE FUNNEL at +0x70: [mv a0,s2], the seven [c.ldsp]s, the
     pop, [c.ret].  FOUR arms of this half reach it and three more will,
     so the continuation is ABSTRACT and the body speaks only of the
     restored registers and the frame.  Slot 5 is s3's and this half never
     writes it, which is why [w5] is the one free slot value. *)
  Definition cr_tail_body
      (j : nat) (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (b : bool)
      (lks : gset string) (CIDt : CpuId) : iProp Σ :=
    (∀ (Mt : regfile) (w5 : mword 64) (dnew : nat -> bv 8),
       ⌜cr_tregs m sp0 Mt⌝ -∗
       sie_cap_gpr KT1 Mt (K - 10)%nat b (proc_addr j) -∗
       pc_is (mword_of_int (CK + 0x70)) -∗
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] w5 -∗
       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] dnew jj) -∗
       wp_next (CID0 := CIDt) true (proc_addr j) (fun CIDf : CpuId =>
         ∀ mf : regfile,
           ⌜callee_saved m mf⌝ -∗
           ⌜mf !!! Regidx Ra0 = (Mt !!! Regidx Rs2 : mword 64)⌝ -∗
           sie_cap_gpr KT1 mf K b (proc_addr j) -∗
           pc_is ret_tgt -∗
           WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (*  ...AND THE FUNNEL ITSELF, HOISTED (D0-a pre-work A).                 *)
  (*                                                                       *)
  (*  It was an [iAssert] inside [cr_found_half], where the allocate half  *)
  (*  -- which reaches +0x70 through TWO more arms -- could not see it.    *)
  (*  Nothing about it is found-half-specific: it speaks only of the seven *)
  (*  restored registers, the ten frame slots and [kernel_text], so the    *)
  (*  five premises below are its whole context.  [cr_found_half]'s        *)
  (*  statement is byte-identical either way; it now gets the funnel by    *)
  (*  one [iDestruct] instead of a 230-line bullet.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma cr_tail_half (j : nat) (m : regfile) (sp0 ret_tgt : mword 64)
      (K : nat) (b : bool) (lks : gset string) :
    ((K - 10) + 10)%nat = K ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    kernel_text -∗
    □ wp_next (CID0 := CID) true (proc_addr j)
        (fun CIDt : CpuId => cr_tail_body j m sp0 ret_tgt K b lks CIDt).
  Proof.
    intros HKsum Hal10 Hal9 Hspm Hrt.
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext". iModIntro.
    iIntros (CIDt Hst Mt w5 dnew)
      "%HTr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb Hqc".
    destruct HTr as [HTsp HTthr].
    (* +0x70 c.mv a0,s2 : the answer register *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x70)) Ra0 Rs2 Mt
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_070 with "Htext"). }
    iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mt !!! Regidx Rs2))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mt !!! Regidx Rs2))]> Mt) with P0.
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P0 upd_ne; [exact HTsp | nz]).
    assert (Hq072 : add_vec_int (mword_of_int (CK + 0x70) : mword 64) 2
                    = mword_of_int (CK + 0x72)) by pcw.
    iEval (rewrite Hq072) in "Hpc".
    (* +0x72 .. +0x7e : the seven restores *)
    assert (HT1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HP0sp; apply cr_frm1).
    iEval (rewrite -HT1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x72)) (mword_of_int 9 : mword 6)
              Rra P0 (K - 10)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb1").
    { iApply (cri_072 with "Htext"). }
    iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
    pose (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0) with P1.
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P1 upd_ne; [exact HP0sp | nz]).
    assert (Hq074 : add_vec_int (mword_of_int (CK + 0x72) : mword 64) 2
                    = mword_of_int (CK + 0x74)) by pcw.
    iEval (rewrite Hq074) in "Hpc".
    assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HP1sp; apply cr_frm2).
    iEval (rewrite -HT2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x74)) (mword_of_int 8 : mword 6)
              Rs0 P1 (K - 10)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb2").
    { iApply (cri_074 with "Htext"). }
    iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
    pose (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1) with P2.
    assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hq076 : add_vec_int (mword_of_int (CK + 0x74) : mword 64) 2
                    = mword_of_int (CK + 0x76)) by pcw.
    iEval (rewrite Hq076) in "Hpc".
    assert (HT3 : add_vec (P2 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP2sp; apply cr_frm3).
    iEval (rewrite -HT3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x76)) (mword_of_int 7 : mword 6)
              Rs1 P2 (K - 10)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb3").
    { iApply (cri_076 with "Htext"). }
    iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
    pose (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2) with P3.
    assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hq078 : add_vec_int (mword_of_int (CK + 0x76) : mword 64) 2
                    = mword_of_int (CK + 0x78)) by pcw.
    iEval (rewrite Hq078) in "Hpc".
    assert (HT4 : add_vec (P3 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HP3sp; apply cr_frm4).
    iEval (rewrite -HT4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x78)) (mword_of_int 6 : mword 6)
              Rs2 P3 (K - 10)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb4").
    { iApply (cri_078 with "Htext"). }
    iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
    pose (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3) with P4.
    assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hq07a : add_vec_int (mword_of_int (CK + 0x78) : mword 64) 2
                    = mword_of_int (CK + 0x7a)) by pcw.
    iEval (rewrite Hq07a) in "Hpc".
    assert (HT6 : add_vec (P4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HP4sp; apply cr_frm6).
    iEval (rewrite -HT6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x7a)) (mword_of_int 4 : mword 6)
              Rs4 P4 (K - 10)%nat (m !!! Regidx Rs4 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb6").
    { iApply (cri_07a with "Htext"). }
    iIntros (CIDT5 HqT5) "Hcg Hpc Hb6".
    pose (P5 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P4).
    change (<[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P4) with P5.
    assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hq07c : add_vec_int (mword_of_int (CK + 0x7a) : mword 64) 2
                    = mword_of_int (CK + 0x7c)) by pcw.
    iEval (rewrite Hq07c) in "Hpc".
    assert (HT7 : add_vec (P5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HP5sp; apply cr_frm7).
    iEval (rewrite -HT7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x7c)) (mword_of_int 3 : mword 6)
              Rs5 P5 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb7").
    { iApply (cri_07c with "Htext"). }
    iIntros (CIDT6 HqT6) "Hcg Hpc Hb7".
    pose (P6 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P5).
    change (<[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P5) with P6.
    assert (HP6sp : P6 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hq07e : add_vec_int (mword_of_int (CK + 0x7c) : mword 64) 2
                    = mword_of_int (CK + 0x7e)) by pcw.
    iEval (rewrite Hq07e) in "Hpc".
    assert (HT8 : add_vec (P6 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HP6sp; apply cr_frm8).
    iEval (rewrite -HT8) in "Hb8".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x7e)) (mword_of_int 2 : mword 6)
              Rs6 P6 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb8").
    { iApply (cri_07e with "Htext"). }
    iIntros (CIDT7 HqT7) "Hcg Hpc Hb8".
    pose (P7 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P6).
    change (<[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P6) with P7.
    assert (HP7sp : P7 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hq080 : add_vec_int (mword_of_int (CK + 0x7e) : mword 64) 2
                    = mword_of_int (CK + 0x80)) by pcw.
    iEval (rewrite Hq080) in "Hpc".
    iEval (rewrite HT1) in "Hb1". iEval (rewrite HT2) in "Hb2".
    iEval (rewrite HT3) in "Hb3". iEval (rewrite HT4) in "Hb4".
    iEval (rewrite HT6) in "Hb6". iEval (rewrite HT7) in "Hb7".
    iEval (rewrite HT8) in "Hb8".
    (* the [name] local goes back to being two frame slots *)
    iDestruct (dlk_name_bytes with "Hnb") as "Hnbb".
    iDestruct (cr_bytes_slots sp0 Hal10 Hal9 with "Hnbb") as (w10 w9) "[Hc10 Hc9]".
    iAssert (stack_own (KTR := KT1) sp0 10) with
      "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hc9 Hc10]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
      iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
      iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
      iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
      iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
      iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
      iSplitL "Hb7"; [iExists _; iExact "Hb7" |].
      iSplitL "Hb8"; [iExists _; iExact "Hb8" |].
      iSplitL "Hc9"; [iExists _; iExact "Hc9" |].
      iSplitL "Hc10"; [iExists _; iExact "Hc10" |].
      done. }
    (* ===== +0x80 c.addi16sp sp,80 : the pop ===== *)
    assert (Hwv : add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                  = sp0) by (rewrite HP7sp; apply cr_pop).
    assert (Hpop : (P7 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
      by (rewrite Hwv; exact HP7sp).
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CK + 0x80))
              (mword_of_int 5 : mword 6) P7 (K - 10)%nat 10 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (cri_080 with "Htext"). }
    iIntros (CIDT8 HqT8) "Hcg Hpc".
    pose (P8 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P7).
    change (<[Regidx csp_rs1 := regval_into_reg
                   (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P7) with P8.
    iEval (rewrite HKsum) in "Hcg".
    assert (Hq082 : add_vec_int (mword_of_int (CK + 0x80) : mword 64) 2
                    = mword_of_int (CK + 0x82)) by pcw.
    iEval (rewrite Hq082) in "Hpc".
    (* ===== +0x82 c.ret ===== *)
    assert (CPra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (CK + 0x82)) Rra P8 K b
              ltac:(nz) with "Hcg Hpc []").
    { iApply (cri_082 with "Htext"). }
    iIntros (CIDT9 HqT9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P8 !!! Regidx Rra : mword 64) = ret_tgt)
      by (rewrite CPra; exact Hrt).
    iEval (rewrite Hretf) in "Hpc".
    assert (CPsp : P8 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P8 upd_eq. rewrite Hwv. symmetry. exact Hspm. }
    assert (CPs0 : P8 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (CPs1 : P8 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (CPs2 : P8 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_eq. reflexivity. }
    assert (CPs4 : P8 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
    assert (CPs5 : P8 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_eq. reflexivity. }
    assert (CPs6 : P8 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_eq. reflexivity. }
    assert (CPo : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
              P8 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N20 N21 N22.
      rewrite /P8 upd_ne; [| dlk_xne N2].
      rewrite /P7 upd_ne; [| dlk_xne N22].
      rewrite /P6 upd_ne; [| dlk_xne N21].
      rewrite /P5 upd_ne; [| dlk_xne N20].
      rewrite /P4 upd_ne; [| dlk_xne N18].
      rewrite /P3 upd_ne; [| dlk_xne N9].
      rewrite /P2 upd_ne; [| dlk_xne N8].
      rewrite /P1 upd_ne; [| dlk_rne2 Hcsra Hc].
      rewrite /P0 upd_ne; [| dlk_rne2 Hcsa0 Hc].
      exact (HTthr c Hc N2 N8 N9 N18 N20 N21 N22). }
    assert (CPa0 : P8 !!! Regidx Ra0 = (Mt !!! Regidx Rs2 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_ne; [| nz].
      rewrite /P0 upd_eq. apply add_vec_zero_l. }
    iSpecialize ("Hqc" $! CIDT9 with "[%]"); [wp_next_chain |].
    iApply ("Hqc" $! P8 with "[%] [%] Hcg Hpc").
    - unfold callee_saved. split_and!;
        first [ exact CPsp | exact CPs0 | exact CPs1 | exact CPs2
              | exact CPs4 | exact CPs5 | exact CPs6
              | apply CPo; first [ vm_compute; reflexivity
                                 | vm_compute; discriminate ] ].
    - exact CPa0.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE PARKED GATE: the whole ALLOCATE half, +0xa2 onward               *)
  (*                                                                       *)
  (*  Reached ONLY by the [c.beqz a0] at +0x4c being TAKEN, i.e. by        *)
  (*  dirlookup missing.  At that point s2 = a0 = 0 (the [mv s2,a0] at     *)
  (*  +0x4a stored dirlookup's zero), the parent is LOCKED and LOADED, and *)
  (*  the ledger stands at [n1] with [Sb1].                                *)
  (*                                                                       *)
  (*  It is a HYPOTHESIS of [cr_found_half], not an axiom: the allocate    *)
  (*  half will be an ordinary block lemma of this shape and the seal will *)
  (*  compose the two.  The parent's payload is handed over in PIECES      *)
  (*  rather than as [IcacheEscrow.ic_loaded] because the allocate half's  *)
  (*  [dirlink(dp,name)] takes [inode_meta] / [inode_map] / [inode_blocks] *)
  (*  at a NAMED [data], and re-parking is one [iExists] away.             *)
  (* ------------------------------------------------------------------- *)
  Definition cr_alloc_body
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (CIDa : CpuId) : iProp Σ :=
    (∀ (Ma : regfile) (w5 : mword 64)
       (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf : nat -> bv 8) (nsl : nat -> bv 8)
       (n1 : nat) (Sb1 : gset Z) (w : bool) (t : nat),
       (* the frozen decisions of the found half *)
       ⌜cr_regs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
          ty major minor Ma⌝ -∗
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
       (* THE NLINK_MAX GATE'S FALL-THROUGH, in the only form the DIAMOND
          can deliver it.  +0x3e is reached two ways: the [c.bnez] at +0x36
          TAKEN (the count is not at the maximum) and the [c.beqz] at +0x3c
          FALLING THROUGH (the type is not T_DIR).  Neither arm alone gives
          an unconditional bound, and their join is exactly this
          implication -- which is all the mkdir sub-branch needs, since it
          runs at [ty = T_DIR].  It is a WALK-LEVEL fact: no contract
          premise anywhere, and none of the "no name for dp" trouble the
          eleventh stop ruled fatal. *)
       ⌜ty = SpecDirlookup.T_DIR ->
          di_nlink dn <> (mword_of_int 32767 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dn bm data⌝ -∗
       ⌜dir_ok icfg_nib dn data⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dind) dn data⌝ -∗
       ⌜dir_uniq dn data⌝ -∗
       (* durable-disk 2b-inode-3: the payload's record-only facts, which
          [IcacheEscrow.ic_mk_loaded] needs of the record this half parks. *)
       ⌜inode_rec_local dn⌝ -∗
       ⌜exists es e, nameiparent_of (bview plen pfun) es e
                     /\ bname 14 nf = e⌝ -∗
       ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn)))
                  (bname 14 nf) = None⌝ -∗
       (* the ledger, as the found half leaves it *)
       ⌜Sb ⊆ Sb1⌝ -∗
       ⌜w = true -> fsc_bmapstart ∈ Sb1⌝ -∗
       ⌜((u - (SpecNamex.walk_spend w + 0))%nat <= n1)%nat /\ (n1 <= u)%nat⌝ -∗
       (* the machine *)
       sie_cap_gpr KT1 Ma (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) b lks -∗
       pc_is (mword_of_int (CK + 0xa2)) -∗
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] w5 -∗
       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nsl jj) -∗
       (* THE LOCKED PARENT, in pieces *)
       is_sleeplock_genl γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       (∃ lodc tldc : nat,
          ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
          ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/2))) -∗
          off_rows off_cfg kd cur_ctx -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at fsc_ireg dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map fsc_fs (ientry kd) bm -∗
       inode_blocks fsc_fs bm data -∗
       (* ...and the era's abstract value, which the half retags at its
          own write (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dn bm data) -∗
       ity_shot gd (di_type dn) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
            icfg_dev dind gd lo) -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* everything the contract still owes back *)
       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
       proc_priv γf (proc_addr j) pidv U -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 1) -∗
       log_opS icfg_log n1 Sb1 -∗
       (* ...and THE HOLDER'S RESIDUE (durable-disk B''-tx2): the parent's
          escrow holds the other half of this transaction's element, and
          this arm's child needs the residue to suspend its row with. *)
       t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
       (* and the contract's own continuation, ANCHORED AT THE ENTRY HART
          (ProofDirlink's [dl_after_body]): the block's own proof does the
          retargeting, so this file hands over [Hcont] untouched. *)
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γf
 plen pfun pv ty major minor
                         U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (*  THE TWO BODIES THE C-OK-FILE WALK PARKS (D0-a).                      *)
  (*                                                                       *)
  (*  Both are HYPOTHESES of [cr_alloc_half], exactly as [cr_alloc_body]   *)
  (*  is a hypothesis of [cr_found_half]: [Print Assumptions] sees         *)
  (*  neither, and whoever proves them composes.                          *)
  (*                                                                       *)
  (*  [cr_mkdir_body] is the [beq s4,a4] at +0xca TAKEN, i.e. the whole    *)
  (*  T_DIR sub-branch (+0xf8..+0x144: the two interior [dirlink]s on the  *)
  (*  child, the parent's [dirlink], its [nlink++] and its [iupdate]).     *)
  (*  D0-b consumes it.  Note what it is handed and what it is NOT: the    *)
  (*  child's link fragment is UNDEPOSITED -- +0xc4 minted it and the      *)
  (*  non-directory arm spends it at +0xd8, so on this branch it is still  *)
  (*  in hand and the mkdir arm's own [dirlink(dp,name)] at +0x12c is      *)
  (*  what spends it.                                                     *)
  (*                                                                       *)
  (*  [cr_fail_body] is +0x146, reached HERE only from the [bltz] at       *)
  (*  +0xdc (the other three entries are behind the T_DIR branch and       *)
  (*  therefore inside [cr_mkdir_body]), so a LINEAR premise is right and  *)
  (*  D0-b will re-shape it into the persistent four-entry form.  It is    *)
  (*  handed the parent's [dlinks] AT THE ENTRY INDICES together with     *)
  (*  the undeposited fragment and dirlink's own range clause, and NOT a   *)
  (*  re-parked payload: at [0 < tot < 16] a partial record has gone LIVE  *)
  (*  wanting a fragment this arm does not have, so no re-park exists at   *)
  (*  all -- which is why dirlink's atomicity clause is what it relies on. *)
  (* ------------------------------------------------------------------- *)
  Definition cr_mkdir_body
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (* ---- what the found half froze, i.e. [cr_alloc_body]'s own binders *)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDm : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname) (lo tl : nat)
       (cinum : mword 32) (dnc : dinode) (bmc : blkmap)
       (datc : nat -> list (bv 8)) (n3 : nat) (Sb3 : gset Z),
       (* the register file: s1 = dp, s2 = 0, s3 = ip, and s3's saved word
          is still [m]'s own in slot 5 *)
       ⌜cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64) (ientry kslot)
          ty major minor Mx⌝ -∗
       (* THE BRANCH ITSELF: +0xca is taken exactly on [ty = T_DIR] *)
       ⌜ty = SpecDirlookup.T_DIR⌝ -∗
       (* the parent, as the found half left it *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
       (* ...AND THE GATE'S FALL-THROUGH, DISCHARGED: this branch runs at
          [ty = T_DIR], so [cr_alloc_body]'s implication collapses to the
          bound itself.  It is what [SpecIupdate.wp_iupdate_link] takes at
          +0x140 beside the [sh]'s own value, and without it the flush --
          hence the whole arm, since the fragment at [dind] it mints is the
          only one for the [".."] written at +0x11a -- is unprovable. *)
       ⌜di_nlink dn <> (mword_of_int 32767 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dn bm data⌝ -∗
       ⌜dir_ok icfg_nib dn data⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dind) dn data⌝ -∗
       ⌜dir_uniq dn data⌝ -∗
       (* durable-disk 2b-inode-3: the payload's record-only facts, which
          [IcacheEscrow.ic_mk_loaded] needs of the record this half parks. *)
       ⌜inode_rec_local dn⌝ -∗
       ⌜exists es e, nameiparent_of (bview plen pfun) es e
                     /\ bname 14 nf = e⌝ -∗
       ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn)))
                  (bname 14 nf) = None⌝ -∗
       (* the child, as the gate and the three [sh]s left it *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < fsc_ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts, at the
          record this half parks (the count [cr_setf] writes is a literal,
          so only the enumeration really travels). *)
       ⌜inode_rec_local dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dnc bmc datc⌝ -∗
       ⌜dir_ok icfg_nib dnc datc⌝ -∗
       (* the ledger *)
       ⌜Sb ⊆ Sb3⌝ -∗
       ⌜IBLOCK cinum icfg_ist ∈ Sb3⌝ -∗
       ⌜(8 <= n3)%nat /\ (n3 <= u)%nat⌝ -∗
       (* THE WALK'S OWN nameiparent CORRELATION, and the arm cannot close
          without it.  [8 <= n3] alone busts this chain by EXACTLY one unit
          at [crb1 = false], [n3 = 8]: the three [dirlink]s plus the
          parent's [iupdate] leave [iput_units] with ZERO slack
          ([CreateBudget.cr_budget_mkdir]'s [u6 = 3]).  What closes it is
          that the two are not independent -- at [w = true] nameiparent
          PAID for the bitmap block, so it is in the set and the first
          interior link absorbs; at [w = false] it did not pay and the
          count is one higher.  Free at [cr_alloc_half], which holds both
          halves ([w = true -> bmapstart ∈ Sb1] and [create_units <= u]). *)
       ⌜fsc_bmapstart ∈ Sb3 \/ (9 <= n3)%nat⌝ -∗
       (* the machine *)
       sie_cap_gpr KT1 Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) b lks -∗
       pc_is (mword_of_int (CK + 0xf8)) -∗
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nsl jj) -∗
       (* THE LOCKED PARENT, in pieces *)
       is_sleeplock_genl γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       (∃ lodc tldc : nat,
          ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
          ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4))) -∗
          off_rows off_cfg kd cur_ctx -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at fsc_ireg dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map fsc_fs (ientry kd) bm -∗
       inode_blocks fsc_fs bm data -∗
       (* ...and the era's abstract value, which the half retags at its
          own write (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dn bm data) -∗
       ity_shot gd (di_type dn) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
            icfg_dev dind gd lo) -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD, in pieces, at the FLUSHED record *)
       is_sleeplock_genl gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_slp fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       (∃ locc tlcc : nat,
          ⌜(locc <= tlcc)%nat⌝ ∗ IcacheRef.cred_floor locc tlcc ∗
          ic_handle fsc_ic kslot (DepTx (q/2)%Qp icfg_dev cinum g locc t (1/4))) -∗
          off_rows off_cfg kslot cur_ctx -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned cinum) dnc bmc datc -∗
       dinode_at fsc_ireg cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* ...and the CHILD's abstract value, at the same record *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc) -∗
       ity_shot g (di_type dnc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       ⌜(lo <= tl)%nat⌝ -∗ IcacheRef.cred_floor lo tl -∗
       IcacheRef.inode_ref_short_genlo kslot (q/2 + q/2)%Qp (q/2)%Qp icfg_dev cinum g lo -∗
       (* the child's PROVENANCE UNIT (item 7a-wire). *)
       runit_any (bv_unsigned cinum) -∗
       (* THE MINT, UNDEPOSITED (durable-disk 2b-inode-5):
          the [ip->nlink = 0] flush returns it to the region on the fail
          arms, and the [dirlink] files it in [dp] on the mkdir arm. *)
       (* ...AND IT IS A PILE (lane G5): the fill minted [cr_delta ty] of
          them at the value it CHOSE, [cr_ity ty dp]. *)
       FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
         (FsStateLink.link_reps (cr_delta ty)
            (cr_ity ty (bv_unsigned dind))) -∗
       (* everything the contract still owes back *)
       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
       proc_priv_bare (proc_addr j) pidv U -∗
       (proc_priv_bare (proc_addr j) pidv U -∗
          proc_priv γf (proc_addr j) pidv U) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS icfg_log n3 Sb3 -∗
       (* THE CHILD'S ROW IS SUSPENDED: it is a directory with a link
          count and no dots until the interior dirlinks land, so the arm
          carries the registry's receipt (durable-disk lane A) *)
       cr_dirty t (bv_unsigned cinum) -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γf
 plen pfun pv ty major minor
                         U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition cr_fail_body
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDf : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname) (lo tl : nat)
       (cinum : mword 32) (dnc : dinode) (bmc : blkmap)
       (datc : nat -> list (bv 8))
       (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
       (tot : nat) (n4 : nat) (Sb4 : gset Z),
       ⌜cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64) (ientry kslot)
          ty major minor Mx⌝ -∗
       ⌜ty <> SpecDirlookup.T_DIR⌝ -∗
       (* the parent's ENTRY facts *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dn bm data⌝ -∗
       ⌜dir_ok icfg_nib dn data⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dind) dn data⌝ -∗
       ⌜dir_uniq dn data⌝ -∗
       (* durable-disk 2b-inode-3: the payload's record-only facts, which
          [IcacheEscrow.ic_mk_loaded] needs of the record this half parks. *)
       ⌜inode_rec_local dn⌝ -∗
       (* the child *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < fsc_ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts, at the
          record this half parks (the count [cr_setf] writes is a literal,
          so only the enumeration really travels). *)
       ⌜inode_rec_local dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dnc bmc datc⌝ -∗
       ⌜dir_ok icfg_nib dnc datc⌝ -∗
       (* WHAT THE FAILING [dirlink(dp,name)] AT +0xd8 LEFT, verbatim from
          [SpecDirlink]'s append arm.  The [bltz] at +0xdc having fired says
          [tot < 16]; with dirlink's ATOMICITY clause (relayed from
          [SpecWritei.wi16_atomic], D0-c) that IS [tot = 0], and the arm
          needs the sharper form: it re-parks the parent's [dlinks]
          unchanged before +0x158's [iunlockput(dp)], and at [0 < tot < 16]
          no re-park exists (a partial record has gone live wanting a
          fragment, and the one in hand is what +0x14c spends).  The RE-PARK is still the body's own work, as before --
          what changed is that it is now possible. *)
       ⌜tot = 0%nat⌝ -∗
       (* NO CLAUSE ABOUT THE BITMAP.  The block bitmap is the persistent
          [BitmapInv.bitmap_inv] now: the fail tail neither reports nor
          receives a set. *)
       ⌜blkmap_wf fsc_cov fsc_logst bm'⌝ -∗
       ⌜blk_holes_zero bm' data'⌝ -∗
       ⌜di_addrs dn' = bm_cells bm'⌝ -∗
       ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
       ⌜bm_covers bm' (bv_unsigned (di_size dn'))⌝ -∗
       ⌜bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE⌝ -∗
       ⌜inode_sized data'⌝ -∗
       ⌜dn' = wi_dinode dn bm'
                (16 * dir_slot data (dir_nrec (bv_unsigned (di_size dn))))%nat
                tot⌝ -∗
       ⌜dn0' = dn'⌝ -∗
       ⌜forall x : nat,
          file_byte data' x
          = if decide ((16 * dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn))) <= x)%nat
                       /\ (x < 16 * dir_slot data
                             (dir_nrec (bv_unsigned (di_size dn))) + tot)%nat)
            then dirent_bytes
                   (de_of_name (cr_low16 cinum) (bname 14 nf))
                   !!! (x - 16 * dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn))))%nat
            else file_byte data x⌝ -∗
       (* the ledger, at the figure [CreateBudget.cr_fail_closes_at_zero]
          and [cr_fail_closes_with_credit] are the theorems for *)
       ⌜Sb ⊆ Sb4⌝ -∗
       ⌜IBLOCK cinum icfg_ist ∈ Sb4⌝ -∗
       ⌜(iput_units <= n4)%nat /\ (n4 <= u)%nat⌝ -∗
       (* THE ARM'S SECOND [iunlockput] IS WHAT THIS SAYS (D0-c).  The tail
          runs TWO of them and the first is entered UNCREDITED on the bitmap
          ([bmapstart ∈ Sb4] is not a fact any route into [fail:] carries),
          so its post admits the report [w = true] and spends one whatever
          [cru]/[crz] say -- and [iunlockput(dp)] then wants [iput_units] out
          of [n4 - 1].  Either disjunct closes it: the LEFT gives the unit
          outright, the RIGHT buys [crb := true], which pins [w = false]
          (fs-log.md §G.25) and makes the first call free.  Both are
          suppliable at every entry -- +0xdc has FOUR unconditionally
          ([cr_alloc_ip4]: eight in, [wi16_spend <= 4]), and the two interior
          mkdir entries, which sit at exactly three, reach their failing
          dirlink with the bitmap block already logged.  A single
          [S iput_units <= n4] would have re-blocked those two. *)
       ⌜(S iput_units <= n4)%nat \/ fsc_bmapstart ∈ Sb4⌝ -∗
       (* the machine *)
       sie_cap_gpr KT1 Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) b lks -∗
       pc_is (mword_of_int (CK + 0x146)) -∗
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nsl jj) -∗
       (* THE LOCKED PARENT, in pieces, at the POST-dirlink indices --
          with [dlinks] still at the ENTRY ones and the fragment in hand *)
       is_sleeplock_genl γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       (∃ lodc tldc : nat,
          ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
          ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4))) -∗
          off_rows off_cfg kd cur_ctx -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at fsc_ireg dind dn0' -∗
       inode_meta (ientry kd) dn' -∗
       inode_map fsc_fs (ientry kd) bm' -∗
       inode_blocks fsc_fs bm' data' -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       (* THE PARENT'S FRAGMENT ARRIVES UNRETAGGED (durable-disk lane A):
          the retag owes the registry's row, and the post record's
          well-formedness is assembled inside [cr_fail_half] (its
          [Hiok']/[Hrl']/[Hduq']/[Hddix']), not at the hand-over. *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dn bm data) -∗
       ity_shot gd (di_type dn) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
            icfg_dev dind gd lo) -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD, at the flushed record *)
       is_sleeplock_genl gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_slp fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       (∃ locc tlcc : nat,
          ⌜(locc <= tlcc)%nat⌝ ∗ IcacheRef.cred_floor locc tlcc ∗
          ic_handle fsc_ic kslot (DepTx (q/2)%Qp icfg_dev cinum g locc t (1/4))) -∗
          off_rows off_cfg kslot cur_ctx -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned cinum) dnc bmc datc -∗
       dinode_at fsc_ireg cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* ...and the CHILD's abstract value, at the same record *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc) -∗
       ity_shot g (di_type dnc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       ⌜(lo <= tl)%nat⌝ -∗ IcacheRef.cred_floor lo tl -∗
       IcacheRef.inode_ref_short_genlo kslot (q/2 + q/2)%Qp (q/2)%Qp icfg_dev cinum g lo -∗
       (* the child's PROVENANCE UNIT (item 7a-wire). *)
       runit_any (bv_unsigned cinum) -∗
       (* THE MINT, UNDEPOSITED (durable-disk 2b-inode-5):
          the [ip->nlink = 0] flush returns it to the region on the fail
          arms, and the [dirlink] files it in [dp] on the mkdir arm. *)
       (* ...AND IT IS A PILE (lane G5): the fill minted [cr_delta ty] of
          them at the value it CHOSE, [cr_ity ty dp]. *)
       FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
         (FsStateLink.link_reps (cr_delta ty)
            (cr_ity ty (bv_unsigned dind))) -∗
       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
       proc_priv_bare (proc_addr j) pidv U -∗
       (proc_priv_bare (proc_addr j) pidv U -∗
          proc_priv γf (proc_addr j) pidv U) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS icfg_log n4 Sb4 -∗
       (* ...and the transaction token, which this arm's child needs to
          suspend its row with (durable-disk lane A) *)
       t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γf
 plen pfun pv ty major minor
                         U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.


  (* =================================================================== *)
  (*  3.  THE WALK                                                        *)
  (* =================================================================== *)




  (* =================================================================== *)
  (*  4.  THE ALLOCATE HALF, +0xa2 .. +0xea                               *)
  (*                                                                      *)
  (*  [cr_alloc_half] discharges [cr_alloc_body]: the eighth save, the     *)
  (*  fresh-type gate span, ARM A-FAIL, the three metadata [sh]s, the      *)
  (*  MINT at +0xc4, the T_DIR branch and ARM C-OK-FILE.  Two branches     *)
  (*  leave through a PREMISE -- the T_DIR sub-branch through              *)
  (*  [cr_mkdir_body] and the failing [dirlink] through [cr_fail_body] --  *)
  (*  so [Print Assumptions] sees the standing six and nothing else.      *)
  (*                                                                      *)
  (*  THE LEDGER, in one place: the walk enters at [n1 >= 9], the gate     *)
  (*  spends ialloc's ONE unit (so it runs at [u := q1] where              *)
  (*  [n1 = S q1 >= 9], i.e. [q1 >= 8]), the mint at +0xc4 is CREDITED     *)
  (*  ([cru := true], because the gate's own payout put [IBLOCK cinum] in  *)
  (*  the set) and therefore spends nothing, and the [dirlink] at +0xd8    *)
  (*  reports the credit-aware figure that [cr_alloc_ip] turns into the    *)
  (*  [iput_units] its [iunlockput(dp)] needs.  [CreateBudget.             *)
  (*  cr_budget_file] is the theorem; the three lemmas above are it at the *)
  (*  figures the CONTRACTS state.                                        *)
  (* =================================================================== *)



  (* =================================================================== *)
  (*  4.  ARM FAIL, +0x146..+0x15e -- [cr_fail_body] PROVEN (D0-c)        *)
  (*                                                                      *)
  (*  The tail xv6 runs when a [dirlink] on the fresh child could not be  *)
  (*  written: zero the child's link count, flush it, put the child (the  *)
  (*  put that FREES), put the parent, restore s3 and funnel out with     *)
  (*  [s2 = 0].  Five calls' worth of walking and three findings, all of  *)
  (*  them about what the arm may CLAIM rather than about any step:       *)
  (*                                                                      *)
  (*  (1) THE FLUSH AT +0x14c IS [wp_iupdate_unlink] AND IT TAKES THE     *)
  (*      RECEIPT PREMISE ON THE LEFT (fs-log.md §G.23's C4): the record  *)
  (*      it writes has [nlink = 0], so the witness route is the only     *)
  (*      one, and its two ambient ties are create's own premises.  The   *)
  (*      fragment the +0xc4 mint made is what pays for the decrement -- *)
  (*      it is consumed here, which is why the parent's re-park below    *)
  (*      may not want one.                                               *)
  (*                                                                      *)
  (*  (2) THE FREEING PUT AT +0x152 RUNS ON [cru], NOT ON [crz].          *)
  (*      [SpecIput.ip_spend_w] is [ip_bm w + (if cru || crz then 0 else  *)
  (*      1)]: the two credits buy the SAME unit, and create -- unlike a  *)
  (*      walker -- can make the own-set claim, because its own [ialloc]  *)
  (*      and [iupdate] logged the child's inode block and the flush      *)
  (*      above unions it in again.  So no [InodeRegion.nlz_obs] is       *)
  (*      minted anywhere on this arm.  It could not have been: the mint  *)
  (*      needs [nlink <> 0] and therefore must run BEFORE +0x14c, while  *)
  (*      the credit needs the epoch of the [log_opSe] handed to the iput *)
  (*      and [wp_iupdate_unlink] re-closes that existential -- two lower *)
  (*      bounds on the epoch counter are incomparable (fs-log.md §G.14), *)
  (*      so the two epochs cannot be related.  A [crz] fail arm would    *)
  (*      need a SEVENTH iupdate body ([log_opSe] in and out), not a      *)
  (*      different mint placement.                                       *)
  (*                                                                      *)
  (*  (3) THE BITMAP REPORT IS WHY THE BODY CARRIES ITS DISJUNCTION.      *)
  (*      The call is entered at [crb := bool_decide (bmapstart ∈ Sb)] --  *)
  (*      the honest reading, and the ONE call the arm makes either way,  *)
  (*      so the walk is not duplicated.  Where that is true the report   *)
  (*      is pinned [w = false] and the freeing put is free; where it is  *)
  (*      false the body's other disjunct pays the unit.  Both readings   *)
  (*      land on [iput_units <= n5], which is what +0x158 needs.         *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  4.  THE T_DIR SUB-BRANCH'S [fail:] TWIN                             *)
  (*                                                                      *)
  (*  [cr_fail_body] is the NON-directory entry (+0xdc's [bltz] only).     *)
  (*  The mkdir arm reaches the SAME code at +0x146 from three more        *)
  (*  [bltz]es (+0x10a / +0x11e / +0x130) and cannot use that body: its    *)
  (*  child IS a directory, so its payload has records to account for.     *)
  (*                                                                      *)
  (*  The [sh zero,74(s3)] at +0x146 is what pays for it: at count zero    *)
  (*  the child is an ORPHAN, its live records are exactly ["."] and       *)
  (*  [".."] ([DirView.dir_orphan_clean]), and both are tokenless -- so    *)
  (*  its re-parked [dlinks] is [FsStateEra.ent_toks_era_dots_only]'s      *)
  (*  empty marker set and nothing is owed.  (Until lane G6 this arm also  *)
  (*  had to rebuild the old ledger's grey big-op from [ireg_inv], design  *)
  (*  C1's free mint; the ledger is gone and so is the mint's consumer.)   *)
  (* =================================================================== *)

  (* ---- (b) THE BODY ------------------------------------------------- *)
  Definition cr_fail_mkdir_body
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDf : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname) (lo tl : nat)
       (cinum : mword 32)
       (dp : dinode) (bmp : blkmap) (datap : nat -> list (bv 8))
       (dc : dinode) (bmc : blkmap) (datc : nat -> list (bv 8))
       (n4 : nat) (Sb4 : gset Z),
       ⌜cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64) (ientry kslot)
          ty major minor Mx⌝ -∗
       ⌜ty = SpecDirlookup.T_DIR⌝ -∗
       (* THE PARENT, at whatever record the entry reached [fail:] with --
          and ALREADY RE-PARKED.  All three entries sit BEFORE the +0x134
          [lhu], so the count is the entry one and the walk has already
          put the entry fragments back. *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dp = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dp <> (mword_of_int 0 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dp bmp datap⌝ -∗
       ⌜dir_ok icfg_nib dp datap⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dind) dp datap⌝ -∗
       ⌜dir_uniq dp datap⌝ -∗
       (* durable-disk 2b-inode-3: the PARENT's record-only facts *)
       ⌜inode_rec_local dp⌝ -∗
       (* THE CHILD, as an ABSTRACT record: what the three entries share is
          not its size (0, 1 or 2 records) but its FIELDS -- the three [sh]s
          at +0xb4/+0xb8/+0xbe put [major]/[minor]/1 there and no dirlink
          moves them, which is what makes the [sh zero,74(s3)] below land on
          [cr_setf dc major minor 0]. *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < fsc_ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dc = ty⌝ -∗
       ⌜di_major dc = major⌝ -∗
       ⌜di_minor dc = minor⌝ -∗
       ⌜di_nlink dc = (mword_of_int 1 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dc bmc datc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts *)
       ⌜inode_rec_local dc⌝ -∗
       ⌜dir_ok icfg_nib dc datc⌝ -∗
       ⌜dir_uniq dc datc⌝ -∗
       (* ...AND WHAT THE CHILD'S RECORDS ARE.  Stated as the CONTENT form
          [DirView.dir_dots_only] rather than the guarded
          [dir_orphan_clean], and that is forced: the entry hands the child
          over at [nlink = 1], where the guarded clause is VACUOUS, and the
          [sh zero,74(s3)] at +0x146 then parks it at [nlink = 0], where it
          is DEMANDED.  A guarded premise would therefore carry nothing in
          and owe everything out.  The three entries supply it from what
          their own interior links wrote -- nothing at [nrec = 0], the
          ["."] alone at [nrec = 1], both dots at [nrec = 2] -- which is
          why the clause's bound is [dir_nrec] and not a size equation. *)
       ⌜dir_dots_only dc datc⌝ -∗
       (* the ledger, at [cr_fail_body]'s own two figures *)
       ⌜Sb ⊆ Sb4⌝ -∗
       ⌜IBLOCK cinum icfg_ist ∈ Sb4⌝ -∗
       ⌜(iput_units <= n4)%nat /\ (n4 <= u)%nat⌝ -∗
       ⌜(S iput_units <= n4)%nat \/ fsc_bmapstart ∈ Sb4⌝ -∗
       (* the machine *)
       sie_cap_gpr KT1 Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) b lks -∗
       pc_is (mword_of_int (CK + 0x146)) -∗
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nsl jj) -∗
       (* THE LOCKED PARENT *)
       is_sleeplock_genl γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       (∃ lodc tldc : nat,
          ⌜(lodc <= tldc)%nat⌝ ∗ IcacheRef.cred_floor lodc tldc ∗
          ic_handle fsc_ic kd (DepTx (qd/2)%Qp icfg_dev dind gd lodc t (1/4))) -∗
          off_rows off_cfg kd cur_ctx -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dp bmp datap -∗
       dinode_at fsc_ireg dind dp -∗
       inode_meta (ientry kd) dp -∗
       inode_map fsc_fs (ientry kd) bmp -∗
       inode_blocks fsc_fs bmp datap -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dp bmp datap) -∗
       ity_shot gd (di_type dp) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          IcacheRef.inode_ref_short_genlo kd (qd/2 + qd/2)%Qp (qd/2)%Qp
            icfg_dev dind gd lo) -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD -- WITHOUT its [dlinks] (see the header) *)
       is_sleeplock_genl gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_slp fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       (∃ locc tlcc : nat,
          ⌜(locc <= tlcc)%nat⌝ ∗ IcacheRef.cred_floor locc tlcc ∗
          ic_handle fsc_ic kslot (DepTx (q/2)%Qp icfg_dev cinum g locc t (1/4))) -∗
          off_rows off_cfg kslot cur_ctx -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dinode_at fsc_ireg cinum dc -∗
       inode_meta (ientry kslot) dc -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* ...and the CHILD's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum) (era_node dc bmc datc) -∗
       ity_shot g (di_type dc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       ⌜(lo <= tl)%nat⌝ -∗ IcacheRef.cred_floor lo tl -∗
       IcacheRef.inode_ref_short_genlo kslot (q/2 + q/2)%Qp (q/2)%Qp icfg_dev cinum g lo -∗
       (* the child's PROVENANCE UNIT (item 7a-wire). *)
       runit_any (bv_unsigned cinum) -∗
       (* THE MINT, still undeposited -- the +0x14c flush spends it
          (durable-disk 2b-inode-5):
          the [ip->nlink = 0] flush returns it to the region on the fail
          arms, and the [dirlink] files it in [dp] on the mkdir arm. *)
       (* ...AND IT IS A PILE (lane G5): the fill minted [cr_delta ty] of
          them at the value it CHOSE, [cr_ity ty dp]. *)
       FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
         (FsStateLink.link_reps (cr_delta ty)
            (cr_ity ty (bv_unsigned dind))) -∗
       sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
       proc_priv_bare (proc_addr j) pidv U -∗
       (proc_priv_bare (proc_addr j) pidv U -∗
          proc_priv γf (proc_addr j) pidv U) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS icfg_log n4 Sb4 -∗
       (* THE CHILD'S ROW IS SUSPENDED: it is a directory with a link
          count and no dots until the interior dirlinks land, so the arm
          carries the registry's receipt (durable-disk lane A) *)
       cr_dirty t (bv_unsigned cinum) -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γf
 plen pfun pv ty major minor
                         U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ---- (c) THE HALF -------------------------------------------------- *)


  (* =================================================================== *)
  (*  5.  THE T_DIR SUB-BRANCH, +0xf8 .. +0x144 -- [cr_mkdir_body] PROVEN *)
  (*                                                                      *)
  (*  Three [dirlink]s, the parent's [nlink++], its flush, and [c.j +0xe0] *)
  (*  into ARM C-OK's own block (which this arm therefore re-walks: the    *)
  (*  join is BELOW [cr_alloc_half]'s branch, so there is nothing to       *)
  (*  share).  The three [bltz]es at +0x10a / +0x11e / +0x130 all leave    *)
  (*  through [cr_fail_mkdir_half], which this proof instantiates itself   *)
  (*  -- its premises are all persistent, so one lemma serves three        *)
  (*  mutually exclusive branches with no extra hypothesis.                *)
  (*                                                                      *)
  (*  THE TWO INTERIOR LINKS' FRAGMENTS.  The [ "." ] record names the     *)
  (*  child ITSELF, and its fragment is the child's OWN self-unit out of   *)
  (*  the pile the fill minted; the [ ".." ] record names the PARENT and    *)
  (*  its fragment is the one the +0x140 flush mints -- so the child's     *)
  (*  re-park is DEFERRED across the whole rest of the arm and completed   *)
  (*  after the mint.  The parent's own round trip across the [++] opens   *)
  (*  its [dlinks] and re-seals it with the exactness equation restored    *)
  (*  ([IcacheEscrow.dlinks_open] / [dlinks_intro]), which is what lets it *)
  (*  cross an [nlink] change at all.                                      *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  6.  THE SEAL                                                        *)
  (*                                                                      *)
  (*  The three halves were stated at each other's shapes on purpose, so   *)
  (*  the whole function is four [iApply]s and no glue: [cr_found_half]    *)
  (*  takes the allocate half as a HYPOTHESIS, [cr_alloc_half] takes the   *)
  (*  two parked bodies as hypotheses, and both parked bodies are          *)
  (*  ∀-quantified over exactly the binders the found half froze.          *)
  (* =================================================================== *)

  (* The one thing that is NOT free.  The three lower halves take the two
     frame-slot alignments as pure premises, and they are not derivable
     from [pa_stk]: a word points-to carries alignment, a byte run does not
     (StackBytes.v's header) -- so no rearrangement of the bodies produces
     them.  They are, however, already OWNED here: [sie_cap_gpr] holds this
     hart's stack, and the prologue's [c.addi16sp] is exactly the split
     that would hand it out.  So the seal READS them off the capability and
     keeps the resource: the conclusion is PURE, so the [iDestruct .. as %_]
     leaves [Hcg] in place (the same idiom [StackBytes.slot_bytes_own (KTR := KT1)] uses
     on its own argument). *)
  Lemma cr_cap_align (m : regfile) (avail : nat) (b : bool) (pp : mword 64) :
    (10 <= avail)%nat ->
    sie_cap_gpr KT1 m avail b pp ⊢
    ⌜is_aligned_paddr
       (Physaddr (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)) 8 = true
     /\ is_aligned_paddr
       (Physaddr (pa_stk (m !!! Regidx csp_rs1 : mword 64) 9)) 8 = true⌝.
  Proof.
    intro Hn. iIntros "(_ & _ & Hcap & _)".
    iDestruct (sie_cap_push m
                 (<[Regidx csp_rs1 := regval_into_reg
                      (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)]> m)
                 avail 10 b Hn ltac:(apply upd_eq) with "Hcap") as "[_ Hfr]".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hfr".
    iDestruct "Hfr" as "(_ & _ & _ & _ & _ & _ & _ & _ & S9 & S10 & _)".
    iDestruct "S9" as (w9) "H9". iDestruct "S10" as (w10) "H10".
    iDestruct (ctx_word_pointsto_aligned_p with "H9") as %Ha9.
    iDestruct (ctx_word_pointsto_aligned_p with "H10") as %Ha10.
    iPureIntro. split; [exact Ha10 | exact Ha9].
  Qed.

End ProofCreateMain.
