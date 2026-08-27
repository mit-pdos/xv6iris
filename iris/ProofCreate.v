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
Require Import KernelText KernelDataInv.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DinodeSlot.
Require Import DirentEnc.
Require Import BvShift.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IregLinkNz.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import SpecBmap SpecWritei.
Require Import SpecIput SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNamex SpecNameiparent.
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

Module CreateProof (NP : NAMEIPARENT) (IL : ILOCK) (IUP : IUNLOCKPUT)
                   (DL : DIRLOOKUP) (IA : IALLOC) (IU : IUPDATE)
                   (DLK : DIRLINK) : CREATE.

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
Lemma cr_regs3_of_span (m : regfile) (sp0 dpv ansv s3v : mword 64)
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
  Context `{GEN : GenId} `{CID : CpuId}.

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
  Lemma cr_carve_gen (k : nat) (q s : Qp) (dev inum : mword 32) (g : gname) :
    inode_ref_gen k (q + s)%Qp dev inum g ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q dev inum g ∗ inode_shr_gen k s dev inum g.
  Proof.
    rewrite /inode_ref_gen /inode_ref_short_gen /inode_shr_gen
            live_gen_split inode_ident_split SleepLock.slh_tok_split.
    iSplit.
    - iIntros "($ & [$ Hl2] & [$ Hi2] & [$ Hs2])". iFrame.
    - iIntros "[($ & $ & $ & $) ($ & $ & $)]".
  Qed.

  Lemma cr_shed_gen (k : nat) (q : Qp) (dev inum : mword 32) (g : gname) :
    inode_ref_gen k q dev inum g ⊣⊢
    inode_ref_short_gen k (q/2 + q/2)%Qp (q/2)%Qp dev inum g ∗
    inode_shr_gen k (q/2)%Qp dev inum g.
  Proof.
    pose proof (cr_carve_gen k (q/2)%Qp (q/2)%Qp dev inum g) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

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
    Lemma cr_esc_acc (γi : gname)
      (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗ ic_escrow fsc_ic fsc_fs γi fsc_cov fsc_logst k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
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
  Lemma cr_dirty_arm (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    ftop_inv fsc_fs -∗ t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
    top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      cr_dirty t i ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE) "#Hi Htx Hf".
    iMod (ireg_arm E fsc_fs i t (1/2)%Qp HE with "Hi Htx") as (k) "Harm".
    iMod (ireg_top_retag_armed E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) with "Hi Harm Hf")
      as "[Harm Hf]".
    iModIntro. iFrame "Hf". rewrite /cr_dirty. iExists k. iExact "Harm".
  Qed.

  Lemma cr_dirty_retag (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    ftop_inv fsc_fs -∗ cr_dirty t i -∗ top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      cr_dirty t i ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE) "#Hi Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) with "Hi Harm Hf")
      as "[Harm Hf]".
    iModIntro. iFrame "Hf". iExists k. iExact "Harm".
  Qed.

  Lemma cr_dirty_clear (E : coPset) (t : nat) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local i n' ->
    ftop_inv fsc_fs -∗ cr_dirty t i -∗ top_frag (fs_gamma_L fsc_fs) i n ={E}=∗
      t ↪[ln_tx icfg_log]{#(1/2)} tt ∗ top_frag (fs_gamma_L fsc_fs) i n'.
  Proof.
    iIntros (HE Hloc) "#Hi Hd Hf". rewrite /cr_dirty.
    iDestruct "Hd" as (k) "Harm".
    iMod (ireg_top_retag_armed E fsc_fs k t (1/2)%Qp {[i]} i n n' HE
            ltac:(apply elem_of_singleton, eq_refl) with "Hi Harm Hf")
      as "[Harm Hf]".
    iMod (ireg_disarm E fsc_fs k t (1/2)%Qp {[i]} i n' HE Hloc with "Hi Harm Hf")
      as "[Harm Hf]".
    iEval (rewrite difference_diag_L) in "Harm".
    iMod (ireg_release E fsc_fs k t (1/2)%Qp HE with "Hi Harm") as "Htx".
    iModIntro. iFrame "Htx Hf".
  Qed.

  Definition cr_cont_body
      (γi : gname) (γ : log_names)
      (γf : gname) (bn : bio_names)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
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
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       proc_priv γf (proc_addr j) pidv V -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       ⌜if ok then (S ns' = ns)%nat else ns' = ns⌝ -∗
       iref_slots ns' -∗
       ⌜Sb ⊆ Sb' /\ (u' <= u)%nat
         /\ (ok = true -> (iput_units <= u')%nat)⌝ -∗
       log_opS γ u' Sb' -∗
       (* THE TRANSACTION TOKEN GOES WITH THE ANSWER (durable-disk B''-tx2).
          On the SUCCESS arm create returns with the child still write-locked
          and its escrow holding the arm, so the token is inside
          [SpecCreate.create_locked]'s [IcacheEscrow.ic_tx_dep] and there is
          nothing to hand back beside it; on the FAILURE arm no inode is
          locked and the whole token comes home. *)
       (if ok
        then ⌜mf !!! Regidx Ra0 = ientry k
              /\ (k < NINODE)%nat
              /\ 0 < bv_unsigned inum < 16 * Z.of_nat nib
              /\ (if made
                  then di_type dn = ty
                       /\ di_major dn = major
                       /\ di_minor dn = minor
                       /\ bv_unsigned (di_nlink dn) = 1
                       /\ (ty <> SpecDirlookup.T_DIR ->
                           dn = create_made ty major minor)
                  else ty = T_FILE
                       /\ (di_type dn = T_FILE \/ di_type dn = T_DEVICE))⌝ ∗
          create_locked γi dev pidv k qi s g inum dn bm
        else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗ log_tx γ) -∗
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
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
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
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
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
       ⌜dir_ok nib dn data⌝ -∗
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
       ⌜w = true -> bmapstart ∈ Sb1⌝ -∗
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
       is_sleeplock_gen γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       ic_deposit fsc_ic kd (DepTx (qd/2)%Qp dev dind gd t (1/2)) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at γi dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map fsc_fs (ientry kd) bm -∗
       inode_blocks fsc_fs bm data -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dind) (dv_of dn data) -∗
       (* ...and its per-FILE twin (N-5.2A), beside it everywhere *)
       fv_ride (bv_unsigned dind) (fv_of dn data) -∗
       (* ...and the era's abstract value, which the half retags at its
          own write (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dn bm data) -∗
       ity_shot gd (di_type dn) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* everything the contract still owes back *)
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
       proc_priv γf (proc_addr j) pidv V -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 1) -∗
       log_opS γ n1 Sb1 -∗
       (* ...and THE HOLDER'S RESIDUE (durable-disk B''-tx2): the parent's
          escrow holds the other half of this transaction's element, and
          this arm's child needs the residue to suspend its row with. *)
       t ↪[ln_tx γ]{#(1/2)} tt -∗
       (* and the contract's own continuation, ANCHORED AT THE ENTRY HART
          (ProofDirlink's [dl_after_body]): the block's own proof does the
          retargeting, so this file hands over [Hcont] untouched. *)
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γi γ γf bn bmapstart inodestart
                         nib ninodes size dev plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
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
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (* ---- what the found half froze, i.e. [cr_alloc_body]'s own binders *)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDm : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname)
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
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
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
       ⌜dir_ok nib dn data⌝ -∗
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
       ⌜0 < bv_unsigned cinum < ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts, at the
          record this half parks (the count [cr_setf] writes is a literal,
          so only the enumeration really travels). *)
       ⌜inode_rec_local dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dnc bmc datc⌝ -∗
       ⌜dir_ok nib dnc datc⌝ -∗
       (* the ledger *)
       ⌜Sb ⊆ Sb3⌝ -∗
       ⌜IBLOCK cinum inodestart ∈ Sb3⌝ -∗
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
       ⌜bmapstart ∈ Sb3 \/ (9 <= n3)%nat⌝ -∗
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
       is_sleeplock_gen γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       ic_deposit fsc_ic kd (DepTx (qd/2)%Qp dev dind gd t (1/4)) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at γi dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map fsc_fs (ientry kd) bm -∗
       inode_blocks fsc_fs bm data -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dind) (dv_of dn data) -∗
       (* ...and its per-FILE twin (N-5.2A), beside it everywhere *)
       fv_ride (bv_unsigned dind) (fv_of dn data) -∗
       (* ...and the era's abstract value, which the half retags at its
          own write (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dn bm data) -∗
       ity_shot gd (di_type dn) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD, in pieces, at the FLUSHED record *)
       is_sleeplock_gen gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_tok fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       ic_deposit fsc_ic kslot (DepTx (q/2)%Qp dev cinum g t (1/4)) -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned cinum) dnc bmc datc -∗
       dinode_at γi cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned cinum)
               (dv_of (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc) -∗
       fv_ride (bv_unsigned cinum)
               (fv_of (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc) -∗
       (* ...and the CHILD's abstract value, at the same record *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc) -∗
       ity_shot g (di_type dnc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev cinum g -∗
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
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
       proc_priv_bare (proc_addr j) pidv V -∗
       (proc_priv_bare (proc_addr j) pidv V -∗
          proc_priv γf (proc_addr j) pidv V) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS γ n3 Sb3 -∗
       (* THE CHILD'S ROW IS SUSPENDED: it is a directory with a link
          count and no dots until the interior dirlinks land, so the arm
          carries the registry's receipt (durable-disk lane A) *)
       cr_dirty t (bv_unsigned cinum) -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γi γ γf bn bmapstart inodestart
                         nib ninodes size dev plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition cr_fail_body
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDf : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname)
       (cinum : mword 32) (dnc : dinode) (bmc : blkmap)
       (datc : nat -> list (bv 8))
       (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
       (tot : nat) (n4 : nat) (Sb4 : gset Z),
       ⌜cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64) (ientry kslot)
          ty major minor Mx⌝ -∗
       ⌜ty <> SpecDirlookup.T_DIR⌝ -∗
       (* the parent's ENTRY facts *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dn bm data⌝ -∗
       ⌜dir_ok nib dn data⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dind) dn data⌝ -∗
       ⌜dir_uniq dn data⌝ -∗
       (* durable-disk 2b-inode-3: the payload's record-only facts, which
          [IcacheEscrow.ic_mk_loaded] needs of the record this half parks. *)
       ⌜inode_rec_local dn⌝ -∗
       (* the child *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts, at the
          record this half parks (the count [cr_setf] writes is a literal,
          so only the enumeration really travels). *)
       ⌜inode_rec_local dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dnc bmc datc⌝ -∗
       ⌜dir_ok nib dnc datc⌝ -∗
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
       ⌜IBLOCK cinum inodestart ∈ Sb4⌝ -∗
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
       ⌜(S iput_units <= n4)%nat \/ bmapstart ∈ Sb4⌝ -∗
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
       is_sleeplock_gen γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       ic_deposit fsc_ic kd (DepTx (qd/2)%Qp dev dind gd t (1/4)) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dn bm data -∗
       dinode_at γi dind dn0' -∗
       inode_meta (ientry kd) dn' -∗
       inode_map fsc_fs (ientry kd) bm' -∗
       inode_blocks fsc_fs bm' data' -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dind) (dv_of dn' data') -∗
       fv_ride (bv_unsigned dind) (fv_of dn' data') -∗
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
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD, at the flushed record *)
       is_sleeplock_gen gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_tok fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       ic_deposit fsc_ic kslot (DepTx (q/2)%Qp dev cinum g t (1/4)) -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned cinum) dnc bmc datc -∗
       dinode_at γi cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned cinum)
               (dv_of (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc) -∗
       fv_ride (bv_unsigned cinum)
               (fv_of (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc) -∗
       (* ...and the CHILD's abstract value, at the same record *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc) -∗
       ity_shot g (di_type dnc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev cinum g -∗
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
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
       proc_priv_bare (proc_addr j) pidv V -∗
       (proc_priv_bare (proc_addr j) pidv V -∗
          proc_priv γf (proc_addr j) pidv V) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS γ n4 Sb4 -∗
       (* ...and the transaction token, which this arm's child needs to
          suspend its row with (durable-disk lane A) *)
       t ↪[ln_tx γ]{#(1/2)} tt -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γi γ γf bn bmapstart inodestart
                         nib ninodes size dev plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.


  (* =================================================================== *)
  (*  3.  THE WALK                                                        *)
  (* =================================================================== *)

  Lemma cr_found_half
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (V : pprivate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    (K_create <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= inodestart ->
    cov_below fsc_cov size ->
    bitmap_geom_ok fsc_cov fsc_logst bmapstart size ->
    InodeInv.ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    bv_unsigned ty <> 0 ->
    (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) *)
    InodeRegion.ireg_ty_ok (ialloc_fresh ty) ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    m !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64) ->
    m !!! Regidx Ra2 = (sign_extend' 64 major : mword 64) ->
    m !!! Regidx Ra3 = (sign_extend' 64 minor : mword 64) ->
    eb = true ->
    sie_cap_gpr KT1 m K b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.create) -∗
    kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view fsc_fs γd dev fsc_cov) -∗
    log_ctx γ bn fsc_fs fsc_cov fsc_logst dev -∗
    kalloc_env γa None -∗
    is_itable2 gtl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv γi fsc_fs inodestart nib -∗
    ireg_open -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
    proc_priv γf (proc_addr j) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen),
       pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ[KT1] pfun i) -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots 3 -∗
    iref_slots ns -∗
    log_opS γ u Sb -∗
    (* the transaction token, for the child's suspended row inside
       (durable-disk lane A) *)
    log_tx γ -∗
    (* ---- THE PARKED ALLOCATE HALF, as a HYPOTHESIS ---- *)
    wp_next true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                    bmapstart inodestart nib ninodes size dev
                    plen pfun (m !!! Regidx Ra0 : mword 64)
                    ty major minor V u Sb ns pidv dqb dqs dqbs dqn m
                    (m !!! Regidx csp_rs1 : mword 64)
                    (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks CIDa) -∗
    (* ---- the contract's own continuation ---- *)
    wp_next true (proc_addr j) (fun CIDc : CpuId =>
      cr_cont_body γi γ γf bn bmapstart inodestart nib
                   ninodes size dev plen pfun (m !!! Regidx Ra0 : mword 64)
                   ty major minor V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                   (ret_pc (m !!! Regidx Rra : mword 64)) CIDc) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc Hbmsl
           Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3 Htynz Htyk Hpkc
           Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    iIntros "Hcg Hcnt #Htext Hpc #Hkd #Hpk #Hbio #Hlogc #Hkenv
             #Hitb2 #Hitbl #Hesc #Hslks #Hiregi #Hiopen
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hpriv Hpath #Hprocs #Hdevi #Hgeom #Hdlk
             Hbsl Hislots Hop Htx Halloc Hcont".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    (* PIN THE INDEX: at level 0 [cpu_own_eb_agree] gives [eb = b], and the
       crossings below are the literal [true] (create parks everywhere). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE.  create's contract carries no
       order premise because it does not need one: it is a level-0 contract,
       and [cpu_own_size_le] forces [lks = ∅] there.  Keep the EQUATION rather
       than substituting -- [lks] is spelled by name in every body below --
       and let [lkbelow] close each callee's bound from it. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    pose (ret_tgt := ret_pc (m !!! Regidx Rra : mword 64)).
    (* ===== +0x00 c.addi16sp sp,-80 : the 10-slot frame ================ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)
      by apply cr_push.
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.create)
              (mword_of_int 59 : mword 6) m K 10 b
              ltac:(exact HK10) Hpush with "Hcg Hpc []").
    { iApply (cri_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    pose (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R1 upd_eq; exact Hpush).
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply cr_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply cr_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply cr_frm3).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply cr_frm4).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply cr_frm6).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply cr_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply cr_frm8).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3". iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf6) in "Hb6". iEval (rewrite -Hf7) in "Hb7".
    iEval (rewrite -Hf8) in "Hb8".
    assert (Hp002 : add_vec_int (mword_of_int KernelSyms.create : mword 64) 2
                    = mword_of_int (CK + 0x02)) by pcw.
    iEval (rewrite Hp002) in "Hpc".
    (* ===== +0x02 .. +0x0e : the SEVEN saves (slot 40 is NOT touched) == *)
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x02)) (mword_of_int 9 : mword 6)
              Rra R1 (K - 10)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (cri_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hp004 : add_vec_int (mword_of_int (CK + 0x02) : mword 64) 2
                    = mword_of_int (CK + 0x04)) by pcw.
    iEval (rewrite Hp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x04)) (mword_of_int 8 : mword 6)
              Rs0 R1 (K - 10)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (cri_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hp006 : add_vec_int (mword_of_int (CK + 0x04) : mword 64) 2
                    = mword_of_int (CK + 0x06)) by pcw.
    iEval (rewrite Hp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x06)) (mword_of_int 7 : mword 6)
              Rs1 R1 (K - 10)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (cri_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hp008 : add_vec_int (mword_of_int (CK + 0x06) : mword 64) 2
                    = mword_of_int (CK + 0x08)) by pcw.
    iEval (rewrite Hp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x08)) (mword_of_int 6 : mword 6)
              Rs2 R1 (K - 10)%nat u4 b with "Hcg Hpc [] Hb4").
    { iApply (cri_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hp00a : add_vec_int (mword_of_int (CK + 0x08) : mword 64) 2
                    = mword_of_int (CK + 0x0a)) by pcw.
    iEval (rewrite Hp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0a)) (mword_of_int 4 : mword 6)
              Rs4 R1 (K - 10)%nat u6 b with "Hcg Hpc [] Hb6").
    { iApply (cri_00a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hp00c : add_vec_int (mword_of_int (CK + 0x0a) : mword 64) 2
                    = mword_of_int (CK + 0x0c)) by pcw.
    iEval (rewrite Hp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0c)) (mword_of_int 3 : mword 6)
              Rs5 R1 (K - 10)%nat u7 b with "Hcg Hpc [] Hb7").
    { iApply (cri_00c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hp00e : add_vec_int (mword_of_int (CK + 0x0c) : mword 64) 2
                    = mword_of_int (CK + 0x0e)) by pcw.
    iEval (rewrite Hp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0e)) (mword_of_int 2 : mword 6)
              Rs6 R1 (K - 10)%nat u8 b with "Hcg Hpc [] Hb8").
    { iApply (cri_00e with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hp010 : add_vec_int (mword_of_int (CK + 0x0e) : mword 64) 2
                    = mword_of_int (CK + 0x10)) by pcw.
    iEval (rewrite Hp010) in "Hpc".
    (* ===== +0x10 c.addi4spn s0,sp,80 : the frame pointer ============== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CK + 0x10))
              (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) Rs0
              R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (cri_010 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    pose (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1) with R2.
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply cr_fp. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2o : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 ->
                     R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (Hp012 : add_vec_int (mword_of_int (CK + 0x10) : mword 64) 2
                    = mword_of_int (CK + 0x12)) by pcw.
    iEval (rewrite Hp012) in "Hpc".
    (* ===== +0x12 / +0x14 / +0x16 : ty / major / minor to s4 / s5 / s6 = *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x12)) Rs4 Ra1 R2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_012 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R3 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra1))]> R2).
    change (<[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra1))]> R2) with R3.
    assert (HR3s4 : R3 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64)).
    { rewrite /R3 upd_eq. rewrite (HR2o Ra1 ltac:(nz) ltac:(nz)) Ha1.
      apply add_vec_zero_l. }
    assert (Hp014 : add_vec_int (mword_of_int (CK + 0x12) : mword 64) 2
                    = mword_of_int (CK + 0x14)) by pcw.
    iEval (rewrite Hp014) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14)) Rs5 Ra2 R3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_014 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R4 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra2))]> R3).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra2))]> R3) with R4.
    assert (HR4s5 : R4 !!! Regidx Rs5 = (sign_extend' 64 major : mword 64)).
    { rewrite /R4 upd_eq. rewrite /R3 upd_ne; [| nz].
      rewrite (HR2o Ra2 ltac:(nz) ltac:(nz)) Ha2. apply add_vec_zero_l. }
    assert (Hp016 : add_vec_int (mword_of_int (CK + 0x14) : mword 64) 2
                    = mword_of_int (CK + 0x16)) by pcw.
    iEval (rewrite Hp016) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x16)) Rs6 Ra3 R4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_016 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R5 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra3))]> R4).
    change (<[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra3))]> R4) with R5.
    assert (HR5s6 : R5 !!! Regidx Rs6 = (sign_extend' 64 minor : mword 64)).
    { rewrite /R5 upd_eq. rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite (HR2o Ra3 ltac:(nz) ltac:(nz)) Ha3. apply add_vec_zero_l. }
    assert (HR5s0 : R5 !!! Regidx Rs0 = sp0).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2s0 | nz]. }
    assert (Hp018 : add_vec_int (mword_of_int (CK + 0x16) : mword 64) 2
                    = mword_of_int (CK + 0x18)) by pcw.
    iEval (rewrite Hp018) in "Hpc".
    (* ===== +0x18 addi a1,s0,-80 : a1 = &name = the frame's bottom ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x18)) Ra1 Rs0
              (mword_of_int 4016 : mword 12) R5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_018 with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    pose (R6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R5 Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R5).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R5 Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R5) with R6.
    assert (HR6a1 : R6 !!! Regidx Ra1 = pa_stk sp0 10).
    { rewrite /R6 upd_eq. rewrite rget_ne;
        [| intro Hq1'; injection Hq1' as Hq2'; vm_compute in Hq2'; congruence ].
      rewrite HR5s0. apply cr_name_addr. }
    assert (Hp01c : add_vec_int (mword_of_int (CK + 0x18) : mword 64) 4
                    = mword_of_int (CK + 0x1c)) by pcw.
    iEval (rewrite Hp01c) in "Hpc".
    (* ===== +0x1c jal nameiparent ===================================== *)
    assert (Htgnp : add_vec (mword_of_int (CK + 0x1c) : mword 64)
              (sign_extend' 64 (mword_of_int 2092760 : mword 21))
              = mword_of_int KernelSyms.nameiparent) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x1c)) Rra
              (mword_of_int 2092760 : mword 21) R6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_01c with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    iEval (rewrite Htgnp) in "Hpc".
    pose (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)]> R6).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)]> R6) with R7.
    assert (HR7ra : R7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    assert (HR7a0 : R7 !!! Regidx Ra0 = (m !!! Regidx Ra0 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. exact (HR2o Ra0 ltac:(nz) ltac:(nz)). }
    assert (HR7a1 : R7 !!! Regidx Ra1 = pa_stk sp0 10).
    { rewrite /R7 upd_ne; [exact HR6a1 | nz]. }
    assert (HR7regs : cr_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) ty major minor R7).
    { unfold cr_regs. split_and!.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [exact HR2sp | nz].
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        exact HR5s0.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [| nz]. exact (HR2o Rs1 ltac:(nz) ltac:(nz)).
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
        rewrite /R3 upd_ne; [| nz]. exact (HR2o Rs2 ltac:(nz) ltac:(nz)).
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz]. exact HR3s4.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [| nz]. exact HR4s5.
      - rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz]. exact HR5s6.
      - intros c Hc N2 N8 N9 N18 N20 N21 N22.
        rewrite /R7 upd_ne; [| dlk_rne2 Hcsra Hc].
        rewrite /R6 upd_ne; [| dlk_rne2 Hcsa1 Hc].
        rewrite /R5 upd_ne; [| dlk_xne N22].
        rewrite /R4 upd_ne; [| dlk_xne N21].
        rewrite /R3 upd_ne; [| dlk_xne N20].
        exact (HR2o c N2 N8). }
    (* ---- the sixteen-byte [name] local, and the fourteen it lends ---- *)
    iDestruct (cr_slots_bytes sp0 u10 u9 with "Hb10 Hb9") as "[%Hal Hnb]".
    destruct Hal as [Hal10 Hal9].
    iDestruct (dlk_bytes_name with "Hnb") as (nf0) "Hnb".
    iEval (rewrite cr_split14) in "Hnb".
    iDestruct "Hnb" as "[Hnb14 Hnb2]".
    (* ---- the ledger: two slots out for nameiparent ---- *)
    assert (Hnsplit : ns = (2 + (ns - 2))%nat)
      by exact (cr_ns_split ns Hns).
    iEval (rewrite {1}Hnsplit iref_slots_op) in "Hislots".
    iDestruct "Hislots" as "[Hisl2 Hislr]".
    (* ---- the running process: the BLOCK and the cwd reference ---- *)
    iDestruct (proc_priv_bare_cref γf (proc_addr j) pidv V with "Hpriv")
      as "(Hppid & Hcref & Hpclose)".
    iDestruct (cwd_ref_held with "Hcref") as "Hcref".
    iEval (rewrite -HR7a0) in "Hpath".
    iEval (rewrite -HR7a1) in "Hnb14".
    iDestruct (cpu_own_transport CID CID14 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (NP.wp_nameiparent_gen γs j γl γu γd γk pd pav pu bn γ γi gtl
              γa γf bmapstart inodestart nib size dev
              plen pfun nf0 u Sb pidv (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
              R7 (K - 10)%nat eb b lks V
              ltac:(exact HKnp) Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize
              Hbms0 Hbmsc Hbmsl Hist0 Hcovb Hiregb Hcstr Hplen31
              ltac:(exact (cr_walk_need _ u Hu)) Hj Hgs
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk Hsbb Hsbi Hbmr
                    Hppid Hcref Hpath Hnb14 Hbsl Hisl2 [$Hop $Htx]").
    (* nameiparent is eb-generic now; create is still at [eb = true]. *)
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CIDnp Hsnp mnp n1 Sb1 okp nfp ipv w)
      "%Hcsnp Hcg Hcnt _ _ Hpc Hsbb Hsbi Hppid Hcref Hpath Hnb14
       Hbsl %Hsb1 %Hwmem %Hnp1 [Hop Htx] Hres".
    iEval (rewrite HR7a0) in "Hpath".
    iEval (rewrite HR7a1) in "Hnb14".
    assert (Hpcnp : ret_pc (R7 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x20)) by (rewrite HR7ra; pcw).
    iEval (rewrite Hpcnp) in "Hpc".
    assert (Hmnpregs : cr_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                         (m !!! Regidx Rs2 : mword 64) ty major minor mnp)
      by exact (cr_regs_cs m sp0 _ _ ty major minor R7 mnp Hcsnp HR7regs).
    (* the process block goes back whole: create copies nothing to or from
       user memory, so [V] is unchanged. *)
    iDestruct (cwd_ref_of_held with "Hcref") as "Hcref".
    iDestruct ("Hpclose" with "Hppid Hcref") as "Hpriv".
    (* ===== +0x20 c.mv s1,a0 : s1 = dp ================================ *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x20)) Rs1 Ra0 mnp (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_020 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (Q1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))]> mnp).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))]> mnp) with Q1.
    assert (HQ1s1 : Q1 !!! Regidx Rs1
                    = add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1a0 : Q1 !!! Regidx Ra0 = (mnp !!! Regidx Ra0 : mword 64))
      by (rewrite /Q1 upd_ne; [reflexivity | nz]).
    assert (Hp022 : add_vec_int (mword_of_int (CK + 0x20) : mword 64) 2
                    = mword_of_int (CK + 0x22)) by pcw.
    iEval (rewrite Hp022) in "Hpc".
    assert (Htg160 : add_vec (mword_of_int (CK + 0x22) : mword 64)
              (sign_extend' 64 (mword_of_int 318 : mword 13))
              = mword_of_int (CK + 0x160)) by pcw.
    (* ================================================================== *)
    (*  THE EPILOGUE FUNNEL at +0x70 -- SIX arms reach it, so the          *)
    (*  continuation is abstract and the body speaks only of [cr_tregs].   *)
    (* ================================================================== *)
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9
                 eq_refl eq_refl with "Htext") as "#Htail".
    destruct okp.
    - (* ============================================================== *)
      (*  nameiparent SUCCEEDED -- the parent is a LOCKED-ABLE DIRECTORY  *)
      (* ============================================================== *)
      iDestruct "Hres" as "((%Hnpa0 & %Hnpname) & Hipty & Hisl1)".
      iDestruct "Hipty" as (kd qd dind gd)
        "(%Hie & %Hkd & %Hdib & Href & #Hshotd & Hrud)".
      assert (Hdib' : bv_unsigned dind < 16 * Z.of_nat nib)
        by (rewrite Hnib; exact Hdib).
      destruct (Hiregb dind Hdib') as [Hdblk Hdblog].
      (* ===== +0x22 beqz a0 : FALLS THROUGH (an entry is never null) === *)
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (CK + 0x22))
                (mword_of_int 318 : mword 13) Ra0 Q1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HQ1a0 Hnpa0 Hie;
                      apply (proj2 (eq_vec_false_iff _ _));
                      exact (ientry_ne_zero kd (Nat.lt_le_incl _ _ Hkd)))
                with "Hcg Hpc []").
      { iApply (cri_022 with "Htext"). }
      iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Hp026 : add_vec_int (mword_of_int (CK + 0x22) : mword 64) 4
                      = mword_of_int (CK + 0x26)) by pcw.
      iEval (rewrite Hp026) in "Hpc".
      (* the [mv s1,a0]'s value, as its OWN equation: an inline [ltac:] in
         argument position would be spliced while [v] is still an evar
         (durable-notes). *)
      assert (Hs1v : add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0) = ipv)
        by (rewrite Hnpa0; apply add_vec_zero_l).
      assert (HQ1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q1)
        by exact (cr_regs_s1 m sp0 (m !!! Regidx Rs1 : mword 64) ipv
                    (m !!! Regidx Rs2 : mword 64) ty major minor mnp _
                    Hs1v Hmnpregs).
      (* ---- THE SHED: ilock takes a share AT THE SAME GENERATION ------
         [nameiparent] handed back [inode_held_ty ipv T_DIR], i.e. the
         reference with its generation NAMED and that generation's type
         one-shot beside it.  Shedding at that generation is what lets the
         [ity_shot_agree] below read ilock's own one-shot against it, and
         is why create needs no parent type test of its own (fs-sysfile
         Blocker B, closed by fs-log.md G-4d). *)
      iEval (rewrite -Hdev) in "Href".
      iEval (rewrite cr_shed_gen) in "Href".
      iDestruct "Href" as "[Hkeep Hshr]".
      iDestruct (cr_esc_acc γi kd Hkd with "Hesc") as "#Hescd".
      iDestruct (ic_sleeplocks_lookup fsc_ic kd Hkd with "Hslks") as (gild gisld) "#Hslkd".
      iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (proc_priv_bare_acc γf (proc_addr j) pidv V with "Hpriv")
        as "[Hppid Hppback]".
      (* ===== +0x26 jal ilock (a0 is STILL dp -- not reloaded) ========= *)
      assert (Htgil : add_vec (mword_of_int (CK + 0x26) : mword 64)
                (sign_extend' 64 (mword_of_int 2090536 : mword 21))
                = mword_of_int KernelSyms.ilock) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0x26)) Rra
                (mword_of_int 2090536 : mword 21) Q1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_026 with "Htext"). }
      iIntros (CID17 Hq17) "Hcg Hpc".
      iEval (rewrite Htgil) in "Hpc".
      pose (Q2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)]> Q1).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)]> Q1) with Q2.
      assert (HQ2ra : Q2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)
        by (rewrite /Q2; apply upd_eq).
      assert (HQ2a0 : Q2 !!! Regidx Ra0 = ientry kd).
      { rewrite /Q2 upd_ne; [| nz]. rewrite HQ1a0 Hnpa0. exact Hie. }
      assert (HQ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q2)
        by (rewrite /Q2; apply cr_regs_caller; [exact Hcsra | exact HQ1regs]).
      iDestruct (cpu_own_transport CIDnp CID17 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      (* THE PARENT'S CHECKOUT IS ARMED (durable-disk B''-tx2) AT THE
         CHECKOUT ITSELF (B''-tx3), and the TRANSACTION ID IS NAMED FROM HERE
         ON.  create's second lock has to park at the SAME transaction as this
         one, so the id leaves [LogInv.log_tx]'s existential once, before the
         first lock, and re-enters it only at an exit that holds no lock at
         all. *)
      iEval (rewrite Hglog) in "Htx".
      iDestruct (log_tx_open with "Htx") as (t) "Htw".
      iDestruct (log_tx_split icfg_log t 1 (1/2) (1/2)
                   (eq_sym Qp.half_half) with "Htw") as "[Htp Htx]".
      iApply (IL.wp_ilock_dep_sconf γs j γl γu γd γk pd pav pu bn γi
                gild gisld inodestart nib kd (qd/2)%Qp gd
                (DepTx (qd/2)%Qp dev dind gd t (1/2)) PlainK
                dev dind
                pidv (DfracOwn (1/4)) dqs Q2 (K - 10)%nat eb b lks
                V ltac:(exact HKil) eq_refl ltac:(discriminate)
                Hkd Hlg Hist0 Hdblk Hdib' Hj Hgs HQ2a0
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hescd Hiregi
                      Hslkd Hshr [Htp] Hrud Hsbi Hppid Hprocs Hdevi Hgeom Hdlk Hbs1").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { rewrite /ic_dep_side. iExact "Htp". }
      iIntros (CIDil Hqil mil dnl bml fld)
        "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hslkdd Hdep
         Hidev Hiinum Hivalid Hload #Hshotl Hfrzl %Hfrd Hrud %Hilkpd".
      iEval (rewrite /ic_dep_held /=) in "Hload".
      assert (Hpcil : ret_pc (Q2 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0x2a)) by (rewrite HQ2ra; pcw).
      iEval (rewrite Hpcil) in "Hpc".
      assert (Hmilregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                           ty major minor mil)
        by exact (cr_regs_cs m sp0 _ _ ty major minor Q2 mil Hcsil HQ2regs).
      pose proof Hmilregs as HmilR.
      destruct HmilR as (Y2 & Y8 & Y9 & Y18 & Y20 & Y21 & Y22 & Ythr).
      (* THE PARENT IS A DIRECTORY, and the walker said so.  [ity_shot] is
         a one-shot per generation, so the two readings agree. *)
      iDestruct (ity_shot_agree with "Hshotd Hshotl") as %Htyd.
      assert (Htydir : di_type dnl = SpecDirlookup.T_DIR) by (symmetry; exact Htyd).
      iDestruct (ic_loaded_open with "Hload") as (datl)
        "(%Hiok & %Hrl_datl & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta
          & Haddrs & Hind & Hblocks & Hdview & Hfview & Htop)".
      iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
      iEval (rewrite /i_nlink) in "Hinl".
      (* ===== +0x2a lh a5,74(s1) : dp->nlink -- THE GUARD (9da28f5) ==== *)
      iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x2a)) Ra5 Rs1
                (mword_of_int 74 : mword 12) mil (K - 10)%nat
                (di_nlink dnl : mword 16) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] [Hinl]").
      { iApply (cri_02a with "Htext"). }
      { iEval (rgne; rewrite Y9 Hie). iExact "Hinl". }
      iIntros (CID18 Hq18) "Hcg Hpc Hinl".
      iEval (rgne; rewrite Y9 Hie) in "Hinl".
      pose (Q3 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)]> mil).
      change (<[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)]> mil) with Q3.
      assert (HQ3a5 : Q3 !!! Regidx Ra5
                      = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
        by (rewrite /Q3; apply upd_eq).
      assert (HQ3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q3)
        by (rewrite /Q3; apply cr_regs_caller; [exact Hcsa5 | exact Hmilregs]).
      assert (Hp02e : add_vec_int (mword_of_int (CK + 0x2a) : mword 64) 4
                      = mword_of_int (CK + 0x2e)) by pcw.
      iEval (rewrite Hp02e) in "Hpc".
      assert (Htg084 : add_vec (mword_of_int (CK + 0x2e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 43 : mword 8) ('b"0"))))
                = mword_of_int (CK + 0x84)) by pcw.
      (* the ledger, as [CreateBudget.cr_budget_found_w]'s first row *)
      assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
      assert (Hn1ip : (iput_units <= n1)%nat) by exact (cr_ip_of9 n1 Hn1lo).
      destruct (decide (di_nlink dnl = (mword_of_int 0 : mword 16))) as [Hnl0 | Hnl0].
      + (* ========== ARM G: the guard FIRES -- nlink == 0 ============= *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_eq _ Hnl0))
                  ltac:(rewrite Htg084; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_02e with "Htext"). }
        iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg084) in "Hpc".
        (* [ic_loaded]'s tail is [inode_blocks]' 268-element big-op
           ([IcacheEscrow.ic_mk_loaded]'s comment) -- assembled by the
           constructor, not by [iFrame], which would re-search the whole
           function context against that big-op's goal shape. *)
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmetal".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind dnl bml datl
                     Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                     with "Hdlnk Hdiat Hmetal Haddrs Hind Hblocks Hdview Hfview
                           Htop")
          as "Hload".
        iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x84 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x84)) Ra0 Rs1 Q3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_084 with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (G1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3) with G1.
        assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kd).
        { rewrite /G1 upd_eq. rewrite /Q3 upd_ne; [| nz].
          rewrite Y9 Hie. apply add_vec_zero_l. }
        assert (HG1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G1)
          by (rewrite /G1; apply cr_regs_caller; [exact Hcsa0 | exact HQ3regs]).
        assert (Hp086 : add_vec_int (mword_of_int (CK + 0x84) : mword 64) 2
                        = mword_of_int (CK + 0x86)) by pcw.
        iEval (rewrite Hp086) in "Hpc".
        (* +0x86 jal iunlockput (dp) -- AT crb = cru = crz = false.
           [crz] is unavailable BY CONSTRUCTION on this arm: it is bought
           with [InodeRegion.nlz_obs], minted only at a NONZERO nlink
           observation, and this arm IS the zero observation. *)
        assert (Htgup : add_vec (mword_of_int (CK + 0x86) : mword 64)
                  (sign_extend' 64 (mword_of_int 2091036 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x86)) Rra
                  (mword_of_int 2091036 : mword 21) G1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_086 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite Htgup) in "Hpc".
        pose (G2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)]> G1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)]> G1) with G2.
        assert (HG2ra : G2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)
          by (rewrite /G2; apply upd_eq).
        assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
        assert (HG2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G2)
          by (rewrite /G2; apply cr_regs_caller; [exact Hcsra | exact HG1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
           goes in and the share it parked comes back in the post, so no
           bundleless out-state stands across the call. *)
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
        iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
                  gtl gild gisld bmapstart inodestart nib size dev
                  kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/2)%Qp) dind dnl bml n1 Sb1
                  false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                  G2 (K - 10)%nat eb b lks
                  V ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HG2a0 ltac:(lkbelow) Hglog eq_refl
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                        Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        all: try lkbelow.
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl Htp".
        iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                     (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
        iDestruct (log_tx_full with "Htw") as "Htx".
        iEval (rewrite -Hglog) in "Htx".
        assert (Hpcup : ret_pc (G2 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x8a)) by (rewrite HG2ra; pcw).
        iEval (rewrite Hpcup) in "Hpc".
        assert (Hmupregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mup)
          by exact (cr_regs_cs m sp0 _ _ ty major minor G2 mup Hcsup HG2regs).
        iDestruct ("Hppback" with "Hppid") as "Hpriv".
        (* +0x8a c.li s2,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x8a)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mup (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_08a with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc".
        pose (G3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
        change (<[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup) with G3.
        assert (HG3s2 : G3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
          by (rewrite /G3; apply upd_eq).
        assert (Hg2v : (mword_of_int 0 : mword 64) = (mword_of_int 0 : mword 64))
          by reflexivity.
        assert (HG3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                            ty major minor G3)
          by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mup _
                      Hg2v Hmupregs).
        assert (Hp08c : add_vec_int (mword_of_int (CK + 0x8a) : mword 64) 2
                        = mword_of_int (CK + 0x8c)) by pcw.
        iEval (rewrite Hp08c) in "Hpc".
        (* +0x8c c.j +0x70 *)
        assert (Htg070g : add_vec (mword_of_int (CK + 0x8c) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                  = mword_of_int (CK + 0x70)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (CK + 0x8c))
                  (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                  G3 (K - 10)%nat b
                  ltac:(rewrite Htg070g; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_08c with "Htext"). }
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070g) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! G3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor G3 HG3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [$Htx]").
        { exact Hcsf. }
        { exact (cr_slots_ns _ ns eq_refl Hns). }
        { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                      | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                      | discriminate]. }
        { iPureIntro. rewrite Ha0f. exact HG3s2. }
      + (* ====== THE GUARD FALLS THROUGH: dp->nlink <> 0 ============== *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_ne _ Hnl0))
                  with "Hcg Hpc []").
        { iApply (cri_02e with "Htext"). }
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hp030 : add_vec_int (mword_of_int (CK + 0x2e) : mword 64) 2
                        = mword_of_int (CK + 0x30)) by pcw.
        iEval (rewrite Hp030) in "Hpc".
        (* ============================================================== *)
        (*  THE NLINK_MAX GATE, +0x30 .. +0x3c (xv6 117c0e7): the parent   *)
        (*  of a NEW DIRECTORY is refused once its own link count has      *)
        (*  reached 32767, because the ".." the mkdir arm writes would     *)
        (*  raise it past what the on-disk [short] holds.                  *)
        (*                                                                *)
        (*  Six instructions and a DIAMOND: the [c.bnez] at +0x36 (the     *)
        (*  count is not at the maximum) and the [c.beqz] at +0x3c's       *)
        (*  fall-through (the type is not T_DIR) BOTH land at +0x3e.  So   *)
        (*  the rest of the found half is proven ONCE, as the first        *)
        (*  conjunct of an [∧] -- which hands the whole context to both    *)
        (*  arms exactly as the two arms of a [destruct] would, and is     *)
        (*  the only shape that does: an [iAssert] of the continuation     *)
        (*  alone would consume the resources ARM G2 also needs.  The      *)
        (*  second conjunct IS ARM G2, the guard's own exit block at       *)
        (*  +0x8e: [iunlockput(dp)] then [return 0], which is ARM G's      *)
        (*  block at a different address -- gcc emitted the two cold       *)
        (*  blocks in source order, so ARM G is at +0x84 and the new one   *)
        (*  below it.  (That ordering is also what [relayout_shift.py]     *)
        (*  gets wrong: difflib pairs the new [c.beqz] with the old one    *)
        (*  and reports the guard as landing at +0x2e.)                    *)
        (* ============================================================== *)
        (*  Each conjunct is [wp_next]-WRAPPED, and a bare [(CIDj : CpuId)]
            parameter would make it unprovable: the tail transports
            [cpu_own] from the harts the found half already visited, and a
            free hart has nothing tying it to them -- the missing link IS
            the [wp_next] guard (D₀-a's finding, one increment on). *)
        iAssert ((wp_next (CID0 := CID19) b (proc_addr j) (fun CIDj : CpuId =>
                    ∀ Mj : regfile,
                    ⌜cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                       ty major minor Mj⌝ -∗
                    (* THE GATE'S FALL-THROUGH FACT, carried by the JOIN
                       and not by either arm: the [c.bnez] arm proves it
                       from the count, the [c.beqz] arm from the type, and
                       what +0x3e knows is their disjunction written as an
                       implication.  The allocate half relays it and only
                       the T_DIR sub-branch spends it. *)
                    ⌜ty = SpecDirlookup.T_DIR ->
                       di_nlink dnl <> (mword_of_int 32767 : mword 16)⌝ -∗
                    sie_cap_gpr KT1 (CID := CIDj) Mj (K - 10)%nat b (proc_addr j) -∗
                    pc_is (CID := CIDj) (mword_of_int (CK + 0x3e)) -∗
                    WP (Loop : expr riscv_lang)))
                 ∧ (wp_next (CID0 := CID19) b (proc_addr j) (fun CIDg : CpuId =>
                    ∀ Mg : regfile,
                    ⌜cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                       ty major minor Mg⌝ -∗
                    sie_cap_gpr KT1 (CID := CIDg) Mg (K - 10)%nat b (proc_addr j) -∗
                    pc_is (CID := CIDg) (mword_of_int (CK + 0x8e)) -∗
                    WP (Loop : expr riscv_lang))))%I
          with "[-Hcg Hpc]" as "Hgate".
        { iSplit.
          - (* ===== THE JOIN AT +0x3e: dirlookup and everything after === *)
            iIntros (CIDj) "%Hqj". iIntros (Mj) "%HMjregs %Hnlmax Hcg Hpc".
            pose proof HMjregs as HMjR.
            destruct HMjR as (W2 & W8 & W9 & W18 & W20 & W21 & W22 & Wthr).
        (* the locked directory's payload, in the pieces dirlookup takes *)
        (* KEEP [Hiok] WHOLE -- the two re-parks below want it back, so take
           the three clauses dirlookup asks for as projections. *)
        assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bml) by exact (proj1 Hiok).
        assert (Hbmcov : bm_covers bml (bv_unsigned (di_size dnl)))
          by exact (proj1 (proj2 Hiok)).
        assert (Hszcap : bv_unsigned (di_size dnl)
                         <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
        assert (Hdz : bv_unsigned (di_type dnl) = T_DIR_z)
          by (rewrite Htydir; vm_compute; reflexivity).
        (* ===== +0x3e c.li a2,0 : dirlookup's [poff] is NOT wanted ===== *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x3e)) Ra2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  Mj (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_03e with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc".
        pose (D1 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Mj).
        change (<[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Mj) with D1.
        assert (HD1a2 : D1 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D1; apply upd_eq).
        assert (HD1s0 : D1 !!! Regidx Rs0 = sp0).
        { rewrite /D1 upd_ne; [| nz]. exact W8. }
        assert (HD1s1 : D1 !!! Regidx Rs1 = ipv).
        { rewrite /D1 upd_ne; [| nz]. exact W9. }
        assert (HD1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D1)
          by (rewrite /D1; apply cr_regs_caller; [exact Hcsa2 | exact HMjregs]).
        assert (Hp040 : add_vec_int (mword_of_int (CK + 0x3e) : mword 64) 2
                        = mword_of_int (CK + 0x40)) by pcw.
        iEval (rewrite Hp040) in "Hpc".
        (* ===== +0x40 addi a1,s0,-80 : a1 = &name ====================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x40)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) D1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_040 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        pose (D2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> D1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> D1) with D2.
        assert (HD2a1 : D2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /D2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HD1s0. apply cr_name_addr. }
        assert (HD2a2 : D2 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D2 upd_ne; [exact HD1a2 | nz]).
        assert (HD2s1 : D2 !!! Regidx Rs1 = ipv)
          by (rewrite /D2 upd_ne; [exact HD1s1 | nz]).
        assert (HD2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D2)
          by (rewrite /D2; apply cr_regs_caller; [exact Hcsa1 | exact HD1regs]).
        assert (Hp044 : add_vec_int (mword_of_int (CK + 0x40) : mword 64) 4
                        = mword_of_int (CK + 0x44)) by pcw.
        iEval (rewrite Hp044) in "Hpc".
        (* ===== +0x44 c.mv a0,s1 ======================================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x44)) Ra0 Rs1 D2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_044 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (D3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (D2 !!! Regidx Rs1))]> D2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (D2 !!! Regidx Rs1))]> D2) with D3.
        assert (HD3a0 : D3 !!! Regidx Ra0 = ientry kd).
        { rewrite /D3 upd_eq. rewrite HD2s1 Hie. apply add_vec_zero_l. }
        assert (HD3a1 : D3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /D3 upd_ne; [exact HD2a1 | nz]).
        assert (HD3a2 : D3 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D3 upd_ne; [exact HD2a2 | nz]).
        assert (HD3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D3)
          by (rewrite /D3; apply cr_regs_caller; [exact Hcsa0 | exact HD2regs]).
        assert (Hp046 : add_vec_int (mword_of_int (CK + 0x44) : mword 64) 2
                        = mword_of_int (CK + 0x46)) by pcw.
        iEval (rewrite Hp046) in "Hpc".
        (* ===== +0x46 jal dirlookup(dp, name, 0) ======================= *)
        assert (Htgdl : add_vec (mword_of_int (CK + 0x46) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092016 : mword 21))
                  = mword_of_int KernelSyms.dirlookup) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x46)) Rra
                  (mword_of_int 2092016 : mword 21) D3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_046 with "Htext"). }
        iIntros (CID23 Hq23) "Hcg Hpc".
        iEval (rewrite Htgdl) in "Hpc".
        pose (D4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)]> D3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)]> D3) with D4.
        assert (HD4ra : D4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)
          by (rewrite /D4; apply upd_eq).
        assert (HD4a0 : D4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /D4 upd_ne; [exact HD3a0 | nz]).
        assert (HD4a1 : D4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /D4 upd_ne; [exact HD3a1 | nz]).
        assert (HD4a2 : D4 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D4 upd_ne; [exact HD3a2 | nz]).
        assert (HD4regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D4)
          by (rewrite /D4; apply cr_regs_caller; [exact Hcsra | exact HD3regs]).
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iAssert (inode_map fsc_fs (ientry kd) bml) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        iEval (rewrite -HD4a1) in "Hnb14".
        iDestruct (cpu_own_transport CIDil CID23 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE BORROWED LICENCE (fs-fragments.md §7.5.6, row 2).  The LEFT
           disjunct is what create brings, and the guard that earns it is
           [sysfile.c:269]'s [dp->nlink == 0] refusal at +0x2a/+0x2e: this
           branch is the [c.beqz] at +0x2e FALLING THROUGH, whose own
           hypothesis [Hnl0] says the parent's count is not zero.  The
           ticket list [Hdlnk] and the home's record [Hdiat] are lent to
           dirlookup's iget and come straight back on both arms -- nothing
           is spent, and both are already in hand out of
           [IcacheEscrow.ic_loaded]. *)
        (* dirlookup borrows the LEDGER half alone (durable-disk
           2b-inode-5); the counting RA's tokens stay in this walk's hand
           and go back into the payload with the same node. *)
        assert (Hholesl : blk_holes_zero bml datl)
          by (destruct Hiok as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
        iApply (DL.wp_dirlookup_sconf γs j γl γu γd γk pd pav pu bn γi
                  gtl γa γf inodestart nib dev (ientry kd) dind bml datl
                  dnl dnl nfp
                  false (mword_of_int 0 : mword 32)
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  D4 (K - 10)%nat eb b lks
                  V ltac:(exact HKdlu) Htydir Hlg Hbmwf Hbmcov Hszcap Hholesl
                  ltac:(rewrite Hnib; exact (Hdok Hdz))
                  ltac:(left; exact (cr_nl0z dnl Hnl0))
                  ltac:(exact Hdoc)
                  ltac:(rewrite Hdz; unfold T_DIR_z; lia)
                  (* premise (6'), iclaim-ledger.md §3.3: the region record
                     IS the in-core one here (both slots take [dnl]). *)
                  eq_refl
                  Hj Hgs HD4a0
                  ltac:(cbn [negb]; rewrite HD4a2 dlk_zero_moi;
                        exact (eq_vec_refl _))
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hkenv Hidev Hmeta Hmap
                        Hblocks Hnb14 [] Hppid Hprocs Hdevi Hgeom Hdlk Hbs1
                        Hitb2 Hitbl Hesc Hiregi Hisl1 Hdlnk Hdiat").
        all: try lkbelow.
        (* dirlookup is eb-generic now; create is still at [eb = true]. *)
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { done. }
        iIntros (CIDdl Hsdl mdl found kk kslot qq)
          "%Hcsdl Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks Hnb14 Hppid Hbs1
           Hdlnk Hdiat Hres2".
        iEval (rewrite HD4a1) in "Hnb14".
        assert (Hpcdl : ret_pc (D4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x4a)) by (rewrite HD4ra; pcw).
        iEval (rewrite Hpcdl) in "Hpc".
        assert (Hmdlregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mdl)
          by exact (cr_regs_cs m sp0 _ _ ty major minor D4 mdl Hcsdl HD4regs).
        assert (Htg0a2 : add_vec (mword_of_int (CK + 0x4c) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 43 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0xa2)) by pcw.
        assert (Hp04c : add_vec_int (mword_of_int (CK + 0x4a) : mword 64) 2
                        = mword_of_int (CK + 0x4c)) by pcw.
        destruct found.
        * (* ========================================================== *)
          (*  THE NAME IS ALREADY THERE -- the FOUND half's two arms      *)
          (* ========================================================== *)
          iDestruct "Hres2" as "((%Hfst & %Hkslot & %Hdla0) & Hchild & Hruc & _)".
          (* the child's inum is inside the region, and NONZERO because a
             directory record is live exactly when its inum is. *)
          assert (Hklt : (kk < dir_nrec (bv_unsigned (di_size dnl)))%nat)
            by exact (dir_first_lt datl _ kk _ Hfst).
          assert (Hklive : dir_live datl kk)
            by exact (dir_first_live datl _ kk _ Hfst).
          pose (cinum := (zero_extend' 32 (dir_inum datl kk : mword 16) : mword 32)).
          assert (Hcu : bv_unsigned cinum = bv_unsigned (dir_inum datl kk))
            by (rewrite /cinum; apply dlk_zext32_unsigned).
          assert (Hcinb : bv_unsigned cinum < 16 * Z.of_nat nib)
            by (rewrite Hcu Hnib; exact (Hdok Hdz kk Hklt Hklive)).
          assert (Hcpos : 0 < bv_unsigned cinum).
          { rewrite Hcu.
            destruct (bv_unsigned_in_range _ (dir_inum datl kk)) as [Hlo _].
            destruct (Z.eq_dec (bv_unsigned (dir_inum datl kk)) 0) as [Hz | Hz];
              [| exact (cr_pos_of_nz _ Hlo Hz)].
            exfalso. apply Hklive. apply bv_eq. rewrite Hz. reflexivity. }
          destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
          (* ===== +0x4a c.mv s2,a0 : s2 = ip ========================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04a with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl) with F1.
          assert (Hf1v : add_vec (zero_reg : mword 64) (mdl !!! Regidx Ra0)
                         = ientry kslot)
            by (rewrite Hdla0; apply add_vec_zero_l).
          assert (HF1s2 : F1 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /F1 upd_eq; exact Hf1v).
          assert (HF1a0 : F1 !!! Regidx Ra0 = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /F1 upd_ne; [reflexivity | nz]).
          assert (HF1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F1)
            by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mdl _ Hf1v
                        Hmdlregs).
          iEval (rewrite Hp04c) in "Hpc".
          (* ===== +0x4c c.beqz a0 : FALLS THROUGH (a hit is an entry) == *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x4c))
                    (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    F1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HF1a0 Hdla0;
                          apply (proj2 (eq_vec_false_iff _ _));
                          exact (ientry_ne_zero kslot
                                   (Nat.lt_le_incl _ _ Hkslot)))
                    with "Hcg Hpc []").
          { iApply (cri_04c with "Htext"). }
          iIntros (CID25 Hq25) "Hcg Hpc".
          assert (Hp04e : add_vec_int (mword_of_int (CK + 0x4c) : mword 64) 2
                          = mword_of_int (CK + 0x4e)) by pcw.
          iEval (rewrite Hp04e) in "Hpc".
          (* ===== +0x4e c.mv a0,s1 : the PARENT, for iunlockput ======== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4e)) Ra0 Rs1 F1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04e with "Htext"). }
          iIntros (CID26 Hq26) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F2 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (F1 !!! Regidx Rs1))]> F1).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (F1 !!! Regidx Rs1))]> F1) with F2.
          assert (HF2a0 : F2 !!! Regidx Ra0 = ientry kd).
          { rewrite /F2 upd_eq. rewrite /F1 upd_ne; [| nz].
            destruct Hmdlregs as (_ & _ & Hd9 & _). rewrite Hd9 Hie.
            apply add_vec_zero_l. }
          assert (HF2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F2)
            by (rewrite /F2; apply cr_regs_caller; [exact Hcsa0 | exact HF1regs]).
          assert (Hp050 : add_vec_int (mword_of_int (CK + 0x4e) : mword 64) 2
                          = mword_of_int (CK + 0x50)) by pcw.
          iEval (rewrite Hp050) in "Hpc".
          (* ===== +0x50 jal iunlockput (dp), UNCREDITED ================ *)
          assert (Htgup1 : add_vec (mword_of_int (CK + 0x50) : mword 64)
                    (sign_extend' 64 (mword_of_int 2091090 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x50)) Rra
                    (mword_of_int 2091090 : mword 21) F2 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_050 with "Htext"). }
          iIntros (CID27 Hq27) "Hcg Hpc".
          iEval (rewrite Htgup1) in "Hpc".
          pose (F3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)]> F2).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)]> F2) with F3.
          assert (HF3ra : F3 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)
            by (rewrite /F3; apply upd_eq).
          assert (HF3a0 : F3 !!! Regidx Ra0 = ientry kd)
            by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
          assert (HF3regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F3)
            by (rewrite /F3; apply cr_regs_caller; [exact Hcsra | exact HF2regs]).
          iDestruct "Hmap" as "[Haddrs Hind]".
          iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind dnl bml datl
                       Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                       with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview
                             Htop")
            as "Hload".
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (cpu_own_transport CIDdl CID27 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
             goes in and the share it parked comes back in the post, so no
             bundleless out-state stands across the call. *)
          iDestruct (log_opS_named with "Hop") as (e0) "Hop".
          iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
          iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
                    gtl gild gisld bmapstart inodestart nib size
                    dev kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/2)%Qp) dind dnl bml n1 Sb1
                    false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                    F3 (K - 10)%nat eb b lks
                    V ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                    Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                    ltac:(exact Hn1ip) Hj Hgs HF3a0 ltac:(lkbelow) Hglog eq_refl
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                          Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                          Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                          Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iEval (cbn beta iota). iEmpIntro. }
          iIntros (CIDu1 Hqu1 mu1 n2 Sb2 wf1)
            "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
             %Hsb2 %Hwf1 %Hwf1c %Hn2 Hop Hisl Htp".
          assert (Hpcu1 : ret_pc (F3 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x54)) by (rewrite HF3ra; pcw).
          iEval (rewrite Hpcu1) in "Hpc".
          assert (Hmu1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu1)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F3 mu1 Hcsu1 HF3regs).
          (* GR-2c FINDING 5: the credited bound is STRONGER than the row
             the ledger cites; weaken ONCE, keeping the name. *)
          destruct (cr_after_ip n1 n2 wf1 Hn1lo (proj1 Hn2)) as [Hn2ip Hn2lo].
          (* ===== +0x54 c.mv a0,s2 : the CHILD ========================= *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x54)) Ra0 Rs2 mu1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_054 with "Htext"). }
          iIntros (CID28 Hq28) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (F4 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu1 !!! Regidx Rs2))]> mu1).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu1 !!! Regidx Rs2))]> mu1) with F4.
          assert (HF4a0 : F4 !!! Regidx Ra0 = ientry kslot).
          { rewrite /F4 upd_eq.
            destruct Hmu1regs as (_ & _ & _ & Hd18 & _). rewrite Hd18.
            apply add_vec_zero_l. }
          assert (HF4regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F4)
            by (rewrite /F4; apply cr_regs_caller; [exact Hcsa0 | exact Hmu1regs]).
          assert (Hp056 : add_vec_int (mword_of_int (CK + 0x54) : mword 64) 2
                          = mword_of_int (CK + 0x56)) by pcw.
          iEval (rewrite Hp056) in "Hpc".
          (* ===== +0x56 jal ilock (ip) ================================= *)
          assert (Htgil2 : add_vec (mword_of_int (CK + 0x56) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090488 : mword 21))
                    = mword_of_int KernelSyms.ilock) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x56)) Rra
                    (mword_of_int 2090488 : mword 21) F4 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_056 with "Htext"). }
          iIntros (CID29 Hq29) "Hcg Hpc".
          iEval (rewrite Htgil2) in "Hpc".
          pose (F5 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)]> F4).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)]> F4) with F5.
          assert (HF5ra : F5 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)
            by (rewrite /F5; apply upd_eq).
          assert (HF5a0 : F5 !!! Regidx Ra0 = ientry kslot)
            by (rewrite /F5 upd_ne; [exact HF4a0 | nz]).
          assert (HF5regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F5)
            by (rewrite /F5; apply cr_regs_caller; [exact Hcsra | exact HF4regs]).
          (* the child's reference, shed for ilock (generation UNNAMED on
             this side: dirlookup's iget hands back a plain [inode_ref]) *)
          iEval (rewrite inode_ref_shed) in "Hchild".
          iDestruct "Hchild" as "[Hckeep Hcshr]".
          iEval (rewrite inode_shr_gen_intro) in "Hcshr".
          iDestruct "Hcshr" as (gc) "Hcshr".
          iEval (rewrite inode_ref_short_gen_intro) in "Hckeep".
          iDestruct "Hckeep" as (gck) "Hckeep".
          iDestruct (inode_ref_short_shr_gen_agree with "Hckeep Hcshr") as %->.
          iDestruct (cr_esc_acc γi kslot Hkslot with "Hesc")
            as "#Hescc".
          iDestruct (ic_sleeplocks_lookup fsc_ic kslot Hkslot with "Hslks")
            as (gilc gislc) "#Hslkc".
          iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
          iDestruct (cpu_own_transport CIDu1 CID29 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE CHILD'S CHECKOUT IS ARMED (durable-disk B''-tx2) AT THE
             CHECKOUT ITSELF (B''-tx3).  The parent went home at +0x50, so
             this arm parks exactly the half that came back from its disarm,
             at the same transaction. *)
          iApply (IL.wp_ilock_dep_sconf γs j γl γu γd γk pd pav pu bn γi
                    gilc gislc inodestart nib kslot (qq/2)%Qp gc
                    (DepTx (qq/2)%Qp dev cinum gc t (1/2)) PlainK
                    dev cinum pidv (DfracOwn (1/4)) dqs F5 (K - 10)%nat eb b lks
                    V ltac:(exact HKil) eq_refl ltac:(discriminate)
                    Hkslot Hlg Hist0 Hcblk Hcinb Hj Hgs HF5a0
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hescc
                          Hiregi Hslkc Hcshr [Htp] Hruc Hsbi Hppid Hprocs Hdevi Hgeom
                          Hdlk Hbs1").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { rewrite /ic_dep_side. iExact "Htp". }
          iIntros (CIDic Hqic mic dnc bmc flc)
            "%Hcsic Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hcslkd Hcdep
             Hcidev Hciinum Hcivalid Hcload #Hcshot Hcfrz %Hfrc Hruc %Hilkpc".
          iEval (rewrite /ic_dep_held /=) in "Hcload".
          assert (Hpcic : ret_pc (F5 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x5a)) by (rewrite HF5ra; pcw).
          iEval (rewrite Hpcic) in "Hpc".
          assert (Hmicregs : cr_regs m sp0 ipv (ientry kslot) ty major minor mic)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F5 mic Hcsic HF5regs).
          pose proof Hmicregs as HmicR.
          destruct HmicR as (Z2 & Z8 & Z9 & Z18 & Z20 & Z21 & Z22 & Zthr).
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          (* ============================================================ *)
          (*  ARM F-BAD (+0x98), reached from BOTH type tests -- so it is  *)
          (*  a [□]-persistent block that takes every linear resource,     *)
          (*  the contract's own continuation included, as an ARGUMENT.    *)
          (*  ONE [iunlockput], on the CHILD: the parent was released at   *)
          (*  +0x50, which is shared with F-OK.  Both are uncredited, and  *)
          (*  [CreateBudget.cr_budget_found_w]'s third conjunct is the     *)
          (*  row that closes it.                                          *)
          (* ============================================================ *)
          iAssert (□ wp_next (CID0 := CID) true (proc_addr j) (fun CIDb : CpuId =>
                     ∀ Mb : regfile,
                       ⌜cr_regs m sp0 ipv (ientry kslot) ty major minor Mb⌝ -∗
                       sie_cap_gpr KT1 Mb (K - 10)%nat b (proc_addr j) -∗
                       cpu_own 0 eb (proc_addr j) b lks -∗
                       pc_is (mword_of_int (CK + 0x98)) -∗
                       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
                       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
                       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
                       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
                       (pa_stk sp0 5) ↦₈[KT1] u5 -∗
                       (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
                       (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
                       (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
                       ([∗ list] jj ∈ seq 0 14,
                          pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nfp jj) -∗
                       ([∗ list] jj ∈ seq 14 2,
                          pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf0 jj) -∗
                       sleeplocked_q gislc (qq/2)%Qp (i_lock (ientry kslot)) pidv -∗
                       ic_deposit fsc_ic kslot (DepTx (qq/2)%Qp dev cinum gc t (1/2)) -∗
                       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
                       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
                       i_valid (ientry kslot) ↦₄ valid_word true -∗
                       ic_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum dnc bmc -∗
                       ity_shot gc (di_type dnc) -∗
                       (* the child payload's freeze token (§3.9) *)
                       ifreeze_off (bv_unsigned cinum) -∗
                       inode_ref_short_gen kslot (qq/2 + qq/2)%Qp (qq/2)%Qp
                                           dev cinum gc -∗
                       (* the child's PROVENANCE UNIT (item 7a-wire). *)
                       runit_any (bv_unsigned cinum) -∗
                       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
                       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
                       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                       proc_priv_bare (proc_addr j) pidv V -∗
                       (proc_priv_bare (proc_addr j) pidv V -∗
                          proc_priv γf (proc_addr j) pidv V) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ[KT1] pfun i) -∗
                       bslots 3 -∗
                       iref_slots 1 -∗ iref_slots (ns - 2) -∗
                       log_opS γ n2 Sb2 -∗
                       t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
                       wp_next (CID0 := CID) true (proc_addr j)
                         (fun CIDc : CpuId =>
                            cr_cont_body γi γ γf bn bmapstart
                              inodestart nib ninodes size dev plen pfun
                              (m !!! Regidx Ra0 : mword 64) ty major minor V u Sb
                              ns pidv dqb dqs dqbs dqn m K eb b lks j ret_tgt
                              CIDc) -∗
                       WP (Loop : expr riscv_lang)))%I
            with "[]" as "#Hfbad".
          { iModIntro.
            iIntros (CIDb Hsb Mb)
              "%HBr Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
               Hcslkd Hcdep Hcidev Hciinum Hcivalid Hcload Hcshotb
               Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs Hsbb Hppid Hppback Hpath Hbsl
               Hisl Hislr Hop Htx Hcontb".
            pose proof HBr as HBr2.
            destruct HBr2 as (X2 & X8 & X9 & X18 & X20 & X21 & X22 & Xthr).
            (* +0x98 c.mv a0,s2 : the CHILD *)
            iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x98)) Ra0 Rs2 Mb
                      (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
            { iApply (cri_098 with "Htext"). }
            iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
            pose (B1 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb).
            change (<[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb) with B1.
            assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kslot).
            { rewrite /B1 upd_eq. rewrite X18. apply add_vec_zero_l. }
            assert (HB1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B1)
              by (rewrite /B1; apply cr_regs_caller; [exact Hcsa0 | exact HBr]).
            assert (Hq09a : add_vec_int (mword_of_int (CK + 0x98) : mword 64) 2
                            = mword_of_int (CK + 0x9a)) by pcw.
            iEval (rewrite Hq09a) in "Hpc".
            (* +0x9a jal iunlockput (ip), at crb = cru = crz = false *)
            assert (Htgup2 : add_vec (mword_of_int (CK + 0x9a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091016 : mword 21))
                      = mword_of_int KernelSyms.iunlockput) by pcw.
            iApply (wp_jal_s_sconf (mword_of_int (CK + 0x9a)) Rra
                      (mword_of_int 2091016 : mword 21) B1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (cri_09a with "Htext"). }
            iIntros (CIDB2 HqB2) "Hcg Hpc".
            iEval (rewrite Htgup2) in "Hpc".
            pose (B2 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)]> B1).
            change (<[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)]> B1) with B2.
            assert (HB2ra : B2 !!! Regidx Rra
                            = add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)
              by (rewrite /B2; apply upd_eq).
            assert (HB2a0 : B2 !!! Regidx Ra0 = ientry kslot)
              by (rewrite /B2 upd_ne; [exact HB1a0 | nz]).
            assert (HB2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B2)
              by (rewrite /B2; apply cr_regs_caller; [exact Hcsra | exact HB1regs]).
            iDestruct (cpu_own_transport CIDb CIDB2 0%nat eb (proc_addr j) b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
               goes in and the share it parked comes back in the post, so no
               bundleless out-state stands across the call. *)
            iDestruct (log_opS_named with "Hop") as (ec) "Hop".
            iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckeep2".
            iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
                      gtl gilc gislc bmapstart inodestart nib
                      size dev kslot (qq/2)%Qp (qq/2)%Qp gc (DepTx (qq/2)%Qp dev cinum gc t (1/2)%Qp) cinum dnc bmc
                      n2 Sb2 false false false ec _ _ pidv (DfracOwn (1/4)) dqb dqs
                      B2 (K - 10)%nat eb b lks
                      V ltac:(exact HKiup) eq_refl Hkslot ltac:(discriminate)
                      ltac:(discriminate)
                      Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
                      ltac:(exact Hn2ip) Hj Hgs HB2a0 ltac:(lkbelow) Hglog eq_refl
                      with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                            Hitbl Hescc Hiregi Hiopen Hslkc Hcslkd Hcdep
                            Hcidev Hciinum Hcivalid Hcload Hcshotb Hcfrz [$Hckeep2 $Hruc] Hsbb
                            Hsbi Hbmr Hppid Hprocs Hdevi Hgeom Hdlk Hbsl []
                            Hop").
            all: try lkbelow.
            { rewrite Heb /trap_csrs_ext. done. }
            { rewrite Heb /cpu_claim_ext. done. }
            { iEval (cbn beta iota). iEmpIntro. }
            iIntros (CIDU2 HqU2 mu2 n3 Sb3 wf2)
              "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
               %Hsb3 %Hwf2 %Hwf2c %Hn3 Hop Hisl2 Htp".
            iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                         (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
            iDestruct (log_tx_full with "Htw") as "Htx".
            iEval (rewrite -Hglog) in "Htx".
            assert (Hpcu2 : ret_pc (B2 !!! Regidx Rra : mword 64)
                            = mword_of_int (CK + 0x9e)) by (rewrite HB2ra; pcw).
            iEval (rewrite Hpcu2) in "Hpc".
            assert (Hmu2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu2)
              by exact (cr_regs_cs m sp0 _ _ ty major minor B2 mu2 Hcsu2 HB2regs).
            iDestruct ("Hppback" with "Hppid") as "Hpriv".
            (* +0x9e c.li s2,0 *)
            iApply (wp_cli_s_sconf (mword_of_int (CK + 0x9e)) Rs2
                      (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                      mu2 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                      with "Hcg Hpc []").
            { iApply (cri_09e with "Htext"). }
            iIntros (CIDB3 HqB3) "Hcg Hpc".
            pose (B3 := <[Regidx Rs2 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> mu2).
            change (<[Regidx Rs2 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> mu2) with B3.
            assert (HB3s2 : B3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
              by (rewrite /B3; apply upd_eq).
            assert (Hb3v : (mword_of_int 0 : mword 64)
                           = (mword_of_int 0 : mword 64)) by reflexivity.
            assert (HB3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                                ty major minor B3)
              by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mu2 _ Hb3v
                          Hmu2regs).
            assert (Hq0a0 : add_vec_int (mword_of_int (CK + 0x9e) : mword 64) 2
                            = mword_of_int (CK + 0xa0)) by pcw.
            iEval (rewrite Hq0a0) in "Hpc".
            (* +0xa0 c.j +0x70 *)
            assert (Htg070b : add_vec (mword_of_int (CK + 0xa0) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2024 : mword 11) ('b"0"))))
                      = mword_of_int (CK + 0x70)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (CK + 0xa0))
                      (sign_extend' 21
                         (concat_vec (mword_of_int 2024 : mword 11) ('b"0")))
                      B3 (K - 10)%nat b
                      ltac:(rewrite Htg070b; vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (cri_0a0 with "Htext"). }
            iIntros (CIDB4 HqB4). iApply bi.later_intro. iIntros "Hcg Hpc".
            iEval (rewrite Htg070b) in "Hpc".
            iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
              as (nfjb) "Hnb16".
            iPoseProof ("Htail" $! CIDB4) as "Ht".
            iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
            iApply ("Ht" $! B3 u5 nfjb with
                      "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
            { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor B3 HB3regs). }
            iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
            iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (iref_slots_combine with "Hisl2 Hisl") as "Hisl".
            iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
            iSpecialize ("Hcontb" $! CIDf with "[%]"); [wp_next_chain |].
            iApply ("Hcontb" $! mf false false 0%nat 1%Qp 1%Qp γf
                      (mword_of_int 0 : mword 32) dnc bmc n3 Sb3
                      (1 + (1 + (ns - 2)))%nat
                      with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                            Hpath Hbsl [%] Hisl [%] Hop [$Htx]").
            { exact Hcsf. }
            { exact (cr_slots_2 _ ns eq_refl Hns). }
            { split_and!;
                [exact (cr_sub3 _ _ _ _ Hsb1 Hsb2 Hsb3)
                | exact (cr_le3 _ _ _ _ (proj2 Hn3) (proj2 Hn2) (proj2 Hnp1))
                | discriminate]. }
            { iPureIntro. rewrite Ha0f. exact HB3s2. } }
          (* ===== +0x5a c.li a5,2 ===================================== *)
          iApply (wp_cli_s_sconf (mword_of_int (CK + 0x5a)) Ra5
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    mic (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc []").
          { iApply (cri_05a with "Htext"). }
          iIntros (CID30 Hq30) "Hcg Hpc".
          pose (F6 := <[Regidx Ra5 := regval_into_reg
                        (mword_of_int 2 : mword 64)]> mic).
          change (<[Regidx Ra5 := regval_into_reg
                        (mword_of_int 2 : mword 64)]> mic) with F6.
          assert (HF6a5 : F6 !!! Regidx Ra5 = (mword_of_int 2 : mword 64))
            by (rewrite /F6; apply upd_eq).
          assert (HF6s4 : F6 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64))
            by (rewrite /F6 upd_ne; [exact Z20 | nz]).
          assert (HF6s2 : F6 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /F6 upd_ne; [exact Z18 | nz]).
          assert (HF6regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F6)
            by (rewrite /F6; apply cr_regs_caller; [exact Hcsa5 | exact Hmicregs]).
          assert (Hp05c : add_vec_int (mword_of_int (CK + 0x5a) : mword 64) 2
                          = mword_of_int (CK + 0x5c)) by pcw.
          iEval (rewrite Hp05c) in "Hpc".
          assert (Htg098 : add_vec (mword_of_int (CK + 0x5c) : mword 64)
                    (sign_extend' 64 (mword_of_int 60 : mword 13))
                    = mword_of_int (CK + 0x98)) by pcw.
          destruct (decide (ty = T_FILE)) as [Htyf | Htyf].
          -- (* the requested type IS T_FILE: the second test decides *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (CK + 0x5c))
                       (mword_of_int 60 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_eq _ Htyf))
                       with "Hcg Hpc []").
             { iApply (cri_05c with "Htext"). }
             iIntros (CID31 Hq31) "Hcg Hpc".
             assert (Hp060 : add_vec_int (mword_of_int (CK + 0x5c) : mword 64) 4
                             = mword_of_int (CK + 0x60)) by pcw.
             iEval (rewrite Hp060) in "Hpc".
             iDestruct (ic_loaded_open with "Hcload") as (datc)
        "(%Hciok & %Hrl_datc & %Hcdok & %Hcddix & %Hcdoc & %Hcduq & Hcdlnk & Hcdiat
          & Hcmeta & Hcaddrs & Hcind & Hcblocks & Hcdview & Hcfview & Hctop)".
      iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
             iEval (rewrite /i_type) in "Hcity".
             (* ===== +0x60 lhu a5,68(s2) : ip->type, ZERO-extended ==== *)
             iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x60)) Ra5 Rs2
                       (mword_of_int 68 : mword 12) F6 (K - 10)%nat
                       (di_type dnc : mword 16) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc [] [Hcity]").
             { iApply (cri_060 with "Htext"). }
             { iEval (rgne; rewrite HF6s2). iExact "Hcity". }
             iIntros (CID32 Hq32) "Hcg Hpc Hcity".
             iEval (rgne; rewrite HF6s2) in "Hcity".
             pose (F7 := <[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6).
             change (<[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6) with F7.
             assert (HF7regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F7)
               by (rewrite /F7; apply cr_regs_caller; [exact Hcsa5 | exact HF6regs]).
             assert (Hp064 : add_vec_int (mword_of_int (CK + 0x60) : mword 64) 4
                             = mword_of_int (CK + 0x64)) by pcw.
             iEval (rewrite Hp064) in "Hpc".
             (* ===== +0x64 c.addiw a5,-2 ============================== *)
             iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x64)) Ra5
                       (mword_of_int 62 : mword 6) F7 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
             { iApply (cri_064 with "Htext"). }
             iIntros (CID33 Hq33) "Hcg Hpc".
             pose (F8 := <[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64
                              (subrange_vec_dec
                                 (add_vec (rget F7 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 62 : mword 6))))
                                 31 0))]> F7).
             change (<[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64
                              (subrange_vec_dec
                                 (add_vec (rget F7 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 62 : mword 6))))
                                 31 0))]> F7) with F8.
             assert (HF8regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F8)
               by (rewrite /F8; apply cr_regs_caller; [exact Hcsa5 | exact HF7regs]).
             assert (Hp066 : add_vec_int (mword_of_int (CK + 0x64) : mword 64) 2
                             = mword_of_int (CK + 0x66)) by pcw.
             iEval (rewrite Hp066) in "Hpc".
             (* ===== +0x66 c.slli a5,48 / +0x68 c.srli a5,48 ========== *)
             iApply (wp_cslli_s_sconf (mword_of_int (CK + 0x66))
                       (Regidx Ra5) Ra5 (mword_of_int 48 : mword 6)
                       F8 (K - 10)%nat b eq_refl ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_066 with "Htext"). }
             iIntros (CID34 Hq34) "Hcg Hpc".
             pose (F9 := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8).
             change (<[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8) with F9.
             assert (HF9regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F9)
               by (rewrite /F9; apply cr_regs_caller; [exact Hcsa5 | exact HF8regs]).
             assert (Hp068 : add_vec_int (mword_of_int (CK + 0x66) : mword 64) 2
                             = mword_of_int (CK + 0x68)) by pcw.
             iEval (rewrite Hp068) in "Hpc".
             iApply (wp_csrli_s_sconf (mword_of_int (CK + 0x68))
                       (Cregidx (mword_of_int 7)) Ra5 (mword_of_int 48 : mword 6)
                       F9 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
             { iApply (cri_068 with "Htext"). }
             iIntros (CID35 Hq35) "Hcg Hpc".
             pose (FA := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_right (rget F9 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F9).
             change (<[Regidx Ra5 := regval_into_reg
                           (shift_bits_right (rget F9 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F9) with FA.
             assert (HFAregs : cr_regs m sp0 ipv (ientry kslot) ty major minor FA)
               by (rewrite /FA; apply cr_regs_caller; [exact Hcsa5 | exact HF9regs]).
             (* THE THREE ALU LEAVES HAVE LEFT EXACTLY [cr_trange] IN a5.
                Each leaf spells its own output at [rget], so the chain is
                built one equation at a time, and the [rget] the STORED
                VALUE carries is normalised by [rgne] AFTER the [upd_eq]
                that exposes it.  It must be [rgne] and not a hand-written
                bridge: [rget] is HART-INDEXED, the leaf's output names the
                REBOUND hart, and an equation written fresh in the proof
                means the SECTION one -- so the two print identically and
                do not rewrite (durable-notes).  [cr_trange] then closes by
                conversion, which is the whole reason it was named. *)
             assert (HF7a5 : F7 !!! Regidx Ra5
                             = (zero_extend' 64 (di_type dnc : mword 16)
                                : mword 64))
               by (rewrite /F7; apply upd_eq).
             assert (HF8a5 : F8 !!! Regidx Ra5
                             = sign_extend' 64
                                 (subrange_vec_dec
                                    (add_vec (zero_extend' 64
                                                (di_type dnc : mword 16)
                                              : mword 64)
                                       (sign_extend' 64
                                          (sign_extend' 12
                                             (mword_of_int 62 : mword 6))))
                                    31 0)).
             { rewrite /F8 upd_eq. rgne. rewrite HF7a5. reflexivity. }
             assert (HF9a5 : F9 !!! Regidx Ra5
                             = shift_bits_left
                                 (sign_extend' 64
                                    (subrange_vec_dec
                                       (add_vec (zero_extend' 64
                                                   (di_type dnc : mword 16)
                                                 : mword 64)
                                          (sign_extend' 64
                                             (sign_extend' 12
                                                (mword_of_int 62 : mword 6))))
                                       31 0))
                                 (subrange_vec_dec (mword_of_int 48 : mword 6)
                                    (Z.sub log2_xlen 1) 0)).
             { rewrite /F9 upd_eq. rgne. rewrite HF8a5. reflexivity. }
             assert (HFAa5 : FA !!! Regidx Ra5 = cr_trange (di_type dnc)).
             { rewrite /FA upd_eq. rgne. rewrite HF9a5 /cr_trange. reflexivity. }
             assert (Hp06a : add_vec_int (mword_of_int (CK + 0x68) : mword 64) 2
                             = mword_of_int (CK + 0x6a)) by pcw.
             iEval (rewrite Hp06a) in "Hpc".
             (* ===== +0x6a c.li a4,1 ================================== *)
             iApply (wp_cli_s_sconf (mword_of_int (CK + 0x6a)) Ra4
                       (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                       FA (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                       with "Hcg Hpc []").
             { iApply (cri_06a with "Htext"). }
             iIntros (CID36 Hq36) "Hcg Hpc".
             pose (FB := <[Regidx Ra4 := regval_into_reg
                           (mword_of_int 1 : mword 64)]> FA).
             change (<[Regidx Ra4 := regval_into_reg
                           (mword_of_int 1 : mword 64)]> FA) with FB.
             assert (HFBa4 : FB !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
               by (rewrite /FB; apply upd_eq).
             assert (HFBa5 : FB !!! Regidx Ra5 = cr_trange (di_type dnc))
               by (rewrite /FB upd_ne; [exact HFAa5 | nz]).
             assert (HFBs2 : FB !!! Regidx Rs2 = ientry kslot).
             { rewrite /FB upd_ne; [| nz]. rewrite /FA upd_ne; [| nz].
               rewrite /F9 upd_ne; [| nz]. rewrite /F8 upd_ne; [| nz].
               rewrite /F7 upd_ne; [exact HF6s2 | nz]. }
             assert (HFBregs : cr_regs m sp0 ipv (ientry kslot) ty major minor FB)
               by (rewrite /FB; apply cr_regs_caller; [exact Hcsa4 | exact HFAregs]).
             assert (Hp06c : add_vec_int (mword_of_int (CK + 0x6a) : mword 64) 2
                             = mword_of_int (CK + 0x6c)) by pcw.
             iEval (rewrite Hp06c) in "Hpc".
             assert (Htg098b : add_vec (mword_of_int (CK + 0x6c) : mword 64)
                       (sign_extend' 64 (mword_of_int 44 : mword 13))
                       = mword_of_int (CK + 0x98)) by pcw.
             iAssert (inode_meta (ientry kslot) dnc)
               with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmetal".
             { rewrite /inode_meta /i_type. iFrame. }
             iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum dnc bmc
                          datc Hciok Hrl_datc Hcdok Hcddix Hcdoc Hcduq
                          with "Hcdlnk Hcdiat Hcmetal Hcaddrs Hcind Hcblocks
                                Hcdview Hcfview Hctop")
               as "Hcload".
             destruct (zopz0zI_u (mword_of_int 1 : mword 64)
                         (cr_trange (di_type dnc))) eqn:Hrng.
             ++ (* ===== ARM F-BAD (second entry): the type is out of
                    range, so the found inode is a directory or free ==== *)
                iApply (wp_bltu_taken_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          ltac:(rewrite Htg098b; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (cri_06c with "Htext"). }
                iIntros (CID37 Hq37). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htg098b) in "Hpc".
                iDestruct (cpu_own_transport CIDic CID37 0%nat eb
                             (proc_addr j) b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
                  as "Hcnt".
                iPoseProof ("Hfbad" $! CID37) as "Hfb".
                iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
                iApply ("Hfb" $! FB with
                          "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                           Hnb14 Hnb2 Hcslkd Hcdep Hcidev Hciinum
                           Hcivalid Hcload Hcshot Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs
                           Hsbb
                           Hppid Hppback Hpath Hbsl Hisl Hislr Hop Htx Hcont").
                { exact HFBregs. }
             ++ (* ===== ARM F-OK: the found inode is a file or a device *)
                iApply (wp_bltu_fall_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          with "Hcg Hpc []").
                { iApply (cri_06c with "Htext"). }
                iIntros (CID37 Hq37) "Hcg Hpc".
                assert (Hp070 : add_vec_int (mword_of_int (CK + 0x6c) : mword 64) 4
                                = mword_of_int (CK + 0x70)) by pcw.
                iEval (rewrite Hp070) in "Hpc".
                iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
                  as (nfj) "Hnb16".
                iDestruct ("Hppback" with "Hppid") as "Hpriv".
                iPoseProof ("Htail" $! CID37) as "Ht".
                iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
                iApply ("Ht" $! FB u5 nfj with
                          "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
                { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor FB HFBregs). }
                iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
                iDestruct (cpu_own_transport CIDic CIDf 0%nat eb (proc_addr j) b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
                iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
                iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
                iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
                iApply ("Hcont" $! mf true false kslot (qq/2)%Qp (qq/2)%Qp gc
                          cinum dnc bmc n2 Sb2 (1 + (ns - 2))%nat
                          with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                                Hpath Hbsl [%] Hisl [%] Hop [Hcslkd Hcdep
                                Hcidev Hciinum Hcivalid Hcload Hcfrz Hckeep Hruc]").
                { exact Hcsf. }
                { exact (cr_slots_1 _ ns eq_refl Hns). }
                { split_and!;
                    [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                    | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                    | intros _; exact Hn2ip]. }
                iSplitR.
                { iPureIntro. split; [rewrite Ha0f; exact HFBs2 |].
                  split; [exact Hkslot |].
                  split; [split; [exact Hcpos | exact Hcinb] |].
                  split; [exact Htyf |].
                  exact (cr_trange_in (di_type dnc) Hrng). }
                iApply (create_locked_mk γi
                          _ _ _ _ _ _ _ _ _ gilc gislc
                          with "Hslkc Hcslkd Hcdep Hcidev Hciinum
                                Hcivalid Hcload Hcshot Hcfrz Hckeep Hruc").
          -- (* ===== ARM F-BAD (first entry): type != T_FILE ========== *)
             iApply (wp_bne_taken_s_sconf (mword_of_int (CK + 0x5c))
                       (mword_of_int 60 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_ne _ Htyf))
                       ltac:(rewrite Htg098; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_05c with "Htext"). }
             iIntros (CID31 Hq31). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg098) in "Hpc".
             iDestruct (cpu_own_transport CIDic CID31 0%nat eb
                          (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
               as "Hcnt".
             iPoseProof ("Hfbad" $! CID31) as "Hfb".
             iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
             iApply ("Hfb" $! F6 with
                       "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hcslkd Hcdep Hcidev Hciinum
                        Hcivalid Hcload Hcshot Hcfrz Hckeep Hruc Hsbn Hsbi Hsbs
                        Hsbb
                        Hppid Hppback Hpath Hbsl Hisl Hislr Hop Htx Hcont").
             { exact HF6regs. }
        * (* ========================================================== *)
          (*  THE NAME IS NOT THERE -- the ALLOCATE half, PARKED         *)
          (* ========================================================== *)
          iDestruct "Hres2" as "((%Hnone & %Hdla0) & Hisl1 & _)".
          (* +0x4a c.mv s2,a0 : s2 := 0, and it STAYS 0 all the way to
             +0xe6 / +0xf2 -- the live invariant the failure arms use. *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_04a with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (A1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl) with A1.
          assert (Ha1v : add_vec (zero_reg : mword 64) (mdl !!! Regidx Ra0)
                         = (mword_of_int 0 : mword 64))
            by (rewrite Hdla0; apply add_vec_zero_l).
          assert (HA1a0 : A1 !!! Regidx Ra0 = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /A1 upd_ne; [reflexivity | nz]).
          assert (HA1regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                              ty major minor A1)
            by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mdl _ Ha1v
                        Hmdlregs).
          iEval (rewrite Hp04c) in "Hpc".
          (* ===== +0x4c c.beqz a0 : TAKEN -> the allocate half ======== *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x4c))
                    (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    A1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HA1a0 Hdla0;
                          apply (proj2 (eq_vec_true_iff _ _));
                          exact dlk_zero_moi)
                    ltac:(rewrite Htg0a2; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_04c with "Htext"). }
          iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg0a2) in "Hpc".
          iDestruct ("Hppback" with "Hppid") as "Hpriv".
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (iref_slots_combine with "Hisl1 Hislr") as "Hisl".
          assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat)
            by exact (cr_ns_1 ns Hns).
          iEval (rewrite Hns1) in "Hisl".
          iDestruct (cpu_own_transport CIDdl CID25 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iPoseProof ("Halloc" $! CID25) as "Ha".
          iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
          iEval (rewrite -Hglog) in "Htx".
          iApply ("Ha" $! A1 u5 kd qd gd gild gisld dind dnl bml datl nfp nf0
                    n1 Sb1 w t
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%] [%] [%]
                          Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                          Hnb14 Hnb2 Hslkd Hslkdd Hdep Hidev Hiinum
                          Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview
                          Htop Hshotl Hfrzl Hkeep Hrud
                          Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath Hbsl Hisl Hop Htx
                          Hcont").
          { rewrite -Hie. exact HA1regs. }
          { exact Hkd. }
          { exact Hdib'. }
          { exact Htydir. }
          { exact Hnl0. }
          { exact Hnlmax. }
          { exact Hiok. }
          { rewrite Hnib. exact Hdok. }
          { exact Hddix. }
          { exact Hduq. }
          { exact Hrl_datl. }
          { exact Hnpname. }
          { exact Hnone. }
          { exact Hsb1. }
          { exact Hwmem. }
          { exact Hnp1. }
          - (* ===== ARM G2: the guard FIRES -- the parent is a full ====
               directory and the caller asked for another one.  The block
               is ARM G's, at +0x8e, and it closes the same way: the
               [iunlockput(dp)] runs uncredited and the answer is 0.  What
               differs is only the hypothesis it is under -- [nlink] is
               32767 here rather than 0 -- and no step below reads it. *)
            iIntros (CIDg) "%Hqg". iIntros (Mg) "%HMgregs Hcg Hpc".
            pose proof HMgregs as HMgR.
            destruct HMgR as (V2 & V8 & V9 & V18 & V20 & V21 & V22 & Vthr).
        (* Same fix as this file's other [ic_loaded] sites: assembled by
           the constructor, not by [iFrame], which would re-search the
           whole function context against the 268-element [inode_blocks]
           big-op. *)
        iAssert (inode_meta (ientry kd) dnl)
          with "[Hity Himaj Himin Hinl Hisz]" as "Hmetal".
        { rewrite /inode_meta /i_type /i_nlink. iFrame. }
        iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind dnl bml datl
                     Hiok Hrl_datl Hdok Hddix Hdoc Hduq
                     with "Hdlnk Hdiat Hmetal Haddrs Hind Hblocks Hdview Hfview
                           Htop")
          as "Hload".
        iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x8e c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x8e)) Ra0 Rs1 Mg
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_08e with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (J1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Mg !!! Regidx Rs1))]> Mg).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Mg !!! Regidx Rs1))]> Mg) with J1.
        assert (HJ1a0 : J1 !!! Regidx Ra0 = ientry kd).
        { rewrite /J1 upd_eq.
          rewrite V9 Hie. apply add_vec_zero_l. }
        assert (HJ1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor J1)
          by (rewrite /J1; apply cr_regs_caller; [exact Hcsa0 | exact HMgregs]).
        assert (Hp090 : add_vec_int (mword_of_int (CK + 0x8e) : mword 64) 2
                        = mword_of_int (CK + 0x90)) by pcw.
        iEval (rewrite Hp090) in "Hpc".
        (* +0x90 jal iunlockput (dp) -- AT crb = cru = crz = false.
           [crz] is unavailable BY CONSTRUCTION on this arm: it is bought
           with [InodeRegion.nlz_obs], minted only at a NONZERO nlink
           observation, and this arm IS the zero observation. *)
        assert (HtgupG : add_vec (mword_of_int (CK + 0x90) : mword 64)
                  (sign_extend' 64 (mword_of_int 2091026 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x90)) Rra
                  (mword_of_int 2091026 : mword 21) J1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_090 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite HtgupG) in "Hpc".
        pose (J2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)]> J1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)]> J1) with J2.
        assert (HJ2ra : J2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)
          by (rewrite /J2; apply upd_eq).
        assert (HJ2a0 : J2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
        assert (HJ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor J2)
          by (rewrite /J2; apply cr_regs_caller; [exact Hcsra | exact HJ1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
           goes in and the share it parked comes back in the post, so no
           bundleless out-state stands across the call. *)
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
        iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
                  gtl gild gisld bmapstart inodestart nib size dev
                  kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/2)%Qp) dind dnl bml n1 Sb1
                  false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                  J2 (K - 10)%nat eb b lks
                  V ltac:(exact HKiup) eq_refl Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HJ2a0 ltac:(lkbelow) Hglog eq_refl
                  with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                        Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        all: try lkbelow.
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl Htp".
        iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                     (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
        iDestruct (log_tx_full with "Htw") as "Htx".
        iEval (rewrite -Hglog) in "Htx".
        assert (Hpcup : ret_pc (J2 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x94)) by (rewrite HJ2ra; pcw).
        iEval (rewrite Hpcup) in "Hpc".
        assert (Hmupregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mup)
          by exact (cr_regs_cs m sp0 _ _ ty major minor J2 mup Hcsup HJ2regs).
        iDestruct ("Hppback" with "Hppid") as "Hpriv".
        (* +0x94 c.li s2,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x94)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mup (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc []").
        { iApply (cri_094 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc".
        pose (J3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
        change (<[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup) with J3.
        assert (HJ3s2 : J3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
          by (rewrite /J3; apply upd_eq).
        assert (Hg2v : (mword_of_int 0 : mword 64) = (mword_of_int 0 : mword 64))
          by reflexivity.
        assert (HJ3regs : cr_regs m sp0 ipv (mword_of_int 0 : mword 64)
                            ty major minor J3)
          by exact (cr_regs_s2 m sp0 ipv _ _ ty major minor mup _
                      Hg2v Hmupregs).
        assert (Hp096 : add_vec_int (mword_of_int (CK + 0x94) : mword 64) 2
                        = mword_of_int (CK + 0x96)) by pcw.
        iEval (rewrite Hp096) in "Hpc".
        (* +0x96 c.j +0x70 *)
        assert (Htg070h : add_vec (mword_of_int (CK + 0x96) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
                  = mword_of_int (CK + 0x70)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (CK + 0x96))
                  (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
                  J3 (K - 10)%nat b
                  ltac:(rewrite Htg070h; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_096 with "Htext"). }
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070h) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! J3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor J3 HJ3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [$Htx]").
        { exact Hcsf. }
        { exact (cr_slots_ns _ ns eq_refl Hns). }
        { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                      | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                      | discriminate]. }
        { iPureIntro. rewrite Ha0f. exact HJ3s2. }
        }
        (* ===== +0x30 c.lui a4,0xffff8 ================================= *)
        iApply (wp_clui_s_sconf (mword_of_int (CK + 0x30)) Ra4
                  (sign_extend' 20 (mword_of_int 56 : mword 6))
                  (mword_of_int (-32768) : mword 64) Q3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_030 with "Htext"). }
        iIntros (CID20 Hq20) "Hcg Hpc".
        pose (N1 := <[Regidx Ra4 := regval_into_reg
                      (mword_of_int (-32768) : mword 64)]> Q3).
        change (<[Regidx Ra4 := regval_into_reg
                      (mword_of_int (-32768) : mword 64)]> Q3) with N1.
        assert (HN1a4 : N1 !!! Regidx Ra4 = (mword_of_int (-32768) : mword 64))
          by (rewrite /N1; apply upd_eq).
        assert (HN1a5 : N1 !!! Regidx Ra5
                        = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
          by (rewrite /N1 upd_ne; [exact HQ3a5 | nz]).
        assert (HN1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N1)
          by (rewrite /N1; apply cr_regs_caller; [exact Hcsa4 | exact HQ3regs]).
        assert (Hp032 : add_vec_int (mword_of_int (CK + 0x30) : mword 64) 2
                        = mword_of_int (CK + 0x32)) by pcw.
        iEval (rewrite Hp032) in "Hpc".
        (* ===== +0x32 c.addi a4,a4,1 : a4 = -NLINK_MAX ================= *)
        iApply (wp_caddi_s_sconf (mword_of_int (CK + 0x32)) Ra4
                  (mword_of_int 1 : mword 6) N1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_032 with "Htext"). }
        iIntros (CID21 Hq21) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (N2 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (N1 !!! Regidx Ra4)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N1).
        change (<[Regidx Ra4 := regval_into_reg
                      (add_vec (N1 !!! Regidx Ra4)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N1) with N2.
        assert (HN2a4 : N2 !!! Regidx Ra4 = (mword_of_int (-32767) : mword 64)).
        { rewrite /N2 upd_eq HN1a4. apply bv_eq; vm_compute; reflexivity. }
        assert (HN2a5 : N2 !!! Regidx Ra5
                        = (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64))
          by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
        assert (HN2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N2)
          by (rewrite /N2; apply cr_regs_caller; [exact Hcsa4 | exact HN1regs]).
        assert (Hp034 : add_vec_int (mword_of_int (CK + 0x32) : mword 64) 2
                        = mword_of_int (CK + 0x34)) by pcw.
        iEval (rewrite Hp034) in "Hpc".
        (* ===== +0x34 c.add a5,a5,a4 : a5 = nlink - NLINK_MAX ========== *)
        iApply (wp_cadd_s_sconf (mword_of_int (CK + 0x34)) Ra5 Ra4
                  N2 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_034 with "Htext"). }
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
        pose (N3 := <[Regidx Ra5 := regval_into_reg
                      (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2).
        change (<[Regidx Ra5 := regval_into_reg
                      (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2) with N3.
        assert (HN3a5 : N3 !!! Regidx Ra5
                        = add_vec
                            (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)
                            (mword_of_int (-32767) : mword 64)).
        { rewrite /N3 upd_eq HN2a5 HN2a4. reflexivity. }
        assert (HN3regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor N3)
          by (rewrite /N3; apply cr_regs_caller; [exact Hcsa5 | exact HN2regs]).
        pose proof HN3regs as HN3R.
        destruct HN3R as (_ & _ & _ & _ & HN3s4 & _ & _ & _).
        assert (Hp036 : add_vec_int (mword_of_int (CK + 0x34) : mword 64) 2
                        = mword_of_int (CK + 0x36)) by pcw.
        iEval (rewrite Hp036) in "Hpc".
        assert (Htg03e : add_vec (mword_of_int (CK + 0x36) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0x3e)) by pcw.
        destruct (decide (di_nlink dnl = (mword_of_int 32767 : mword 16)))
          as [Hnlm | Hnlm].
        * (* ---- the count IS at NLINK_MAX: on to the type test ------- *)
          iApply (wp_cbnez_fall_s_sconf (mword_of_int (CK + 0x36))
                    (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N3 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN3a5; exact (cr_nlmax_eq _ Hnlm))
                    with "Hcg Hpc []").
          { iApply (cri_036 with "Htext"). }
          iIntros (CID23 Hq23) "Hcg Hpc".
          assert (Hp038 : add_vec_int (mword_of_int (CK + 0x36) : mword 64) 2
                          = mword_of_int (CK + 0x38)) by pcw.
          iEval (rewrite Hp038) in "Hpc".
          (* ===== +0x38 addi a5,s4,-1 : a5 = type - T_DIR ============== *)
          iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x38)) Ra5 Rs4
                    (mword_of_int 4095 : mword 12) N3 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_038 with "Htext"). }
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (N4 := <[Regidx Ra5 := regval_into_reg
                        (add_vec (N3 !!! Regidx Rs4)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> N3).
          change (<[Regidx Ra5 := regval_into_reg
                        (add_vec (N3 !!! Regidx Rs4)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> N3) with N4.
          assert (HN4a5 : N4 !!! Regidx Ra5
                          = add_vec (sign_extend' 64 ty : mword 64)
                              (sign_extend' 64
                                 (mword_of_int 4095 : mword 12) : mword 64)).
          { rewrite /N4 upd_eq HN3s4. reflexivity. }
          assert (HN4regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                              ty major minor N4)
            by (rewrite /N4; apply cr_regs_caller; [exact Hcsa5 | exact HN3regs]).
          assert (Hp03c : add_vec_int (mword_of_int (CK + 0x38) : mword 64) 4
                          = mword_of_int (CK + 0x3c)) by pcw.
          iEval (rewrite Hp03c) in "Hpc".
          assert (Htg08e : add_vec (mword_of_int (CK + 0x3c) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 41 : mword 8) ('b"0"))))
                    = mword_of_int (CK + 0x8e)) by pcw.
          destruct (decide (ty = SpecDirlookup.T_DIR)) as [Htdirg | Htdirg].
          ** (* ---- ARM G2: a new DIRECTORY under a full parent ------- *)
             iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x3c))
                       (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                       N4 (K - 10)%nat b
                       ltac:(vm_compute; reflexivity) ltac:(nz)
                       ltac:(rgne; rewrite HN4a5; exact (cr_tym1_eq _ Htdirg))
                       ltac:(rewrite Htg08e; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_03c with "Htext"). }
             iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg08e) in "Hpc".
             iDestruct "Hgate" as "[_ Hg2]".
             iSpecialize ("Hg2" $! CID25 with "[%]"); [wp_next_chain |].
             iApply ("Hg2" $! N4 with "[%] Hcg Hpc").
             { exact HN4regs. }
          ** (* ---- not a directory: the gate does not apply ---------- *)
             iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x3c))
                       (mword_of_int 41 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                       N4 (K - 10)%nat b
                       ltac:(vm_compute; reflexivity) ltac:(nz)
                       ltac:(rgne; rewrite HN4a5; exact (cr_tym1_ne _ Htdirg))
                       with "Hcg Hpc []").
             { iApply (cri_03c with "Htext"). }
             iIntros (CID25 Hq25) "Hcg Hpc".
             assert (Hp03e : add_vec_int (mword_of_int (CK + 0x3c) : mword 64) 2
                             = mword_of_int (CK + 0x3e)) by pcw.
             iEval (rewrite Hp03e) in "Hpc".
             iDestruct "Hgate" as "[Hj _]".
             iSpecialize ("Hj" $! CID25 with "[%]"); [wp_next_chain |].
             iApply ("Hj" $! N4 with "[%] [%] Hcg Hpc").
             { exact HN4regs. }
             { intros Hc. exfalso. exact (Htdirg Hc). }
        * (* ---- the count is below NLINK_MAX: jump the type test ----- *)
          iApply (wp_cbnez_taken_s_sconf (mword_of_int (CK + 0x36))
                    (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N3 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN3a5; exact (cr_nlmax_ne _ Hnlm))
                    ltac:(rewrite Htg03e; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_036 with "Htext"). }
          iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg03e) in "Hpc".
          iDestruct "Hgate" as "[Hj _]".
          iSpecialize ("Hj" $! CID23 with "[%]"); [wp_next_chain |].
          iApply ("Hj" $! N3 with "[%] [%] Hcg Hpc").
          { exact HN3regs. }
          { intros _. exact Hnlm. }
    - (* ============================================================== *)
      (*  ARM N: nameiparent returned 0                                  *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hnpa0 & Hisl2)".
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (CK + 0x22))
                (mword_of_int 318 : mword 13) Ra0 Q1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HQ1a0 Hnpa0;
                      apply (proj2 (eq_vec_true_iff _ _)); exact dlk_zero_moi)
                ltac:(rewrite Htg160; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_022 with "Htext"). }
      iIntros (CID16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg160) in "Hpc".
      assert (Hs1v : add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0)
                     = (mword_of_int 0 : mword 64))
        by (rewrite Hnpa0; apply add_vec_zero_l).
      assert (HQ1regs : cr_regs m sp0 (mword_of_int 0 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) ty major minor Q1)
        by exact (cr_regs_s1 m sp0 (m !!! Regidx Rs1 : mword 64)
                    (mword_of_int 0 : mword 64) (m !!! Regidx Rs2 : mword 64)
                    ty major minor mnp _ Hs1v Hmnpregs).
      (* +0x160 c.mv s2,a0 (a0 = 0) *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x160)) Rs2 Ra0 Q1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_160 with "Htext"). }
      iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (N1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0))]> Q1).
      change (<[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0))]> Q1) with N1.
      assert (HN1s2 : N1 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
      { rewrite /N1 upd_eq. rewrite HQ1a0 Hnpa0. apply add_vec_zero_l. }
      assert (Hs2v : add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0)
                     = (mword_of_int 0 : mword 64))
        by (rewrite HQ1a0 Hnpa0; apply add_vec_zero_l).
      assert (HN1regs : cr_regs m sp0 (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor N1)
        by exact (cr_regs_s2 m sp0 _ _ _ ty major minor Q1 _ Hs2v HQ1regs).
      assert (Hp162 : add_vec_int (mword_of_int (CK + 0x160) : mword 64) 2
                      = mword_of_int (CK + 0x162)) by pcw.
      iEval (rewrite Hp162) in "Hpc".
      (* +0x162 c.j +0x70 *)
      assert (Htg070n : add_vec (mword_of_int (CK + 0x162) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 1927 : mword 11) ('b"0"))))
                = mword_of_int (CK + 0x70)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CK + 0x162))
                (sign_extend' 21 (concat_vec (mword_of_int 1927 : mword 11) ('b"0")))
                N1 (K - 10)%nat b
                ltac:(rewrite Htg070n; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_162 with "Htext"). }
      iIntros (CID18 Hq18). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg070n) in "Hpc".
      iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
      iPoseProof ("Htail" $! CID18) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! N1 u5 nfj with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
      { exact (cr_tregs_of_regs m sp0 _ _ ty major minor N1 HN1regs). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDnp CIDf 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hisl2 Hislr") as "Hisl".
      iEval (rewrite -Hnsplit) in "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32)
                (MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
                          (replicate 13 (bv_0 32)))
                bm_empty n1 Sb1 ns
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [$Htx]").
      { exact Hcsf. }
      { exact (cr_slots_ns _ ns eq_refl Hns). }
      { split_and!; [exact Hsb1 | exact (proj2 Hnp1) | discriminate]. }
      { iPureIntro. rewrite Ha0f. exact HN1s2. }
  Qed.



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

  Lemma cr_alloc_half
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    (K_create <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= inodestart ->
    cov_below fsc_cov size ->
    bitmap_geom_ok fsc_cov fsc_logst bmapstart size ->
    InodeInv.ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    (* mkfs's own [ushort] geometry, carried as a premise rather than as a
       slot widening (D0-a, the eleventh stop's item-2 ruling): it is what
       makes the [lw a2,4(s3)] at +0xce agree with dirlink's ZERO-extended
       halfword argument. *)
    16 * Z.of_nat nib <= 2 ^ 16 ->
    bv_unsigned ty <> 0 ->
    (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) *)
    InodeRegion.ireg_ty_ok (ialloc_fresh ty) ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view fsc_fs γd dev fsc_cov) -∗
    log_ctx γ bn fsc_fs fsc_cov fsc_logst dev -∗
    kalloc_env γa None -∗
    is_itable2 gtl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv γi fsc_fs inodestart nib -∗
    (* RULING B (iclaim-ledger.md §3.2): the sealed regime, for the
       [create_fresh_ty] span's [jal ialloc].  Persistent, borrowed. *)
    ireg_open -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    (* ---- THE T_DIR SUB-BRANCH, PARKED (D0-b consumes it) ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8) (t : nat),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDm : CpuId =>
         cr_mkdir_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                       bmapstart inodestart nib ninodes size dev
                       plen pfun pv ty major minor V u Sb ns pidv
                       dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                       kd qd gd γil γisl dind dn bm data nf nsl t CIDm)) -∗
    (* ---- ARM FAIL's NON-DIRECTORY ENTRY, PARKED ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8) (t : nat),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
         cr_fail_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                      bmapstart inodestart nib ninodes size dev
                      plen pfun pv ty major minor V u Sb ns pidv
                      dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                      kd qd gd γil γisl dind dn bm data nf nsl t CIDf)) -∗
    (* THE CONCLUSION IS [wp_next]-WRAPPED, and it has to be.  The two parked
       bodies and [cr_alloc_body]'s own [Hcont] are all anchored at the
       SECTION hart, while the allocate half's resources arrive at whatever
       hart the [c.beqz] at +0x4c rebound to -- so the walk needs that hart's
       own chain link, which is exactly what [wp_next]'s guard is.  Stated at
       a bare [CIDa : CpuId] parameter the lemma is UNPROVABLE (nothing
       relates [CIDa] to [CID]), and this is also the shape [cr_found_half]
       takes its premise in, so the seal is one [iApply]. *)
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                    bmapstart inodestart nib ninodes size dev
                    plen pfun pv ty major minor V u Sb ns pidv dqb dqs dqbs dqn
                    m sp0 ret_tgt K eb b lks CIDa).
  Proof.
    intros HK Hdev Hnib Hglog Hist Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
           Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Htynz Htyk Hpkc Hu Hns Hj Hgs
           Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpk #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl #Hesc
             #Hslks #Hiregi #Hiopen #Hprocs #Hdevi #Hgeom #Hdlk Hmk Hfl".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDa Hsa).
    iIntros (Ma w5 kd qd gd γil γisl dind dn bm data nf nsl n1 Sb1 w t).
    iIntros "%HAregs %Hkdlt %Hdib %Htydir %Hnl0 %Hnlmax %Hiok %Hdok %Hddix %Hduq %Hrl %Hnpname
             %Hnone %Hsb1 %Hwmem %Hnp1".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Hdview Hfview Htop #Hshotl Hfrzl Hkeep Hrud
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hpriv Hpath Hbsl Hisl Hop Htx Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE.  create's contract carries no
       order premise because it does not need one: it is a level-0 contract,
       and [cpu_own_size_le] forces [lks = ∅] there.  Keep the EQUATION rather
       than substituting -- [lks] is spelled by name in every body below --
       and let [lkbelow] close each callee's bound from it. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HAregs as HAr.
    destruct HAr as (A2 & A8 & A9 & A18 & A20 & A21 & A22 & Athr).
    (* the ledger row [CreateBudget.cr_budget_found_w] is stated at *)
    assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
    assert (Hn1u : (n1 <= u)%nat) by exact (proj2 Hnp1).
    destruct n1 as [| q1]; [exfalso; lia |].
    assert (Hq1 : (8 <= q1)%nat) by lia.
    assert (Hn1ip : (iput_units <= S q1)%nat) by exact (cr_ip_of9 _ Hn1lo).
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    iDestruct (cr_esc_acc γi kd Hkdlt with "Hesc") as "#Hescd".
    (* ===== +0xa2 c.sdsp s3,40(sp) : THE EIGHTH SAVE ================== *)
    assert (HAs3 : (Ma !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (Athr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                     ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (Hf5 : add_vec (Ma !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite A2; apply cr_frm5).
    iEval (rewrite -Hf5) in "Hb5".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0xa2)) (mword_of_int 5 : mword 6)
              Rs3 Ma (K - 10)%nat w5 b with "Hcg Hpc [] Hb5").
    { iApply (cri_0a2 with "Htext"). }
    iIntros (CIDA1 HqA1) "Hcg Hpc Hb5".
    iEval (rgne; rewrite HAs3 Hf5) in "Hb5".
    assert (Hq0a4 : add_vec_int (mword_of_int (CK + 0xa2) : mword 64) 2
                    = mword_of_int (CK + 0xa4)) by pcw.
    iEval (rewrite Hq0a4) in "Hpc".
    (* ---- the ledger, split for the gate ---- *)
    assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat) by exact (cr_ns_1 ns Hns).
    iEval (rewrite -Hns1 iref_slots_op) in "Hisl".
    iDestruct "Hisl" as "[Hisl1 Hislr]".
    iDestruct (proc_priv_bare_acc γf (proc_addr j) pidv V with "Hpriv")
      as "[Hppid Hppback]".
    iDestruct (cpu_own_transport CIDa CIDA1 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE PARENT'S ARM SHRINKS BEFORE THE SPAN (durable-disk B''-tx3): the
       child's checkout is what parks the quarter, and the span's [ilock] is
       the checkout, so the quarter has to be in hand on the way IN.  On the
       ALLOC arm it comes back inside the child's deposit; on the FAIL arm,
       bare, and the parent's arm grows back to a half. *)
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
            t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htp)".
    iModIntro.
    (* THE CLAIM BOX'S SHARE (durable-disk C-5).  The span's [ialloc] leaves
       a claim box standing until its own [ilock] fills it, and what proves
       that window is inside a transaction is a POSITIVE share of this one
       parked in the region.  It cannot be the quarter the child's checkout
       parks -- the fill parks that at the same instant the claim returns
       this one -- so create lends a second quarter out of its own residue
       and takes it back on BOTH arms of the span. *)
    iEval (rewrite Hglog) in "Htx".
    iDestruct (log_tx_split icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htx") as "[Htcl Htx]".
    (* ===== +0xa4 .. +0xb0 : THE FRESH-TYPE GATE SPAN ================= *)
    iApply (create_fresh_ty γs j γl γu γd γk pd pav pu bn γ γi gtl
              γpr inodestart ninodes nib dev ty kd (DfracOwn (1/2))
              q1 Sb1 t (1/4)%Qp (1/4)%Qp
              pidv (DfracOwn (1/4)) dqs dqn Ma (K - 10)%nat eb b lks V
              ltac:(exact HKia) ltac:(exact HKil) Hlg Hist0 Hiregb Hni1 Hni2
              Hni3 Htynz Htyk Hpkc Hj Hgs Hroot A20 A9 Hkdlt Heb ltac:(lkbelow)
              (fun CIDx : CpuId => IA.wp_ialloc_gen (CID := CIDx))
              (fun CIDx : CpuId => IL.wp_ilock_dep_sconf (CID := CIDx))
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hitb2 Hitbl
                    Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk Hsbn Hsbi
                    Hppid Hbsl Hisl1 Hidev Htp Htcl Hop").
    all: try lkbelow.
    iIntros (CIDo Hso Mo alloc kslot q g cinum gil gisl dnc bmc)
      "%Hcs3 Hcg Hcnt Hsbn Hsbi Hppid Hbsl Hidev Hres".
    destruct alloc.
    - (* ============================================================== *)
      (*  THE INODE WAS CLAIMED, LOCKED AND FILLED -- control at +0xb4   *)
      (* ============================================================== *)
      (* [Hcfrz] is A-prime's token, relayed out of the span (which ends at
         [ilock]'s return, and [SpecIlock]'s post now hands it over).  It is
         what pays the freeze pin at the +0xc4 [ip->nlink = 1] below, where
         the pure arm is FALSE. *)
      iDestruct "Hres" as "(%Hpure & Hpc & #Hslkc & Hcslkd & Hcdep &
                            Hcidev & Hciinum & Hcivalid & Hcload & #Hcshot &
                            Hcfrz & Hckeep & Hruc & Htcl & Hop)".
      (* the claim box's quarter is home (durable-disk C-5) *)
      iDestruct (log_tx_join_q icfg_log t (1/2) (1/4) (1/4)
                   (eq_sym Qp.quarter_quarter) with "Htcl Htx") as "Htx".
      iEval (rewrite -Hglog) in "Htx".
      destruct Hpure as (Hs3 & Hkslt & Hcpos & Hcinb & Htyc & Hfresh).
      destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor Ma Mo Hcs3 Hs3 HAregs).
      pose proof HMoregs as HMoR.
      destruct HMoR as (M2 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & Mthr).
      iDestruct (ic_loaded_open with "Hcload") as (datc)
        "(%Hciok & %Hrl_datc & %Hcdok & %Hcddix & %Hcdoc & %Hcduq & Hcdlnk & Hcdiat
          & Hcmeta & Hcaddrs & Hcind & Hcblocks & Hcdview & Hcfview & Hctop)".
      (* the child's record acquires [cr_setf]'s four fields below and NONE
         of them is [di_size], so its contents value never moves; convert the
         hold once, here (namei-pinned-lookup.md §9 W3). *)
      iDestruct (dv_ride_size (bv_unsigned cinum) dnc
                   (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc
                   (eq_sym (cr_setf_size dnc major minor
                              (mword_of_int 1 : mword 16)))
                  with "Hcdview") as "Hcdview".
      iDestruct (fv_ride_size (bv_unsigned cinum) dnc
                   (cr_setf dnc major minor (mword_of_int 1 : mword 16)) datc
                   (eq_sym (cr_setf_size dnc major minor
                              (mword_of_int 1 : mword 16)))
                  with "Hcfview") as "Hcfview".
      (* ...and the ERA's abstract value moves with the record, once, here:
         [cr_setf] rewrites four fields and no block, so the node's blkmap
         and data columns are untouched (durable-disk 2b-inode-3).

         AND THIS IS WHERE THE CHILD'S ROW IS SUSPENDED (durable-disk lane A,
         plan section 4b).  The record this store flushes carries
         [nlink = 1], and on the mkdir arm the child is a DIRECTORY whose two
         dot entries are still three calls away: that node is not
         well-formed, and it is the ONE mid-transaction state this kernel
         actually produces.  So create hands the registry its transaction
         token here and takes back the receipt; every arm below gives the
         token back at the point the child is well-formed again -- the dots
         on the mkdir arm, the [nlink = 0] flush on the two failing ones.
         The FILE arm disarms immediately (its child is well-formed the
         moment the count lands), which is why nothing outside create ever
         sees a suspended row on that path. *)
      (* BOTH INODES ARE WRITE-LOCKED NOW (durable-disk B''-tx2): the
         parent's arm shrank to a quarter before the span and the child's
         CHECKOUT parked what came back (B''-tx3), so the half that is left
         is what the registry's arm below parks.  Quarter + quarter + half =
         the whole element. *)
      iDestruct (cr_esc_acc γi kslot Hkslt with "Hesc")
        as "#Hescc".
      iEval (rewrite Hglog) in "Htx".
      iApply fupd_wp.
      iMod (cr_dirty_arm ⊤ t (bv_unsigned cinum)
              (era_node dnc bmc datc)
              (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                        bmc datc)
              ltac:(solve_ndisj) with "[] Htx Hctop")
        as "[Hdirty Hctop]";
        [iApply (ireg_inv_ftop with "Hiregi") |].
      iModIntro.
      iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
      iEval (rewrite /i_major) in "Hcimaj".
      iEval (rewrite /i_minor) in "Hcimin".
      iEval (rewrite /i_nlink) in "Hcinl".
      (* ===== +0xb4 sh s5,70(s3) : ip->major = major ================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xb4)) Rs5 Rs3
                (mword_of_int 70 : mword 12) Mo (K - 10)%nat (di_major dnc) b
                with "Hcg Hpc [] [Hcimaj]").
      { iApply (cri_0b4 with "Htext"). }
      { iEval (rgne; rewrite M19). iExact "Hcimaj". }
      iIntros (CIDB1 HqB1) "Hcg Hpc Hcimaj".
      iEval (rgne; rgne; rewrite M19 M21 trunc16_sext64) in "Hcimaj".
      assert (Hq0b8 : add_vec_int (mword_of_int (CK + 0xb4) : mword 64) 4
                      = mword_of_int (CK + 0xb8)) by pcw.
      iEval (rewrite Hq0b8) in "Hpc".
      (* ===== +0xb8 sh s6,72(s3) : ip->minor = minor ================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xb8)) Rs6 Rs3
                (mword_of_int 72 : mword 12) Mo (K - 10)%nat (di_minor dnc) b
                with "Hcg Hpc [] [Hcimin]").
      { iApply (cri_0b8 with "Htext"). }
      { iEval (rgne; rewrite M19). iExact "Hcimin". }
      iIntros (CIDB2 HqB2) "Hcg Hpc Hcimin".
      iEval (rgne; rgne; rewrite M19 M22 trunc16_sext64) in "Hcimin".
      assert (Hq0bc : add_vec_int (mword_of_int (CK + 0xb8) : mword 64) 4
                      = mword_of_int (CK + 0xbc)) by pcw.
      iEval (rewrite Hq0bc) in "Hpc".
      (* ===== +0xbc c.li a4,1 ======================================== *)
      iApply (wp_cli_s_sconf (mword_of_int (CK + 0xbc)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                Mo (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (cri_0bc with "Htext"). }
      iIntros (CIDB3 HqB3) "Hcg Hpc".
      pose (W1 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> Mo).
      change (<[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> Mo) with W1.
      assert (HW1a4 : W1 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
        by (rewrite /W1; apply upd_eq).
      assert (HW1s3 : W1 !!! Regidx Rs3 = ientry kslot)
        by (rewrite /W1 upd_ne; [exact M19 | nz]).
      assert (HW1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W1)
        by (rewrite /W1; apply cr_regs3_caller; [exact Hcsa4 | exact HMoregs]).
      assert (Hq0be : add_vec_int (mword_of_int (CK + 0xbc) : mword 64) 2
                      = mword_of_int (CK + 0xbe)) by pcw.
      iEval (rewrite Hq0be) in "Hpc".
      (* ===== +0xbe sh a4,74(s3) : ip->nlink = 1 ===================== *)
      iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xbe)) Ra4 Rs3
                (mword_of_int 74 : mword 12) W1 (K - 10)%nat (di_nlink dnc) b
                with "Hcg Hpc [] [Hcinl]").
      { iApply (cri_0be with "Htext"). }
      { iEval (rgne; rewrite HW1s3). iExact "Hcinl". }
      iIntros (CIDB4 HqB4) "Hcg Hpc Hcinl".
      iEval (rgne; rgne; rewrite HW1s3 HW1a4 cr_trunc16_one) in "Hcinl".
      assert (Hq0c2 : add_vec_int (mword_of_int (CK + 0xbe) : mword 64) 4
                      = mword_of_int (CK + 0xc2)) by pcw.
      iEval (rewrite Hq0c2) in "Hpc".
      (* the record the three stores leave *)
      iAssert (inode_meta (ientry kslot)
                 (cr_setf dnc major minor (mword_of_int 1 : mword 16)))
        with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmeta".
      { rewrite /inode_meta /cr_setf /=. rewrite /i_major /i_minor /i_nlink.
        iFrame. }
      iAssert (inode_map fsc_fs (ientry kslot) bmc)
        with "[Hcaddrs Hcind]" as "Hcmap".
      { rewrite /inode_map. iFrame. }
      (* ===== +0xc2 c.mv a0,s3 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xc2)) Ra0 Rs3 W1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0c2 with "Htext"). }
      iIntros (CIDB5 HqB5) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (W2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs3))]> W1).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs3))]> W1) with W2.
      assert (HW2a0 : W2 !!! Regidx Ra0 = ientry kslot).
      { rewrite /W2 upd_eq. rewrite HW1s3. apply add_vec_zero_l. }
      assert (HW2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W2)
        by (rewrite /W2; apply cr_regs3_caller; [exact Hcsa0 | exact HW1regs]).
      assert (Hq0c4 : add_vec_int (mword_of_int (CK + 0xc2) : mword 64) 2
                      = mword_of_int (CK + 0xc4)) by pcw.
      iEval (rewrite Hq0c4) in "Hpc".
      (* ===== +0xc4 jal iupdate : THE MINT ========================== *)
      assert (Htgiu : add_vec (mword_of_int (CK + 0xc4) : mword 64)
                (sign_extend' 64 (mword_of_int 2090198 : mword 21))
                = mword_of_int KernelSyms.iupdate) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xc4)) Rra
                (mword_of_int 2090198 : mword 21) W2 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0c4 with "Htext"). }
      iIntros (CIDB6 HqB6) "Hcg Hpc".
      iEval (rewrite Htgiu) in "Hpc".
      pose (W3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)]> W2).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)]> W2) with W3.
      assert (HW3ra : W3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)
        by (rewrite /W3; apply upd_eq).
      assert (HW3a0 : W3 !!! Regidx Ra0 = ientry kslot)
        by (rewrite /W3 upd_ne; [exact HW2a0 | nz]).
      assert (HW3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W3)
        by (rewrite /W3; apply cr_regs3_caller; [exact Hcsra | exact HW2regs]).
      (* the mint's arithmetic and its membership premise *)
      assert (Htyz : bv_unsigned (di_type dnc) <> 0) by exact (proj1 Hfresh).
      (* THE MINT'S TWO WALK-LEVEL FACTS (the reshaped premise, the twelfth
         stop).  [wp_iupdate_link] no longer takes the Z-level increment --
         no caller could prove it at an arbitrary count -- but the value
         the [sh] committed and the guard's own disequality.  At the FRESH
         child both are [fresh_shape]'s zero, so both are [vm_compute]. *)
      assert (Hcnl0 : di_nlink dnc = (mword_of_int 0 : mword 16)).
      { apply bv_eq. rewrite (fresh_shape_nlink dnc Hfresh).
        vm_compute. reflexivity. }
      assert (Hbump : di_nlink (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16))
                      = add_vec (di_nlink dnc : mword 16) (mword_of_int 1)).
      { rewrite cr_setf_nlink Hcnl0. apply bv_eq; vm_compute; reflexivity. }
      assert (Hgrd : di_nlink dnc <> (mword_of_int 32767 : mword 16)).
      { rewrite Hcnl0. intro Hc. apply (f_equal bv_unsigned) in Hc.
        vm_compute in Hc. discriminate. }
      assert (Hcadd : di_addrs (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16)) = bm_cells bmc)
        by (rewrite cr_setf_addrs; exact (proj1 (proj2 (proj2 Hciok)))).
      assert (Hcdirlen : length (bm_dir bmc) = NDIRECT)
        by exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc (proj1 Hciok)).
      destruct q1 as [| q2]; [exfalso; lia |].
      iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (cpu_own_transport CIDo CIDB6 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IU.wp_iupdate_link γs j γl γu γd γk pd pav pu bn γ γi
                inodestart nib dev (ientry kslot) cinum
                (cr_setf dnc major minor (mword_of_int 1 : mword 16)) dnc bmc
                q2 (Sb1 ∪ {[IBLOCK cinum inodestart]}) true
                (* pin = true: this site pays the TOKEN arm (§3.9) *) true
                (Some (cr_ity ty (bv_unsigned dind)))
                pidv
                (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                W3 (K - 10)%nat eb b lks
                V ltac:(exact HKiu)
                ltac:(intros _; exact (cr_in_union_sing Sb1 _))
                Hlg Hist0 Hcblk Hcblog Hcinb
                ltac:(exact (di_type_stable_eq _ _
                        (cr_setf_type dnc major minor _)))
                ltac:(exact (cr_setf_type_nz dnc major minor _ Htyz))

                (* THE FILL'S OWN PREMISE (lane G5): the claim box's
                   multiplicity is ZERO -- [fresh_shape_nlink]'s count --
                   so the value is free to be CHOSEN here, and the choice
                   is [TDir dp] at a directory (which is what lets [dp]'s
                   name record for the child assert "my target's parent is
                   me") and [TFile] otherwise. *)
                ltac:(exact (cr_fill_choice_ok ty major minor dnc dind
                               ltac:(rewrite Hcnl0; vm_compute; reflexivity)
                               Htyc))
                Hbump Hgrd
                (* ===== THE IIIc WALL, SITE 1 OF 2 -- PAID (RULING A-prime,
                   iclaim-ledger.md §3.9) =====================================
                   [SpecIupdate.wp_iupdate_link]'s freeze-pin premise is now
                   the two-armed
                     |_di_nlink dnc <> 0_| \/ ifreeze_off (bv_unsigned cinum),
                   and this site pays the RIGHT arm with [Hcfrz].  The LEFT
                   arm is FALSE here, not merely unavailable: this is
                   create's FRESH CHILD and [Hcnl0] -- read off
                   [fresh_shape_nlink] -- says its pre-count is exactly ZERO,
                   on BOTH the tagged mkdir arm and the plain file one
                   ([ip->nlink = 1] is a 0 -> 1 move either way).  No
                   record-level fact could ever have saved it (the B1/B2
                   debt, §0: a mid-free box and a fresh claim box are the
                   SAME record), which is why the supply had to be a LEDGER
                   COLUMN.  The token is BORROWED: it comes straight back in
                   the continuation below and travels on to the child's
                   iunlock. *)
                Hcadd Hcdirlen Hj Hgs HW3a0 Heb
                with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hcidev Hciinum
                      Hcmeta Hcmap Hsbi Hiregi Hcdiat [Hcfrz] Hppid Hprocs
                      Hdevi Hgeom Hdlk Hbs2 Hop").
      all: try lkbelow.
      { rewrite /InodeRegion.ireg_link_pin. iExact "Hcfrz". }
      all: try lkbelow.
      iIntros (CIDiu Hsiu miu)
        "%Hcsiu Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
         (%vfill & [%Hvok %Hvchoice] & Htoken) Hpin Hbs2 Hop".
      (* the FILL's value IS the one this site chose ([oty = Some _]) *)
      assert (Hvfill : vfill = cr_ity ty (bv_unsigned dind))
        by exact (Hvchoice _ eq_refl).
      subst vfill.
      (* ...and the pile is [cr_delta ty] wide: the claim box's count is
         zero, so [ireg_dot_delta] is TWO at a directory and ONE at a
         file. *)
      assert (Hdelta : InodeRegion.ireg_dot_delta (bv_unsigned (di_type dnc))
                         (bv_unsigned (di_nlink dnc)) = cr_delta ty).
      { rewrite /InodeRegion.ireg_dot_delta /cr_delta Htyc.
        assert (Hz : bv_unsigned (di_nlink dnc) = 0)
          by (rewrite Hcnl0; vm_compute; reflexivity).
        rewrite (bool_decide_eq_true_2 (bv_unsigned (di_nlink dnc) = 0) Hz)
          andb_true_r.
        assert (Hdty : InodeRegion.ireg_dir_ty
                       = bv_unsigned SpecDirlookup.T_DIR)
          by (vm_compute; reflexivity).
        rewrite Hdty.
        destruct (decide (ty = SpecDirlookup.T_DIR)) as [-> | Hne].
        - rewrite (bool_decide_eq_true_2 _ eq_refl) //.
        - rewrite (bool_decide_eq_false_2
                     (bv_unsigned ty = bv_unsigned SpecDirlookup.T_DIR)
                     ltac:(intros Hc; apply Hne; by apply bv_eq)) //. }
      iEval (rewrite Hdelta) in "Htoken".
      (* the pin premise came back, and at [pin = true] it IS the token
         ([InodeRegion.ireg_link_pin]'s own definition).  It goes home at the
         child's iunlock. *)
      iEval (rewrite /InodeRegion.ireg_link_pin) in "Hpin".
      iRename "Hpin" into "Hcfrz".
      assert (Hpciu : ret_pc (W3 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0xc8)) by (rewrite HW3ra; pcw).
      iEval (rewrite Hpciu) in "Hpc".
      assert (Hmiuregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                           (ientry kslot) ty major minor miu)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor W3 miu Hcsiu HW3regs).
      pose proof Hmiuregs as HmiuR.
      destruct HmiuR as (N2 & N8 & N9 & N18 & N19 & N20 & N21 & N22 & Nthr).
      iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
        [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
      (* ===== +0xc8 c.li a4,1 ====================================== *)
      iApply (wp_cli_s_sconf (mword_of_int (CK + 0xc8)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                miu (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (cri_0c8 with "Htext"). }
      iIntros (CIDB7 HqB7) "Hcg Hpc".
      pose (W4 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> miu).
      change (<[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> miu) with W4.
      assert (HW4a4 : W4 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
        by (rewrite /W4; apply upd_eq).
      assert (HW4s4 : W4 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64))
        by (rewrite /W4 upd_ne; [exact N20 | nz]).
      assert (HW4s3 : W4 !!! Regidx Rs3 = ientry kslot)
        by (rewrite /W4 upd_ne; [exact N19 | nz]).
      assert (HW4s1 : W4 !!! Regidx Rs1 = ientry kd)
        by (rewrite /W4 upd_ne; [exact N9 | nz]).
      assert (HW4s0 : W4 !!! Regidx Rs0 = sp0)
        by (rewrite /W4 upd_ne; [exact N8 | nz]).
      assert (HW4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor W4)
        by (rewrite /W4; apply cr_regs3_caller; [exact Hcsa4 | exact Hmiuregs]).
      assert (Hq0ca : add_vec_int (mword_of_int (CK + 0xc8) : mword 64) 2
                      = mword_of_int (CK + 0xca)) by pcw.
      iEval (rewrite Hq0ca) in "Hpc".
      assert (Htg0f8 : add_vec (mword_of_int (CK + 0xca) : mword 64)
                (sign_extend' 64 (mword_of_int 46 : mword 13))
                = mword_of_int (CK + 0xf8)) by pcw.
      destruct (decide (ty = SpecDirlookup.T_DIR)) as [Htdir | Htdir].
      + (* ============================================================ *)
        (*  +0xca TAKEN: the whole T_DIR sub-branch, PARKED.  The child's *)
        (*  fragment is UNDEPOSITED here -- +0xc4 minted it and this arm's *)
        (*  own [dirlink(dp,name)] at +0x12c is what spends it.            *)
        (* ============================================================ *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_eq ty Htdir))
                  ltac:(rewrite Htg0f8; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_0ca with "Htext"). }
        iIntros (CIDB8 HqB8). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg0f8) in "Hpc".
        iDestruct (cpu_own_transport CIDiu CIDB8 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the child's suspended row travels into the mkdir arm, which is
           where its dot entries land and the row comes back (lane A) *)
        iSpecialize ("Hmk" $! kd qd gd γil γisl dind dn bm data nf nsl t).
        iPoseProof ("Hmk" $! CIDB8) as "Hm".
        iSpecialize ("Hm" with "[%]"); [wp_next_chain |].
        iApply ("Hm" $! W4 kslot q g gil gisl cinum dnc bmc datc
                  (S q2) (Sb1 ∪ {[IBLOCK cinum inodestart]}
                          ∪ {[IBLOCK cinum inodestart]})
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hslkd Hslkdd Hdep Hidev Hiinum
                        Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview
                        Htop Hshotl Hfrzl Hkeep Hrud
                        Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
                        Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop Hcshot Hcfrz
                        Hckeep Hruc Htoken Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath
                        Hbsl Hislr Hop Hdirty Hcont").
        { exact HW4regs. }
        { exact Htdir. }
        { exact Hkdlt. }
        { exact Hdib. }
        { exact Htydir. }
        { exact Hnl0. }
        { exact (Hnlmax Htdir). }
        { exact Hiok. }
        { exact Hdok. }
        { exact Hddix. }
        { exact Hduq. }
        { exact Hrl. }
        { exact Hnpname. }
        { exact Hnone. }
        { exact Hkslt. }
        { exact Hcpos. }
        { exact Hcinb. }
        { exact Hfresh. }
        { exact Hrl_datc. }
        { exact Htyc. }
        { exact Hciok. }
        { rewrite Hnib. exact Hcdok. }
        { exact (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb1 (cr_sub_union_sing Sb1 _))
                   (cr_sub_union_sing _ _)). }
        { exact (cr_in_union_sing _ _). }
        { split; [lia | lia]. }
        (* THE CORRELATION, discharged where both halves are in hand. *)
        { destruct w.
          - left.
            exact (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                     (cr_sub_union_sing _ _) _ (Hwmem eq_refl)).
          - right.
            exact (cr_n3_lo u q2 false Hu (proj1 Hnp1) eq_refl). }
      + (* ============================================================ *)
        (*  +0xca FALLS THROUGH: the non-directory path                  *)
        (* ============================================================ *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_ne ty Htdir))
                  with "Hcg Hpc []").
        { iApply (cri_0ca with "Htext"). }
        iIntros (CIDB8 HqB8) "Hcg Hpc".
        assert (Htdirz : bv_unsigned (di_type dnc) <> T_DIR_z).
        { rewrite Htyc. intro Hc. apply Htdir.
          apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
        (* THE CHILD'S ROW COMES BACK AT ONCE ON THIS ARM (durable-disk lane
           A): a FILE or DEVICE record at [nlink = 1] is well-formed the
           moment the count lands -- only a DIRECTORY owes dot entries -- so
           the suspension the shared prologue took out is released here and
           the transaction token goes home.  Nothing outside create ever
           sees a suspended row on this path. *)
        assert (Hlocfile : inode_local (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                            bmc datc)).
        { apply (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst _ bmc
                   datc).
          - exact (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                     (mword_of_int 1 : mword 16) Hciok).
          - apply (cr_setf_rec_local dnc major minor
                     (mword_of_int 1 : mword 16) Hrl_datc).
            vm_compute. discriminate.
          - apply dir_uniq_not_dir. rewrite cr_setf_type. exact Htdirz.
          - apply dir_dots_ix_not_dir. rewrite cr_setf_type. exact Htdirz. }
        iApply fupd_wp.
        iMod (cr_dirty_clear ⊤ t (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc)
                (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc)
                ltac:(solve_ndisj) Hlocfile with "[] Hdirty Hctop")
          as "[Htx Hctop]";
          [iApply (ireg_inv_ftop with "Hiregi") |].
        iModIntro.
        assert (Hq0ce : add_vec_int (mword_of_int (CK + 0xca) : mword 64) 4
                        = mword_of_int (CK + 0xce)) by pcw.
        iEval (rewrite Hq0ce) in "Hpc".
        (* ===== +0xce lw a2,4(s3) : the child's inum ================ *)
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xce)) Ra2 Rs3
                  (mword_of_int 4 : mword 12) W4 (K - 10)%nat cinum b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
        { iApply (cri_0ce with "Htext"). }
        { iEval (rgne; rewrite HW4s3). iExact "Hciinum". }
        iIntros (CIDC1 HqC1) "Hcg Hpc Hciinum".
        iEval (rgne; rewrite HW4s3) in "Hciinum".
        pose (X1 := <[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> W4).
        change (<[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> W4) with X1.
        assert (HX1a2 : X1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X1; apply upd_eq).
        assert (HX1s0 : X1 !!! Regidx Rs0 = sp0)
          by (rewrite /X1 upd_ne; [exact HW4s0 | nz]).
        assert (HX1s1 : X1 !!! Regidx Rs1 = ientry kd)
          by (rewrite /X1 upd_ne; [exact HW4s1 | nz]).
        assert (HX1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X1)
          by (rewrite /X1; apply cr_regs3_caller; [exact Hcsa2 | exact HW4regs]).
        assert (Hq0d2 : add_vec_int (mword_of_int (CK + 0xce) : mword 64) 4
                        = mword_of_int (CK + 0xd2)) by pcw.
        iEval (rewrite Hq0d2) in "Hpc".
        (* ===== +0xd2 addi a1,s0,-80 : a1 = &name =================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0xd2)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) X1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_0d2 with "Htext"). }
        iIntros (CIDC2 HqC2) "Hcg Hpc".
        pose (X2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget X1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> X1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget X1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> X1) with X2.
        assert (HX2a1 : X2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /X2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HX1s0. apply cr_name_addr. }
        assert (HX2a2 : X2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X2 upd_ne; [exact HX1a2 | nz]).
        assert (HX2s1 : X2 !!! Regidx Rs1 = ientry kd)
          by (rewrite /X2 upd_ne; [exact HX1s1 | nz]).
        assert (HX2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X2)
          by (rewrite /X2; apply cr_regs3_caller; [exact Hcsa1 | exact HX1regs]).
        assert (Hq0d6 : add_vec_int (mword_of_int (CK + 0xd2) : mword 64) 4
                        = mword_of_int (CK + 0xd6)) by pcw.
        iEval (rewrite Hq0d6) in "Hpc".
        (* ===== +0xd6 c.mv a0,s1 : the PARENT ======================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xd6)) Ra0 Rs1 X2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_0d6 with "Htext"). }
        iIntros (CIDC3 HqC3) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (X3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (X2 !!! Regidx Rs1))]> X2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (X2 !!! Regidx Rs1))]> X2) with X3.
        assert (HX3a0 : X3 !!! Regidx Ra0 = ientry kd).
        { rewrite /X3 upd_eq. rewrite HX2s1. apply add_vec_zero_l. }
        assert (HX3a1 : X3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /X3 upd_ne; [exact HX2a1 | nz]).
        assert (HX3a2 : X3 !!! Regidx Ra2
                        = (sign_extend' 64 cinum : mword 64))
          by (rewrite /X3 upd_ne; [exact HX2a2 | nz]).
        assert (HX3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X3)
          by (rewrite /X3; apply cr_regs3_caller; [exact Hcsa0 | exact HX2regs]).
        assert (Hq0d8 : add_vec_int (mword_of_int (CK + 0xd6) : mword 64) 2
                        = mword_of_int (CK + 0xd8)) by pcw.
        iEval (rewrite Hq0d8) in "Hpc".
        (* ===== +0xd8 jal dirlink(dp, name, ip->inum) =============== *)
        (* THE HALFWORD BRIDGE: the [lw] sign-extends a 32-bit cell and
           dirlink's a2 premise is a ZERO-extended SIXTEEN-bit one.  The two
           agree below 2^16, and what bounds the inum there is the ruled
           premise [16 * nib <= 2^16]. *)
        assert (Hc16 : bv_unsigned cinum < 2 ^ 16) by lia.
        assert (Hcl16 : bv_unsigned (cr_low16 cinum) = bv_unsigned cinum)
          by exact (cr_low16_unsigned cinum Hc16).
        assert (Htgdlk : add_vec (mword_of_int (CK + 0xd8) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092376 : mword 21))
                  = mword_of_int KernelSyms.dirlink) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0xd8)) Rra
                  (mword_of_int 2092376 : mword 21) X3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_0d8 with "Htext"). }
        iIntros (CIDC4 HqC4) "Hcg Hpc".
        iEval (rewrite Htgdlk) in "Hpc".
        pose (X4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)]> X3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)]> X3) with X4.
        assert (HX4ra : X4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)
          by (rewrite /X4; apply upd_eq).
        assert (HX4a0 : X4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /X4 upd_ne; [exact HX3a0 | nz]).
        assert (HX4a1 : X4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /X4 upd_ne; [exact HX3a1 | nz]).
        assert (HX4a2 : X4 !!! Regidx Ra2
                        = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
        { rewrite /X4 upd_ne; [| nz]. rewrite HX3a2.
          exact (cr_a2_low16 cinum Hc16). }
        assert (HX4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                            (ientry kslot) ty major minor X4)
          by (rewrite /X4; apply cr_regs3_caller; [exact Hcsra | exact HX3regs]).
        (* dirlink's premises, off the parent's [inode_ok] and [dir_ok] *)
        assert (Hdz : bv_unsigned (di_type dn) = T_DIR_z)
          by (rewrite Htydir; vm_compute; reflexivity).
        assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bm) by exact (proj1 Hiok).
        assert (Hbmcov : bm_covers bm (bv_unsigned (di_size dn)))
          by exact (proj1 (proj2 Hiok)).
        assert (Hdaddr : di_addrs dn = bm_cells bm)
          by exact (proj1 (proj2 (proj2 Hiok))).
        assert (Hszcap : bv_unsigned (di_size dn)
                         <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
        assert (Hholes : blk_holes_zero bm data)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
        assert (Htynzd : bv_unsigned (di_type dn) <> 0)
          by exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
        assert (Hsized : inode_sized data)
          by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
        assert (Hsz31 : bv_unsigned (di_size dn) < 2 ^ 31)
          by (unfold MAXFILE, BSIZE in Hszcap; simpl in Hszcap; lia).
        assert (Hcl16b : bv_unsigned (cr_low16 cinum) < 16 * Z.of_nat nib)
          by (rewrite Hcl16; exact Hcinb).
        iEval (rewrite -HX4a1) in "Hnb14".
        iEval (rewrite /inode_map) in "Hmap".
        iDestruct "Hmap" as "[Haddrs Hind]".
        iAssert (inode_map fsc_fs (ientry kd) bm) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        assert (Hns2 : (1 + (ns - 3))%nat = (ns - 2)%nat)
          by exact (cr_ns_2 ns Hns).
        iEval (rewrite -Hns2 iref_slots_op) in "Hislr".
        iDestruct "Hislr" as "[Hislk Hislrr]".
        iDestruct (cpu_own_transport CIDiu CIDC4 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* dirlink borrows the LEDGER half alone (durable-disk 2b-inode-5);
           the counting RA's tokens stay in this walk's hand and the
           deposit below files the [+0xc4] mint's unit among them. *)
        (* dirlink's own [iput] may need a share (durable-disk B''-tx5); the
           FILE arm has the residue free, so it simply lends it. *)
        iEval (rewrite -Hglog) in "Htx".
        iApply (DLK.wp_dirlink_gen γs j γl γu γd γk pd pav pu bn γ γi
                  gtl γa γf γpr inodestart nib bmapstart size dev
                  (ientry kd) dind bm data dn dn nf (cr_low16 cinum)
                  (S q2) (Sb1 ∪ {[IBLOCK cinum inodestart]}
                          ∪ {[IBLOCK cinum inodestart]})
                  _ _
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1) dqs
                  dqb dqbs (DfracOwn (1/2))
                  X4 (K - 10)%nat eb b lks
                  V ltac:(exact HKdlk) Htydir Hbmcov Hszcap
                  ltac:(exact (Hdok Hdz))
                  (* THE RELAYED LICENCE (§7.5.6, row 5).  LEFT disjunct,
                     earned by the same [sysfile.c:269] guard the found half
                     fell through at +0x2a/+0x2e and froze into [Hnl0]. *)
                  ltac:(left; exact (cr_nl0z dn Hnl0))
                  ltac:(exact (cr_doc_of_live dn dn data eq_refl Hnl0))
                  ltac:(exact (di_type_stable_refl dn))
                  ltac:(exact (di_nlink_stable_refl dn Htynzd))
                  Hlg Hbmwf Hholes Hdaddr Hsz31 Hist0 Hdblk Hdblog Hdib
                  Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                  ltac:(exact (cr_alloc_dlneed (S q2) _ _ ltac:(lia)))
                  Hj Hgs HX4a0 HX4a2 Heb ltac:(lkbelow) Hglog
                  with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs Hsbb
                        Hbmr Hiregi Hiopen Hdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                        Hitb2 Hitbl Hesc Hslks Hislk Hdlnk Hop Htx").
        all: try lkbelow.
        iIntros (CIDdl Hsdl mdl found bm' data' dn' dn0' n' Sb' tot)
          "%Hcsdl Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs
           Hsbb Hdiat Hppid Hbsl Hislk Hdlnk %Hn' %Hsb' %Hdl16 %Hfd0 Hop Htx
           %Hcapp %Hsizedp %Harm".
        iEval (rewrite Hglog) in "Htx".
        (* the borrow comes back as the PAIR; open it here, because the
           deposit below files the [+0xc4] mint's unit among the home's
           entry units (durable-disk 2b-inode-5) *)
        iDestruct (dlinks_open with "Hdlnk")
          as "(%D & [%Hdok0 %Hxact0] & Hetk)".
        iEval (rewrite HX4a1) in "Hnb14".
        assert (Hpcdl : ret_pc (X4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0xdc)) by (rewrite HX4ra; pcw).
        iEval (rewrite Hpcdl) in "Hpc".
        assert (Hmdlregs : cr_regs3 m sp0 (ientry kd)
                             (mword_of_int 0 : mword 64) (ientry kslot)
                             ty major minor mdl)
          by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                      (ientry kslot) ty major minor X4 mdl Hcsdl HX4regs).
        assert (Htg146 : add_vec (mword_of_int (CK + 0xdc) : mword 64)
                  (sign_extend' 64 (mword_of_int 106 : mword 13))
                  = mword_of_int (CK + 0x146)) by pcw.
        destruct found.
        * (* dirlookup INSIDE dirlink found the name -- refuted by the
             found half's own [dir_first ... = None] *)
          exfalso. destruct Harm as (Hfst & _). exact (Hfst Hnone).
        * destruct Harm as (_ & Hwf' & Hholes' & Haddr' & Hsz31' &
                            Hcov' & Hdn' & Hdn0' & Htot16 & Hrng & Hbl).
          (* the append arm's two halves: the spend is UNGUARDED (it prices
             the failing append at the same credit-aware figure), the
             memberships are guarded by [0 < tot] and this walk never wants
             them -- the parent's next call is an [iunlockput], which reads
             the ledger only. *)
          destruct (Hdl16 eq_refl) as (Hspend & Hatom & Hmem).
          (* the re-park's arithmetic: the append slot is inside the file *)
          assert (Hk0le : (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))
                           <= dir_nrec (bv_unsigned (di_size dn)))%nat)
            by apply dir_slot_le.
          assert (Hsznn : 0 <= bv_unsigned (di_size dn))
            by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
          destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn)
            as [Hnr1 _].
          assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
            by (vm_compute; reflexivity).
          assert (Hnatle : (16 * dir_slot data
                              (dir_nrec (bv_unsigned (di_size dn))) + tot
                            <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat).
          { clear -Hk0le Htot16. lia. }
          assert (HzA : (Z.of_nat (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot)%nat
                         <= Z.of_nat (16 * dir_nrec
                              (bv_unsigned (di_size dn)) + 16)%nat)%Z)
            by (apply Nat2Z.inj_le; exact Hnatle).
          assert (HzB : Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)) + 16)%nat
                        = (Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)))%nat + 16)%Z)
            by (rewrite Nat2Z.inj_add; reflexivity).
          assert (Hoff32 : (Z.of_nat (16 * dir_slot data
                              (dir_nrec (bv_unsigned (di_size dn))) + tot)
                            < 2 ^ 32)%Z).
          { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z.
            (* [lia] is quadratic-ish in how much of the context it has to
               scan for arithmetic atoms, and this is a syscall-altitude
               proof -- hundreds of unrelated hyps.  The four facts just
               built above are the whole chain; drop the rest first
               (durable-notes.md's "clear - H1 H2; lia" recipe). *)
            clear -Hnatle HzA HzB Hszcap Hnr1. lia. }
          assert (Hszmax : bv_unsigned (di_size dn')
                    = Z.max (bv_unsigned (di_size dn))
                        (Z.of_nat (16 * dir_slot data
                           (dir_nrec (bv_unsigned (di_size dn))) + tot)))
            by (rewrite Hdn'; exact (cr_wi_size_max dn bm' _ tot Hoff32)).
          assert (Hty' : di_type dn' = di_type dn) by (rewrite Hdn'; reflexivity).
          assert (Hnl' : di_nlink dn' = di_nlink dn)
            by (rewrite Hdn'; reflexivity).
          (* the branchless a0, which is what the [bltz] at +0xdc reads *)
          destruct Hbl as [[Ha0z Ht16] | [Ha0m Htlt]].
          -- (* ======================================================== *)
             (*  ARM C-OK-FILE: all sixteen bytes went in                 *)
             (* ======================================================== *)
             (* THE PARENT'S INODE BLOCK IS LOGGED ON THIS ARM, and that is
                what buys [cru := true] at the [iunlockput(dp)] below: the
                append went in whole, so [dl16_post]'s membership trio fires
                (it is guarded on [0 < tot], and the FAIL arms are exactly
                the ones that cannot have it).  With [cru] the put's spend is
                its bitmap report alone, and [cr_alloc_ip4]'s FOUR then
                leaves [iput_units] behind it -- the floor create's
                [ok = true] post now owes. *)
             assert (Ht0lt : (0 < tot)%nat) by (clear -Ht16; lia).
             assert (Hmemu : IBLOCK dind inodestart ∈ Sb')
               by exact (proj1 (proj2 (Hmem Ht0lt))).
             assert (Hcruu : true = true -> IBLOCK dind inodestart ∈ Sb')
               by (intros _; exact Hmemu).
             (* ===== +0xdc bltz a0 : FALLS THROUGH ================== *)
             iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0z; exact cr_bltz_zero)
                       with "Hcg Hpc []").
             { iApply (cri_0dc with "Htext"). }
             iIntros (CIDD1 HqD1) "Hcg Hpc".
             assert (Hq0e0 : add_vec_int (mword_of_int (CK + 0xdc) : mword 64) 4
                             = mword_of_int (CK + 0xe0)) by pcw.
             iEval (rewrite Hq0e0) in "Hpc".
             (* THE PARENT'S RE-PARK (durable-disk 2b-inode-5): the unit the
                [ip->nlink = 1] flush minted goes in at the NAME the
                appended record now carries. *)
             (* the two facts the marker set owes at this append: the name
                is not an entry yet (so it is not marked), and it is not a
                dot name ([DirView.dir_dots_miss_not_dots]). *)
             destruct (dir_dots_miss_not_dots (bv_unsigned dind) dn data
                         (bname 14 nf)
                         ltac:(rewrite Htydir; vm_compute; reflexivity)
                         (cr_nl0z dn Hnl0) Hddix Hnone) as [Hnfd Hnfdd].
             assert (Hnfd' : bname 14 nf <> DOT)
               by (rewrite FsStateEra.DOT_dot; exact Hnfd).
             assert (Hnfdd' : bname 14 nf <> DOTDOT)
               by (rewrite FsStateEra.DOTDOT_dotdot; exact Hnfdd).
             assert (HsD : bname 14 nf ∉ D).
             { intros Hin. destruct (Hdok0 _ Hin) as ([tt Htt] & _ & _).
               rewrite (dir_entries_era_node dn bm data Hholes Hszcap)
                 (bool_decide_eq_true_2 _ Hdz)
                 (proj2 (dir_view_lookup_None data _ (bname 14 nf)) Hnone)
                 in Htt. discriminate. }
             iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned dind)
                          dn dn' bm bm' data data'
                          (cr_low16 cinum) (bname 14 nf)
                          (dir_nrec (bv_unsigned (di_size dn)))
                          (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                          tot D false eq_refl eq_refl Hatom
                          (bname_length_le 14 nf) (cut_nul_nonul _)
                          Hdz Hty' Hnl' Hszmax Hrng Hnone
                          Hholes Hholes' Hszcap (Hcapp Hszcap) HsD Hnfdd'
                          with "Hetk [Htoken]") as "Hetk".
             { iEval (rewrite -Hcl16) in "Htoken".
               rewrite (cr_delta_file ty Htdir) FsStateLink.link_reps_1.
               iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned dind)
                         (fn_dd (era_node dn bm data))
                         (fn_orphan (era_node dn bm data)) false
                         (bname 14 nf) (bv_unsigned (cr_low16 cinum))
                         (cr_ity ty (bv_unsigned dind))
                         ltac:(apply FsStateInode.ent_ty_ok_name;
                               [exact Hnfd' | exact Hnfdd' |
                                exact (cr_ity_file ty (bv_unsigned dind) Htdir)])
                         with "Htoken"). }
             assert (Hgrow := dir_entries_dirlink_grow dn dn' bm bm' data data'
                        (cr_low16 cinum) (bname 14 nf)
                        (dir_nrec (bv_unsigned (di_size dn)))
                        (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                        tot eq_refl eq_refl Hatom
                        (bname_length_le 14 nf) (cut_nul_nonul _)
                        Hdz Hty' Hszmax Hrng Hnone
                        Hholes Hholes' Hszcap (Hcapp Hszcap)).
             assert (Hisdir' : fn_is_dir (era_node dn' bm' data')
                               = fn_is_dir (era_node dn bm data))
               by (rewrite /fn_is_dir /fn_type !era_node_rec Hty' //).
             assert (Hnleq : fn_nlink (era_node dn' bm' data')
                             = fn_nlink (era_node dn bm data))
               by (rewrite /fn_nlink !era_node_rec Hnl' //).
             iDestruct (dlinks_intro _ _ _ _ _ D
                          ltac:(exact (FsStateInode.ent_dset_ok_grow _ _ D
                                         Hgrow Hdok0))
                          ltac:(exact (FsStateInode.node_exact_cong _ _ D
                                         Hisdir' Hnleq Hxact0))
                          with "Hetk") as "Hdlnk".
             assert (Hiok' : inode_ok fsc_cov fsc_logst dn' bm' data').
             { rewrite /inode_ok. split_and!.
               - exact Hwf'.
               - exact Hcov'.
               - exact Haddr'.
               - rewrite Hty'. exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
               - exact (Hcapp Hszcap).
               - exact Hholes'.
               - exact (Hsizedp Hsized). }
             assert (Hdok' : dir_ok nib dn' data')
               by exact (dir_ok_dirlink nib dn dn' data data' (cr_low16 cinum)
                           (bname 14 nf) _ _ tot eq_refl eq_refl Htot16
                           Hcl16b Hty' Hszmax Hrng Hdok).
             (* ...and the dot records across the same write: the window is
                [dir_slot], which the clause's own liveness at 0 and 1 keeps
                away from both, and the count rides on [Hszmax]. *)
             assert (Hszle : bv_unsigned (di_size dn)
                             <= bv_unsigned (di_size dn'))
               by (clear -Hszmax; rewrite Hszmax; lia).
             assert (Hddix' : dir_dots_ix (bv_unsigned dind) dn' data')
               by exact (dir_dots_ix_dirlink (bv_unsigned dind) dn dn'
                           data data' (cr_low16 cinum) (bname 14 nf) _ _ tot
                           eq_refl eq_refl Htot16 Hty' Hnl' Hszle Hrng Hddix).
             (* ...and the UNIQUENESS clause across the same write: the
                atomicity ([Htot16], off dirlink's own relay) and the append
                guard [Hnone] are what pay for it. *)
             assert (Hduq' : dir_uniq dn' data')
               by exact (dir_uniq_dirlink dn dn' data data'
                           (cr_low16 cinum) (bname 14 nf) _ _ tot
                           eq_refl eq_refl Hatom
                           (bname_length_le 14 nf) (cut_nul_nonul _)
                           Hty' Hszmax Hrng Hnone Hduq).
             (* NOT [ic_mk_loaded]: [Hdiat]/[Hmeta] are stated at [dn0'], one
                rewrite short of the goal's [dn'], so the assembly stays
                inline here.  Only the tail -- [inode_addrs]/[ind_res]/
                [inode_blocks], the 268-element big-op -- is closed by name
                instead of [iFrame]. *)
             (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row) *)
             iApply fupd_wp.
             iMod (dvw_set_rt ⊤ γi fsc_fs inodestart nib
                     (bv_unsigned dind) (dv_of dn data) (dv_of dn' data')
                     (fv_of dn data) (fv_of dn' data')
                     ltac:(solve_ndisj) with "Hiregi Hdview Hfview")
               as "[Hdview Hfview]".
             iModIntro.
             (* THE THREE RECORD-ONLY FACTS AT THE APPENDED PARENT
                (durable-disk 2b-inode-3): dirlink keeps the TYPE and the
                COUNT, and it grows the size to a MAX of two multiples of
                sixteen -- the old size (a directory's, by the incoming
                clause) and one whole record past a slot. *)
             assert (Hrl' : inode_rec_local dn').
             { apply (inode_rec_local_same_type dn dn' Hrl Hty').
               - rewrite Hnl'. exact (proj1 (proj2 Hrl)).
               - intros _. rewrite Hszmax. apply cr_max_div16.
                 + apply (proj2 (proj2 Hrl)).
                   rewrite Htydir. vm_compute. reflexivity.
                 + exists (Z.of_nat (dir_slot data
                             (dir_nrec (bv_unsigned (di_size dn)))) + 1)%Z.
                   rewrite Ht16 Nat2Z.inj_add Nat2Z.inj_mul. lia. }
             (* ...AND THE ERA'S ABSTRACT VALUE IS RETAGGED: dirlink MOVED
                the parent's record and its bytes, and
                [InodeRegion.ireg_top_retag] opens [ftopN] alone. *)
             iApply fupd_wp.
             (* THE RETAG OWES THE ROW (durable-disk lane A): an appended
                entry leaves the parent well-formed, and these are the four
                facts the re-pack below proves anyway. *)
             iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
                     (era_node dn bm data) (era_node dn' bm' data')
                     ltac:(solve_ndisj)
                     (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst
                        dn' bm' data' Hiok' Hrl' Hduq' Hddix')
                     with "[] Htop") as "Htop";
               [iApply (ireg_inv_ftop with "Hiregi") |].
             iModIntro.
             iAssert (ic_loaded fsc_fs γi fsc_cov fsc_logst kd dind dn' bm')
               with "[Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop]"
               as "Hload".
             { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists data'.
               iSplitR; [iPureIntro; exact Hiok' |].
               iSplitR; [iPureIntro; exact Hrl' |].
               iSplitR; [iPureIntro; rewrite -Hnib; exact Hdok' |].
               iSplitR; [iPureIntro; exact Hddix' |].
               iSplitR; [iPureIntro;
                         exact (cr_doc_of_live dn dn' data' Hnl' Hnl0) |].
               iSplitR; [iPureIntro; exact Hduq' |].
               iSplitL "Hdlnk"; [iExact "Hdlnk" |].
               rewrite (Hdn0' eq_refl). iFrame "Hdiat Hmeta".
               iEval (rewrite /inode_map) in "Hmap".
               iDestruct "Hmap" as "[Haddrs Hind]".
               iSplitL "Haddrs"; [iExact "Haddrs" |].
               iSplitL "Hind"; [iExact "Hind" |].
               iSplitL "Hblocks"; [iExact "Hblocks" |].
               iSplitL "Hdview"; [iExact "Hdview" |].
               iSplitL "Hfview"; [iExact "Hfview" | iExact "Htop"]. }
             (* ===== +0xe0 c.mv a0,s1 ============================== *)
             iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe0)) Ra0 Rs1 mdl
                       (K - 10)%nat b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_0e0 with "Htext"). }
             iIntros (CIDD2 HqD2) "Hcg Hpc". iEval (rgne) in "Hcg".
             pose (Y1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mdl !!! Regidx Rs1))]> mdl).
             change (<[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mdl !!! Regidx Rs1))]> mdl) with Y1.
             assert (HY1a0 : Y1 !!! Regidx Ra0 = ientry kd).
             { rewrite /Y1 upd_eq.
               destruct Hmdlregs as (_ & _ & Hd9 & _). rewrite Hd9.
               apply add_vec_zero_l. }
             assert (HY1regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor Y1)
               by (rewrite /Y1; apply cr_regs3_caller;
                   [exact Hcsa0 | exact Hmdlregs]).
             assert (Hq0e2 : add_vec_int (mword_of_int (CK + 0xe0) : mword 64) 2
                             = mword_of_int (CK + 0xe2)) by pcw.
             iEval (rewrite Hq0e2) in "Hpc".
             (* ===== +0xe2 jal iunlockput(dp) ====================== *)
             assert (Htgu2 : add_vec (mword_of_int (CK + 0xe2) : mword 64)
                       (sign_extend' 64 (mword_of_int 2090944 : mword 21))
                       = mword_of_int KernelSyms.iunlockput) by pcw.
             iApply (wp_jal_s_sconf (mword_of_int (CK + 0xe2)) Rra
                       (mword_of_int 2090944 : mword 21) Y1 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0e2 with "Htext"). }
             iIntros (CIDD3 HqD3) "Hcg Hpc".
             iEval (rewrite Htgu2) in "Hpc".
             pose (Y2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]> Y1).
             change (<[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]> Y1) with Y2.
             assert (HY2ra : Y2 !!! Regidx Rra
                             = add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)
               by (rewrite /Y2; apply upd_eq).
             assert (HY2a0 : Y2 !!! Regidx Ra0 = ientry kd)
               by (rewrite /Y2 upd_ne; [exact HY1a0 | nz]).
             assert (HY2regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor Y2)
               by (rewrite /Y2; apply cr_regs3_caller;
                   [exact Hcsra | exact HY1regs]).
             assert (Hipn' : (iput_units <= n')%nat)
               by exact (cr_alloc_ip (S q2) n' _ _ _ _ _ ltac:(lia) Hspend).
             iDestruct (cpu_own_transport CIDdl CIDD3 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
                goes in and the share it parked comes back in the post, so no
                bundleless out-state stands across the call. *)
             iDestruct (log_opS_named with "Hop") as (e0) "Hop".
             iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
             iAssert (ity_shot gd (di_type dn')) as "#Hshotl'".
             { rewrite Hty'. iExact "Hshotl". }
             iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ
                       γi gtl γil γisl bmapstart inodestart nib
                       size dev kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/4)%Qp) dind dn' bm'
                       n' Sb' false true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                       Y2 (K - 10)%nat eb b lks
                       V ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) Hcruu
                       Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                       ltac:(exact Hipn') Hj Hgs HY2a0 ltac:(lkbelow) Hglog eq_refl
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                             Hitbl Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev
                             Hiinum Hivalid Hload Hshotl' Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr
                             Hppid Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             { iEval (cbn beta iota). iEmpIntro. }
             iIntros (CIDU2 HqU2 mu2 n2 Sb2 wf2)
               "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
                %Hsb2 %Hwf2 %Hwf2c %Hn2 Hop Hisl2 Htp".
             assert (Hpcu2 : ret_pc (Y2 !!! Regidx Rra : mword 64)
                             = mword_of_int (CK + 0xe6)) by (rewrite HY2ra; pcw).
             iEval (rewrite Hpcu2) in "Hpc".
             assert (Hmu2regs : cr_regs3 m sp0 (ientry kd)
                       (mword_of_int 0 : mword 64) (ientry kslot)
                       ty major minor mu2)
               by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                           (ientry kslot) ty major minor Y2 mu2 Hcsu2 HY2regs).
             iDestruct ("Hppback" with "Hppid") as "Hpriv".
             (* ===== +0xe6 c.mv s2,s3 : the ANSWER ================= *)
             iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe6)) Rs2 Rs3 mu2
                       (K - 10)%nat b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (cri_0e6 with "Htext"). }
             iIntros (CIDD4 HqD4) "Hcg Hpc". iEval (rgne) in "Hcg".
             assert (Hy2v : add_vec (zero_reg : mword 64) (mu2 !!! Regidx Rs3)
                            = ientry kslot).
             { destruct Hmu2regs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
               apply add_vec_zero_l. }
             pose (Y3 := <[Regidx Rs2 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mu2 !!! Regidx Rs3))]> mu2).
             change (<[Regidx Rs2 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mu2 !!! Regidx Rs3))]> mu2) with Y3.
             assert (HY3s2 : Y3 !!! Regidx Rs2 = ientry kslot)
               by (rewrite /Y3 upd_eq; exact Hy2v).
             assert (HY3regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                       (ientry kslot) ty major minor Y3)
               by exact (cr_regs3_s2 m sp0 (ientry kd)
                           (mword_of_int 0 : mword 64) (ientry kslot)
                           (ientry kslot) ty major minor mu2 _ Hy2v Hmu2regs).
             assert (Hq0e8 : add_vec_int (mword_of_int (CK + 0xe6) : mword 64) 2
                             = mword_of_int (CK + 0xe8)) by pcw.
             iEval (rewrite Hq0e8) in "Hpc".
             (* ===== +0xe8 c.ldsp s3,40(sp) : the LAZY RESTORE ===== *)
             assert (HY3sp : Y3 !!! Regidx csp_rs1 = pa_stk sp0 10)
               by (destruct HY3regs as (H2 & _); exact H2).
             assert (HT5 : add_vec (Y3 !!! Regidx csp_rs1)
                             (zero_extend' 64
                                (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                           = pa_stk sp0 5) by (rewrite HY3sp; apply cr_frm5).
             iEval (rewrite -HT5) in "Hb5".
             iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xe8))
                       (mword_of_int 5 : mword 6) Rs3 Y3 (K - 10)%nat
                       (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc [] Hb5").
             { iApply (cri_0e8 with "Htext"). }
             iIntros (CIDD5 HqD5) "Hcg Hpc Hb5".
             iEval (rewrite HT5) in "Hb5".
             pose (Y4 := <[Regidx Rs3 := regval_into_reg
                           (m !!! Regidx Rs3 : mword 64)]> Y3).
             change (<[Regidx Rs3 := regval_into_reg
                           (m !!! Regidx Rs3 : mword 64)]> Y3) with Y4.
             assert (HY4regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                       (m !!! Regidx Rs3 : mword 64) ty major minor Y4)
               by exact (cr_regs3_s3 m sp0 (ientry kd) (ientry kslot)
                           (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                           ty major minor Y3 _ eq_refl HY3regs).
             assert (HY4s2 : Y4 !!! Regidx Rs2 = ientry kslot)
               by (rewrite /Y4 upd_ne; [exact HY3s2 | nz]).
             assert (Hq0ea : add_vec_int (mword_of_int (CK + 0xe8) : mword 64) 2
                             = mword_of_int (CK + 0xea)) by pcw.
             iEval (rewrite Hq0ea) in "Hpc".
             (* ===== +0xea c.j +0x70 =============================== *)
             assert (Htg070c : add_vec (mword_of_int (CK + 0xea) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1987 : mword 11) ('b"0"))))
                       = mword_of_int (CK + 0x70)) by pcw.
             iApply (wp_cj_s_sconf (mword_of_int (CK + 0xea))
                       (sign_extend' 21
                          (concat_vec (mword_of_int 1987 : mword 11) ('b"0")))
                       Y4 (K - 10)%nat b
                       ltac:(rewrite Htg070c; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0ea with "Htext"). }
             iIntros (CIDD6 HqD6). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg070c) in "Hpc".
             iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
               as (nfj) "Hnb16".
             iPoseProof ("Htail" $! CIDD6) as "Ht".
             iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
             iApply ("Ht" $! Y4 (m !!! Regidx Rs3 : mword 64) nfj with
                       "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
             { exact (cr_tregs_of_regs3 m sp0 (ientry kd) (ientry kslot)
                        ty major minor Y4 HY4regs). }
             iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
             iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (iref_slots_combine with "Hislk Hisl2") as "Hisl".
             iDestruct (iref_slots_combine with "Hisl Hislrr") as "Hisl".
             iApply fupd_wp.
             iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kslot (q/2)%Qp dev cinum
                     g true t (1/2) (1/4) (1/4)
                     (eq_sym Qp.quarter_quarter) ltac:(solve_ndisj)
                     with "Hescc Hcivalid Hcdep Htp")
               as "(Hcivalid & Hcdep)".
             iModIntro.
             iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
             iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
             iApply ("Hcont" $! mf true true kslot (q/2)%Qp (q/2)%Qp g cinum
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc
                       n2 Sb2 (1 + (1 + (ns - 3)))%nat
                       with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                             Hpath Hbsl [%] Hisl [%] Hop [Hslkc Hcslkd
                             Hcdep Hcidev Hciinum Hcivalid Hcdlnk Hcdiat Hcmeta
                             Hcmap Hcblocks Hcdview Hcfview Hctop Hcfrz Hckeep Hruc]").
             { exact Hcsf. }
             { exact (cr_slots_3 _ ns eq_refl Hns). }
             { split_and!.
               - exact (cr_sub3 _ _ _ _ Hsb1
                          (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                             (cr_sub_union_sing _ _))
                          (cr_sub2 _ _ _ Hsb' Hsb2)).
               - pose proof (proj2 Hn2) as HB1. pose proof (proj2 Hn') as HB2.
                 (* optimization.md: [HB1]/[HB2] alone are not the whole
                    chain -- the goal [n2 <= u] needs the bridge from
                    [n' <= S q2] (HB2) back to [u] as well, which is
                    [Hn1u : S (S q2) <= u], threaded from the walk's own
                    budget call far above (found by a temporary
                    [idtac]-dump of the goal + full context at this site,
                    since the missing fact wasn't reachable by grepping
                    sibling call sites the way [dl_need]'s was). *)
                 clear -HB1 HB2 Hn1u. lia.
               - intros _.
                 exact (cr_fail_ip_left n' n2 wf2
                          (cr_alloc_ip4 (S q2) n' _ _ _ _ _ ltac:(lia) Hspend)
                          (proj1 Hn2)). }
             iSplitR.
             { iPureIntro. split; [rewrite Ha0f; exact HY4s2 |].
               split; [exact Hkslt |].
               split; [split; [exact (proj1 Hcpos) | exact Hcinb] |].
               split; [rewrite cr_setf_type; exact Htyc |].
               split; [reflexivity |].
               split; [reflexivity |].
               split; [rewrite cr_setf_nlink; vm_compute; reflexivity |].
               intros _. exact (cr_setf_fresh_made dnc ty major minor
                                  Hfresh Htyc). }
             (* the CHILD is not a directory on this arm, so its [dlinks]
                is [emp] at either dinode ([dlinks_not_dir]) and the
                flush's [nlink] bump is invisible to it. *)
             iAssert (dlinks fsc_fs (bv_unsigned cinum)
                        (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                        bmc datc)
               as "Hcdlnk1".
             { iApply (dlinks_not_dir fsc_fs (bv_unsigned cinum)
                         (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                         bmc datc).
               intros Hchdir. apply Htdirz.
               rewrite -(cr_setf_type dnc major minor
                           (mword_of_int 1 : mword 16)).
               exact Hchdir. }
             iDestruct "Hcmap" as "[Hca Hci]".
             iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum
                          (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                          bmc datc
                          (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                             _ Hciok)
                          (cr_setf_rec_local dnc major minor
                             (mword_of_int 1 : mword 16) Hrl_datc
                             cr_nl_short_1)
                          (cr_setf_dir_ok icfg_nib dnc datc major minor _ Hcdok)
                          (dir_dots_ix_not_dir (bv_unsigned cinum)
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          (dir_orphan_clean_not_dir
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          (dir_uniq_not_dir
                             (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                             datc ltac:(rewrite cr_setf_type; exact Htdirz))
                          with "Hcdlnk1 Hcdiat Hcmeta Hca Hci Hcblocks Hcdview Hcfview
                                Hctop")
               as "Hcload".
             iAssert (ity_shot g (di_type (cr_setf dnc major minor
                                             (mword_of_int 1 : mword 16))))
               as "Hcshot1".
             { rewrite cr_setf_type. iExact "Hcshot". }
             iApply (create_locked_mk γi
                       _ _ _ _ _ _ _ _ _ gil gisl
                       with "Hslkc Hcslkd Hcdep Hcidev Hciinum
                             Hcivalid Hcload Hcshot1 Hcfrz Hckeep Hruc").
          -- (* ======================================================== *)
             (*  ARM FAIL's non-directory entry: the append fell short    *)
             (* ======================================================== *)
             iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0m; exact cr_bltz_m1)
                       ltac:(rewrite Htg146; vm_compute; reflexivity)
                       with "Hcg Hpc []").
             { iApply (cri_0dc with "Htext"). }
             iIntros (CIDE1 HqE1). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg146) in "Hpc".
             iDestruct (cpu_own_transport CIDdl CIDE1 0%nat eb (proc_addr j) b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             (* THE FAILING APPEND'S TWO ROUTES, and ONE figure prices both.
                [tot < 16] admits zero (writei's own -1 return, the full
                directory), and since the [dl16_post] collapse the spend
                clause is unguarded, so this is the SAME reading the C-OK
                branch above makes -- no [tot]-split, no constant.
                [CreateBudget.cr_fail_closes_with_credit] is the theorem. *)
             assert (Hipn'' : (iput_units <= n')%nat)
               by exact (cr_alloc_ip (S q2) n' _ _ _ _ _ ltac:(lia) Hspend).
             (* dirlink's slot is NET ZERO, so the ledger is back at [ns - 2]
                -- the figure the parked fail arm is stated at. *)
             iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
             iEval (rewrite Hns2) in "Hislr".
             (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row): the
                append moved the parent's bytes even on the failing return,
                and [cr_fail_body] is stated at the POST record. *)
             iApply fupd_wp.
             iMod (dvw_set_rt ⊤ γi fsc_fs inodestart nib
                     (bv_unsigned dind) (dv_of dn data) (dv_of dn' data')
                     (fv_of dn data) (fv_of dn' data')
                     ltac:(solve_ndisj) with "Hiregi Hdview Hfview")
               as "[Hdview Hfview]".
             iModIntro.
             (* THE ERA'S ABSTRACT VALUE IS NOT MOVED HERE (durable-disk
                lane A): the retag owes the registry's row, and the failing
                append's post record is proved well-formed inside
                [cr_fail_half] -- which is where the move now happens. *)
             (* nothing was written, so the tokens ride and the [+0xc4]
                mint's unit travels on to the fail arm's [ip->nlink = 0]
                (durable-disk 2b-inode-5). *)
             iDestruct (dlinks_intro _ _ _ _ _ D Hdok0 Hxact0
                          with "Hetk") as "Hdlnk".
             iEval (rewrite -Hglog) in "Htx".
             iSpecialize ("Hfl" $! kd qd gd γil γisl dind dn bm data nf nsl t).
             iPoseProof ("Hfl" $! CIDE1) as "Hf".
             iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
             iApply ("Hf" $! mdl kslot q g gil gisl cinum dnc bmc datc
                       bm' data' dn' dn0' tot n' Sb'
                       with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                             Hnb14 Hnb2 Hslkd Hslkdd Hdep Hidev Hiinum
                             Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop Hshotl
                             Hfrzl Hkeep Hrud Hslkc Hcslkd Hcdep Hcidev
                             Hciinum Hcivalid Hcdlnk Hcdiat Hcmeta Hcmap
                             Hcblocks Hcdview Hcfview Hctop Hcshot Hcfrz Hckeep Hruc Htoken Hsbn Hsbi Hsbs Hsbb Hbmr
                             Hppid Hppback Hpath Hbsl Hislr Hop Htx Hcont").
             { exact Hmdlregs. }
             { exact Htdir. }
             { exact Hkdlt. }
             { exact Hdib. }
             { exact Htydir. }
             { exact Hnl0. }
             { exact Hiok. }
             { exact Hdok. }
             { exact Hddix. }
             { exact Hduq. }
             { exact Hrl. }
             { exact Hkslt. }
             { exact Hcpos. }
             { exact Hcinb. }
             { exact Hfresh. }
             { exact Hrl_datc. }
             { exact Htyc. }
             { exact Hciok. }
             { rewrite Hnib. exact Hcdok. }
             (* [tot < 16] AND dirlink's atomicity IS [tot = 0]: the shape
                the fail body's re-park needs. *)
             { destruct Hatom as [Hz | H16];
                 [exact Hz | exfalso; clear -H16 Htlt; lia]. }
             { exact Hwf'. }
             { exact Hholes'. }
             { exact Haddr'. }
             { exact Hsz31'. }
             { exact Hcov'. }
             { exact (Hcapp Hszcap). }
             { exact (Hsizedp Hsized). }
             { exact Hdn'. }
             { exact (Hdn0' eq_refl). }
             { exact Hrng. }
             { exact (cr_sub2 _ _ _
                        (cr_sub2 _ _ _ Hsb1
                           (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                              (cr_sub_union_sing _ _))) Hsb'). }
             { exact (Hsb' _ (cr_in_union_sing _ _)). }
             { split; [exact Hipn'' |].
               (* optimization.md: same bridge as the sibling bullet in
                  [cr_found_half] above -- [HB2 : n' <= S q2] needs
                  [Hn1u : S (S q2) <= u] to reach the goal [n' <= u]. *)
               pose proof (proj2 Hn') as HB2.
               clear -HB2 Hn1u. lia. }
             (* the LEFT disjunct, and this entry has it unconditionally:
                eight into the dirlink and [wi16_spend <= 4] out. *)
             { left.
               exact (cr_alloc_ip4 (S q2) n' _ _ _ _ _ ltac:(lia) Hspend). }
    - (* ============================================================== *)
      (*  ARM A-FAIL (+0xec): ialloc returned 0, nothing was claimed     *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hs3z & Hpc & Hislg & Htp & Htcl & Hop)".
      (* the claim box's quarter is home, unspent (durable-disk C-5) *)
      iDestruct (log_tx_join_q icfg_log t (1/2) (1/4) (1/4)
                   (eq_sym Qp.quarter_quarter) with "Htcl Htx") as "Htx".
      iEval (rewrite -Hglog) in "Htx".
      (* nothing was claimed, so no second lock was taken: the quarter goes
         straight back into the parent's arm (durable-disk B''-tx3). *)
      iApply fupd_wp.
      iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
              t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
              ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htp")
        as "(Hivalid & Hdep)".
      iModIntro.
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) ty major minor Ma Mo Hcs3 Hs3z
                    HAregs).
      (* ===== +0xec c.mv a0,s1 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xec)) Ra0 Rs1 Mo
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0ec with "Htext"). }
      iIntros (CIDF1 HqF1) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (Z1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mo !!! Regidx Rs1))]> Mo).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mo !!! Regidx Rs1))]> Mo) with Z1.
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = ientry kd).
      { rewrite /Z1 upd_eq.
        destruct HMoregs as (_ & _ & Hd9 & _). rewrite Hd9.
        apply add_vec_zero_l. }
      assert (HZ1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z1)
        by (rewrite /Z1; apply cr_regs3_caller; [exact Hcsa0 | exact HMoregs]).
      assert (Hq0ee : add_vec_int (mword_of_int (CK + 0xec) : mword 64) 2
                      = mword_of_int (CK + 0xee)) by pcw.
      iEval (rewrite Hq0ee) in "Hpc".
      (* ===== +0xee jal iunlockput(dp), UNCREDITED =================== *)
      assert (Htgu : add_vec (mword_of_int (CK + 0xee) : mword 64)
                (sign_extend' 64 (mword_of_int 2090932 : mword 21))
                = mword_of_int KernelSyms.iunlockput) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xee)) Rra
                (mword_of_int 2090932 : mword 21) Z1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0ee with "Htext"). }
      iIntros (CIDF2 HqF2) "Hcg Hpc".
      iEval (rewrite Htgu) in "Hpc".
      pose (Z2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)]> Z1).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)]> Z1) with Z2.
      assert (HZ2ra : Z2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)
        by (rewrite /Z2; apply upd_eq).
      assert (HZ2a0 : Z2 !!! Regidx Ra0 = ientry kd)
        by (rewrite /Z2 upd_ne; [exact HZ1a0 | nz]).
      assert (HZ2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z2)
        by (rewrite /Z2; apply cr_regs3_caller; [exact Hcsra | exact HZ1regs]).
      iEval (rewrite /inode_map) in "Hmap".
      iDestruct "Hmap" as "[Haddrs Hind]".
      assert (Hdok2 : dir_ok icfg_nib dn data) by (rewrite -Hnib; exact Hdok).
      pose proof Hddix as Hddix2.
      iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind dn bm data
                   Hiok Hrl Hdok2 Hddix2 (cr_doc_of_live dn dn data eq_refl Hnl0)
                   Hduq
                   with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview
                         Htop")
        as "Hload".
      iDestruct (cpu_own_transport CIDo CIDF2 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iEval (rewrite Hglog) in "Htx".
      (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
         goes in and the share it parked comes back in the post, so no
         bundleless out-state stands across the call. *)
      iDestruct (log_opS_named with "Hop") as (e0) "Hop".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
      iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
                gtl γil γisl bmapstart inodestart nib size dev
                kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/2)%Qp) dind dn bm (S q1) Sb1
                false false false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                Z2 (K - 10)%nat eb b lks
                V ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) ltac:(discriminate)
                Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                ltac:(exact Hn1ip) Hj Hgs HZ2a0 ltac:(lkbelow) Hglog eq_refl
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                      Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                      Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid
                      Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { iEval (cbn beta iota). iEmpIntro. }
      iIntros (CIDU HqU mu n2 Sb2 wf)
        "%Hcsu Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
         %Hsb2 %Hwf %Hwfc %Hn2 Hop Hisl Htp".
      iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                   (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
      iDestruct (log_tx_full with "Htw") as "Htx".
      iEval (rewrite -Hglog) in "Htx".
      assert (Hpcu : ret_pc (Z2 !!! Regidx Rra : mword 64)
                     = mword_of_int (CK + 0xf2)) by (rewrite HZ2ra; pcw).
      iEval (rewrite Hpcu) in "Hpc".
      assert (Hmuregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor mu)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) ty major minor Z2 mu Hcsu
                    HZ2regs).
      iDestruct ("Hppback" with "Hppid") as "Hpriv".
      (* ===== +0xf2 c.mv s2,s3 (s3 = 0) ============================= *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xf2)) Rs2 Rs3 mu
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_0f2 with "Htext"). }
      iIntros (CIDF3 HqF3) "Hcg Hpc". iEval (rgne) in "Hcg".
      assert (Hz2v : add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3)
                     = (mword_of_int 0 : mword 64)).
      { destruct Hmuregs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
        apply add_vec_zero_l. }
      pose (Z3 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3))]> mu).
      change (<[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3))]> mu) with Z3.
      assert (HZ3s2 : Z3 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
        by (rewrite /Z3 upd_eq; exact Hz2v).
      assert (HZ3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Z3)
        by exact (cr_regs3_s2 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) (mword_of_int 0 : mword 64)
                    ty major minor mu _ Hz2v Hmuregs).
      assert (Hq0f4 : add_vec_int (mword_of_int (CK + 0xf2) : mword 64) 2
                      = mword_of_int (CK + 0xf4)) by pcw.
      iEval (rewrite Hq0f4) in "Hpc".
      (* ===== +0xf4 c.ldsp s3,40(sp) ================================ *)
      assert (HZ3sp : Z3 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (destruct HZ3regs as (H2 & _); exact H2).
      assert (HT5 : add_vec (Z3 !!! Regidx csp_rs1)
                      (zero_extend' 64
                         (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HZ3sp; apply cr_frm5).
      iEval (rewrite -HT5) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xf4))
                (mword_of_int 5 : mword 6) Rs3 Z3 (K - 10)%nat
                (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] Hb5").
      { iApply (cri_0f4 with "Htext"). }
      iIntros (CIDF4 HqF4) "Hcg Hpc Hb5".
      iEval (rewrite HT5) in "Hb5".
      pose (Z4 := <[Regidx Rs3 := regval_into_reg
                    (m !!! Regidx Rs3 : mword 64)]> Z3).
      change (<[Regidx Rs3 := regval_into_reg
                    (m !!! Regidx Rs3 : mword 64)]> Z3) with Z4.
      assert (HZ4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) ty major minor Z4)
        by exact (cr_regs3_s3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) (m !!! Regidx Rs3 : mword 64)
                    ty major minor Z3 _ eq_refl HZ3regs).
      assert (HZ4s2 : Z4 !!! Regidx Rs2 = (mword_of_int 0 : mword 64))
        by (rewrite /Z4 upd_ne; [exact HZ3s2 | nz]).
      assert (Hq0f6 : add_vec_int (mword_of_int (CK + 0xf4) : mword 64) 2
                      = mword_of_int (CK + 0xf6)) by pcw.
      iEval (rewrite Hq0f6) in "Hpc".
      (* ===== +0xf6 c.j +0x70 ======================================= *)
      assert (Htg070a : add_vec (mword_of_int (CK + 0xf6) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 1981 : mword 11) ('b"0"))))
                = mword_of_int (CK + 0x70)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CK + 0xf6))
                (sign_extend' 21
                   (concat_vec (mword_of_int 1981 : mword 11) ('b"0")))
                Z4 (K - 10)%nat b
                ltac:(rewrite Htg070a; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_0f6 with "Htext"). }
      iIntros (CIDF5 HqF5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg070a) in "Hpc".
      iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
      iPoseProof ("Htail" $! CIDF5) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! Z4 (m !!! Regidx Rs3 : mword 64) nfj with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
      { exact (cr_tregs_of_regs3 m sp0 (ientry kd)
                 (mword_of_int 0 : mword 64) ty major minor Z4 HZ4regs). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDU CIDf 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hislg Hisl") as "Hisl".
      iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32) dn bm n2 Sb2
                (1 + (1 + (ns - 2)))%nat
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [$Htx]").
      { exact Hcsf. }
      { exact (cr_slots_2 _ ns eq_refl Hns). }
      { split_and!; [exact (cr_sub2 _ _ _ Hsb1 Hsb2)
                    | exact (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))
                    | discriminate]. }
      { iPureIntro. rewrite Ha0f. exact HZ4s2. }
  Qed.


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
  Lemma cr_fail_half
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat) :
    (K_create <= K)%nat ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    nib = icfg_nib ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= inodestart ->
    cov_below fsc_cov size ->
    InodeInv.ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗ panic_env -∗
    bio_ctx bn (fs_view fsc_fs γd dev fsc_cov) -∗
    log_ctx γ bn fsc_fs fsc_cov fsc_logst dev -∗
    is_itable2 gtl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
    ireg_inv γi fsc_fs inodestart nib -∗
    ireg_open -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
      cr_fail_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                   bmapstart inodestart nib ninodes size dev
                   plen pfun pv ty major minor V u Sb ns pidv
                   dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                   kd qd gd γil γisl dind dn bm data nf nsl t CIDf).
  Proof.
    intros HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcovb
           Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpenv #Hbio #Hlogc #Hitb2 #Hitbl #Hesc #Hiregi #Hiopen
             #Hprocs #Hdevi #Hgeom #Hdlk".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDf Hsf).
    iIntros (Mx kslot q g gil gisl cinum dnc bmc datc bm' data' dn' dn0'
             tot n4 Sb4).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hiok %Hdok %Hddix %Hduq %Hrl %Hkslt
             %Hcpos %Hcinb %Hfresh %Hrl_datc %Htyc %Hciok %Hcdok %Htot0 %Hwf' %Hholes'
             %Haddr' %Hsz31' %Hcov' %Hszcap' %Hsized' %Hdn' %Hdn0' %Hrng
             %Hsb4 %Hmem4 %Hn4 %Hledge".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Hdview Hfview Htop #Hshotl Hfrzl Hkeep Hrud
             #Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid Hcdlnk
             Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop #Hcshot Hcfrz Hckeep Hruc Htoken
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hppid Hppback Hpath Hbsl Hislr Hop Htx
             Hcont".
    iEval (rewrite Hglog) in "Htx".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE.  create's contract carries no
       order premise because it does not need one: it is a level-0 contract,
       and [cpu_own_size_le] forces [lks = ∅] there.  Keep the EQUATION rather
       than substituting -- [lks] is spelled by name in every body below --
       and let [lkbelow] close each callee's bound from it. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    subst tot. subst dn0'.
    pose proof HXregs as HXr.
    destruct HXr as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & Xthr).
    destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    assert (Htyz : bv_unsigned (di_type dnc) <> 0) by exact (proj1 Hfresh).
    assert (Htdirz : bv_unsigned (di_type dnc) <> T_DIR_z).
    { rewrite Htyc. intro Hc. apply Htdir.
      apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
    assert (Hcadd : di_addrs dnc = bm_cells bmc)
      by exact (proj1 (proj2 (proj2 Hciok))).
    assert (Hcdirlen : length (bm_dir bmc) = NDIRECT)
      by exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc (proj1 Hciok)).
    assert (Hcdok' : dir_ok icfg_nib dnc datc) by (rewrite -Hnib; exact Hcdok).
    (* ===== +0x146 sh zero,74(s3) : ip->nlink = 0 ===================== *)
    iEval (rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
                   cr_setf_nlink cr_setf_size) in "Hcmeta".
    iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
    iEval (rewrite /i_nlink) in "Hcinl".
    iDestruct (sie_cap_gpr_x0 Mx (K - 10)%nat b (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x146)) Rz Rs3
              (mword_of_int 74 : mword 12) Mx (K - 10)%nat
              (mword_of_int 1 : mword 16) b
              with "Hcg Hpc [] [Hcinl]").
    { iApply (cri_146 with "Htext"). }
    { iEval (rgne; rewrite X19). iExact "Hcinl". }
    iIntros (CIDG1 HqG1) "Hcg Hpc Hcinl".
    iEval (rgne; rgne; rewrite X19 Hx0 cr_trunc16_zero) in "Hcinl".
    assert (Hq14a : add_vec_int (mword_of_int (CK + 0x146) : mword 64) 4
                    = mword_of_int (CK + 0x14a)) by pcw.
    iEval (rewrite Hq14a) in "Hpc".
    iAssert (inode_meta (ientry kslot)
               (cr_setf dnc major minor (mword_of_int 0 : mword 16)))
      with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmeta".
    { rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
              cr_setf_nlink cr_setf_size /i_nlink. iFrame. }
    (* ===== +0x14a c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14a)) Ra0 Rs3 Mx
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_14a with "Htext"). }
    iIntros (CIDG2 HqG2) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx) with G1.
    assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G1 upd_eq. rewrite X19. apply add_vec_zero_l. }
    assert (HG1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G1)
      by (rewrite /G1; apply cr_regs3_caller; [exact Hcsa0 | exact HXregs]).
    assert (Hq14c : add_vec_int (mword_of_int (CK + 0x14a) : mword 64) 2
                    = mword_of_int (CK + 0x14c)) by pcw.
    iEval (rewrite Hq14c) in "Hpc".
    (* ===== +0x14c jal iupdate(ip) : THE UNLINK FLUSH ================= *)
    assert (Htgiu : add_vec (mword_of_int (CK + 0x14c) : mword 64)
              (sign_extend' 64 (mword_of_int 2090062 : mword 21))
              = mword_of_int KernelSyms.iupdate) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x14c)) Rra
              (mword_of_int 2090062 : mword 21) G1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_14c with "Htext"). }
    iIntros (CIDG3 HqG3) "Hcg Hpc".
    iEval (rewrite Htgiu) in "Hpc".
    pose (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1) with G2.
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
    assert (HG2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G2)
      by (rewrite /G2; apply cr_regs3_caller; [exact Hcsra | exact HG1regs]).
    assert (Hstab : di_type_stable
                      (cr_setf dnc major minor (mword_of_int 0 : mword 16))
                      (cr_setf dnc major minor (mword_of_int 1 : mword 16))).
    { apply di_type_stable_eq. rewrite !cr_setf_type. reflexivity. }
    assert (Hdec : bv_unsigned (di_nlink
                     (cr_setf dnc major minor (mword_of_int 1 : mword 16)))
                   = bv_unsigned (di_nlink
                       (cr_setf dnc major minor (mword_of_int 0 : mword 16))) + 1).
    { rewrite !cr_setf_nlink. vm_compute. reflexivity. }
    assert (Hcadd0 : di_addrs (cr_setf dnc major minor
                                 (mword_of_int 0 : mword 16)) = bm_cells bmc)
      by (rewrite cr_setf_addrs; exact Hcadd).
    destruct n4 as [| u0]; [exfalso; unfold iput_units in Hn4; lia |].
    iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CIDf CIDG3 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IU.wp_iupdate_unlink γs j γl γu γd γk pd pav pu bn γ γi
              inodestart nib dev (ientry kslot) cinum
              (cr_setf dnc major minor (mword_of_int 0 : mword 16))
              (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc
              u0 Sb4 true
              (cr_ity ty (bv_unsigned dind)) pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G2 (K - 10)%nat eb b lks
              V ltac:(exact HKiu) ltac:(intros _; exact Hmem4)
              Hlg Hist0 Hcblk Hcblog Hcinb Hstab
              ltac:(exact (cr_setf_type_nz dnc major minor _ Htyz))
              Hdec
              Hcadd0 Hcdirlen Hj Hgs HG2a0 Heb
              with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hcidev Hciinum
                    Hcmeta Hcmap Hsbi Hiregi Hcdiat [Htoken] [] Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbs2 Hop").
    all: try lkbelow.
    { rewrite (cr_delta_eq ty major minor dnc (mword_of_int 0 : mword 16)
                 Htyc ltac:(vm_compute; reflexivity)). iExact "Htoken". }
    { iLeft. iSplit; iPureIntro; [exact Hglog | exact Hist]. }
    iIntros (CIDG4 HsG4 mfl)
      "%Hcsfl Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
       Hbs2 Hop".
    assert (Hpcfl : ret_pc (G2 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x150)) by (rewrite HG2ra; pcw).
    iEval (rewrite Hpcfl) in "Hpc".
    assert (Hmflregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mfl)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G2 mfl Hcsfl HG2regs).
    pose proof Hmflregs as HFr.
    destruct HFr as (F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & Fthr).
    iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* ===== +0x150 c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x150)) Ra0 Rs3 mfl
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_150 with "Htext"). }
    iIntros (CIDG5 HqG5) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl) with G3.
    assert (HG3a0 : G3 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G3 upd_eq. rewrite F19. apply add_vec_zero_l. }
    assert (HG3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G3)
      by (rewrite /G3; apply cr_regs3_caller; [exact Hcsa0 | exact Hmflregs]).
    assert (Hq152 : add_vec_int (mword_of_int (CK + 0x150) : mword 64) 2
                    = mword_of_int (CK + 0x152)) by pcw.
    iEval (rewrite Hq152) in "Hpc".
    (* ===== +0x152 jal iunlockput(ip) : THE PUT THAT FREES ============ *)
    assert (Htgu1 : add_vec (mword_of_int (CK + 0x152) : mword 64)
              (sign_extend' 64 (mword_of_int 2090832 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x152)) Rra
              (mword_of_int 2090832 : mword 21) G3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_152 with "Htext"). }
    iIntros (CIDG6 HqG6) "Hcg Hpc".
    iEval (rewrite Htgu1) in "Hpc".
    pose (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3) with G4.
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a0 : G4 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G4)
      by (rewrite /G4; apply cr_regs3_caller; [exact Hcsra | exact HG3regs]).
    (* the child's payload, at the ZEROED record: its own [dlinks] is
       [emp] (it is not a directory -- this is the non-T_DIR arm), and the
       flush handed the region's fragment back retagged. *)
    iAssert (dlinks fsc_fs (bv_unsigned cinum)
               (cr_setf dnc major minor (mword_of_int 0 : mword 16)) bmc datc)
      as "Hcdlnk1".
    { iApply (dlinks_not_dir fsc_fs (bv_unsigned cinum)
                (cr_setf dnc major minor (mword_of_int 0 : mword 16)) bmc datc).
      intros Hchd. apply Htdirz.
      rewrite -(cr_setf_type dnc major minor
                  (mword_of_int 0 : mword 16)).
      exact Hchd. }
    iDestruct "Hcmap" as "[Hca Hci]".
    iDestruct (dv_ride_size (bv_unsigned cinum)
                 (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                 (cr_setf dnc major minor (mword_of_int 0 : mword 16)) datc
                 (eq_trans (cr_setf_size dnc major minor
                              (mword_of_int 1 : mword 16))
                    (eq_sym (cr_setf_size dnc major minor
                               (mword_of_int 0 : mword 16))))
                with "Hcdview") as "Hcdview".
    iDestruct (fv_ride_size (bv_unsigned cinum)
                 (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                 (cr_setf dnc major minor (mword_of_int 0 : mword 16)) datc
                 (eq_trans (cr_setf_size dnc major minor
                              (mword_of_int 1 : mword 16))
                    (eq_sym (cr_setf_size dnc major minor
                               (mword_of_int 0 : mword 16))))
                with "Hcfview") as "Hcfview".
    (* ...and the ERA's abstract value follows the [sh zero,74(s3)]: only
       [di_nlink] moved, so the node's other columns stand (2b-inode-3). *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): the four facts are
       [ic_mk_loaded]'s own, taken a few lines early.  A record at
       [nlink = 0] owes no dot entries, so this is the arm on which the
       fail path leaves the child well-formed. *)
    assert (Hlocz : inode_local (bv_unsigned cinum)
              (era_node (cr_setf dnc major minor (mword_of_int 0 : mword 16))
                        bmc datc)).
    { apply (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst _ bmc datc).
      - exact (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                 (mword_of_int 0 : mword 16) Hciok).
      - exact (cr_setf_rec_local dnc major minor (mword_of_int 0 : mword 16)
                 Hrl_datc cr_nl_short_0).
      - apply dir_uniq_not_dir. rewrite cr_setf_type. exact Htdirz.
      - apply dir_dots_ix_not_dir. rewrite cr_setf_type. exact Htdirz. }
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned cinum)
            (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                      bmc datc)
            (era_node (cr_setf dnc major minor (mword_of_int 0 : mword 16))
                      bmc datc)
            ltac:(solve_ndisj) Hlocz with "[] Hctop") as "Hctop";
      [iApply (ireg_inv_ftop with "Hiregi") |].
    iModIntro.
    iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum
                 (cr_setf dnc major minor (mword_of_int 0 : mword 16))
                 bmc datc
                 (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor
                    _ Hciok)
                 (cr_setf_rec_local dnc major minor (mword_of_int 0 : mword 16)
                    Hrl_datc cr_nl_short_0)
                 (cr_setf_dir_ok icfg_nib dnc datc major minor _ Hcdok')
                 (dir_dots_ix_orphan (bv_unsigned cinum)
                    (cr_setf dnc major minor (mword_of_int 0 : mword 16)) datc
                    ltac:(rewrite cr_setf_nlink; vm_compute; reflexivity))
                 (dir_orphan_clean_not_dir
                    (cr_setf dnc major minor (mword_of_int 0 : mword 16)) datc
                    ltac:(rewrite cr_setf_type; exact Htdirz))
                 (dir_uniq_not_dir
                    (cr_setf dnc major minor (mword_of_int 0 : mword 16)) datc
                    ltac:(rewrite cr_setf_type; exact Htdirz))
                 with "Hcdlnk1 Hcdiat Hcmeta Hca Hci Hcblocks Hcdview Hcfview
                       Hctop")
      as "Hcload".
    iAssert (ity_shot g (di_type (cr_setf dnc major minor
                                    (mword_of_int 0 : mword 16))))
      as "#Hcshot'". { rewrite cr_setf_type. iExact "Hcshot". }
    iPoseProof (cr_esc_acc γi kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckp".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iDestruct (cpu_own_transport CIDG4 CIDG6 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
              gtl gil gisl bmapstart inodestart nib size dev
              kslot (q/2)%Qp (q/2)%Qp g (DepTx (q/2)%Qp dev cinum g t (1/4)%Qp) cinum
              (cr_setf dnc major minor (mword_of_int 0 : mword 16)) bmc
              (S u0) (Sb4 ∪ {[IBLOCK cinum inodestart]})
              (bool_decide (bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum inodestart]})))
              true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G4 (K - 10)%nat eb b lks
              V ltac:(exact HKiup) eq_refl Hkslt
              ltac:(exact (cr_crb_honest (Sb4 ∪ {[IBLOCK cinum inodestart]})
                             bmapstart))
              ltac:(intros _; exact (cr_in_union_sing Sb4
                                       (IBLOCK cinum inodestart)))
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
              ltac:(exact (proj1 Hn4)) Hj Hgs HG4a0 ltac:(lkbelow) Hglog eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescc Hiregi Hiopen Hslkc Hcslkd Hcdep Hcidev Hciinum
                    Hcivalid Hcload Hcshot' Hcfrz [$Hckp $Hruc] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDG7 HqG7 mu1 n5 Sb5 w1)
      "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb5 %Hw5 %Hw5c %Hn5 Hop Hisl1 Htq1".
    (* THE LEDGER, at the body's disjunction (finding (3) in the banner) *)
    assert (Hipn5 : (iput_units <= n5)%nat).
    { destruct (decide (bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum inodestart]})))
        as [Hin | Hout].
      - rewrite (Hw5c (cr_crb_claim _ _ Hin)) in Hn5.
        exact (cr_fail_ip_right (S u0) n5 (proj1 Hn4) (proj1 Hn5)).
      - destruct Hledge as [H4 | Hin4].
        + exact (cr_fail_ip_left (S u0) n5 w1 H4 (proj1 Hn5)).
        + exfalso. apply Hout.
          exact (cr_sub_union_sing Sb4 (IBLOCK cinum inodestart)
                   bmapstart Hin4). }
    assert (Hpcu1 : ret_pc (G4 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x156)) by (rewrite HG4ra; pcw).
    iEval (rewrite Hpcu1) in "Hpc".
    assert (Hmu1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu1)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G4 mu1 Hcsu1 HG4regs).
    pose proof Hmu1regs as HUr.
    destruct HUr as (U2 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & Uthr).
    (* ===== +0x156 c.mv a0,s1 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x156)) Ra0 Rs1 mu1
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_156 with "Htext"). }
    iIntros (CIDG8 HqG8) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1) with G5.
    assert (HG5a0 : G5 !!! Regidx Ra0 = ientry kd).
    { rewrite /G5 upd_eq. rewrite U9. apply add_vec_zero_l. }
    assert (HG5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G5)
      by (rewrite /G5; apply cr_regs3_caller; [exact Hcsa0 | exact Hmu1regs]).
    assert (Hq158 : add_vec_int (mword_of_int (CK + 0x156) : mword 64) 2
                    = mword_of_int (CK + 0x158)) by pcw.
    iEval (rewrite Hq158) in "Hpc".
    (* ===== +0x158 jal iunlockput(dp) ================================= *)
    assert (Htgu2 : add_vec (mword_of_int (CK + 0x158) : mword 64)
              (sign_extend' 64 (mword_of_int 2090826 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x158)) Rra
              (mword_of_int 2090826 : mword 21) G5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_158 with "Htext"). }
    iIntros (CIDG9 HqG9) "Hcg Hpc".
    iEval (rewrite Htgu2) in "Hpc".
    pose (G6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5) with G6.
    assert (HG6ra : G6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)
      by (rewrite /G6; apply upd_eq).
    assert (HG6a0 : G6 !!! Regidx Ra0 = ientry kd)
      by (rewrite /G6 upd_ne; [exact HG5a0 | nz]).
    assert (HG6regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G6)
      by (rewrite /G6; apply cr_regs3_caller; [exact Hcsra | exact HG5regs]).
    (* THE PARENT'S RE-PARK.  [tot = 0]: no byte and no record moved, so
       the whole big-op rides unchanged and no fragment is wanted -- which
       is the only reason this arm exists, since the one it had was spent
       by the flush at +0x14c. *)
    assert (Hszcap : bv_unsigned (di_size dn)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
    assert (Hty' : di_type dn' = di_type dn) by (rewrite Hdn'; reflexivity).
    assert (Hnl' : di_nlink dn' = di_nlink dn) by (rewrite Hdn'; reflexivity).
    assert (Hk0le : (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))
                     <= dir_nrec (bv_unsigned (di_size dn)))%nat)
      by apply dir_slot_le.
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn) as [Hnr1 _].
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hnatle : (16 * dir_slot data
                        (dir_nrec (bv_unsigned (di_size dn))) + 0
                      <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat)
      by lia.
    assert (HzA : (Z.of_nat (16 * dir_slot data
                      (dir_nrec (bv_unsigned (di_size dn))) + 0)%nat
                   <= Z.of_nat (16 * dir_nrec
                        (bv_unsigned (di_size dn)) + 16)%nat)%Z)
      by (apply Nat2Z.inj_le; exact Hnatle).
    assert (HzB : Z.of_nat (16 * dir_nrec
                      (bv_unsigned (di_size dn)) + 16)%nat
                  = (Z.of_nat (16 * dir_nrec
                      (bv_unsigned (di_size dn)))%nat + 16)%Z)
      by (rewrite Nat2Z.inj_add; reflexivity).
    assert (Hoff32 : (Z.of_nat (16 * dir_slot data
                        (dir_nrec (bv_unsigned (di_size dn))) + 0)
                      < 2 ^ 32)%Z).
    { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z. lia. }
    assert (Hszmax : bv_unsigned (di_size dn')
              = Z.max (bv_unsigned (di_size dn))
                  (Z.of_nat (16 * dir_slot data
                     (dir_nrec (bv_unsigned (di_size dn))) + 0)))
      by (rewrite Hdn'; exact (cr_wi_size_max dn bm' _ 0%nat Hoff32)).
    iDestruct (dlinks_open with "Hdlnk")
          as "(%D & [%Hdok0 %Hxact0] & Hetk)".
    (* THE ENTRY UNITS RIDE: nothing was written, so the
       entry map does not move (durable-disk 2b-inode-5). *)
    iDestruct (ent_toks_dirlink_nop (fs_gamma_L fsc_fs) (bv_unsigned dind)
                 dn dn' bm bm' data data'
                 (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                             (bname 14 nf)) !!! j)
                 (dir_nrec (bv_unsigned (di_size dn)))
                 (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))) 0%nat D
                 eq_refl Hk0le eq_refl Hty' Hnl' Hszmax Hrng
                 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok))))))
                 Hholes' Hszcap Hszcap'
                 with "Hetk") as "Hetk".
    assert (Heqent0 := dir_entries_dirlink_nop_eq dn dn' bm bm' data data'
               (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                           (bname 14 nf)) !!! j)
               (dir_nrec (bv_unsigned (di_size dn)))
               (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))) 0%nat
               eq_refl Hk0le eq_refl Hty' Hszmax Hrng
               (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok))))))
               Hholes' Hszcap Hszcap').
    assert (Hgrow0 : forall s', is_Some (dir_entries (era_node dn bm data) !! s')
                                -> is_Some (dir_entries (era_node dn' bm' data') !! s'))
      by (intros s' Hs'; rewrite Heqent0; exact Hs').
    assert (Hdok0' : FsStateInode.ent_dset_ok (era_node dn' bm' data') D)
      by exact (FsStateInode.ent_dset_ok_grow _ _ D Hgrow0 Hdok0).
    assert (Hxact0' : FsStateInode.node_exact (era_node dn' bm' data') D).
    { apply (FsStateInode.node_exact_cong (era_node dn bm data)
               (era_node dn' bm' data') D).
      - rewrite /fn_is_dir /fn_type !era_node_rec Hty' //.
      - rewrite /fn_nlink !era_node_rec Hnl' //.
      - exact Hxact0. }
    iDestruct (dlinks_intro _ _ _ _ _ D Hdok0' Hxact0'
                 with "Hetk") as "Hdlnk".
    assert (Hiok' : inode_ok fsc_cov fsc_logst dn' bm' data').
    { rewrite /inode_ok. split_and!.
      - exact Hwf'.
      - exact Hcov'.
      - exact Haddr'.
      - rewrite Hty'. exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
      - exact Hszcap'.
      - exact Hholes'.
      - exact Hsized'. }
    assert (Hcl16b : bv_unsigned (cr_low16 cinum) < 16 * Z.of_nat nib).
    { rewrite (cr_low16_unsigned cinum ltac:(lia)). exact Hcinb. }
    assert (Hdok' : dir_ok icfg_nib dn' data').
    { rewrite -Hnib.
      exact (dir_ok_dirlink nib dn dn' data data' (cr_low16 cinum)
               (bname 14 nf) _ _ 0%nat eq_refl eq_refl ltac:(lia) Hcl16b
               Hty' Hszmax Hrng Hdok). }
    assert (Ht0le : (0 <= 16)%nat) by (clear; lia).
    assert (Hszle : bv_unsigned (di_size dn) <= bv_unsigned (di_size dn'))
      by (clear -Hszmax; rewrite Hszmax; lia).
    assert (Hddix' : dir_dots_ix (bv_unsigned dind) dn' data')
      by exact (dir_dots_ix_dirlink (bv_unsigned dind) dn dn' data data'
                  (cr_low16 cinum) (bname 14 nf) _ _ 0%nat eq_refl eq_refl
                  Ht0le Hty' Hnl' Hszle Hrng Hddix).
    assert (Hduq' : dir_uniq dn' data')
      by exact (cr_uniq_nop dn dn' data data' (cr_low16 cinum)
                  (bname 14 nf) _ _ eq_refl eq_refl
                  Hty' Hszmax Hrng Hduq).
    iDestruct "Hmap" as "[Haddrs Hind]".
    (* THE RECORD-ONLY FACTS AT THE APPENDED PARENT (durable-disk
       2b-inode-3): the type and the count stand, and the size is a MAX of
       two multiples of sixteen. *)
    assert (Hrl' : inode_rec_local dn').
    { apply (inode_rec_local_same_type dn dn' Hrl Hty').
      - rewrite Hnl'. exact (proj1 (proj2 Hrl)).
      - intros _. rewrite Hszmax. apply cr_max_div16.
        + apply (proj2 (proj2 Hrl)).
          rewrite Htydir. vm_compute. reflexivity.
        + exists (Z.of_nat (dir_slot data
                    (dir_nrec (bv_unsigned (di_size dn)))))%Z.
          rewrite Nat.add_0_r Nat2Z.inj_mul. lia. }
    (* THE ERA'S ABSTRACT VALUE MOVES HERE (durable-disk lane A): the fail
       body hands the parent's fragment over at the ENTRY record, because
       the retag owes the registry's row and this is where the post
       record's four well-formedness facts have just been assembled. *)
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
            (era_node dn bm data) (era_node dn' bm' data')
            ltac:(solve_ndisj)
            (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst dn' bm'
               data' Hiok' Hrl' Hduq' Hddix')
            with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hiregi") |].
    iModIntro.
    iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind dn' bm' data'
                 Hiok' Hrl' Hdok' Hddix' (cr_doc_of_live dn dn' data' Hnl' Hnl0)
                 Hduq'
                 with "Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview
                       Htop")
      as "Hload".
    iAssert (ity_shot gd (di_type dn')) as "#Hshotl'".
    { rewrite Hty'. iExact "Hshotl". }
    iPoseProof (cr_esc_acc γi kd Hkdlt with "Hesc")
      as "#Hescd".
    iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
    iDestruct (log_opS_named with "Hop") as (e1) "Hop".
    iDestruct (cpu_own_transport CIDG7 CIDG9 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
              gtl γil γisl bmapstart inodestart nib size dev
              kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/4)%Qp) dind dn' bm'
              n5 Sb5 false false false e1 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G6 (K - 10)%nat eb b lks
              V ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) ltac:(discriminate)
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
              ltac:(exact Hipn5) Hj Hgs HG6a0 ltac:(lkbelow) Hglog eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                    Hivalid Hload Hshotl' Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDGA HqGA mu2 n6 Sb6 w2)
      "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb6 %Hw6 %Hw6c %Hn6 Hop Hisl2 Htq2".
    iDestruct (log_tx_add icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htq1 Htq2") as "Htp".
    iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
    iDestruct (log_tx_full with "Htw") as "Htx".
    iEval (rewrite -Hglog) in "Htx".
    assert (Hpcu2 : ret_pc (G6 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x15c)) by (rewrite HG6ra; pcw).
    iEval (rewrite Hpcu2) in "Hpc".
    assert (Hmu2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu2)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G6 mu2 Hcsu2 HG6regs).
    iDestruct ("Hppback" with "Hppid") as "Hpriv".
    (* ===== +0x15c c.ldsp s3,40(sp) : THE LAZY RESTORE ================ *)
    assert (HG7sp : mu2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (destruct Hmu2regs as (H2 & _); exact H2).
    assert (HT5 : add_vec (mu2 !!! Regidx csp_rs1)
                    (zero_extend' 64
                       (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HG7sp; apply cr_frm5).
    iEval (rewrite -HT5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x15c))
              (mword_of_int 5 : mword 6) Rs3 mu2 (K - 10)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] Hb5").
    { iApply (cri_15c with "Htext"). }
    iIntros (CIDGB HqGB) "Hcg Hpc Hb5".
    iEval (rewrite HT5) in "Hb5".
    pose (G7 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2).
    change (<[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2) with G7.
    assert (HG7regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) ty major minor G7)
      by exact (cr_regs3_s3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                  ty major minor mu2 _ eq_refl Hmu2regs).
    assert (HG7s2 : G7 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
    { rewrite /G7 upd_ne; [| nz].
      destruct Hmu2regs as (_ & _ & _ & Hd18 & _). exact Hd18. }
    assert (Hq15e : add_vec_int (mword_of_int (CK + 0x15c) : mword 64) 2
                    = mword_of_int (CK + 0x15e)) by pcw.
    iEval (rewrite Hq15e) in "Hpc".
    (* ===== +0x15e c.j +0x70 ========================================== *)
    assert (Htg070f : add_vec (mword_of_int (CK + 0x15e) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0"))))
              = mword_of_int (CK + 0x70)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (CK + 0x15e))
              (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0")))
              G7 (K - 10)%nat b
              ltac:(rewrite Htg070f; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_15e with "Htext"). }
    iIntros (CIDGC HqGC). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htg070f) in "Hpc".
    iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
    iPoseProof ("Htail" $! CIDGC) as "Ht".
    iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
    iApply ("Ht" $! G7 (m !!! Regidx Rs3 : mword 64) nfj with
              "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
    { exact (cr_tregs_of_regs3 m sp0 (ientry kd)
               (mword_of_int 0 : mword 64) ty major minor G7 HG7regs). }
    iIntros (CIDfin Hsfin mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CIDGA CIDfin 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (iref_slots_combine with "Hisl1 Hisl2") as "Hisl".
    iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
    iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
              (mword_of_int 0 : mword 32) dn bm n6 Sb6
              (1 + (1 + (ns - 2)))%nat
              with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                    Hbsl [%] Hisl [%] Hop [$Htx]").
    { exact Hcsf. }
    { exact (cr_slots_2 _ ns eq_refl Hns). }
    { split_and!.
      - exact (cr_sub3 _ _ _ _ Hsb4
                 (cr_sub_union_sing Sb4 (IBLOCK cinum inodestart))
                 (cr_sub2 _ _ _ Hsb5 Hsb6)).
      - pose proof (proj2 Hn6) as HB1. pose proof (proj2 Hn5) as HB2.
        pose proof (proj2 Hn4) as HB3. lia.
      - discriminate. }
    { iPureIntro. rewrite Ha0f. exact HG7s2. }
  Qed.

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
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (nf nsl : nat -> bv 8) (t : nat)
      (CIDf : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname)
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
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dp = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dp <> (mword_of_int 0 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dp bmp datap⌝ -∗
       ⌜dir_ok nib dp datap⌝ -∗
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
       ⌜0 < bv_unsigned cinum < ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dc = ty⌝ -∗
       ⌜di_major dc = major⌝ -∗
       ⌜di_minor dc = minor⌝ -∗
       ⌜di_nlink dc = (mword_of_int 1 : mword 16)⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dc bmc datc⌝ -∗
       (* durable-disk 2b-inode-3: the CHILD's record-only facts *)
       ⌜inode_rec_local dc⌝ -∗
       ⌜dir_ok nib dc datc⌝ -∗
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
       ⌜IBLOCK cinum inodestart ∈ Sb4⌝ -∗
       ⌜(iput_units <= n4)%nat /\ (n4 <= u)%nat⌝ -∗
       ⌜(S iput_units <= n4)%nat \/ bmapstart ∈ Sb4⌝ -∗
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
       is_sleeplock_gen γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q γisl (qd/2)%Qp (i_lock (ientry kd)) pidv -∗
       ic_deposit fsc_ic kd (DepTx (qd/2)%Qp dev dind gd t (1/4)) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dind) dp bmp datap -∗
       dinode_at γi dind dp -∗
       inode_meta (ientry kd) dp -∗
       inode_map fsc_fs (ientry kd) bmp -∗
       inode_blocks fsc_fs bmp datap -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dind) (dv_of dp datap) -∗
       fv_ride (bv_unsigned dind) (fv_of dp datap) -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dind) (era_node dp bmp datap) -∗
       ity_shot gd (di_type dp) -∗
       (* ...AND THE PARENT'S FREEZE TOKEN (iclaim-ledger.md §3.9): the half
          takes the payload UNPACKED, so it takes [ic_payload]'s A-custody
          conjunct too.  It is [SpecIlock]'s output at +0x26 and it goes home
          at this half's [iunlockput(dp)]. *)
       ifreeze_off (bv_unsigned dind) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* the parent's PROVENANCE UNIT (item 7a-wire): the iunlockput that
          closes it spends the unit that rode with the reference. *)
       runit_any (bv_unsigned dind) -∗
       (* THE LOCKED CHILD -- WITHOUT its [dlinks] (see the header) *)
       is_sleeplock_gen gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_tok fsc_ic kslot) (slh_tok (icfg_isl kslot)) -∗
       sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv -∗
       ic_deposit fsc_ic kslot (DepTx (q/2)%Qp dev cinum g t (1/4)) -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dinode_at γi cinum dc -∗
       inode_meta (ientry kslot) dc -∗
       inode_map fsc_fs (ientry kslot) bmc -∗
       inode_blocks fsc_fs bmc datc -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned cinum) (dv_of dc datc) -∗
       fv_ride (bv_unsigned cinum) (fv_of dc datc) -∗
       (* ...and the CHILD's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned cinum) (era_node dc bmc datc) -∗
       ity_shot g (di_type dc) -∗
       (* ...and the CHILD's, for the same reason (§3.9). *)
       ifreeze_off (bv_unsigned cinum) -∗
       inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev cinum g -∗
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
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
       proc_priv_bare (proc_addr j) pidv V -∗
       (proc_priv_bare (proc_addr j) pidv V -∗
          proc_priv γf (proc_addr j) pidv V) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
       bslots 3 -∗
       iref_slots (ns - 2) -∗
       log_opS γ n4 Sb4 -∗
       (* THE CHILD'S ROW IS SUSPENDED: it is a directory with a link
          count and no dots until the interior dirlinks land, so the arm
          carries the registry's receipt (durable-disk lane A) *)
       cr_dirty t (bv_unsigned cinum) -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γi γ γf bn bmapstart inodestart
                         nib ninodes size dev plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ---- (c) THE HALF -------------------------------------------------- *)
  Lemma cr_fail_mkdir_half
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (nf nsl : nat -> bv 8) (t : nat) :
    (K_create <= K)%nat ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    nib = icfg_nib ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= inodestart ->
    cov_below fsc_cov size ->
    InodeInv.ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗ panic_env -∗
    bio_ctx bn (fs_view fsc_fs γd dev fsc_cov) -∗
    log_ctx γ bn fsc_fs fsc_cov fsc_logst dev -∗
    is_itable2 gtl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
    ireg_inv γi fsc_fs inodestart nib -∗
    ireg_open -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
      cr_fail_mkdir_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                   bmapstart inodestart nib ninodes size dev
                   plen pfun pv ty major minor V u Sb ns pidv
                   dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                   kd qd gd γil γisl dind nf nsl t CIDf).
  Proof.
    intros HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcovb
           Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpenv #Hbio #Hlogc #Hitb2 #Hitbl #Hesc #Hiregi #Hiopen
             #Hprocs #Hdevi #Hgeom #Hdlk".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDf Hsf).
    iIntros (Mx kslot q g gil gisl cinum dp bmp datap dc bmc datc
             n4 Sb4).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hiok %Hdok %Hddix %Hduq %Hrl %Hkslt
             %Hcpos %Hcinb %Htyc %Hcmaj %Hcmin %Hcnl1 %Hciok %Hrl_datc %Hcdok %Hcduq %Hcdots
             %Hsb4 %Hmem4 %Hn4 %Hledge".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Hdview Hfview Htop #Hshotl Hfrzl Hkeep Hrud
             #Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
             Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop #Hcshot Hcfrz Hckeep Hruc Htoken
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hppid Hppback Hpath Hbsl Hislr Hop Hdirty
             Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE -- the level-0 pose the
       sibling [cr_fail_half] makes, for the same reason: create's contract
       carries no order premise because it needs none, and [lkbelow] closes
       each callee's bound from this EQUATION.  Keep the equation rather
       than substituting; [lks] is spelled by name in the bodies below. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HXregs as HXr.
    destruct HXr as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & Xthr).
    destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    assert (Htyz : bv_unsigned (di_type dc) <> 0).
    { rewrite Htyc Htdir. vm_compute. discriminate. }
    assert (Hcadd : di_addrs dc = bm_cells bmc)
      by exact (proj1 (proj2 (proj2 Hciok))).
    assert (Hcdirlen : length (bm_dir bmc) = NDIRECT)
      by exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc (proj1 Hciok)).
    assert (Hcdok' : dir_ok icfg_nib dc datc) by (rewrite -Hnib; exact Hcdok).
    (* the ZEROED child's record, and the four fields the [sh] leaves alone *)
    assert (Hzty : di_type (cr_setf dc major minor (mword_of_int 0 : mword 16))
                   = di_type dc) by apply cr_setf_type.
    assert (Hzsz : di_size (cr_setf dc major minor (mword_of_int 0 : mword 16))
                   = di_size dc) by apply cr_setf_size.
    assert (Hznl : bv_unsigned (di_nlink
                     (cr_setf dc major minor (mword_of_int 0 : mword 16))) = 0)
      by (rewrite cr_setf_nlink; vm_compute; reflexivity).
    (* ===== +0x146 sh zero,74(s3) : ip->nlink = 0 ===================== *)
    iEval (rewrite /inode_meta) in "Hcmeta".
    iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
    iEval (rewrite /i_nlink) in "Hcinl".
    iDestruct (sie_cap_gpr_x0 Mx (K - 10)%nat b (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x146)) Rz Rs3
              (mword_of_int 74 : mword 12) Mx (K - 10)%nat
              (di_nlink dc : mword 16) b
              with "Hcg Hpc [] [Hcinl]").
    { iApply (cri_146 with "Htext"). }
    { iEval (rgne; rewrite X19). iExact "Hcinl". }
    iIntros (CIDG1 HqG1) "Hcg Hpc Hcinl".
    iEval (rgne; rgne; rewrite X19 Hx0 cr_trunc16_zero) in "Hcinl".
    assert (Hq14a : add_vec_int (mword_of_int (CK + 0x146) : mword 64) 4
                    = mword_of_int (CK + 0x14a)) by pcw.
    iEval (rewrite Hq14a) in "Hpc".
    iAssert (inode_meta (ientry kslot)
               (cr_setf dc major minor (mword_of_int 0 : mword 16)))
      with "[Hcity Hcimaj Hcimin Hcinl Hcisz]" as "Hcmeta".
    { rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
              cr_setf_nlink cr_setf_size /i_nlink.
      rewrite -Hcmaj -Hcmin. iFrame. }
    (* THE ORPHAN'S RE-PARK (durable-disk
       2b-inode-5): an ORPHAN owns NO tokens.  Its live records are named
       ["."] or [".."] ([DirView.dir_orphan_clean]'s [dir_dots_only], which
       is [Hcdots] carried onto the zeroed record), ["."] is never counted
       and an orphan's [".."] is tokenless -- so nothing is owed and the
       failing [dirlink] left nothing behind. *)
    assert (Hzholes : blk_holes_zero bmc datc)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok)))))).
    assert (Hzcap : bv_unsigned (di_size (cr_setf dc major minor (mword_of_int 0 : mword 16)))
                    <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hciok))))). }
    assert (Hzdok : FsStateInode.ent_dset_ok (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) ∅)
      by (intros tz Htz; exfalso; exact (not_elem_of_empty tz Htz)).
    assert (Hzxact : FsStateInode.node_exact (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) ∅).
    { intros _.
      assert (Hfn0 : fn_nlink (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc) = 0%nat)
        by (rewrite /fn_nlink era_node_rec Hznl //).
      rewrite /fn_orphan Hfn0
        (bool_decide_eq_true_2 (0%nat = 0%nat) eq_refl) size_empty //. }
    iAssert (dlinks fsc_fs (bv_unsigned cinum) (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc)
      with "[]" as "Hcdlnk".
    { iApply (dlinks_intro _ _ _ _ _ ∅ Hzdok Hzxact with "[]").
      iApply (FsStateEra.ent_toks_era_dots_only (fs_gamma_L fsc_fs)
                (bv_unsigned cinum) (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc datc
                ∅ Hznl Hzholes Hzcap
                (dir_dots_only_of dc _ datc
                   ltac:(first [reflexivity
                               | rewrite cr_setf_size; reflexivity])
                   Hcdots)). }
    (* ===== +0x14a c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14a)) Ra0 Rs3 Mx
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_14a with "Htext"). }
    iIntros (CIDG2 HqG2) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx) with G1.
    assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G1 upd_eq. rewrite X19. apply add_vec_zero_l. }
    assert (HG1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G1)
      by (rewrite /G1; apply cr_regs3_caller; [exact Hcsa0 | exact HXregs]).
    assert (Hq14c : add_vec_int (mword_of_int (CK + 0x14a) : mword 64) 2
                    = mword_of_int (CK + 0x14c)) by pcw.
    iEval (rewrite Hq14c) in "Hpc".
    (* ===== +0x14c jal iupdate(ip) : THE UNLINK FLUSH ================= *)
    assert (Htgiu : add_vec (mword_of_int (CK + 0x14c) : mword 64)
              (sign_extend' 64 (mword_of_int 2090062 : mword 21))
              = mword_of_int KernelSyms.iupdate) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x14c)) Rra
              (mword_of_int 2090062 : mword 21) G1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_14c with "Htext"). }
    iIntros (CIDG3 HqG3) "Hcg Hpc".
    iEval (rewrite Htgiu) in "Hpc".
    pose (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1) with G2.
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
    assert (HG2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G2)
      by (rewrite /G2; apply cr_regs3_caller; [exact Hcsra | exact HG1regs]).
    assert (Hstab : di_type_stable
                      (cr_setf dc major minor (mword_of_int 0 : mword 16)) dc).
    { apply di_type_stable_eq. rewrite cr_setf_type. reflexivity. }
    assert (Hdec : bv_unsigned (di_nlink dc)
                   = bv_unsigned (di_nlink
                       (cr_setf dc major minor (mword_of_int 0 : mword 16)))
                     + 1).
    { rewrite cr_setf_nlink Hcnl1. vm_compute. reflexivity. }
    assert (Hcadd0 : di_addrs (cr_setf dc major minor
                                 (mword_of_int 0 : mword 16)) = bm_cells bmc)
      by (rewrite cr_setf_addrs; exact Hcadd).
    assert (Htyz0 : bv_unsigned (di_type (cr_setf dc major minor
                      (mword_of_int 0 : mword 16))) <> 0)
      by (rewrite cr_setf_type; exact Htyz).
    destruct n4 as [| u0]; [exfalso; unfold iput_units in Hn4; lia |].
    iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CIDf CIDG3 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IU.wp_iupdate_unlink γs j γl γu γd γk pd pav pu bn γ γi
              inodestart nib dev (ientry kslot) cinum
              (cr_setf dc major minor (mword_of_int 0 : mword 16)) dc bmc
              u0 Sb4 true
              (cr_ity ty (bv_unsigned dind)) pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G2 (K - 10)%nat eb b lks
              V ltac:(exact HKiu) ltac:(intros _; exact Hmem4)
              Hlg Hist0 Hcblk Hcblog Hcinb Hstab Htyz0
              Hdec
              Hcadd0 Hcdirlen Hj Hgs HG2a0 Heb
              with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hcidev Hciinum
                    Hcmeta Hcmap Hsbi Hiregi Hcdiat [Htoken] [] Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbs2 Hop").
    all: try lkbelow.
    { rewrite (cr_delta_eq ty major minor dc (mword_of_int 0 : mword 16)
                 Htyc ltac:(vm_compute; reflexivity)). iExact "Htoken". }
    { iLeft. iSplit; iPureIntro; [exact Hglog | exact Hist]. }
    iIntros (CIDG4 HsG4 mfl)
      "%Hcsfl Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
       Hbs2 Hop".
    assert (Hpcfl : ret_pc (G2 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x150)) by (rewrite HG2ra; pcw).
    iEval (rewrite Hpcfl) in "Hpc".
    assert (Hmflregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mfl)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G2 mfl Hcsfl HG2regs).
    pose proof Hmflregs as HFr.
    destruct HFr as (F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & Fthr).
    iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* ===== +0x150 c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x150)) Ra0 Rs3 mfl
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_150 with "Htext"). }
    iIntros (CIDG5 HqG5) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl) with G3.
    assert (HG3a0 : G3 !!! Regidx Ra0 = ientry kslot).
    { rewrite /G3 upd_eq. rewrite F19. apply add_vec_zero_l. }
    assert (HG3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G3)
      by (rewrite /G3; apply cr_regs3_caller; [exact Hcsa0 | exact Hmflregs]).
    assert (Hq152 : add_vec_int (mword_of_int (CK + 0x150) : mword 64) 2
                    = mword_of_int (CK + 0x152)) by pcw.
    iEval (rewrite Hq152) in "Hpc".
    (* ===== +0x152 jal iunlockput(ip) : THE PUT THAT FREES ============ *)
    assert (Htgu1 : add_vec (mword_of_int (CK + 0x152) : mword 64)
              (sign_extend' 64 (mword_of_int 2090832 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x152)) Rra
              (mword_of_int 2090832 : mword 21) G3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_152 with "Htext"). }
    iIntros (CIDG6 HqG6) "Hcg Hpc".
    iEval (rewrite Htgu1) in "Hpc".
    pose (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3) with G4.
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a0 : G4 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G4)
      by (rewrite /G4; apply cr_regs3_caller; [exact Hcsra | exact HG3regs]).
    iDestruct (dv_ride_size (bv_unsigned cinum) dc
                 (cr_setf dc major minor (mword_of_int 0 : mword 16)) datc
                 (eq_sym (cr_setf_size dc major minor
                            (mword_of_int 0 : mword 16)))
                with "Hcdview") as "Hcdview".
    iDestruct (fv_ride_size (bv_unsigned cinum) dc
                 (cr_setf dc major minor (mword_of_int 0 : mword 16)) datc
                 (eq_sym (cr_setf_size dc major minor
                            (mword_of_int 0 : mword 16)))
                with "Hcfview") as "Hcfview".
    (* ...and the ERA's abstract value follows the [sh zero,74(s3)]: the
       count moved, no block did (durable-disk 2b-inode-3). *)
    (* THE CHILD'S ROW COMES BACK HERE (durable-disk lane A).  This is the
       mkdir FAIL arm: the child is the dotless directory the shared
       prologue suspended, and the [sh zero,74(s3)] at +0x146 has just made
       it an ORPHAN -- which owes no dot entries at all.  So the retag is
       the disarming one: the row is re-established for this inum and the
       transaction token goes home. *)
    assert (Hlocorph : inode_local (bv_unsigned cinum)
              (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16))
                        bmc datc)).
    { apply (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst _ bmc datc).
      - exact (cr_setf_inode_ok fsc_cov fsc_logst dc bmc datc major minor
                 (mword_of_int 0 : mword 16) Hciok).
      - exact (cr_setf_rec_local dc major minor (mword_of_int 0 : mword 16)
                 Hrl_datc cr_nl_short_0).
      - exact (dir_uniq_cong dc _ datc (cr_setf_type _ _ _ _)
                 (cr_setf_size _ _ _ _) Hcduq).
      - exact (dir_dots_ix_orphan (bv_unsigned cinum) _ datc Hznl). }
    iApply fupd_wp.
    iMod (cr_dirty_clear ⊤ t (bv_unsigned cinum)
            (era_node dc bmc datc)
            (era_node (cr_setf dc major minor (mword_of_int 0 : mword 16))
                      bmc datc)
            ltac:(solve_ndisj) Hlocorph with "[] Hdirty Hctop")
      as "[Htx Hctop]";
      [iApply (ireg_inv_ftop with "Hiregi") |].
    iModIntro.
    iAssert (ic_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum
               (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc)
      with "[Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop]"
      as "Hcload".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists datc.
      iSplitR; [iPureIntro;
                exact (cr_setf_inode_ok fsc_cov fsc_logst dc bmc datc major minor
                         _ Hciok) |].
      iSplitR; [iPureIntro;
                exact (cr_setf_rec_local dc major minor
                         (mword_of_int 0 : mword 16) Hrl_datc
                         cr_nl_short_0) |].
      iSplitR; [iPureIntro;
                exact (cr_setf_dir_ok icfg_nib dc datc major minor
                         _ Hcdok') |].
      (* the ["."]/[".."] clause needs no entry premise here, and that is
         the whole reason the guard names [nlink]: the [sh zero,74(s3)] at
         +0x146 has ALREADY zeroed the count, so whatever record the failing
         link left, what this re-parks is an ORPHAN.  All three [fail:]
         entries discharge through this one line -- at the first two the
         child has no [".."] at all. *)
      iSplitR; [iPureIntro;
                exact (dir_dots_ix_orphan (bv_unsigned cinum) _ datc Hznl) |].
      (* ...and the COMPLEMENT clause is where the entry premise is spent:
         the [sh] moved only the count, so the size -- hence [dir_nrec],
         hence the whole content -- is the entry's, and [dir_dots_only_of]
         carries it verbatim onto the orphaned record. *)
      iSplitR; [iPureIntro;
                apply dir_orphan_clean_of_only;
                apply (dir_dots_only_of dc _ datc);
                [rewrite cr_setf_size; reflexivity | exact Hcdots] |].
      (* ...and UNIQUENESS rides on the same observation one clause over:
         the [sh] moved the COUNT, and this clause reads only the type and
         the size. *)
      iSplitR; [iPureIntro;
                exact (dir_uniq_cong dc _ datc (cr_setf_type _ _ _ _)
                         (cr_setf_size _ _ _ _) Hcduq) |].
      iSplitL "Hcdlnk"; [iExact "Hcdlnk" |].
      iFrame "Hcdiat Hcmeta".
      iEval (rewrite /inode_map) in "Hcmap".
      iDestruct "Hcmap" as "[Hca Hci]". iFrame. }
    iAssert (ity_shot g (di_type (cr_setf dc major minor
                                    (mword_of_int 0 : mword 16))))
      as "#Hcshot'". { rewrite cr_setf_type. iExact "Hcshot". }
    iPoseProof (cr_esc_acc γi kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckp".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iDestruct (cpu_own_transport CIDG4 CIDG6 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
              gtl gil gisl bmapstart inodestart nib size dev
              kslot (q/2)%Qp (q/2)%Qp g (DepTx (q/2)%Qp dev cinum g t (1/4)%Qp) cinum
              (cr_setf dc major minor (mword_of_int 0 : mword 16)) bmc
              (S u0) (Sb4 ∪ {[IBLOCK cinum inodestart]})
              (bool_decide (bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum inodestart]})))
              true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G4 (K - 10)%nat eb b lks
              V ltac:(exact HKiup) eq_refl Hkslt
              ltac:(exact (cr_crb_honest (Sb4 ∪ {[IBLOCK cinum inodestart]})
                             bmapstart))
              ltac:(intros _; exact (cr_in_union_sing Sb4
                                       (IBLOCK cinum inodestart)))
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
              ltac:(exact (proj1 Hn4)) Hj Hgs HG4a0 ltac:(lkbelow) Hglog eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescc Hiregi Hiopen Hslkc Hcslkd Hcdep Hcidev Hciinum
                    Hcivalid Hcload Hcshot' Hcfrz [$Hckp $Hruc] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDG7 HqG7 mu1 n5 Sb5 w1)
      "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb5 %Hw5 %Hw5c %Hn5 Hop Hisl1 Htq1".
    assert (Hipn5 : (iput_units <= n5)%nat).
    { destruct (decide (bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum inodestart]})))
        as [Hin | Hout].
      - rewrite (Hw5c (cr_crb_claim _ _ Hin)) in Hn5.
        exact (cr_fail_ip_right (S u0) n5 (proj1 Hn4) (proj1 Hn5)).
      - destruct Hledge as [H4 | Hin4].
        + exact (cr_fail_ip_left (S u0) n5 w1 H4 (proj1 Hn5)).
        + exfalso. apply Hout.
          exact (cr_sub_union_sing Sb4 (IBLOCK cinum inodestart)
                   bmapstart Hin4). }
    assert (Hpcu1 : ret_pc (G4 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x156)) by (rewrite HG4ra; pcw).
    iEval (rewrite Hpcu1) in "Hpc".
    assert (Hmu1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu1)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G4 mu1 Hcsu1 HG4regs).
    pose proof Hmu1regs as HUr.
    destruct HUr as (U2 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & Uthr).
    (* ===== +0x156 c.mv a0,s1 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x156)) Ra0 Rs1 mu1
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_156 with "Htext"). }
    iIntros (CIDG8 HqG8) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (G5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1) with G5.
    assert (HG5a0 : G5 !!! Regidx Ra0 = ientry kd).
    { rewrite /G5 upd_eq. rewrite U9. apply add_vec_zero_l. }
    assert (HG5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G5)
      by (rewrite /G5; apply cr_regs3_caller; [exact Hcsa0 | exact Hmu1regs]).
    assert (Hq158 : add_vec_int (mword_of_int (CK + 0x156) : mword 64) 2
                    = mword_of_int (CK + 0x158)) by pcw.
    iEval (rewrite Hq158) in "Hpc".
    (* ===== +0x158 jal iunlockput(dp) ================================= *)
    assert (Htgu2 : add_vec (mword_of_int (CK + 0x158) : mword 64)
              (sign_extend' 64 (mword_of_int 2090826 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x158)) Rra
              (mword_of_int 2090826 : mword 21) G5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_158 with "Htext"). }
    iIntros (CIDG9 HqG9) "Hcg Hpc".
    iEval (rewrite Htgu2) in "Hpc".
    pose (G6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5) with G6.
    assert (HG6ra : G6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)
      by (rewrite /G6; apply upd_eq).
    assert (HG6a0 : G6 !!! Regidx Ra0 = ientry kd)
      by (rewrite /G6 upd_ne; [exact HG5a0 | nz]).
    assert (HG6regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G6)
      by (rewrite /G6; apply cr_regs3_caller; [exact Hcsra | exact HG5regs]).
    (* THE PARENT NEEDS NO RE-PARK: all three entries sit before +0x134, so
       its record, its bytes and its ledger are the ones the walk handed
       over -- and the walk has already undone its own failing append. *)
    iAssert (ic_loaded fsc_fs γi fsc_cov fsc_logst kd dind dp bmp)
      with "[Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop]" as "Hload".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists datap.
      iSplitR; [iPureIntro; exact Hiok |].
      iSplitR; [iPureIntro; exact Hrl |].
      iSplitR; [iPureIntro; rewrite -Hnib; exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact (cr_doc_of_live dp dp datap eq_refl Hnl0) |].
      iSplitR; [iPureIntro; exact Hduq |].
      iSplitL "Hdlnk"; [iExact "Hdlnk" |].
      iFrame "Hdiat Hmeta".
      iEval (rewrite /inode_map) in "Hmap".
      iDestruct "Hmap" as "[Haddrs Hind]". iFrame. }
    iPoseProof (cr_esc_acc γi kd Hkdlt with "Hesc")
      as "#Hescd".
    iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
    iDestruct (log_opS_named with "Hop") as (e1) "Hop".
    iDestruct (cpu_own_transport CIDG7 CIDG9 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the share it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ γi
              gtl γil γisl bmapstart inodestart nib size dev
              kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/4)%Qp) dind dp bmp
              n5 Sb5 false false false e1 _ _ pidv (DfracOwn (1/4)) dqb dqs
              G6 (K - 10)%nat eb b lks
              V ltac:(exact HKiup) eq_refl Hkdlt ltac:(discriminate) ltac:(discriminate)
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
              ltac:(exact Hipn5) Hj Hgs HG6a0 ltac:(lkbelow) Hglog eq_refl
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                    Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev Hiinum
                    Hivalid Hload Hshotl Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    all: try lkbelow.
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDGA HqGA mu2 n6 Sb6 w2)
      "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
       %Hsb6 %Hw6 %Hw6c %Hn6 Hop Hisl2 Htq2".
    iDestruct (log_tx_add icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htq1 Htq2") as "Htp".
    iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
    iDestruct (log_tx_full with "Htw") as "Htx".
    iEval (rewrite -Hglog) in "Htx".
    assert (Hpcu2 : ret_pc (G6 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x15c)) by (rewrite HG6ra; pcw).
    iEval (rewrite Hpcu2) in "Hpc".
    assert (Hmu2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                         (ientry kslot) ty major minor mu2)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor G6 mu2 Hcsu2 HG6regs).
    iDestruct ("Hppback" with "Hppid") as "Hpriv".
    (* ===== +0x15c c.ldsp s3,40(sp) : THE LAZY RESTORE ================ *)
    assert (HG7sp : mu2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (destruct Hmu2regs as (H2 & _); exact H2).
    assert (HT5 : add_vec (mu2 !!! Regidx csp_rs1)
                    (zero_extend' 64
                       (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HG7sp; apply cr_frm5).
    iEval (rewrite -HT5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x15c))
              (mword_of_int 5 : mword 6) Rs3 mu2 (K - 10)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] Hb5").
    { iApply (cri_15c with "Htext"). }
    iIntros (CIDGB HqGB) "Hcg Hpc Hb5".
    iEval (rewrite HT5) in "Hb5".
    pose (G7 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2).
    change (<[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2) with G7.
    assert (HG7regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) ty major minor G7)
      by exact (cr_regs3_s3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                  ty major minor mu2 _ eq_refl Hmu2regs).
    assert (HG7s2 : G7 !!! Regidx Rs2 = (mword_of_int 0 : mword 64)).
    { rewrite /G7 upd_ne; [| nz].
      destruct Hmu2regs as (_ & _ & _ & Hd18 & _). exact Hd18. }
    assert (Hq15e : add_vec_int (mword_of_int (CK + 0x15c) : mword 64) 2
                    = mword_of_int (CK + 0x15e)) by pcw.
    iEval (rewrite Hq15e) in "Hpc".
    (* ===== +0x15e c.j +0x70 ========================================== *)
    assert (Htg070f : add_vec (mword_of_int (CK + 0x15e) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0"))))
              = mword_of_int (CK + 0x70)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (CK + 0x15e))
              (sign_extend' 21
                 (concat_vec (mword_of_int 1929 : mword 11) ('b"0")))
              G7 (K - 10)%nat b
              ltac:(rewrite Htg070f; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_15e with "Htext"). }
    iIntros (CIDGC HqGC). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htg070f) in "Hpc".
    iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
    iPoseProof ("Htail" $! CIDGC) as "Ht".
    iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
    iApply ("Ht" $! G7 (m !!! Regidx Rs3 : mword 64) nfj with
              "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
    { exact (cr_tregs_of_regs3 m sp0 (ientry kd)
               (mword_of_int 0 : mword 64) ty major minor G7 HG7regs). }
    iIntros (CIDfin Hsfin mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport CIDGA CIDfin 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (iref_slots_combine with "Hisl1 Hisl2") as "Hisl".
    iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
    iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
              (mword_of_int 0 : mword 32) dp bmp n6 Sb6
              (1 + (1 + (ns - 2)))%nat
              with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv Hpath
                    Hbsl [%] Hisl [%] Hop [$Htx]").
    { exact Hcsf. }
    { exact (cr_slots_2 _ ns eq_refl Hns). }
    { split_and!.
      - exact (cr_sub3 _ _ _ _ Hsb4
                 (cr_sub_union_sing Sb4 (IBLOCK cinum inodestart))
                 (cr_sub2 _ _ _ Hsb5 Hsb6)).
      - pose proof (proj2 Hn6) as HB1. pose proof (proj2 Hn5) as HB2.
        pose proof (proj2 Hn4) as HB3. lia.
      - discriminate. }
    { iPureIntro. rewrite Ha0f. exact HG7s2. }
  Qed.


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
  Lemma cr_mkdir_half
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) (t : nat) :
    (K_create <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ fsc_cov ->
    ~ (bmapstart ∈ log_region_set fsc_logst) ->
    0 <= inodestart ->
    cov_below fsc_cov size ->
    bitmap_geom_ok fsc_cov fsc_logst bmapstart size ->
    InodeInv.ireg_blocks_ok inodestart nib fsc_cov fsc_logst ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view fsc_fs γd dev fsc_cov) -∗
    log_ctx γ bn fsc_fs fsc_cov fsc_logst dev -∗
    kalloc_env γa None -∗
    is_itable2 gtl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv γi fsc_fs inodestart nib -∗
    ireg_open -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDm : CpuId =>
      cr_mkdir_body γs j γl γu γd γk pd pav pu bn γ γi gtl γa γf γpr
                    bmapstart inodestart nib ninodes size dev
                    plen pfun pv ty major minor V u Sb ns pidv
                    dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                    kd qd gd γil γisl dind dn bm data nf nsl t CIDm).
  Proof.
    intros HK Hdev Hnib Hglog Hist Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
           Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Hpkc Hu Hns Hj Hgs
           Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hkd #Hpk #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl #Hesc
             #Hslks #Hiregi #Hiopen #Hprocs #Hdevi #Hgeom #Hdlk".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b lks HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDm Hsm).
    iIntros (Mx kslot q g gil gisl cinum dnc bmc datc n3 Sb3).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hnlmax %Hiok %Hdok
             %Hddix %Hduq %Hrl %Hnpname %Hnone %Hkslt %Hcpos %Hcinb %Hfresh
             %Hrl_datc %Htyc %Hciok %Hcdok
             %Hsb3 %Hmem3 %Hn3 %Hcorr".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks Hdview Hfview Htop #Hshotl Hfrzl Hkeep Hrud
             #Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
             Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop #Hcshot Hcfrz Hckeep Hruc Htoken
             Hsbn Hsbi Hsbs Hsbb #Hbmr Hppid Hppback Hpath Hbsl Hislr Hop Hdirty
             Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    (* THE HELD SET IS EMPTY, AND SAID SO ONCE -- create's contract carries
       no order premise because it needs none, and [lkbelow] closes each
       callee's bound from this EQUATION.  Keep the equation rather than
       substituting; [lks] is spelled by name in the bodies below. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    pose proof HXregs as HXr.
    destruct HXr as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & Xthr).
    destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    iDestruct (cr_esc_acc γi kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (cr_esc_acc γi kd Hkdlt with "Hesc")
      as "#Hescd".
    (* ---- the two rodata name windows, both PERSISTENT ---- *)
    assert (Hn3lo : (8 <= n3)%nat) by exact (proj1 Hn3).
    assert (Hn3u : (n3 <= u)%nat) by exact (proj2 Hn3).
    (* the nameiparent correlation, in the form the ledger lemmas take *)
    assert (Hcorr' : bool_decide (bmapstart ∈ Sb3) = false -> (9 <= n3)%nat).
    { intro Hf. destruct Hcorr as [Hin | Hge]; [| exact Hge].
      exfalso. rewrite (cr_crb_claim Sb3 bmapstart Hin) in Hf. discriminate. }
    (* ---- the parent's own [inode_ok] readings, once ---- *)
    assert (Hdz : bv_unsigned (di_type dn) = T_DIR_z)
      by (rewrite Htydir; vm_compute; reflexivity).
    assert (Hbmwf : blkmap_wf fsc_cov fsc_logst bm) by exact (proj1 Hiok).
    assert (Hbmcov : bm_covers bm (bv_unsigned (di_size dn)))
      by exact (proj1 (proj2 Hiok)).
    assert (Hdaddr : di_addrs dn = bm_cells bm)
      by exact (proj1 (proj2 (proj2 Hiok))).
    assert (Htynzd : bv_unsigned (di_type dn) <> 0)
      by exact (proj1 (proj2 (proj2 (proj2 Hiok)))).
    assert (Hszcap : bv_unsigned (di_size dn)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
    assert (Hholes : blk_holes_zero bm data)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
    assert (Hsized : inode_sized data)
      by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hiok)))))).
    assert (Hsz31 : bv_unsigned (di_size dn) < 2 ^ 31)
      by (unfold MAXFILE, BSIZE in Hszcap; simpl in Hszcap; lia).
    (* ---- and the CHILD's, at the record the three [sh]s left ---- *)
    assert (Hcty : di_type (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                   = SpecDirlookup.T_DIR)
      by (rewrite cr_setf_type Htyc; exact Htdir).
    assert (Hctynz : bv_unsigned
                       (di_type (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16))) <> 0)
      by (rewrite Hcty; vm_compute; discriminate).
    assert (Hcdz : bv_unsigned
                     (di_type (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16))) = T_DIR_z)
      by (rewrite Hcty; vm_compute; reflexivity).
    assert (Hciok' : inode_ok fsc_cov fsc_logst
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                       bmc datc)
      by exact (cr_setf_inode_ok fsc_cov fsc_logst dnc bmc datc major minor _ Hciok).
    assert (Hcdok' : dir_ok nib
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                       datc)
      by exact (cr_setf_dir_ok nib dnc datc major minor _ Hcdok).
    assert (Hcsz0 : bv_unsigned
                      (di_size (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16))) = 0)
      by (rewrite cr_setf_size; exact (proj1 (proj2 Hfresh))).
    assert (Hcnrec0 : dir_nrec (bv_unsigned
              (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16)))) = 0%nat)
      by (rewrite Hcsz0; exact cr_nrec_0).
    assert (Hck0 : dir_slot datc 0 = 0%nat) by apply cr_slot_0.
    assert (Hcbmwf : blkmap_wf fsc_cov fsc_logst bmc) by exact (proj1 Hciok').
    assert (Hcbmcov : bm_covers bmc (bv_unsigned
              (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16)))))
      by exact (proj1 (proj2 Hciok')).
    assert (Hcaddr : di_addrs (cr_setf dnc major minor
                                 (mword_of_int 1 : mword 16)) = bm_cells bmc)
      by exact (proj1 (proj2 (proj2 Hciok'))).
    assert (Hccap : bv_unsigned (di_size (cr_setf dnc major minor
                       (mword_of_int 1 : mword 16)))
                    <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
      by (rewrite Hcsz0; unfold MAXFILE, BSIZE; simpl; lia).
    assert (Hcholes : blk_holes_zero bmc datc)
      by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok')))))).
    assert (Hcsized : inode_sized datc)
      by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hciok')))))).
    assert (Hcsz31 : bv_unsigned (di_size (cr_setf dnc major minor
                       (mword_of_int 1 : mword 16))) < 2 ^ 31)
      by (rewrite Hcsz0; lia).
    (* the halfword bridges: both inums fit in sixteen bits *)
    assert (Hc16 : bv_unsigned cinum < 2 ^ 16) by lia.
    assert (Hcl16 : bv_unsigned (cr_low16 cinum) = bv_unsigned cinum)
      by exact (cr_low16_unsigned cinum Hc16).
    assert (Hd16 : bv_unsigned dind < 2 ^ 16) by lia.
    assert (Hdl16 : bv_unsigned (cr_low16 dind) = bv_unsigned dind)
      by exact (cr_low16_unsigned dind Hd16).
    assert (Hcl16b : bv_unsigned (cr_low16 cinum) < 16 * Z.of_nat nib)
      by (rewrite Hcl16; exact Hcinb).
    assert (Hdl16b : bv_unsigned (cr_low16 dind) < 16 * Z.of_nat nib)
      by (rewrite Hdl16; exact Hdib).
    (* the FIRST link's window is DIRECT and its slot is zero *)
    assert (Hind0 : SpecBmap.bmap_ind ((16 * 0) `div` BSIZE)%nat = false)
      by (vm_compute; reflexivity).
    assert (Hind1 : SpecBmap.bmap_ind ((16 * 1) `div` BSIZE)%nat = false)
      by (vm_compute; reflexivity).
    (* the fresh child's cell zero *)
    assert (Hcell0 : bv_unsigned (blkmap_get bmc 0) = 0).
    { apply cr_fresh_cell0.
      - rewrite -Hcaddr cr_setf_addrs. exact (proj1 (proj2 (proj2 Hfresh))).
      - exact (blkmap_wf_dir_len fsc_cov fsc_logst bmc Hcbmwf). }
    (* ===== +0xf8 lw a2,4(s3) : the child's inum ====================== *)
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0xf8)) Ra2 Rs3
              (mword_of_int 4 : mword 12) Mx (K - 10)%nat cinum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
    { iApply (cri_0f8 with "Htext"). }
    { iEval (rgne; rewrite X19). iExact "Hciinum". }
    iIntros (CIDm1 Hqm1) "Hcg Hpc Hciinum".
    iEval (rgne; rewrite X19) in "Hciinum".
    pose (Z1 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 cinum : mword 64)]> Mx).
    change (<[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 cinum : mword 64)]> Mx) with Z1.
    assert (HZ1a2 : Z1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z1; apply upd_eq).
    assert (HZ1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z1)
      by (rewrite /Z1; apply cr_regs3_caller; [exact Hcsa2 | exact HXregs]).
    assert (Hq0fc : add_vec_int (mword_of_int (CK + 0xf8) : mword 64) 4
                    = mword_of_int (CK + 0xfc)) by pcw.
    iEval (rewrite Hq0fc) in "Hpc".
    (* ===== +0xfc auipc a1,0x3 ======================================= *)
    iApply (wp_auipc_s_sconf (mword_of_int (CK + 0xfc)) Ra1
              (mword_of_int 3 : mword 20) Z1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_0fc with "Htext"). }
    iIntros (CIDm2 Hqm2) "Hcg Hpc".
    pose (Z2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (CK + 0xfc) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> Z1).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (CK + 0xfc) : mword 64)
                     (auipc_off (mword_of_int 3 : mword 20)))]> Z1) with Z2.
    assert (HZ2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z2)
      by (rewrite /Z2; apply cr_regs3_caller; [exact Hcsa1 | exact HZ1regs]).
    assert (HZ2a2 : Z2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z2 upd_ne; [exact HZ1a2 | nz]).
    assert (Hq100 : add_vec_int (mword_of_int (CK + 0xfc) : mword 64) 4
                    = mword_of_int (CK + 0x100)) by pcw.
    iEval (rewrite Hq100) in "Hpc".
    (* ===== +0x100 addi a1,a1,2450 : a1 = &"." ======================= *)
    iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x100)) Ra1 Ra1
              (mword_of_int 2348 : mword 12) Z2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_100 with "Htext"). }
    iIntros (CIDm3 Hqm3) "Hcg Hpc".
    pose (Z3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Z2 Ra1)
                     (sign_extend' 64 (mword_of_int 2348 : mword 12)))]> Z2).
    change (<[Regidx Ra1 := regval_into_reg
                  (add_vec (rget Z2 Ra1)
                     (sign_extend' 64 (mword_of_int 2348 : mword 12)))]> Z2) with Z3.
    assert (HZ3a1 : Z3 !!! Regidx Ra1 = mword_of_int cr_dot_addr).
    { rewrite /Z3 upd_eq. rewrite rget_ne;
        [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
      rewrite /Z2 upd_eq. unfold cr_dot_addr. pcw. }
    assert (HZ3a2 : Z3 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z3 upd_ne; [exact HZ2a2 | nz]).
    assert (HZ3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z3)
      by (rewrite /Z3; apply cr_regs3_caller; [exact Hcsa1 | exact HZ2regs]).
    assert (HZ3s3 : Z3 !!! Regidx Rs3 = ientry kslot)
      by (destruct HZ3regs as (_ & _ & _ & _ & H & _); exact H).
    assert (Hq104 : add_vec_int (mword_of_int (CK + 0x100) : mword 64) 4
                    = mword_of_int (CK + 0x104)) by pcw.
    iEval (rewrite Hq104) in "Hpc".
    (* ===== +0x104 c.mv a0,s3 : the CHILD ============================ *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x104)) Ra0 Rs3 Z3
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cri_104 with "Htext"). }
    iIntros (CIDm4 Hqm4) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (Z4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Z3 !!! Regidx Rs3))]> Z3).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Z3 !!! Regidx Rs3))]> Z3) with Z4.
    assert (HZ4a0 : Z4 !!! Regidx Ra0 = ientry kslot).
    { rewrite /Z4 upd_eq. rewrite HZ3s3. apply add_vec_zero_l. }
    assert (HZ4a1 : Z4 !!! Regidx Ra1 = mword_of_int cr_dot_addr)
      by (rewrite /Z4 upd_ne; [exact HZ3a1 | nz]).
    assert (HZ4a2 : Z4 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
      by (rewrite /Z4 upd_ne; [exact HZ3a2 | nz]).
    assert (HZ4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z4)
      by (rewrite /Z4; apply cr_regs3_caller; [exact Hcsa0 | exact HZ3regs]).
    assert (Hq106 : add_vec_int (mword_of_int (CK + 0x104) : mword 64) 2
                    = mword_of_int (CK + 0x106)) by pcw.
    iEval (rewrite Hq106) in "Hpc".
    (* ===== +0x106 jal dirlink(ip, ".", ip->inum) ==================== *)
    assert (Htgd1 : add_vec (mword_of_int (CK + 0x106) : mword 64)
              (sign_extend' 64 (mword_of_int 2092330 : mword 21))
              = mword_of_int KernelSyms.dirlink) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x106)) Rra
              (mword_of_int 2092330 : mword 21) Z4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_106 with "Htext"). }
    iIntros (CIDm5 Hqm5) "Hcg Hpc".
    iEval (rewrite Htgd1) in "Hpc".
    pose (Z5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)]> Z4).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)]> Z4) with Z5.
    assert (HZ5ra : Z5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x106) : mword 64) 4)
      by (rewrite /Z5; apply upd_eq).
    assert (HZ5a0 : Z5 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /Z5 upd_ne; [exact HZ4a0 | nz]).
    assert (HZ5a1 : Z5 !!! Regidx Ra1 = mword_of_int cr_dot_addr)
      by (rewrite /Z5 upd_ne; [exact HZ4a1 | nz]).
    assert (HZ5a2 : Z5 !!! Regidx Ra2
                    = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
    { rewrite /Z5 upd_ne; [| nz]. rewrite HZ4a2.
      exact (cr_a2_low16 cinum Hc16). }
    assert (HZ5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor Z5)
      by (rewrite /Z5; apply cr_regs3_caller; [exact Hcsra | exact HZ4regs]).
    iPoseProof (cr_dot_window_kt1 (Z5 !!! Regidx Ra1)
                  ltac:(exact HZ5a1) with "Hkd") as "Hdotw".
    assert (Hns3 : (1 + (ns - 3))%nat = (ns - 2)%nat) by exact (cr_ns_3 ns Hns).
    iEval (rewrite -Hns3 iref_slots_op) in "Hislr".
    iDestruct "Hislr" as "[Hislk Hislrr]".
    iDestruct (cpu_own_transport CIDm CIDm5 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iEval (rewrite /inode_map) in "Hcmap".
    iDestruct "Hcmap" as "[Hcaddrs Hcind]".
    iAssert (inode_map fsc_fs (ientry kslot) bmc) with "[Hcaddrs Hcind]"
      as "Hcmap".
    { rewrite /inode_map. iFrame. }
    (* THE BORROWED TICKET LIST FOR THE CHILD'S OWN [dirlink], hoisted here
       because the call now takes it (§7.5.6, row 3).  The body hands the
       child's ledger at [dnc]; [cr_setf] moves only [nlink]/[major]/[minor]
       and at a FRESH child the big-op is empty either way, so it is rebuilt
       rather than transported.  It comes back verbatim on both arms. *)
    iAssert (dlinks fsc_fs (bv_unsigned cinum)
               (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)%I
      as "Hcdlnk0i".
    assert (Hc1dokE : FsStateInode.ent_dset_ok (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) ∅)
      by (intros tz Htz; exfalso; exact (not_elem_of_empty tz Htz)).
    assert (Hc1xactE : FsStateInode.node_exact (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) ∅).
    { intros _.
      assert (Hfn1 : fn_nlink (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = 1%nat)
        by (rewrite /fn_nlink era_node_rec cr_setf_nlink;
            vm_compute; reflexivity).
      rewrite /fn_orphan Hfn1
        (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) size_empty //. }
    { rewrite /dlinks /FsStateInode.ent_toks_x. iExists ∅.
      iSplitR; [iPureIntro; exact Hc1dokE |].
      iSplitR; [iPureIntro; exact Hc1xactE |].
      iApply FsStateEra.ent_toks_era_nrec0.
      rewrite cr_setf_size; exact Hcnrec0. }
    (* THE LICENCE'S LEFT DISJUNCT HERE IS [ip->nlink = 1], flushed by the
       three [sh]s at +0xfc..+0x102 before this call (§7.5.6, row 3): the
       record the contract runs at IS [cr_setf dnc _ _ 1]. *)
    (* THE SHARE DIRLINK'S OWN [iput] MAY NEED (durable-disk B''-tx5).  Inside
       the armed span this walk holds no free residue -- a quarter is in each
       escrow and the registry's arm has the half -- so it shrinks the
       PARENT'S arm by an eighth for the duration of the call and grows it
       back at the return.  The eighth is enough: what iput's windows need is
       a POSITIVE share of an OPEN transaction, and any is. *)
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htxs)".
    iModIntro. iEval (rewrite -Hglog) in "Htxs".
    iApply (DLK.wp_dirlink_gen γs j γl γu γd γk pd pav pu bn γ γi
              gtl γa γf γpr inodestart nib bmapstart size dev
              (ientry kslot) cinum bmc datc
              (cr_setf dnc major minor (mword_of_int 1 : mword 16))
              (cr_setf dnc major minor (mword_of_int 1 : mword 16))
              cr_dot_f (cr_low16 cinum) n3 Sb3
              _ _
              pidv (DfracOwn (1/4)) (DfracOwn (1/2)) DfracDiscarded dqs
              dqb dqbs (DfracOwn (1/2))
              Z5 (K - 10)%nat eb b lks
              V ltac:(exact HKdlk) Hcty Hcbmcov Hccap
              ltac:(exact (Hcdok' Hcdz))
              ltac:(left; rewrite cr_setf_nlink; vm_compute; discriminate)
              ltac:(apply dir_orphan_clean_live;
                    rewrite cr_setf_nlink; vm_compute; discriminate)
              ltac:(exact (di_type_stable_refl _))
              ltac:(exact (di_nlink_stable_refl _ Hctynz))
              Hlg Hcbmwf Hcholes Hcaddr Hcsz31 Hist0 Hcblk Hcblog Hcinb
              Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
              ltac:(rewrite Hcnrec0 Hck0; rewrite Hind0;
                    exact (cr_alloc_dlneed n3 _ false Hn3lo))
              Hj Hgs HZ5a0 HZ5a2 Heb ltac:(lkbelow) Hglog
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                    Hcidev Hciinum Hcmeta Hcmap Hcblocks Hdotw Hsbi Hsbs Hsbb
                    Hbmr Hiregi Hiopen Hcdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                    Hitb2 Hitbl Hesc Hslks Hislk Hcdlnk0i Hop Htxs").
    all: try lkbelow.
    iIntros (CIDd1 Hsd1 md1 found1 bm1 dat1 dc1 dc01 n4 Sb4 tot1)
      "%Hcsd1 Hcg Hcnt Hpc Hcidev Hciinum Hcmeta Hcmap Hcblocks Hdotw1 Hsbi
       Hsbs Hsbb Hcdiat Hppid Hbsl Hislk Hcdlnk0 %Hn4c %Hsb4 %Hdlp1 %Hfd1
       Hop Htxs %Hcap1 %Hsizedp1 %Harm1".
    iEval (rewrite Hglog) in "Htxs".
    iApply fupd_wp.
    iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htxs")
      as "(Hivalid & Hdep)".
    iModIntro.

    (* the borrow comes back as the PAIR; open it here, because the deposit
       below files the child's ["."] entry among its own units *)
    iRename "Hcdlnk0" into "Hcdlnk0P".
    iDestruct (dlinks_open with "Hcdlnk0P")
      as "(%Dc & [%HcdokD %HcxactD] & Hcetk)".
    assert (Hpcd1 : ret_pc (Z5 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0x10a)) by (rewrite HZ5ra; pcw).
    iEval (rewrite Hpcd1) in "Hpc".
    assert (Hmd1regs : cr_regs3 m sp0 (ientry kd)
                         (mword_of_int 0 : mword 64) (ientry kslot)
                         ty major minor md1)
      by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                  (ientry kslot) ty major minor Z5 md1 Hcsd1 HZ5regs).
    assert (Htg146a : add_vec (mword_of_int (CK + 0x10a) : mword 64)
              (sign_extend' 64 (mword_of_int 60 : mword 13))
              = mword_of_int (CK + 0x146)) by pcw.
    (* the FOUND arm is refuted: an EMPTY directory has no records *)
    destruct found1.
    { exfalso. destruct Harm1 as (Hfst & _). apply Hfst.
      rewrite Hcnrec0. apply cr_first_0. }
    destruct Harm1 as (_ & Hwf1 & Hholes1 & Haddr1 & Hsz311 &
                       Hcov1 & Hdc1 & Hdc01 & Htot161 & Hrng1 & Hbl1).
    destruct (Hdlp1 eq_refl) as (Hspend1 & Hatom1 & Hmem1).
    rewrite Hcnrec0 Hck0 in Hspend1, Hmem1, Hrng1, Hdc1.
    (* the region's record IS the metadata one: the first link's writei ran
       its trailing [iupdate] ([dl16_post]'s preservation clause, at the
       [eq_refl] the caller's single [dinode_at] supplies). *)
    assert (Hdceq1 : dc01 = dc1) by exact (Hdc01 eq_refl).
    subst dc01.
    (* ---- the record the first link left, read back off its range clause *)
    assert (Hc1ty0 : di_type dc1
                     = di_type (cr_setf dnc major minor
                                  (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1mj0 : di_major dc1
                     = di_major (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1mn0 : di_minor dc1
                     = di_minor (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1nl0 : di_nlink dc1
                     = di_nlink (cr_setf dnc major minor
                                   (mword_of_int 1 : mword 16)))
      by (rewrite Hdc1; reflexivity).
    assert (Hc1ty : di_type dc1 = ty)
      by (rewrite Hc1ty0 cr_setf_type; exact Htyc).
    assert (Hc1mj : di_major dc1 = major)
      by (rewrite Hc1mj0; apply cr_setf_major).
    assert (Hc1mn : di_minor dc1 = minor)
      by (rewrite Hc1mn0; apply cr_setf_minor).
    assert (Hc1nl : di_nlink dc1 = (mword_of_int 1 : mword 16))
      by (rewrite Hc1nl0; apply cr_setf_nlink).
    assert (Hc1tyd : di_type dc1 = SpecDirlookup.T_DIR)
      by (rewrite Hc1ty; exact Htdir).
    assert (Hc1tynz : bv_unsigned (di_type dc1) <> 0)
      by (rewrite Hc1ty Htdir; vm_compute; discriminate).
    assert (Hc1iok : inode_ok fsc_cov fsc_logst dc1 bm1 dat1).
    { rewrite /inode_ok. split_and!.
      - exact Hwf1.
      - exact Hcov1.
      - exact Haddr1.
      - exact Hc1tynz.
      - exact (Hcap1 Hccap).
      - exact Hholes1.
      - exact (Hsizedp1 Hcsized). }
    assert (Hc1szmax : bv_unsigned (di_size dc1)
              = Z.max (bv_unsigned (di_size (cr_setf dnc major minor
                          (mword_of_int 1 : mword 16))))
                  (Z.of_nat ((16 * 0)%nat + tot1)))
      by (rewrite Hdc1;
          exact (cr_wi_size_max _ bm1 (16 * 0)%nat tot1 ltac:(lia))).
    assert (Hc1dok : dir_ok nib dc1 dat1)
      by exact (dir_ok_dirlink nib
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                  dc1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                  0%nat 0%nat tot1 (eq_sym Hcnrec0) (eq_sym Hck0) Htot161
                  Hcl16b Hc1ty0 Hc1szmax Hrng1 Hcdok').
    (* UNIQUENESS across the same link.  The entry is a FRESH child, whose
       size is 0 and which therefore has no records to collide; the guard
       [dir_first datc 0 _ = None] is free for the same reason. *)
    assert (Hc1duq : dir_uniq dc1 dat1)
      by exact (dir_uniq_dirlink
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16))
                  dc1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                  0%nat 0%nat tot1 (eq_sym Hcnrec0) (eq_sym Hck0) Hatom1
                  (bname_length_le 14 cr_dot_f) (cut_nul_nonul _)
                  Hc1ty0 Hc1szmax Hrng1 (cr_first_0 datc (bname 14 cr_dot_f))
                  (dir_uniq_size_zero _ datc Hcsz0)).
    (* FAIL ENTRY 1's content clause: on the short arm the ["."] write left
       fewer than sixteen bytes, so the child's size is [tot1 < 16] and it
       has NO records at all -- [dir_dots_only] is vacuous at [nrec = 0].
       Stated guarded so it can sit above the [Hbl1] split, beside the
       record facts the two arms share. *)
    assert (Hc1dots : (tot1 < 16)%nat -> dir_dots_only dc1 dat1).
    { intros Hlt k Hk. exfalso.
      assert (Hnr0 : dir_nrec (bv_unsigned (di_size dc1)) = 0%nat).
      { rewrite Hc1szmax Hcsz0. unfold dir_nrec.
        rewrite Z.div_small; [reflexivity | clear -Hlt; lia]. }
      rewrite Hnr0 in Hk. clear -Hk. lia. }
    (* the ledger, at the two figures this arm's exits are stated at *)
    rewrite (cr_crb_claim Sb3 (IBLOCK cinum inodestart) Hmem3) Hind0
      in Hspend1.
    destruct Hbl1 as [[Ha0z1 Ht161] | [Ha0m1 Htlt1]].
    - (* =============================================================== *)
      (*  the FIRST link went in whole: fall through to [dirlink(ip,"..")] *)
      (* =============================================================== *)
      (* ===== +0x10a bltz a0 : FALLS THROUGH ========================= *)
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x10a))
                (mword_of_int 60 : mword 13) Ra0 md1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Ha0z1; exact cr_bltz_zero)
                with "Hcg Hpc []").
      { iApply (cri_10a with "Htext"). }
      iIntros (CIDe1 Hqe1) "Hcg Hpc".
      assert (Hq10e : add_vec_int (mword_of_int (CK + 0x10a) : mword 64) 4
                      = mword_of_int (CK + 0x10e)) by pcw.
      iEval (rewrite Hq10e) in "Hpc".
      (* THE ["."] RECORD IS A SELF RECORD,
         so the entry it creates is TOKENLESS and no unit is spent
         (durable-disk 2b-inode-5, [FsStateInode.ent_tokenless]). *)
      (* THE ["."] ENTRY OWES A FRAGMENT NOW (lane G5).  The fill minted
         TWO -- this one and the one [dirlink(dp, name, ip)] files -- and
         this one is what PINS the child's [".."] target once the next
         [dirlink] writes it ([FsStateInode.ent_ty_ok]'s dot arm).  Its
         clause is VACUOUS here: the child has no records at all, so its
         [fn_dd] is [None]. *)
      assert (Htdirc : ty = SpecDirlookup.T_DIR).
      { apply bv_eq. rewrite -Htyc -(cr_setf_type dnc major minor
          (mword_of_int 1 : mword 16)) Hcdz. vm_compute. reflexivity. }
      assert (Hcfn1 : fn_nlink (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = 1%nat)
        by (rewrite /fn_nlink era_node_rec cr_setf_nlink;
            vm_compute; reflexivity).
      assert (HDc : Dc = ∅).
      { pose proof (HcxactD ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                                 apply bool_decide_eq_true; exact Hcdz)) as Hex.
        rewrite Hcfn1 /fn_orphan Hcfn1
          (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) in Hex.
        apply leibniz_equiv, size_empty_inv. clear -Hex. lia. }
      assert (Hcents0 : dir_entries (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = ∅).
      { rewrite /dir_entries.
        destruct (fn_is_dir (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)); [| reflexivity].
        change (fn_nrec (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc))
          with (dir_nrec (bv_unsigned (di_size (cr_setf dnc major minor (mword_of_int 1 : mword 16))))).
        rewrite cr_setf_size Hcnrec0 dir_view_nil //. }
      assert (Hcddnone : FsStateInode.fn_dd (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc) = None)
        by (rewrite /FsStateInode.fn_dd Hcents0 lookup_empty //).
      iEval (rewrite (cr_delta_dir ty Htdirc)
                     FsStateLink.link_toks_reps_S FsStateLink.link_reps_1)
        in "Htoken".
      iDestruct "Htoken" as "[Htokdot Htoken]".
      iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                   (cr_setf dnc major minor (mword_of_int 1 : mword 16)) dc1
                   bmc bm1 datc dat1 (cr_low16 cinum) (bname 14 cr_dot_f)
                   0%nat 0%nat tot1 Dc false (eq_sym Hcnrec0) (eq_sym Hck0)
                   Hatom1
                   (bname_length_le 14 cr_dot_f) (cut_nul_nonul _)
                   Hcdz Hc1ty0 Hc1nl0 Hc1szmax Hrng1
                   (cr_first_0 datc (bname 14 cr_dot_f))
                   Hcholes Hholes1 Hccap (Hcap1 Hccap)
                   ltac:(rewrite HDc; apply not_elem_of_empty)
                   ltac:(rewrite ProofCreateParts.cr_dot_name /DOTDOT;
                         intros Hcdd; discriminate Hcdd)
                   with "Hcetk [Htokdot]") as "Hcetk1".
      { iEval (rewrite -Hcl16) in "Htokdot".
        iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                  (FsStateInode.fn_dd (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc))
                  (fn_orphan (era_node (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc datc)) false
                  (bname 14 cr_dot_f) (bv_unsigned (cr_low16 cinum))
                  (cr_ity ty (bv_unsigned dind))
                  ltac:(rewrite Hcddnone;
                        apply FsStateInode.ent_ty_ok_dot_none)
                  with "Htokdot"). }
      assert (Hc1dok' : FsStateInode.ent_dset_ok (era_node dc1 bm1 dat1) Dc)
        by (rewrite HDc; intros tz Htz;
          exfalso; exact (not_elem_of_empty tz Htz)).
      assert (Hc1xact' : FsStateInode.node_exact (era_node dc1 bm1 dat1) Dc).
      { intros _.
        assert (Hfn : fn_nlink (era_node dc1 bm1 dat1) = 1%nat)
          by (rewrite /fn_nlink era_node_rec Hc1nl; vm_compute; reflexivity).
        rewrite Hfn /fn_orphan Hfn
          (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) HDc
          size_empty //. }
      iDestruct (dlinks_intro _ _ _ _ _ Dc Hc1dok' Hc1xact'
                   with "Hcetk1") as "Hcdlnk1".
      (* THE FIRST LINK ALLOCATED, and the whole arm's ledger rests on it *)
      assert (Hc1sz : bv_unsigned (di_size dc1) = 16).
      { rewrite Hc1szmax Hcsz0 Ht161. lia. }
      assert (Hal1 : SpecBmap.bmap_alloced bmc bm1 0 = true).
      { apply cr_alloced_first; [exact Hcell0 |].
        apply (bm_covers_get bm1 (bv_unsigned (di_size dc1)) 0%nat Hcov1
                 ltac:(unfold MAXFILE; lia)).
        rewrite Hc1sz. unfold BSIZE. lia. }
      assert (Hal1' : SpecBmap.bmap_alloced bmc bm1 (16 * 0 / BSIZE)%nat
                      = true) by exact Hal1.
      rewrite Hal1' in Hspend1.
      assert (Hbmem4 : bmapstart ∈ Sb4)
        by exact (proj2 (proj2 (Hmem1 ltac:(lia))) Hal1).
      assert (Hcmem4 : IBLOCK cinum inodestart ∈ Sb4)
        by exact (proj1 (proj2 (Hmem1 ltac:(lia)))).
      assert (Hdmem4 : wi_tgt_blk bm1 (16 * 0)%nat ∈ Sb4)
        by exact (proj1 (Hmem1 ltac:(lia))).
      assert (Hcrb2 : bool_decide (bmapstart ∈ Sb4) = true)
        by exact (cr_crb_claim Sb4 bmapstart Hbmem4).
      (* the SECOND link's slot: record zero is LIVE at the child's inum *)
      assert (Hwin1 : forall jj, (jj < 16)%nat ->
                file_byte dat1 (16 * 0 + jj)%nat
                = dirent_bytes (de_of_name (cr_low16 cinum)
                                  (bname 14 cr_dot_f)) !!! jj).
      { intros jj Hjj. rewrite (Hrng1 (16 * 0 + jj)%nat).
        rewrite decide_True; [| lia].
        (* optimization.md: [replace ... by lia] pays the whole ambient
           context in its side proof; the identity needs [jj] alone. *)
        replace (16 * 0 + jj - 16 * 0)%nat with jj by (clear -jj; lia).
        reflexivity. }
      destruct (cr_dot_record dat1 (cr_low16 cinum) Hwin1)
        as [Hd1inum Hd1name].
      assert (Hd1live : dir_inum dat1 0 <> bv_0 16).
      { rewrite Hd1inum. intro Hc.
        assert (Hz : bv_unsigned (cr_low16 cinum) = 0)
          by (rewrite Hc; vm_compute; reflexivity).
        rewrite Hcl16 in Hz. pose proof (proj1 Hcpos) as Hp. lia. }
      assert (Hc1nrec : dir_nrec (bv_unsigned (di_size dc1)) = 1%nat)
        by (rewrite Hc1sz; exact cr_nrec_16).
      assert (Hc1k0 : dir_slot dat1 1 = 1%nat) by exact (cr_slot_1 dat1 Hd1live).
      (* THE CHILD'S ["."] ENTRY, as a fact about its ENTRY VIEW (lane G5).
         Every fail entry below this point has to reach through the child's
         payload for the fragment that record owes -- the [ip->nlink = 0]
         flush spends the WHOLE pile the fill minted, and one of its units
         is filed here -- so the reading is stated once, in the arm that
         wrote the record. *)
      assert (Hc1dzc : bv_unsigned (di_type dc1) = T_DIR_z)
        by (rewrite Hc1ty Htdirc; vm_compute; reflexivity).
      assert (Horph1c : fn_orphan (era_node dc1 bm1 dat1) = false).
      { rewrite /fn_orphan /fn_nlink era_node_rec Hc1nl.
        apply bool_decide_eq_false. clear. vm_compute. discriminate. }
      assert (Hdot1c : dir_entries (era_node dc1 bm1 dat1) !! DOT
                       = Some (bv_unsigned cinum)).
      { rewrite (dir_entries_era_node dc1 bm1 dat1 Hholes1 (Hcap1 Hccap))
          (bool_decide_eq_true_2 _ Hc1dzc) Hc1nrec -Hcl16 -Hd1inum.
        replace DOT with (dir_bname dat1 0%nat)
          by (rewrite /dir_bname Hd1name DOT_dot_name; reflexivity).
        exact (dir_view_live dat1 1%nat 0%nat
                 ltac:(rewrite -Hc1nrec; exact (Hc1duq Hc1dzc))
                 ltac:(clear; apply Nat.lt_0_succ) Hd1live). }
      (* ===== +0x10e c.lw a2,4(s1) : the PARENT's inum ================ *)
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x10e)) Ra2 Rs1
                (mword_of_int 4 : mword 12) md1 (K - 10)%nat dind b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hiinum]").
      { iApply (cri_10e with "Htext"). }
      { iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd1regs)))). iExact "Hiinum". }
      iIntros (CIDe2 Hqe2) "Hcg Hpc Hiinum".
      iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd1regs)))) in "Hiinum".
      pose (Y1 := <[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 dind : mword 64)]> md1).
      change (<[Regidx Ra2 := regval_into_reg
                    (sign_extend' 64 dind : mword 64)]> md1) with Y1.
      assert (HY1a2 : Y1 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y1; apply upd_eq).
      assert (HY1regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y1)
        by (rewrite /Y1; apply cr_regs3_caller; [exact Hcsa2 | exact Hmd1regs]).
      assert (Hq110 : add_vec_int (mword_of_int (CK + 0x10e) : mword 64) 2
                      = mword_of_int (CK + 0x110)) by pcw.
      iEval (rewrite Hq110) in "Hpc".
      (* ===== +0x110 auipc a1,0x3 ==================================== *)
      iApply (wp_auipc_s_sconf (mword_of_int (CK + 0x110)) Ra1
                (mword_of_int 3 : mword 20) Y1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_110 with "Htext"). }
      iIntros (CIDe3 Hqe3) "Hcg Hpc".
      pose (Y2 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (mword_of_int (CK + 0x110) : mword 64)
                       (auipc_off (mword_of_int 3 : mword 20)))]> Y1).
      change (<[Regidx Ra1 := regval_into_reg
                    (add_vec (mword_of_int (CK + 0x110) : mword 64)
                       (auipc_off (mword_of_int 3 : mword 20)))]> Y1) with Y2.
      assert (HY2a2 : Y2 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y2 upd_ne; [exact HY1a2 | nz]).
      assert (HY2regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y2)
        by (rewrite /Y2; apply cr_regs3_caller; [exact Hcsa1 | exact HY1regs]).
      assert (Hq114 : add_vec_int (mword_of_int (CK + 0x110) : mword 64) 4
                      = mword_of_int (CK + 0x114)) by pcw.
      iEval (rewrite Hq114) in "Hpc".
      (* ===== +0x114 addi a1,a1,2438 : a1 = &".." ==================== *)
      iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x114)) Ra1 Ra1
                (mword_of_int 2336 : mword 12) Y2 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_114 with "Htext"). }
      iIntros (CIDe4 Hqe4) "Hcg Hpc".
      pose (Y3 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (rget Y2 Ra1)
                       (sign_extend' 64 (mword_of_int 2336 : mword 12)))]> Y2).
      change (<[Regidx Ra1 := regval_into_reg
                    (add_vec (rget Y2 Ra1)
                       (sign_extend' 64 (mword_of_int 2336 : mword 12)))]> Y2) with Y3.
      assert (HY3a1 : Y3 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr).
      { rewrite /Y3 upd_eq. rewrite rget_ne;
          [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
        rewrite /Y2 upd_eq. unfold cr_dotdot_addr. pcw. }
      assert (HY3a2 : Y3 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y3 upd_ne; [exact HY2a2 | nz]).
      assert (HY3regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y3)
        by (rewrite /Y3; apply cr_regs3_caller; [exact Hcsa1 | exact HY2regs]).
      assert (HY3s3 : Y3 !!! Regidx Rs3 = ientry kslot)
        by (destruct HY3regs as (_ & _ & _ & _ & H & _); exact H).
      assert (Hq118 : add_vec_int (mword_of_int (CK + 0x114) : mword 64) 4
                      = mword_of_int (CK + 0x118)) by pcw.
      iEval (rewrite Hq118) in "Hpc".
      (* ===== +0x118 c.mv a0,s3 : the CHILD ========================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x118)) Ra0 Rs3 Y3
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cri_118 with "Htext"). }
      iIntros (CIDe5 Hqe5) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (Y4 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Y3 !!! Regidx Rs3))]> Y3).
      change (<[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Y3 !!! Regidx Rs3))]> Y3) with Y4.
      assert (HY4a0 : Y4 !!! Regidx Ra0 = ientry kslot).
      { rewrite /Y4 upd_eq. rewrite HY3s3. apply add_vec_zero_l. }
      assert (HY4a1 : Y4 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr)
        by (rewrite /Y4 upd_ne; [exact HY3a1 | nz]).
      assert (HY4a2 : Y4 !!! Regidx Ra2 = (sign_extend' 64 dind : mword 64))
        by (rewrite /Y4 upd_ne; [exact HY3a2 | nz]).
      assert (HY4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y4)
        by (rewrite /Y4; apply cr_regs3_caller; [exact Hcsa0 | exact HY3regs]).
      assert (Hq11a : add_vec_int (mword_of_int (CK + 0x118) : mword 64) 2
                      = mword_of_int (CK + 0x11a)) by pcw.
      iEval (rewrite Hq11a) in "Hpc".
      (* ===== +0x11a jal dirlink(ip, "..", dp->inum) ================= *)
      assert (Htgd2 : add_vec (mword_of_int (CK + 0x11a) : mword 64)
                (sign_extend' 64 (mword_of_int 2092310 : mword 21))
                = mword_of_int KernelSyms.dirlink) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0x11a)) Rra
                (mword_of_int 2092310 : mword 21) Y4 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_11a with "Htext"). }
      iIntros (CIDe6 Hqe6) "Hcg Hpc".
      iEval (rewrite Htgd2) in "Hpc".
      pose (Y5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)]> Y4).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)]> Y4) with Y5.
      assert (HY5ra : Y5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0x11a) : mword 64) 4)
        by (rewrite /Y5; apply upd_eq).
      assert (HY5a0 : Y5 !!! Regidx Ra0 = ientry kslot)
        by (rewrite /Y5 upd_ne; [exact HY4a0 | nz]).
      assert (HY5a1 : Y5 !!! Regidx Ra1 = mword_of_int cr_dotdot_addr)
        by (rewrite /Y5 upd_ne; [exact HY4a1 | nz]).
      assert (HY5a2 : Y5 !!! Regidx Ra2
                      = (zero_extend' 64 (cr_low16 dind) : mword 64)).
      { rewrite /Y5 upd_ne; [| nz]. rewrite HY4a2.
        exact (cr_a2_low16 dind Hd16). }
      assert (HY5regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Y5)
        by (rewrite /Y5; apply cr_regs3_caller; [exact Hcsra | exact HY4regs]).
      iPoseProof (cr_dotdot_window_kt1 (Y5 !!! Regidx Ra1)
                    ltac:(exact HY5a1) with "Hkd") as "Hddw".
      iDestruct (cpu_own_transport CIDd1 CIDe6 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      (* claude-notes/optimization.md: an inline [ltac:] closer is priced by
         the DEPTH of its call site, and with [rget]/[tp_pin]/[rf_upd] sealed
         opaque above, this arm's ambient context is large enough that the
         inline form of this bound regressed [1.36 s -> 8.26 s] (measured,
         isolated [coqc -time], 2026-08-15) -- ProofPipewrite.v's Strategy
         header documents the same shape.  Hoisted to a named [assert] with
         an explicit [clear] down to the six facts [lia] actually draws on
         ([Hn3lo], the eighth-block floor threaded from three [dirlink]s up,
         is the one a first [clear -H..] attempt here dropped -- it is not
         mentioned by the rewrite/pose chain below, only by [lia] itself). *)
      assert (Hdlneed4 :
                (SpecDirlink.dl_need (bool_decide (bmapstart ∈ Sb4))
                   (SpecBmap.bmap_ind
                      ((16 * dir_slot dat1
                              (dir_nrec (bv_unsigned (di_size dc1))))
                       `div` BSIZE)%nat)
                 <= n4)%nat).
      { clear -Hc1nrec Hc1k0 Hind1 Hcrb2 Hspend1 Hn3lo.
        rewrite Hc1nrec Hc1k0 Hind1 Hcrb2
                (proj1 (proj2 SpecDirlink.dl_need_values)).
        pose proof (cr_mkdir_dl1 n3 n4 _ _ _ Hspend1); lia. }
    (* THE SHARE DIRLINK'S OWN [iput] MAY NEED (durable-disk B''-tx5).  Inside
       the armed span this walk holds no free residue -- a quarter is in each
       escrow and the registry's arm has the half -- so it shrinks the
       PARENT'S arm by an eighth for the duration of the call and grows it
       back at the return.  The eighth is enough: what iput's windows need is
       a POSITIVE share of an OPEN transaction, and any is. *)
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep")
      as "(Hivalid & Hdep & Htxs)".
    iModIntro. iEval (rewrite -Hglog) in "Htxs".
      iApply (DLK.wp_dirlink_gen γs j γl γu γd γk pd pav pu bn γ γi
                gtl γa γf γpr inodestart nib bmapstart size dev
                (ientry kslot) cinum bm1 dat1 dc1 dc1
                cr_dotdot_f (cr_low16 dind) n4 Sb4
                _ _
                pidv (DfracOwn (1/4)) (DfracOwn (1/2)) DfracDiscarded dqs
                dqb dqbs (DfracOwn (1/2))
                Y5 (K - 10)%nat eb b lks
                V ltac:(exact HKdlk) Hc1tyd Hcov1 (Hcap1 Hccap)
                ltac:(exact (Hc1dok ltac:(rewrite Hc1ty Htdir;
                                          vm_compute; reflexivity)))
                (* §7.5.6, row 4: LEFT disjunct from [ip->nlink = 1], the
                   value the three [sh]s flushed before the ["."] link and
                   which that link carried through unchanged ([Hc1nl]). *)
                ltac:(left; rewrite Hc1nl; vm_compute; discriminate)
                ltac:(apply dir_orphan_clean_live;
                      rewrite Hc1nl; vm_compute; discriminate)
                ltac:(exact (di_type_stable_refl _))
                ltac:(exact (di_nlink_stable_refl _ Hc1tynz))
                Hlg Hwf1 Hholes1 Haddr1 Hsz311 Hist0 Hcblk Hcblog Hcinb
                Hdl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                Hdlneed4
                Hj Hgs HY5a0 HY5a2 Heb ltac:(lkbelow) Hglog
                with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                      Hcidev Hciinum Hcmeta Hcmap Hcblocks Hddw Hsbi Hsbs Hsbb
                      Hbmr Hiregi Hiopen Hcdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                      Hitb2 Hitbl Hesc Hslks Hislk Hcdlnk1 Hop Htxs").
      all: try lkbelow.
      iIntros (CIDd2 Hsd2 md2 found2 bm2 dat2 dc2 dc02 n5 Sb5 tot2)
        "%Hcsd2 Hcg Hcnt Hpc Hcidev Hciinum Hcmeta Hcmap Hcblocks Hddw2 Hsbi
         Hsbs Hsbb Hcdiat Hppid Hbsl Hislk Hcdlnk1 %Hn5c %Hsb5 %Hdlp2 %Hfd2
         Hop Htxs %Hcap2 %Hsizedp2 %Harm2".
      iEval (rewrite Hglog) in "Htxs".
    iApply fupd_wp.
    iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kd (qd/2)%Qp dev dind gd true
            t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
            ltac:(solve_ndisj) with "Hescd Hivalid Hdep Htxs")
      as "(Hivalid & Hdep)".
    iModIntro.

      iRename "Hcdlnk1" into "Hcdlnk1P".
      iDestruct (dlinks_open with "Hcdlnk1P")
        as "(%Dc1 & [%Hcdok1 %Hcxact1] & Hcetk2)".
      assert (Hpcd2 : ret_pc (Y5 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0x11e)) by (rewrite HY5ra; pcw).
      iEval (rewrite Hpcd2) in "Hpc".
      assert (Hmd2regs : cr_regs3 m sp0 (ientry kd)
                           (mword_of_int 0 : mword 64) (ientry kslot)
                           ty major minor md2)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor Y5 md2 Hcsd2 HY5regs).
      assert (Htg146b : add_vec (mword_of_int (CK + 0x11e) : mword 64)
                (sign_extend' 64 (mword_of_int 40 : mword 13))
                = mword_of_int (CK + 0x146)) by pcw.
      (* the FOUND arm is refuted: slot zero's name is ["."] and not [".."] *)
      destruct found2.
      { exfalso. destruct Harm2 as (Hfst & _). apply Hfst.
        rewrite Hc1nrec.
        exact (cr_first_miss_dotdot dat1 (cr_low16 cinum) Hwin1). }
      destruct Harm2 as (_ & Hwf2 & Hholes2 & Haddr2 & Hsz312 &
                         Hcov2 & Hdc2 & Hdc02 & Htot162 & Hrng2 & Hbl2).
      destruct (Hdlp2 eq_refl) as (Hspend2 & Hatom2 & Hmem2).
      rewrite Hc1nrec Hc1k0 in Hspend2, Hmem2, Hrng2, Hdc2.
      (* [crd] at the second link is NOT derivable -- [dl16_post]'s [crd]
         names the POST blkmap, and nothing relates it to the first link's.
         It is also not needed: at [crb2 = true] the spend is at most one at
         EVERY value of [crd2]. *)
      rewrite Hcrb2 (cr_crb_claim Sb4 (IBLOCK cinum inodestart) Hcmem4)
        Hind1 in Hspend2.
      assert (Hdceq2 : dc02 = dc2) by exact (Hdc02 eq_refl).
      subst dc02.
      assert (Hc2ty0 : di_type dc2 = di_type dc1) by (rewrite Hdc2; reflexivity).
      assert (Hc2mj0 : di_major dc2 = di_major dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2mn0 : di_minor dc2 = di_minor dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2nl0 : di_nlink dc2 = di_nlink dc1)
        by (rewrite Hdc2; reflexivity).
      assert (Hc2ty : di_type dc2 = ty) by (rewrite Hc2ty0; exact Hc1ty).
      assert (Hc2tyd : di_type dc2 = SpecDirlookup.T_DIR)
        by (rewrite Hc2ty; exact Htdir).
      assert (Hc2tynz : bv_unsigned (di_type dc2) <> 0)
        by (rewrite Hc2tyd; vm_compute; discriminate).
      assert (Hc2iok : inode_ok fsc_cov fsc_logst dc2 bm2 dat2).
      { rewrite /inode_ok. split_and!.
        - exact Hwf2.
        - exact Hcov2.
        - exact Haddr2.
        - exact Hc2tynz.
        - exact (Hcap2 (Hcap1 Hccap)).
        - exact Hholes2.
        - exact (Hsizedp2 (Hsizedp1 Hcsized)). }
      assert (Hc2szmax : bv_unsigned (di_size dc2)
                = Z.max (bv_unsigned (di_size dc1))
                    (Z.of_nat ((16 * 1)%nat + tot2)))
        by (rewrite Hdc2;
            exact (cr_wi_size_max _ bm2 (16 * 1)%nat tot2 ltac:(lia))).
      assert (Hc2dok : dir_ok nib dc2 dat2)
        by exact (dir_ok_dirlink nib dc1 dc2 dat1 dat2 (cr_low16 dind)
                    (bname 14 cr_dotdot_f) 1%nat 1%nat tot2
                    (eq_sym Hc1nrec) (eq_sym Hc1k0) Htot162 Hdl16b
                    Hc2ty0 Hc2szmax Hrng2 Hc1dok).
      (* ...and UNIQUENESS, whose guard here is the SAME [dir_first] miss
         that refutes the found arm above: record 0 is the ["."]. *)
      assert (Hc2duq : dir_uniq dc2 dat2)
        by exact (dir_uniq_dirlink dc1 dc2 dat1 dat2 (cr_low16 dind)
                    (bname 14 cr_dotdot_f) 1%nat 1%nat tot2
                    (eq_sym Hc1nrec) (eq_sym Hc1k0) Hatom2
                    (bname_length_le 14 cr_dotdot_f) (cut_nul_nonul _)
                    Hc2ty0 Hc2szmax Hrng2
                    (cr_first_miss_dotdot dat1 (cr_low16 cinum) Hwin1)
                    Hc1duq).
      (* the child's four field readings, at the record TWO links left --
         what [cr_fail_mkdir_body] takes and what [cr_cont_body]'s [made]
         arm asks for.  Both the ARM C-OK re-walk and two of the three
         [fail:] entries spend them, so they are stated once, here. *)
      assert (Hc2mj : di_major dc2 = major) by (rewrite Hc2mj0; exact Hc1mj).
      assert (Hc2mn : di_minor dc2 = minor) by (rewrite Hc2mn0; exact Hc1mn).
      assert (Hc2nl : di_nlink dc2 = (mword_of_int 1 : mword 16))
        by (rewrite Hc2nl0; exact Hc1nl).
      assert (Hc2nlz : bv_unsigned (di_nlink dc2) = 1)
        by (rewrite Hc2nl; vm_compute; reflexivity).
      assert (Hc2dokn : dir_ok icfg_nib dc2 dat2)
        by (rewrite -Hnib; exact Hc2dok).
      (* ================================================================ *)
      (*  THE ESTABLISHMENT.  [DirView.dir_dots_ix] is minted exactly once  *)
      (*  in this kernel and this is the site: the child's two interior     *)
      (*  links have written record 0 = ["."] at its own inum and record    *)
      (*  1 = [".."] at the PARENT's, and the second writei's size makes    *)
      (*  the count two.  Record 1's LIVENESS is [dp->inum <> 0], which has *)
      (*  no supplier anywhere in the tree -- [IcacheRef.inode_held] keeps  *)
      (*  only the upper bound and namex drops [SpecDirlookup]'s own        *)
      (*  [0 < inum] -- so it comes from the PARENT'S OWN copy of this      *)
      (*  clause, whose ["."] half says the parent's record 0 names the     *)
      (*  parent.  That is what the self half is carried for.               *)
      (*                                                                    *)
      (*  It is GUARDED on [tot2 = 16]: on the short arm the child keeps no  *)
      (*  [".."] and goes to [fail:], where the count is zeroed and the      *)
      (*  clause is vacuous.                                                *)
      (* ================================================================ *)
      assert (Hnl0z : bv_unsigned (di_nlink dn) <> 0).
      { intro Hc. apply Hnl0. apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
      assert (Hdindnz : bv_unsigned dind <> 0)
        by exact (dir_dots_ix_self (bv_unsigned dind) dn data
                    ltac:(rewrite Htydir; vm_compute; reflexivity)
                    Hnl0z Hddix).
      assert (Hc2ddix : (tot2 = 16)%nat ->
                        dir_dots_ix (bv_unsigned cinum) dc2 dat2).
      { intro Ht16.
        assert (Hw02 : dir_win_agree dat1 dat2 0).
        { intros jj Hjj. rewrite (Hrng2 (16 * 0 + jj)%nat).
          rewrite decide_False; [reflexivity |].
          intros [Hlo Hhi]. clear -Hlo Hjj. lia. }
        assert (Hwin2 : forall jj, (jj < 16)%nat ->
                  file_byte dat2 (16 * 1 + jj)%nat
                  = dirent_bytes (de_of_name (cr_low16 dind)
                                    (bname 14 cr_dotdot_f)) !!! jj).
        { intros jj Hjj. rewrite (Hrng2 (16 * 1 + jj)%nat).
          rewrite decide_True; [| clear -Hjj Ht16; lia].
          replace (16 * 1 + jj - 16 * 1)%nat with jj by (clear -jj; lia).
          reflexivity. }
        destruct (cr_dotdot_record dat2 (cr_low16 dind) Hwin2)
          as [Hd2inum Hd2name].
        assert (Hn32 : dir_nrec 32 = 2%nat) by (vm_compute; reflexivity).
        assert (H32 : 32 <= bv_unsigned (di_size dc2))
          by (rewrite Hc2szmax; clear -Ht16; lia).
        pose proof (dir_nrec_mono 32 _ H32) as Hmono.
        intros _ _. split_and!.
        - clear -Hmono Hn32. lia.
        - unfold dir_live. rewrite (dir_inum_agree dat1 dat2 0 Hw02).
          exact Hd1live.
        - rewrite (dir_inum_agree dat1 dat2 0 Hw02) Hd1inum. exact Hcl16.
        - rewrite (dir_bname_agree dat1 dat2 0 Hw02) Hd1name. reflexivity.
        - unfold dir_live. rewrite Hd2inum. intro Hc. apply Hdindnz.
          rewrite <- Hdl16. rewrite Hc. reflexivity.
        - exact Hd2name. }
      (* FAIL ENTRIES 2 AND 3's content clause, and unlike the index clause
         it holds on BOTH arms of the second link -- which is the whole
         point of splitting the content out of the guard.  At [tot2 = 16]
         the child has two records and they ARE the two dots; at
         [tot2 < 16] it has one and it is the ["."].  Neither arm needs
         [dp->inum <> 0], so no parent fact enters here. *)
      assert (Hc2dots : dir_dots_only dc2 dat2).
      { assert (Hw02 : dir_win_agree dat1 dat2 0).
        { intros jj Hjj. rewrite (Hrng2 (16 * 0 + jj)%nat).
          rewrite decide_False; [reflexivity |].
          intros [Hlo Hhi]. clear -Hlo Hjj. lia. }
        assert (Hc1sz16 : bv_unsigned (di_size dc1) = 16)
          by (rewrite Hc1szmax Hcsz0 Ht161; vm_compute; reflexivity).
        assert (Hdot0 : bname 14 (dir_name dat2 0) = dot_name).
        { rewrite (dir_bname_agree dat1 dat2 0 Hw02) Hd1name. reflexivity. }
        destruct Hbl2 as [[_ Ht2] | [_ Ht2]].
        - assert (Hwin2 : forall jj, (jj < 16)%nat ->
                    file_byte dat2 (16 * 1 + jj)%nat
                    = dirent_bytes (de_of_name (cr_low16 dind)
                                      (bname 14 cr_dotdot_f)) !!! jj).
          { intros jj Hjj. rewrite (Hrng2 (16 * 1 + jj)%nat).
            rewrite decide_True; [| clear -Hjj Ht2; lia].
            replace (16 * 1 + jj - 16 * 1)%nat with jj by (clear -jj; lia).
            reflexivity. }
          destruct (cr_dotdot_record dat2 (cr_low16 dind) Hwin2)
            as [_ Hd2name2].
          assert (Hsz32 : bv_unsigned (di_size dc2) = 32)
            by (rewrite Hc2szmax Hc1sz16 Ht2; vm_compute; reflexivity).
          assert (Hn32 : dir_nrec 32 = 2%nat) by (vm_compute; reflexivity).
          intros k Hk _. rewrite Hsz32 Hn32 in Hk.
          destruct k as [| [| k]]; [| | exfalso; clear -Hk; lia].
          + left. exact Hdot0.
          + right. exact Hd2name2.
        - assert (Hnr1 : dir_nrec (bv_unsigned (di_size dc2)) = 1%nat).
          { rewrite Hc2szmax Hc1sz16.
            replace (Z.max 16 (Z.of_nat ((16 * 1)%nat + tot2)))
              with (Z.of_nat tot2 + 1 * 16) by (clear -Ht2; lia).
            unfold dir_nrec. rewrite Z.div_add; [| clear; lia].
            rewrite Z.div_small; [reflexivity | clear -Ht2; lia]. }
          intros k Hk _. rewrite Hnr1 in Hk.
          destruct k as [| k]; [| exfalso; clear -Hk; lia].
          left. exact Hdot0. }
      destruct Hbl2 as [[Ha0z2 Ht162] | [Ha0m2 Htlt2]].
      + (* ============================================================= *)
        (*  the [".."] link went in whole: on to [dirlink(dp, name)]      *)
        (* ============================================================= *)
        (* ===== +0x11e bltz a0 : FALLS THROUGH ======================= *)
        iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x11e))
                  (mword_of_int 40 : mword 13) Ra0 md2 (K - 10)%nat b
                  ltac:(nz)
                  ltac:(rgne; rewrite Ha0z2; exact cr_bltz_zero)
                  with "Hcg Hpc []").
        { iApply (cri_11e with "Htext"). }
        iIntros (CIDe7 Hqe7) "Hcg Hpc".
        assert (Hq122 : add_vec_int (mword_of_int (CK + 0x11e) : mword 64) 4
                        = mword_of_int (CK + 0x122)) by pcw.
        iEval (rewrite Hq122) in "Hpc".
        (* THE DEFERRED RE-PARK: slot ONE names the PARENT, whose fragment
           is minted only by the +0x140 flush, so the child's [dlinks] stays
           at [dc1]/[dat1] until then and the range clause travels with it. *)
        (* THE CHILD'S RECORD-ONLY FACTS AFTER ITS OWN TWO LINKS
           (durable-disk 2b-inode-3): the type rode both [dirlink]s, the
           count is still the literal 1, and the size is 32 -- two whole
           records, hence a multiple of sixteen.  Asserted HERE, where
           [tot2 = 16] first holds, because both this arm's exits re-park
           the child at [dc2]. *)
        assert (Hc2rl : inode_rec_local dc2).
        { apply (inode_rec_local_same_type dnc dc2 Hrl_datc).
          - rewrite Hc2ty0 Hc1ty0 cr_setf_type. reflexivity.
          - rewrite Hc2nlz. lia.
          - intros _. rewrite Hc2szmax Hc1szmax Hcsz0 Ht161 Ht162.
            exists 2%Z. vm_compute. reflexivity. }
        assert (Hbmem5 : bmapstart ∈ Sb5) by exact (Hsb5 _ Hbmem4).
        assert (Hcrb3 : bool_decide (bmapstart ∈ Sb5) = true)
          by exact (cr_crb_claim Sb5 bmapstart Hbmem5).
        assert (Hn5lo : (6 <= n5)%nat)
          by exact (cr_mkdir_n5 n3 n4 n5 _ _ _ _ _ Hn3lo Hcorr' Hspend1
                      Hspend2 eq_refl).
        (* ===== +0x122 lw a2,4(s3) : the child's inum ================ *)
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x122)) Ra2 Rs3
                  (mword_of_int 4 : mword 12) md2 (K - 10)%nat cinum b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hciinum]").
        { iApply (cri_122 with "Htext"). }
        { iEval (rgne; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Hmd2regs)))))).
          iExact "Hciinum". }
        iIntros (CIDe8 Hqe8) "Hcg Hpc Hciinum".
        iEval (rgne; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 Hmd2regs))))))
          in "Hciinum".
        pose (W1 := <[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> md2).
        change (<[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> md2) with W1.
        assert (HW1a2 : W1 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W1; apply upd_eq).
        assert (HW1regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W1)
          by (rewrite /W1; apply cr_regs3_caller; [exact Hcsa2 | exact Hmd2regs]).
        assert (HW1s0 : W1 !!! Regidx Rs0 = sp0)
          by (destruct HW1regs as (_ & H & _); exact H).
        assert (HW1s1 : W1 !!! Regidx Rs1 = ientry kd)
          by (destruct HW1regs as (_ & _ & H & _); exact H).
        assert (Hq126 : add_vec_int (mword_of_int (CK + 0x122) : mword 64) 4
                        = mword_of_int (CK + 0x126)) by pcw.
        iEval (rewrite Hq126) in "Hpc".
        (* ===== +0x126 addi a1,s0,-80 : a1 = &name =================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x126)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) W1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_126 with "Htext"). }
        iIntros (CIDe9 Hqe9) "Hcg Hpc".
        pose (W2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget W1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> W1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (rget W1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> W1) with W2.
        assert (HW2a1 : W2 !!! Regidx Ra1 = pa_stk sp0 10).
        { rewrite /W2 upd_eq. rewrite rget_ne;
            [| intro Hz1; injection Hz1 as Hz2; vm_compute in Hz2; congruence ].
          rewrite HW1s0. apply cr_name_addr. }
        assert (HW2a2 : W2 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W2 upd_ne; [exact HW1a2 | nz]).
        assert (HW2s1 : W2 !!! Regidx Rs1 = ientry kd)
          by (rewrite /W2 upd_ne; [exact HW1s1 | nz]).
        assert (HW2regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W2)
          by (rewrite /W2; apply cr_regs3_caller; [exact Hcsa1 | exact HW1regs]).
        assert (Hq12a : add_vec_int (mword_of_int (CK + 0x126) : mword 64) 4
                        = mword_of_int (CK + 0x12a)) by pcw.
        iEval (rewrite Hq12a) in "Hpc".
        (* ===== +0x12a c.mv a0,s1 : the PARENT ======================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x12a)) Ra0 Rs1 W2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cri_12a with "Htext"). }
        iIntros (CIDe10 Hqe10) "Hcg Hpc". iEval (rgne) in "Hcg".
        pose (W3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (W2 !!! Regidx Rs1))]> W2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (W2 !!! Regidx Rs1))]> W2) with W3.
        assert (HW3a0 : W3 !!! Regidx Ra0 = ientry kd).
        { rewrite /W3 upd_eq. rewrite HW2s1. apply add_vec_zero_l. }
        assert (HW3a1 : W3 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /W3 upd_ne; [exact HW2a1 | nz]).
        assert (HW3a2 : W3 !!! Regidx Ra2 = (sign_extend' 64 cinum : mword 64))
          by (rewrite /W3 upd_ne; [exact HW2a2 | nz]).
        assert (HW3regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W3)
          by (rewrite /W3; apply cr_regs3_caller; [exact Hcsa0 | exact HW2regs]).
        assert (Hq12c : add_vec_int (mword_of_int (CK + 0x12a) : mword 64) 2
                        = mword_of_int (CK + 0x12c)) by pcw.
        iEval (rewrite Hq12c) in "Hpc".
        (* ===== +0x12c jal dirlink(dp, name, ip->inum) =============== *)
        assert (Htgd3 : add_vec (mword_of_int (CK + 0x12c) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092292 : mword 21))
                  = mword_of_int KernelSyms.dirlink) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x12c)) Rra
                  (mword_of_int 2092292 : mword 21) W3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_12c with "Htext"). }
        iIntros (CIDe11 Hqe11) "Hcg Hpc".
        iEval (rewrite Htgd3) in "Hpc".
        pose (W4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)]> W3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)]> W3) with W4.
        assert (HW4ra : W4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x12c) : mword 64) 4)
          by (rewrite /W4; apply upd_eq).
        assert (HW4a0 : W4 !!! Regidx Ra0 = ientry kd)
          by (rewrite /W4 upd_ne; [exact HW3a0 | nz]).
        assert (HW4a1 : W4 !!! Regidx Ra1 = pa_stk sp0 10)
          by (rewrite /W4 upd_ne; [exact HW3a1 | nz]).
        assert (HW4a2 : W4 !!! Regidx Ra2
                        = (zero_extend' 64 (cr_low16 cinum) : mword 64)).
        { rewrite /W4 upd_ne; [| nz]. rewrite HW3a2.
          exact (cr_a2_low16 cinum Hc16). }
        assert (HW4regs : cr_regs3 m sp0 (ientry kd)
                            (mword_of_int 0 : mword 64) (ientry kslot)
                            ty major minor W4)
          by (rewrite /W4; apply cr_regs3_caller; [exact Hcsra | exact HW3regs]).
        iEval (rewrite -HW4a1) in "Hnb14".
        iEval (rewrite /inode_map) in "Hmap".
        iDestruct "Hmap" as "[Haddrs Hind]".
        iAssert (inode_map fsc_fs (ientry kd) bm) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        iDestruct (cpu_own_transport CIDd2 CIDe11 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the eighth dirlink's own [iput] may need -- see the two dot
           links above; here it comes off the CHILD's arm, because the call
           itself is over the parent. *)
        iApply fupd_wp.
        iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kslot (q/2)%Qp dev cinum g
                true t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
                ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep")
          as "(Hcivalid & Hcdep & Htxs)".
        iModIntro. iEval (rewrite -Hglog) in "Htxs".
        iApply (DLK.wp_dirlink_gen γs j γl γu γd γk pd pav pu bn γ γi
                  gtl γa γf γpr inodestart nib bmapstart size dev
                  (ientry kd) dind bm data dn dn nf (cr_low16 cinum)
                  n5 Sb5
                  _ _
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1) dqs
                  dqb dqbs (DfracOwn (1/2))
                  W4 (K - 10)%nat eb b lks
                  V ltac:(exact HKdlk) Htydir Hbmcov Hszcap
                  ltac:(exact (Hdok Hdz))
                  (* §7.5.6, row 5 again, on the mkdir arm: LEFT disjunct
                     from the same [sysfile.c:269] guard, relayed into this
                     body as [Hnl0]. *)
                  ltac:(left; exact (cr_nl0z dn Hnl0))
                  ltac:(exact (cr_doc_of_live dn dn data eq_refl Hnl0))
                  ltac:(exact (di_type_stable_refl dn))
                  ltac:(exact (di_nlink_stable_refl dn Htynzd))
                  Hlg Hbmwf Hholes Hdaddr Hsz31 Hist0 Hdblk Hdblog Hdib
                  Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                  ltac:(rewrite Hcrb3;
                        exact (cr_mkdir_dl3_need n3 n4 n5 _ _ _ _ _ true _
                                 Hn3lo Hcorr' Hspend1 Hspend2 eq_refl eq_refl))
                  Hj Hgs HW4a0 HW4a2 Heb ltac:(lkbelow) Hglog
                  with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs Hsbb
                        Hbmr Hiregi Hiopen Hdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                        Hitb2 Hitbl Hesc Hslks Hislk Hdlnk Hop Htxs").
        all: try lkbelow.
        iIntros (CIDd3 Hsd3 md3 found3 bm3 dat3 dp3 dp03 n6 Sb6 tot3)
          "%Hcsd3 Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi
           Hsbs Hsbb Hdiat Hppid Hbsl Hislk Hdlnk %Hn6c %Hsb6 %Hdlp3 %Hfd3
           Hop Htxs %Hcap3 %Hsizedp3 %Harm3".
        iEval (rewrite Hglog) in "Htxs".
        iApply fupd_wp.
        iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kslot (q/2)%Qp dev cinum g
                true t (1/4) ((1/4)/2) ((1/4)/2) (eq_sym (Qp.div_2 (1/4)))
                ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep Htxs")
          as "(Hcivalid & Hcdep)".
        iModIntro.

        iDestruct (dlinks_open with "Hdlnk")
          as "(%D & [%Hdok0 %Hxact0] & Hetk)".
        iEval (rewrite HW4a1) in "Hnb14".
        assert (Hpcd3 : ret_pc (W4 !!! Regidx Rra : mword 64)
                        = mword_of_int (CK + 0x130)) by (rewrite HW4ra; pcw).
        iEval (rewrite Hpcd3) in "Hpc".
        assert (Hmd3regs : cr_regs3 m sp0 (ientry kd)
                             (mword_of_int 0 : mword 64) (ientry kslot)
                             ty major minor md3)
          by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                      (ientry kslot) ty major minor W4 md3 Hcsd3 HW4regs).
        assert (Htg146c : add_vec (mword_of_int (CK + 0x130) : mword 64)
                  (sign_extend' 64 (mword_of_int 22 : mword 13))
                  = mword_of_int (CK + 0x146)) by pcw.
        destruct found3.
        { exfalso. destruct Harm3 as (Hfst & _). exact (Hfst Hnone). }
        destruct Harm3 as (_ & Hwf3 & Hholes3 & Haddr3 & Hsz313 &
                           Hcov3 & Hdp3 & Hdp03 & Htot163 & Hrng3 & Hbl3).
        destruct (Hdlp3 eq_refl) as (Hspend3 & Hatom3 & Hmem3').
        rewrite Hcrb3 in Hspend3.
        assert (Hdpeq : dp03 = dp3) by exact (Hdp03 eq_refl).
        subst dp03.
        assert (Hp3ty : di_type dp3 = di_type dn) by (rewrite Hdp3; reflexivity).
        assert (Hp3nl : di_nlink dp3 = di_nlink dn)
          by (rewrite Hdp3; reflexivity).
        (* THE SIZE READ-BACK, IN ORIGIN'S [Hoff32] SHAPE.  The chain is
           four small facts and then ONE [lia] with the context CLEARED:
           written inline (a single [lia] over the whole syscall-altitude
           context) this sentence does not terminate -- the parent's [k0] is
           a [dir_slot data (dir_nrec ...)] term rather than a literal, so
           [lia]'s atom scan has to normalise it against every arithmetic
           hypothesis three [dirlink]s have accumulated. *)
        assert (Hk0le : (dir_slot data (dir_nrec (bv_unsigned (di_size dn)))
                         <= dir_nrec (bv_unsigned (di_size dn)))%nat)
          by apply dir_slot_le.
        assert (Hsznn : 0 <= bv_unsigned (di_size dn))
          by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
        destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hsznn)
          as [Hnr1 _].
        assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
          by (vm_compute; reflexivity).
        assert (Hnatle : (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot3
                          <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat).
        { clear -Hk0le Htot163. lia. }
        assert (HzA : (Z.of_nat (16 * dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn))) + tot3)%nat
                       <= Z.of_nat (16 * dir_nrec
                            (bv_unsigned (di_size dn)) + 16)%nat)%Z)
          by (apply Nat2Z.inj_le; exact Hnatle).
        assert (HzB : Z.of_nat (16 * dir_nrec
                          (bv_unsigned (di_size dn)) + 16)%nat
                      = (Z.of_nat (16 * dir_nrec
                          (bv_unsigned (di_size dn)))%nat + 16)%Z)
          by (rewrite Nat2Z.inj_add; reflexivity).
        assert (Hoff32 : (Z.of_nat (16 * dir_slot data
                            (dir_nrec (bv_unsigned (di_size dn))) + tot3)
                          < 2 ^ 32)%Z).
        { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z.
          clear -Hnatle HzA HzB Hszcap Hnr1. lia. }
        assert (Hp3szmax : bv_unsigned (di_size dp3)
                  = Z.max (bv_unsigned (di_size dn))
                      (Z.of_nat (16 * dir_slot data
                         (dir_nrec (bv_unsigned (di_size dn))) + tot3)))
          by (rewrite Hdp3; exact (cr_wi_size_max dn bm3 _ tot3 Hoff32)).
        assert (Hp3iok : inode_ok fsc_cov fsc_logst dp3 bm3 dat3).
        { rewrite /inode_ok. split_and!.
          - exact Hwf3.
          - exact Hcov3.
          - exact Haddr3.
          - rewrite Hp3ty. exact Htynzd.
          - exact (Hcap3 Hszcap).
          - exact Hholes3.
          - exact (Hsizedp3 Hsized). }
        assert (Hp3dok : dir_ok nib dp3 dat3)
          by exact (dir_ok_dirlink nib dn dp3 data dat3 (cr_low16 cinum)
                      (bname 14 nf) _ _ tot3 eq_refl eq_refl Htot163
                      Hcl16b Hp3ty Hp3szmax Hrng3 Hdok).
        assert (Hp3duq : dir_uniq dp3 dat3)
          by exact (dir_uniq_dirlink dn dp3 data dat3 (cr_low16 cinum)
                      (bname 14 nf) _ _ tot3 eq_refl eq_refl Hatom3
                      (bname_length_le 14 nf) (cut_nul_nonul _)
                      Hp3ty Hp3szmax Hrng3 Hnone Hduq).
        assert (Hp3szle : bv_unsigned (di_size dn)
                          <= bv_unsigned (di_size dp3))
          by (clear -Hp3szmax; rewrite Hp3szmax; lia).
        assert (Hp3ddix : dir_dots_ix (bv_unsigned dind) dp3 dat3)
          by exact (dir_dots_ix_dirlink (bv_unsigned dind) dn dp3 data dat3
                      (cr_low16 cinum) (bname 14 nf) _ _ tot3 eq_refl eq_refl
                      Htot163 Hp3ty Hp3nl Hp3szle Hrng3 Hddix).
        assert (Hp3setfsz : bv_unsigned (di_size dp3)
                  <= bv_unsigned (di_size (cr_setf dp3 (di_major dp3)
                       (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16)))))
          by (clear; rewrite cr_setf_size; lia).
        assert (Hp3nlnz : bv_unsigned (di_nlink dp3) <> 0).
        { rewrite Hp3nl. intro Hc. apply Hnl0. apply bv_eq. rewrite Hc.
          vm_compute. reflexivity. }
        destruct Hbl3 as [[Ha0z3 Ht163] | [Ha0m3 Htlt3]].
        * (* =========================================================== *)
          (*  ARM C-OK-DIR: the parent's record went in, so the [++] and   *)
          (*  the flush follow and [c.j +0xe0] joins ARM C-OK's block.     *)
          (* =========================================================== *)
          (* THE THREE [tot] READINGS, HOISTED OUT OF ARGUMENT POSITION.  An
             inline [ltac:(lia)] here scans a context three [dirlink]s deep
             and does not terminate (>10 min, 20 GB); with the context
             cleared to the one equation it is instantaneous.  Same rule as
             [Hoff32] above -- durable-notes' "clear - H; lia". *)
          assert (Ht2le3 : (2 <= tot3)%nat) by (clear -Ht163; lia).
          assert (Ht0lt3 : (0 < tot3)%nat) by (clear -Ht163; lia).
          assert (Ht2le2 : (2 <= tot2)%nat) by (clear -Ht162; lia).
          (* ===== +0x130 bltz a0 : FALLS THROUGH ===================== *)
          iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0x130))
                    (mword_of_int 22 : mword 13) Ra0 md3 (K - 10)%nat b
                    ltac:(nz)
                    ltac:(rgne; rewrite Ha0z3; exact cr_bltz_zero)
                    with "Hcg Hpc []").
          { iApply (cri_130 with "Htext"). }
          iIntros (CIDh1 Hqh1) "Hcg Hpc".
          assert (Hq134 : add_vec_int (mword_of_int (CK + 0x130) : mword 64) 4
                          = mword_of_int (CK + 0x134)) by pcw.
          iEval (rewrite Hq134) in "Hpc".
          (* the child is not the parent: two records held at once are two
             records ([InodeRegion.dinode_at_ne], pure, consumes neither) *)
          iDestruct (InodeRegion.dinode_at_ne γi cinum dind _ _
                       with "Hcdiat Hdiat") as %Hcned.
          (* ===== +0x134 lhu a5,74(s1) : dp->nlink =================== *)
          iEval (rewrite /inode_meta) in "Hmeta".
          iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
          iEval (rewrite /i_nlink) in "Hinl".
          iApply (wp_lhu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x134)) Ra5 Rs1
                    (mword_of_int 74 : mword 12) md3 (K - 10)%nat
                    (di_nlink dp3) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc [] [Hinl]").
          { iApply (cri_134 with "Htext"). }
          { iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd3regs)))).
            iExact "Hinl". }
          iIntros (CIDh2 Hqh2) "Hcg Hpc Hinl".
          iEval (rgne; rewrite (proj1 (proj2 (proj2 Hmd3regs)))) in "Hinl".
          pose (V1 := <[Regidx Ra5 := regval_into_reg
                        (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64)]> md3).
          change (<[Regidx Ra5 := regval_into_reg
                        (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64)]> md3) with V1.
          assert (HV1a5 : V1 !!! Regidx Ra5
                          = (zero_extend' 64 (di_nlink dp3 : mword 16) : mword 64))
            by (rewrite /V1; apply upd_eq).
          assert (HV1regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V1)
            by (rewrite /V1; apply cr_regs3_caller;
                [exact Hcsa5 | exact Hmd3regs]).
          assert (Hq138 : add_vec_int (mword_of_int (CK + 0x134) : mword 64) 4
                          = mword_of_int (CK + 0x138)) by pcw.
          iEval (rewrite Hq138) in "Hpc".
          (* ===== +0x138 c.addiw a5,1 =============================== *)
          iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x138)) Ra5
                    (mword_of_int 1 : mword 6) V1 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_138 with "Htext"). }
          iIntros (CIDh3 Hqh3) "Hcg Hpc".
          pose (V2 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (rget V1 Ra5)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                           31 0))]> V1).
          change (<[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (rget V1 Ra5)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                           31 0))]> V1) with V2.
          assert (HV2regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V2)
            by (rewrite /V2; apply cr_regs3_caller;
                [exact Hcsa5 | exact HV1regs]).
          assert (HV2s1 : V2 !!! Regidx Rs1 = ientry kd)
            by (destruct HV2regs as (_ & _ & H & _); exact H).
          assert (Hq13a : add_vec_int (mword_of_int (CK + 0x138) : mword 64) 2
                          = mword_of_int (CK + 0x13a)) by pcw.
          iEval (rewrite Hq13a) in "Hpc".
          (* ===== +0x13a sh a5,74(s1) : dp->nlink++ ================== *)
          iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CK + 0x13a)) Ra5 Rs1
                    (mword_of_int 74 : mword 12) V2 (K - 10)%nat
                    (di_nlink dp3) b with "Hcg Hpc [] [Hinl]").
          { iApply (cri_13a with "Htext"). }
          { iEval (rgne; rewrite HV2s1). iExact "Hinl". }
          iIntros (CIDh4 Hqh4) "Hcg Hpc Hinl".
          iEval (rgne; rgne; rewrite HV2s1 /V2 upd_eq; rgne;
                 rewrite HV1a5 cr_nlink_incr) in "Hinl".
          assert (Hq13e : add_vec_int (mword_of_int (CK + 0x13a) : mword 64) 4
                          = mword_of_int (CK + 0x13e)) by pcw.
          iEval (rewrite Hq13e) in "Hpc".
          iAssert (inode_meta (ientry kd)
                     (cr_setf dp3 (di_major dp3) (di_minor dp3)
                        (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))))
            with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
          { rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
                    cr_setf_nlink cr_setf_size /i_nlink. iFrame. }
          (* THE PARENT'S FRAGMENTS ACROSS THE DEPOSIT AND THE [++], IN
             ONE STEP.  The record at the append slot becomes live and
             MARKED, so the parent's marker set grows by exactly one --
             which is what the raised count on the other side of
             [FsStateInode.node_exact] costs. *)
          (* optimization.md's rule, as everywhere else in this walk: every
             one of the eight side facts is a NAMED assert with the context
             cleared to what it needs, never an inline [ltac:] in argument
             position at this depth. *)
          assert (Hdntdir : bv_unsigned (di_type dn) = T_DIR_z)
            by (clear -Htydir; rewrite Htydir; vm_compute; reflexivity).
          assert (Hdnnlnz : bv_unsigned (di_nlink dn) <> 0)
            by (clear -Hp3nlnz Hp3nl; rewrite <- Hp3nl; exact Hp3nlnz).
          assert (Hcl16nz : cr_low16 cinum <> bv_0 16).
          { assert (Hz0 : bv_unsigned (bv_0 16 : bv 16) = 0)
              by (vm_compute; reflexivity).
            clear -Hcpos Hcl16 Hz0. intro Hc.
            apply (f_equal bv_unsigned) in Hc. rewrite Hcl16 Hz0 in Hc. lia. }
          assert (Hcl16ne : bv_unsigned (cr_low16 cinum) <> bv_unsigned dind)
            by (clear -Hcned Hcl16; rewrite Hcl16; exact Hcned).
          assert (Hbumpty : di_type (cr_setf dp3 (di_major dp3) (di_minor dp3)
                              (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))) = di_type dn)
            by (clear -Hp3ty; rewrite cr_setf_type; exact Hp3ty).
          assert (Hbumpsz : bv_unsigned (di_size (cr_setf dp3 (di_major dp3)
                              (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))))
                            = Z.max (bv_unsigned (di_size dn))
                                (Z.of_nat (16 * dir_slot data
                                   (dir_nrec (bv_unsigned (di_size dn)))
                                 + tot3)))
            by (clear -Hp3szmax; rewrite cr_setf_size; exact Hp3szmax).
          (* THE FUSED DEPOSIT IS DEFERRED PAST THE FLUSH.  The re-seal's
             exactness equation wants the EXACT [+1], and the only honest
             source of "the [++] did not wrap" is the flush's own nonzero
             read-back -- so the deposit fires three instructions below,
             right after [ireg_tok_nz], with the record and the fragment
             both still in hand.  Nothing in between touches either. *)
          (* ===== +0x13e c.mv a0,s1 ================================= *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x13e)) Ra0 Rs1 V2
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
          { iApply (cri_13e with "Htext"). }
          iIntros (CIDh5 Hqh5) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (V3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (V2 !!! Regidx Rs1))]> V2).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (V2 !!! Regidx Rs1))]> V2) with V3.
          assert (HV3a0 : V3 !!! Regidx Ra0 = ientry kd).
          { rewrite /V3 upd_eq. rewrite HV2s1. apply add_vec_zero_l. }
          assert (HV3regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V3)
            by (rewrite /V3; apply cr_regs3_caller;
                [exact Hcsa0 | exact HV2regs]).
          assert (Hq140 : add_vec_int (mword_of_int (CK + 0x13e) : mword 64) 2
                          = mword_of_int (CK + 0x140)) by pcw.
          iEval (rewrite Hq140) in "Hpc".
          (* ===== +0x140 jal iupdate(dp) : THE SECOND MINT =========== *)
          assert (Htgiu2 : add_vec (mword_of_int (CK + 0x140) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090074 : mword 21))
                    = mword_of_int KernelSyms.iupdate) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x140)) Rra
                    (mword_of_int 2090074 : mword 21) V3 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_140 with "Htext"). }
          iIntros (CIDh6 Hqh6) "Hcg Hpc".
          iEval (rewrite Htgiu2) in "Hpc".
          pose (V4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)]>
                       V3).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)]>
                       V3) with V4.
          assert (HV4ra : V4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x140) : mword 64) 4)
            by (rewrite /V4; apply upd_eq).
          assert (HV4a0 : V4 !!! Regidx Ra0 = ientry kd)
            by (rewrite /V4 upd_ne; [exact HV3a0 | nz]).
          assert (HV4regs : cr_regs3 m sp0 (ientry kd)
                              (mword_of_int 0 : mword 64) (ientry kslot)
                              ty major minor V4)
            by (rewrite /V4; apply cr_regs3_caller;
                [exact Hcsra | exact HV3regs]).
          destruct (cr_mkdir_ip n3 n4 n5 n6 _ _ _ _ _ true _ _ _ _
                      Hn3lo Hcorr' Hspend1 Hspend2 Hspend3 eq_refl eq_refl)
            as [Hipn6 Hn6pos].
          (* the mint's premises, every one NAMED: an inline [ltac:] in
             argument position has to guess its type from an evar
             (durable-notes), and this contract has eight of them. *)
          assert (Hmtcru : true = true -> IBLOCK dind inodestart ∈ Sb6)
            by (intros _; exact (proj1 (proj2 (Hmem3' Ht0lt3)))).
          assert (Hmtstab : InodeRegion.di_type_stable
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    dp3)
            by (apply di_type_stable_eq; apply cr_setf_type).
          assert (Hmttynz : bv_unsigned (di_type
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))))
                    <> 0)
            by (rewrite cr_setf_type Hp3ty; exact Htynzd).
          assert (Hmtbump : di_nlink
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    = add_vec (di_nlink dp3 : mword 16) (mword_of_int 1))
            by apply cr_setf_nlink.
          assert (Hmtgrd : di_nlink dp3 <> (mword_of_int 32767 : mword 16))
            by (rewrite Hp3nl; exact Hnlmax).
          assert (Hmtaddr : di_addrs
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    = bm_cells bm3)
            by (rewrite cr_setf_addrs; exact Haddr3).
          assert (Hmtdirlen : length (bm_dir bm3) = NDIRECT)
            by exact (blkmap_wf_dir_len fsc_cov fsc_logst bm3 Hwf3).
          destruct n6 as [| u6]; [exfalso; lia |].
          iDestruct (cr_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
          iDestruct (cpu_own_transport CIDd3 CIDh6 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (IU.wp_iupdate_link γs j γl γu γd γk pd pav pu bn γ γi
                    inodestart nib dev (ientry kd) dind
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    dp3 bm3 u6 Sb6 true
                    (* pin = false: mkdir's [dp->nlink++] is RULING A's one
                       free site -- a live directory the caller has locked --
                       so it pays the PURE arm (§3.9). *) false
                    (* NO VALUE IS CHOSEN (lane G5): [dp]'s register already
                       stands, and the unit that comes out carries whatever
                       it holds -- which is all the child's [".."] entry
                       needs ([FsStateInode.ent_ty_ok]'s dotdot arm is
                       [True]). *)
                    None
                    pidv
                    (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                    V4 (K - 10)%nat eb b lks
                    V HKiu Hmtcru
                    Hlg Hist0 Hdblk Hdblog Hdib
                    Hmtstab Hmttynz
                    ltac:(intros vz Hc; discriminate Hc)
                    Hmtbump Hmtgrd
                    Hmtaddr Hmtdirlen
                    Hj Hgs HV4a0 Heb
                    with "Hcg Hcnt Htext Hkd Hpc Hpenv Hbio Hlogc Hidev Hiinum
                          Hmeta Hmap Hsbi Hiregi Hdiat [%] Hppid Hprocs Hdevi
                          Hgeom Hdlk Hbs2 Hop").
          all: try lkbelow.
          { (* the PURE arm, RULING A's one free site: [dp] is the live
               directory create locked at +0x2e, whose [dp->nlink == 0]
               refusal is exactly [Hdpnl0]. *)
            rewrite /InodeRegion.ireg_link_pin. exact Hp3nlnz. }
          iIntros (CIDh7 Hsh7 mmt)
            "%Hcsmt Hcg Hcnt Hpc Hppid Hidev Hiinum Hmeta Hmap Hsbi Hdiat
             (%vend & [%Hvokend _] & Htokend) Hpin Hbs2 Hop".
          (* [dp] is a LIVE directory, so its multiplicity rises by one *)
          iEval (rewrite (InodeRegion.ireg_dot_delta_live _ _ Hp3nlnz)
                         FsStateLink.link_reps_1) in "Htokend".
          (* THE COUNT'S LOWER BOUND AT THE BUMPED RECORD, and it has to be
             taken HERE: the [link_tok] the flush just minted is the only
             witness, and three lines below it is spent into the child's
             [".."] entry.  It is what the complement dot clause needs at
             the re-park -- the [++] is the one create site where
             [dir_orphan_clean] is not free, because [nlink + 1 = 0] is a
             wrap the NLINK_MAX guard (a SIGNED test) does not exclude and
             no pure fact in this walk rules out.
             [IregLinkNz.ireg_tok_nz] is mask-preserving and hands
             everything back. *)
          iApply fupd_wp.
          iMod (ireg_tok_nz ⊤ γi fsc_fs inodestart nib dind
                  (cr_setf dp3 (di_major dp3) (di_minor dp3)
                     (add_vec (di_nlink dp3 : mword 16)
                        (mword_of_int 1 : mword 16)))
                  vend ltac:(solve_ndisj) Hdib
                  with "Hiregi Hdiat Htokend")
            as "([%Hmtnz _] & Hdiat & Htokend)".
          iModIntro.
          (* THE FUSED DEPOSIT, DEFERRED TO HERE (see the note at +0x13a):
             the read-back [Hmtnz] is what turns the machine's [++] into
             the EXACT [+1] the lower clause needs. *)
          assert (Hbumpeq : bv_unsigned (di_nlink (cr_setf dp3 (di_major dp3)
                              (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                                 (mword_of_int 1 : mword 16))))
                            = bv_unsigned (di_nlink dn) + 1).
          { rewrite cr_setf_nlink. rewrite <- Hp3nl.
            apply nlink_add1_nz_eq.
            rewrite cr_setf_nlink in Hmtnz. exact Hmtnz. }
          (* ============ THE MARKER SET AND THE ["."] RE-PIN ==========
             Everything the two [dirlink]s below owe the type register, in
             the ONE place where the walk still holds BOTH units the fill
             minted (durable-disk G5).  [Htoken] is the second one -- the
             first went into the child's ["."] entry at +0x10a -- and it is
             what values the ["."] fragment by the register's own
             agreement, which is what re-pins that fragment's clause when
             [dirlink(ip, "..", dp)] moves the child's [".."] target. *)
          assert (Htdirm : ty = SpecDirlookup.T_DIR).
          { apply bv_eq. rewrite -Hc1ty Hc1tyd. reflexivity. }
          destruct (dir_dots_miss_not_dots (bv_unsigned dind) dn data
                      (bname 14 nf) Hdntdir Hdnnlnz Hddix Hnone)
            as [Hnfd1m Hnfd2m].
          assert (Hnfd'm : bname 14 nf <> DOT)
            by (rewrite FsStateEra.DOT_dot; exact Hnfd1m).
          assert (Hnfdd'm : bname 14 nf <> DOTDOT)
            by (rewrite FsStateEra.DOTDOT_dotdot; exact Hnfd2m).
          assert (HsDm : bname 14 nf ∉ D).
          { intros Hin. destruct (Hdok0 _ Hin) as ([tt Htt] & _ & _).
            rewrite (dir_entries_era_node dn bm data Hholes Hszcap)
              (bool_decide_eq_true_2 _ Hdntdir)
              (proj2 (dir_view_lookup_None data _ (bname 14 nf)) Hnone)
              in Htt. discriminate. }
          (* the child's marker set is EMPTY: its count is exact and one *)
          assert (Hc1fn1 : fn_nlink (era_node dc1 bm1 dat1) = 1%nat)
            by (rewrite /fn_nlink era_node_rec Hc1nl; vm_compute; reflexivity).
          assert (Hc1dz : bv_unsigned (di_type dc1) = T_DIR_z)
            by (rewrite Hc1tyd; vm_compute; reflexivity).
          assert (Horph1 : fn_orphan (era_node dc1 bm1 dat1) = false)
            by (rewrite /fn_orphan Hc1fn1
                  (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) //).
          assert (HDc1 : Dc1 = ∅).
          { pose proof (Hcxact1 ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                                      apply bool_decide_eq_true;
                                      exact Hc1dz)) as Hex.
            rewrite Hc1fn1 Horph1 in Hex.
            apply leibniz_equiv, size_empty_inv. clear -Hex. lia. }
          assert (Hdot1 : dir_entries (era_node dc1 bm1 dat1) !! DOT
                          = Some (bv_unsigned cinum)).
          { rewrite (dir_entries_era_node dc1 bm1 dat1 Hholes1 (Hcap1 Hccap))
              (bool_decide_eq_true_2 _ Hc1dz) Hc1nrec -Hcl16 -Hd1inum.
            replace DOT with (dir_bname dat1 0%nat)
              by (rewrite /dir_bname Hd1name DOT_dot_name; reflexivity).
            exact (dir_view_live dat1 1%nat 0%nat
                     ltac:(rewrite -Hc1nrec; exact (Hc1duq Hc1dz))
                     ltac:(clear; apply Nat.lt_0_succ) Hd1live). }
          iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                       Hdot1 Horph1 with "Hcetk2")
            as "[(%vdot0 & Hdot0) Hcnodot]".
          iApply fupd_wp.
          iMod (IregLinkNz.ireg_toks_agree ⊤ γi fsc_fs inodestart nib cinum _
                  vdot0 (cr_ity ty (bv_unsigned dind))
                  ltac:(solve_ndisj) Hcinb
                  with "Hiregi Hcdiat Hdot0 Htoken")
            as "([%Hvdot0 _] & Hcdiat & Hdot0 & Htoken)".
          iModIntro.
          (* THE PARENT'S RE-PARK, in TWO steps (durable-disk
             2b-inode-5): the append files the child's unit at the name the
             record now carries, and the [++] moves only the count, which
             the entry map does not read. *)
          iDestruct (ent_toks_dirlink_arm (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dn dp3 bm bm3 data dat3
                       (cr_low16 cinum) (bname 14 nf)
                       (dir_nrec (bv_unsigned (di_size dn)))
                       (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                       tot3 D true eq_refl eq_refl Hatom3
                       (bname_length_le 14 nf) (cut_nul_nonul _)
                       Hdntdir Hp3ty Hp3nl Hp3szmax Hrng3 Hnone
                       Hholes Hholes3 Hszcap (Hcap3 Hszcap) HsDm Hnfdd'm
                       with "Hetk [Htoken]") as "Hetk".
          { iEval (rewrite -Hcl16) in "Htoken".
            iApply (ent_tok_of_link (fs_gamma_L fsc_fs) (bv_unsigned dind)
                      (FsStateInode.fn_dd (era_node dn bm data))
                      (fn_orphan (era_node dn bm data)) true (bname 14 nf)
                      (bv_unsigned (cr_low16 cinum))
                      (cr_ity ty (bv_unsigned dind))
                      ltac:(apply FsStateInode.ent_ty_ok_name;
                            [exact Hnfd'm | exact Hnfdd'm |
                             exact (cr_ity_dir ty (bv_unsigned dind) Htdirm)])
                      with "Htoken"). }
          iDestruct (ent_toks_era_nlink (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dp3 (cr_setf dp3 (di_major dp3) (di_minor dp3)
                          (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16))) bm3 dat3
                       ({[bname 14 nf]} ∪ D)
                       (cr_setf_type dp3 _ _ _) (cr_setf_size dp3 _ _ _)
                       ltac:(rewrite Hp3nl; exact Hdnnlnz)
                       ltac:(rewrite cr_setf_nlink;
                             rewrite cr_setf_nlink in Hmtnz; exact Hmtnz)
                       with "Hetk") as "Hetk".
          (* THE COUNT AND THE MARKER SET RISE TOGETHER (G5's (D2), the
             write half): the appended name IS a subdirectory's, and the
             [++] two instructions back is what pays for it. *)
          assert (Hins3 := dir_entries_dirlink_ins dn dp3 bm bm3 data dat3
                     (cr_low16 cinum) (bname 14 nf)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     eq_refl eq_refl
                     (bname_length_le 14 nf) (cut_nul_nonul _) Hcl16nz
                     Hdntdir Hp3ty ltac:(rewrite Hp3szmax Ht163; reflexivity)
                     ltac:(rewrite Ht163 in Hrng3; exact Hrng3) Hnone
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hgrow3 := dir_entries_dirlink_grow dn dp3 bm bm3 data dat3
                     (cr_low16 cinum) (bname 14 nf)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     tot3 eq_refl eq_refl Hatom3
                     (bname_length_le 14 nf) (cut_nul_nonul _)
                     Hdntdir Hp3ty Hp3szmax Hrng3 Hnone
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hbumpdok : FsStateInode.ent_dset_ok
                    (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) ({[bname 14 nf]} ∪ D)).
          { intros tz Htz.
            assert (Hents3 : dir_entries (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3)
                             = dir_entries (era_node dp3 bm3 dat3))
              by (rewrite /dir_entries /fn_is_dir /fn_type /fn_nrec /fn_size
                    /fn_data !era_node_rec cr_setf_type cr_setf_size //).
            rewrite Hents3.
            destruct (decide (tz = bname 14 nf)) as [-> | Hne].
            - split_and!; [| exact Hnfd'm | exact Hnfdd'm].
              rewrite Hins3 lookup_insert. by eexists.
            - destruct (Hdok0 tz ltac:(destruct (proj1 (elem_of_union _ _ _) Htz)
                                        as [Hc | Hc];
                                      [exfalso; apply Hne;
                                       exact (proj1 (elem_of_singleton _ _) Hc)
                                      | exact Hc]))
                as (Hsome & Hd & Hdd).
              split_and!; [exact (Hgrow3 tz Hsome) | exact Hd | exact Hdd]. }
          assert (Hbumpxact : FsStateInode.node_exact
                    (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) ({[bname 14 nf]} ∪ D)).
          { apply (FsStateInode.node_exact_bump (era_node dn bm data)
                     (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16))) bm3 dat3) D (bname 14 nf)).
            - rewrite /fn_is_dir /fn_type !era_node_rec cr_setf_type Hp3ty //.
            - rewrite /fn_nlink !era_node_rec Hbumpeq.
              pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))) as Hb0.
              clear -Hb0. lia.
            - rewrite /fn_nlink era_node_rec. intros Hc. apply Hdnnlnz.
              pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))) as Hb0.
              clear -Hb0 Hc. lia.
            - exact HsDm.
            - exact Hxact0. }
          iDestruct (dlinks_intro _ _ _ _ _ ({[bname 14 nf]} ∪ D)
                       Hbumpdok Hbumpxact with "Hetk") as "Hdlnk".
          assert (Hpcmt : ret_pc (V4 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x144)) by (rewrite HV4ra; pcw).
          iEval (rewrite Hpcmt) in "Hpc".
          assert (Hmmtregs : cr_regs3 m sp0 (ientry kd)
                               (mword_of_int 0 : mword 64) (ientry kslot)
                               ty major minor mmt)
            by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor V4 mmt Hcsmt HV4regs).
          iDestruct (cr_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          (* THE CHILD'S DEFERRED RE-PARK COMPLETES: the unit the
             [dp->nlink++] minted goes into the child's [".."] entry
             (durable-disk 2b-inode-5).  The [".."] side condition of
             [ent_tok_of_link] is the child's own [nlink = 1]. *)
          (* THE ["."] FRAGMENT IS RE-PINNED HERE (durable-disk G5): this
             is the write that moves the child's [".."] target off [None],
             so it is the one write in the kernel whose ["."] clause has to
             be re-established.  The value comes from the agreement taken
             above, against the sibling unit the fill minted. *)
          assert (Hdlne1 : bv_unsigned (cr_low16 dind) <> bv_unsigned cinum)
            by (rewrite Hdl16; intros Hc; apply Hcl16ne;
                rewrite Hcl16; exact (eq_sym Hc)).
          assert (Hdl16nz : cr_low16 dind <> bv_0 16).
          { intros Hc. assert (Hz : bv_unsigned (cr_low16 dind) = 0)
              by (rewrite Hc; vm_compute; reflexivity).
            rewrite Hdl16 in Hz. exact (Hdindnz Hz). }
          assert (Hddname : bname 14 cr_dotdot_f = DOTDOT)
            by (rewrite ProofCreateParts.cr_dotdot_name DOTDOT_dotdot;
                reflexivity).
          iDestruct (ent_toks_dirlink_dotdot (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) dc1 dc2 bm1 bm2 dat1 dat2
                       (cr_low16 dind) 1%nat 1%nat Dc1 vdot0 vend
                       (eq_sym Hc1nrec) (eq_sym Hc1k0) Hdl16nz
                       ltac:(rewrite Hc1ty Htdirm; vm_compute; reflexivity)
                       Hc2ty0 Hc2nl0
                       ltac:(rewrite Hc2szmax Ht162; reflexivity)
                       ltac:(rewrite -Hddname;
                             rewrite Ht162 in Hrng2; exact Hrng2)
                       ltac:(rewrite -Hddname;
                             exact (cr_first_miss_dotdot dat1
                                      (cr_low16 cinum) Hwin1))
                       Hholes1 Hholes2 (Hcap1 Hccap) (Hcap2 (Hcap1 Hccap))
                       ltac:(rewrite HDc1; apply not_elem_of_empty)
                       Hdlne1 Hdot1 Horph1
                       ltac:(rewrite Hvdot0
                                     (cr_ity_dir ty (bv_unsigned dind) Htdirm)
                                     Hdl16; reflexivity)
                       with "Hcnodot Hdot0 [Htokend]") as "Hcetk3".
          { iEval (rewrite -Hdl16) in "Htokend". iExact "Htokend". }
          assert (Hc2dokE : FsStateInode.ent_dset_ok
                             (era_node dc2 bm2 dat2) Dc1)
            by (rewrite HDc1; intros tz Htz;
                exfalso; exact (not_elem_of_empty tz Htz)).
          assert (Hc2xactE : FsStateInode.node_exact
                              (era_node dc2 bm2 dat2) Dc1).
          { intros _.
            assert (Hfn : fn_nlink (era_node dc2 bm2 dat2) = 1%nat)
              by (rewrite /fn_nlink era_node_rec Hc2nl;
                  vm_compute; reflexivity).
            rewrite Hfn /fn_orphan Hfn
              (bool_decide_eq_false_2 (1%nat = 0%nat)
           ltac:(intros Hcz; discriminate Hcz)) HDc1
              size_empty //. }
          iDestruct (dlinks_intro _ _ _ _ _ Dc1 Hc2dokE Hc2xactE
                       with "Hcetk3") as "Hcdlnk2".
          (* ===== +0x144 c.j +0xe0 : into ARM C-OK's own block ======= *)
          assert (Htg0e0 : add_vec (mword_of_int (CK + 0x144) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 1998 : mword 11) ('b"0"))))
                    = mword_of_int (CK + 0xe0)) by pcw.
          iApply (wp_cj_s_sconf (mword_of_int (CK + 0x144))
                    (sign_extend' 21
                       (concat_vec (mword_of_int 1998 : mword 11) ('b"0")))
                    mmt (K - 10)%nat b
                    ltac:(rewrite Htg0e0; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_144 with "Htext"). }
          iIntros (CIDh8 Hqh8). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg0e0) in "Hpc".
          (* ============================================================ *)
          (*  ARM C-OK, RE-WALKED (+0xe0..+0xea).  The join is BELOW      *)
          (*  [cr_alloc_half]'s branch, so there is nothing to share and   *)
          (*  these five instructions are proved again -- here against a   *)
          (*  parent at its BUMPED [nlink] and a child at the record its   *)
          (*  two interior links left.                                     *)
          (* ============================================================ *)
          assert (Hp3dokn : dir_ok icfg_nib dp3 dat3)
            by (rewrite -Hnib; exact Hp3dok).
          (* THE MOVER (namei-pinned-lookup.md §9 W3, dirlink's row): the
             parent's bytes moved, so its hold moves with them.  One free
             own-update; no delta is proved. *)
          iApply fupd_wp.
          iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _
                  (dv_of (cr_setf dp3 (di_major dp3) (di_minor dp3)
                                     (add_vec (di_nlink dp3 : mword 16)
                                        (mword_of_int 1 : mword 16))) dat3)
                  ltac:(solve_ndisj) with "Hiregi Hdview") as "Hdview".
          iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _
                  (fv_of (cr_setf dp3 (di_major dp3) (di_minor dp3)
                                     (add_vec (di_nlink dp3 : mword 16)
                                        (mword_of_int 1 : mword 16))) dat3)
                  ltac:(solve_ndisj) with "Hiregi Hfview") as "Hfview".
          iModIntro.
          assert (Hpfty : di_type (cr_setf dp3 (di_major dp3) (di_minor dp3)
                            (add_vec (di_nlink dp3 : mword 16)
                               (mword_of_int 1 : mword 16)))
                          = di_type dn)
            by (rewrite cr_setf_type; exact Hp3ty).
          iAssert (ity_shot gd (di_type (cr_setf dp3 (di_major dp3)
                     (di_minor dp3) (add_vec (di_nlink dp3 : mword 16)
                        (mword_of_int 1 : mword 16))))) as "#Hshotf".
          { rewrite Hpfty. iExact "Hshotl". }
          (* THE STRUCTURAL CONSTRUCTOR, not [iFrame]: [ic_loaded]'s tail is
             a 268-element big-op and [iFrame] re-searches it quadratically.
             Both [Hdiat] and [Hmeta] come back from the flush ALREADY at the
             bumped record, so unlike the file arm's site there is no
             trailing rewrite and [ic_mk_loaded] applies outright. *)
          iEval (rewrite /inode_map) in "Hmap".
          iDestruct "Hmap" as "[Hpaddrs Hpind]".
          (* ...and the ERA's abstract value at the bumped parent: mkdir's
             append moved the record AND the bytes, and [ireg_top_retag]
             opens [ftopN] alone (durable-disk 2b-inode-3). *)
          (* THE RECORD-ONLY FACTS AT THE BUMPED PARENT (durable-disk
             2b-inode-3): the type rides [cr_setf], the [++] is short by
             the walk's own [<> 32767] guard, and the size is a MAX of two
             multiples of sixteen.  They come BEFORE the retag now, because
             the retag owes the registry's row (durable-disk lane A). *)
          assert (Hbumprl : inode_rec_local
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16)
                          (mword_of_int 1 : mword 16)))).
          { apply (inode_rec_local_same_type dn _ Hrl Hbumpty).
            - rewrite Hbumpeq. apply cr_nl_bump_short.
              + exact (proj1 (proj2 Hrl)).
              + exact (cr_nl_ne_32767 (di_nlink dn) Hnlmax).
            - intros _. rewrite Hbumpsz. apply cr_max_div16.
              + apply (proj2 (proj2 Hrl)). exact Hdntdir.
              + exists (Z.of_nat (dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn)))) + 1)%Z.
                rewrite Ht163 Nat2Z.inj_add Nat2Z.inj_mul. lia. }
          (* ...and the ERA's abstract value at the bumped parent: mkdir's
             append moved the record AND the bytes, and [ireg_top_retag]
             opens [ftopN] alone (durable-disk 2b-inode-3).  A raised link
             count and an appended entry leave the parent well-formed, which
             is the row the retag owes (durable-disk lane A) -- and these are
             [ic_mk_loaded]'s own four facts, one line below. *)
          iApply fupd_wp.
          iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
                  (era_node dn bm data)
                  (era_node (cr_setf dp3 (di_major dp3) (di_minor dp3)
                               (add_vec (di_nlink dp3 : mword 16)
                                  (mword_of_int 1 : mword 16))) bm3 dat3)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst _
                     bm3 dat3
                     (cr_setf_inode_ok fsc_cov fsc_logst dp3 bm3 dat3
                        (di_major dp3) (di_minor dp3) _ Hp3iok)
                     Hbumprl
                     (dir_uniq_cong dp3 _ dat3 (cr_setf_type _ _ _ _)
                        (cr_setf_size _ _ _ _) Hp3duq)
                     (dir_dots_ix_eq (bv_unsigned dind) dp3 _ dat3 dat3
                        (cr_setf_type _ _ _ _)
                        (fun _ => Hp3nlnz)
                        Hp3setfsz eq_refl Hp3ddix))
                  with "[] Htop") as "Htop";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kd dind
                       (cr_setf dp3 (di_major dp3) (di_minor dp3)
                          (add_vec (di_nlink dp3 : mword 16)
                             (mword_of_int 1 : mword 16))) bm3 dat3
                       (cr_setf_inode_ok fsc_cov fsc_logst dp3 bm3 dat3
                          (di_major dp3) (di_minor dp3) _ Hp3iok)
                       Hbumprl
                       (cr_setf_dir_ok icfg_nib dp3 dat3 (di_major dp3)
                          (di_minor dp3) _ Hp3dokn)
                       (dir_dots_ix_eq (bv_unsigned dind) dp3 _ dat3 dat3
                          (cr_setf_type _ _ _ _)
                          (fun _ => Hp3nlnz)
                          Hp3setfsz eq_refl Hp3ddix)
                       (dir_orphan_clean_live _ dat3 Hmtnz)
                       (dir_uniq_cong dp3 _ dat3 (cr_setf_type _ _ _ _)
                          (cr_setf_size _ _ _ _) Hp3duq)
                       with "Hdlnk Hdiat Hmeta Hpaddrs Hpind Hblocks Hdview Hfview
                             Htop")
            as "Hload".
          (* ===== +0xe0 c.mv a0,s1 ==================================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe0)) Ra0 Rs1 mmt
                    (K - 10)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (cri_0e0 with "Htext"). }
          iIntros (CIDT1 HqT1) "Hcg Hpc". iEval (rgne) in "Hcg".
          pose (T1 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mmt !!! Regidx Rs1))]> mmt).
          change (<[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mmt !!! Regidx Rs1))]> mmt) with T1.
          assert (HT1a0 : T1 !!! Regidx Ra0 = ientry kd).
          { rewrite /T1 upd_eq.
            destruct Hmmtregs as (_ & _ & Hd9 & _). rewrite Hd9.
            apply add_vec_zero_l. }
          assert (HT1regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor T1)
            by (rewrite /T1; apply cr_regs3_caller;
                [exact Hcsa0 | exact Hmmtregs]).
          assert (Hq0e2 : add_vec_int (mword_of_int (CK + 0xe0) : mword 64) 2
                          = mword_of_int (CK + 0xe2)) by pcw.
          iEval (rewrite Hq0e2) in "Hpc".
          (* ===== +0xe2 jal iunlockput(dp) ============================= *)
          assert (Htgu2 : add_vec (mword_of_int (CK + 0xe2) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090944 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0xe2)) Rra
                    (mword_of_int 2090944 : mword 21) T1 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_0e2 with "Htext"). }
          iIntros (CIDT2 HqT2) "Hcg Hpc".
          iEval (rewrite Htgu2) in "Hpc".
          pose (T2 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]>
                       T1).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]>
                       T1) with T2.
          assert (HT2ra : T2 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)
            by (rewrite /T2; apply upd_eq).
          assert (HT2a0 : T2 !!! Regidx Ra0 = ientry kd)
            by (rewrite /T2 upd_ne; [exact HT1a0 | nz]).
          assert (HT2regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor T2)
            by (rewrite /T2; apply cr_regs3_caller;
                [exact Hcsra | exact HT1regs]).
          (* BOTH CREDITS ARE IN HAND HERE, which is why this arm's
             [iunlockput(dp)] is FREE: the +0x140 flush unioned [IBLOCK dp]
             in itself, and [bmapstart] has been in the set since the first
             interior [dirlink] allocated the child's block 0.  [crb] pins
             the report [w = false] and [cru] kills the remaining unit, so
             the put spends nothing and [cr_budget_mkdir]'s ZERO-SLACK three
             survives it -- which is the floor create's [ok = true] post
             now owes, at the arm that has the least of it. *)
          assert (Hbm6 : bmapstart ∈ Sb6) by exact (Hsb6 _ Hbmem5).
          assert (Hcrbu : true = true
                    -> bmapstart ∈ (Sb6 ∪ {[IBLOCK dind inodestart]}))
            by (intros _;
                exact (cr_sub_union_sing Sb6 (IBLOCK dind inodestart)
                         bmapstart Hbm6)).
          assert (Hcruu : true = true
                    -> IBLOCK dind inodestart
                       ∈ (Sb6 ∪ {[IBLOCK dind inodestart]}))
            by (intros _; exact (cr_in_union_sing Sb6 (IBLOCK dind inodestart))).
          iDestruct (cpu_own_transport CIDh7 CIDT2 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
             goes in and the share it parked comes back in the post, so no
             bundleless out-state stands across the call. *)
          iDestruct (log_opS_named with "Hop") as (e0) "Hop".
          iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
          iApply (IUP.wp_iunlockput_dep_gen γs j γl γu γd γk pd pav pu bn γ
                    γi gtl γil γisl bmapstart inodestart nib
                    size dev kd (qd/2)%Qp (qd/2)%Qp gd (DepTx (qd/2)%Qp dev dind gd t (1/4)%Qp) dind
                    (cr_setf dp3 (di_major dp3) (di_minor dp3)
                       (add_vec (di_nlink dp3 : mword 16) (mword_of_int 1 : mword 16)))
                    bm3 (S u6) (Sb6 ∪ {[IBLOCK dind inodestart]})
                    true true false e0 _ _ pidv (DfracOwn (1/4)) dqb dqs
                    T2 (K - 10)%nat eb b lks
                    V ltac:(exact HKiup) eq_refl Hkdlt Hcrbu Hcruu
                    Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                    ltac:(exact Hipn6) Hj Hgs HT2a0 ltac:(lkbelow) Hglog eq_refl
                    with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2
                          Hitbl Hescd Hiregi Hiopen Hslkd Hslkdd Hdep Hidev
                          Hiinum Hivalid Hload Hshotf Hfrzl [$Hkeep2 $Hrud] Hsbb Hsbi Hbmr
                          Hppid Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
          all: try lkbelow.
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iEval (cbn beta iota). iEmpIntro. }
          iIntros (CIDT3 HqT3 mu2 n7 Sb7 wf7)
            "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi Hbsl
             %Hsb7 %Hwf7 %Hwf7c %Hn7 Hop Hisl2 Htq2".
          assert (Hpcu2 : ret_pc (T2 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0xe6)) by (rewrite HT2ra; pcw).
          iEval (rewrite Hpcu2) in "Hpc".
          assert (Hmu2regs : cr_regs3 m sp0 (ientry kd)
                    (mword_of_int 0 : mword 64) (ientry kslot)
                    ty major minor mu2)
            by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor T2 mu2 Hcsu2 HT2regs).
          iDestruct ("Hppback" with "Hppid") as "Hpriv".
          (* ===== +0xe6 c.mv s2,s3 : the ANSWER ======================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe6)) Rs2 Rs3 mu2
                    (K - 10)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (cri_0e6 with "Htext"). }
          iIntros (CIDT4 HqT4) "Hcg Hpc". iEval (rgne) in "Hcg".
          assert (Ht3v : add_vec (zero_reg : mword 64) (mu2 !!! Regidx Rs3)
                         = ientry kslot).
          { destruct Hmu2regs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
            apply add_vec_zero_l. }
          pose (T3 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu2 !!! Regidx Rs3))]> mu2).
          change (<[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu2 !!! Regidx Rs3))]> mu2) with T3.
          assert (HT3s2 : T3 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /T3 upd_eq; exact Ht3v).
          assert (HT3regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                    (ientry kslot) ty major minor T3)
            by exact (cr_regs3_s2 m sp0 (ientry kd)
                        (mword_of_int 0 : mword 64) (ientry kslot)
                        (ientry kslot) ty major minor mu2 _ Ht3v Hmu2regs).
          assert (Hq0e8 : add_vec_int (mword_of_int (CK + 0xe6) : mword 64) 2
                          = mword_of_int (CK + 0xe8)) by pcw.
          iEval (rewrite Hq0e8) in "Hpc".
          (* ===== +0xe8 c.ldsp s3,40(sp) : the LAZY RESTORE ============ *)
          assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 10)
            by (destruct HT3regs as (H2 & _); exact H2).
          assert (HT5 : add_vec (T3 !!! Regidx csp_rs1)
                          (zero_extend' 64
                             (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                        = pa_stk sp0 5) by (rewrite HT3sp; apply cr_frm5).
          iEval (rewrite -HT5) in "Hb5".
          iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0xe8))
                    (mword_of_int 5 : mword 6) Rs3 T3 (K - 10)%nat
                    (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc [] Hb5").
          { iApply (cri_0e8 with "Htext"). }
          iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
          iEval (rewrite HT5) in "Hb5".
          pose (T4 := <[Regidx Rs3 := regval_into_reg
                        (m !!! Regidx Rs3 : mword 64)]> T3).
          change (<[Regidx Rs3 := regval_into_reg
                        (m !!! Regidx Rs3 : mword 64)]> T3) with T4.
          assert (HT4regs : cr_regs3 m sp0 (ientry kd) (ientry kslot)
                    (m !!! Regidx Rs3 : mword 64) ty major minor T4)
            by exact (cr_regs3_s3 m sp0 (ientry kd) (ientry kslot)
                        (ientry kslot) (m !!! Regidx Rs3 : mword 64)
                        ty major minor T3 _ eq_refl HT3regs).
          assert (HT4s2 : T4 !!! Regidx Rs2 = ientry kslot)
            by (rewrite /T4 upd_ne; [exact HT3s2 | nz]).
          assert (Hq0ea : add_vec_int (mword_of_int (CK + 0xe8) : mword 64) 2
                          = mword_of_int (CK + 0xea)) by pcw.
          iEval (rewrite Hq0ea) in "Hpc".
          (* ===== +0xea c.j +0x70 ====================================== *)
          assert (Htg070m : add_vec (mword_of_int (CK + 0xea) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 1987 : mword 11) ('b"0"))))
                    = mword_of_int (CK + 0x70)) by pcw.
          iApply (wp_cj_s_sconf (mword_of_int (CK + 0xea))
                    (sign_extend' 21
                       (concat_vec (mword_of_int 1987 : mword 11) ('b"0")))
                    T4 (K - 10)%nat b
                    ltac:(rewrite Htg070m; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_0ea with "Htext"). }
          iIntros (CIDT6 HqT6). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg070m) in "Hpc".
          iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2")
            as (nfj) "Hnb16".
          iPoseProof ("Htail" $! CIDT6) as "Ht".
          iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
          iApply ("Ht" $! T4 (m !!! Regidx Rs3 : mword 64) nfj with
                    "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
          { exact (cr_tregs_of_regs3 m sp0 (ientry kd) (ientry kslot)
                     ty major minor T4 HT4regs). }
          iIntros (CIDfm Hsfm mf) "%Hcsf %Ha0f Hcg Hpc".
          iDestruct (cpu_own_transport CIDT3 CIDfm 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (iref_slots_combine with "Hislk Hisl2") as "Hisl".
          iDestruct (iref_slots_combine with "Hisl Hislrr") as "Hisl".
          (* THE MOVER (§9 W3): the child's own ["."] and [".."] links moved
             its bytes. *)
          iApply fupd_wp.
          iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (dv_of dc2 dat2)
                  ltac:(solve_ndisj) with "Hiregi Hcdview") as "Hcdview".
          iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (fv_of dc2 dat2)
                  ltac:(solve_ndisj) with "Hiregi Hcfview") as "Hcfview".
          (* ...and the ERA's abstract value at that same record
             (durable-disk 2b-inode-3). *)
          iMod (cr_dirty_clear ⊤ t (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor
                               (mword_of_int 1 : mword 16)) bmc datc)
                  (era_node dc2 bm2 dat2)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned cinum) fsc_cov fsc_logst
                     dc2 bm2 dat2 Hc2iok Hc2rl Hc2duq (Hc2ddix Ht162))
                  with "[] Hdirty Hctop") as "[Htx Hctop]";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          iApply fupd_wp.
          iMod (ic_grow_tx ⊤ fsc_ic fsc_fs γi fsc_cov fsc_logst kslot (q/2)%Qp dev cinum g
                  true t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
                  ltac:(solve_ndisj) with "Hescc Hcivalid Hcdep Htq2")
            as "(Hcivalid & Hcdep)".
          iModIntro.
          iDestruct (ic_tx_dep_intro with "Hcdep Htx") as "Hcdep".
          iSpecialize ("Hcont" $! CIDfm with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf true true kslot (q/2)%Qp (q/2)%Qp g cinum
                    dc2 bm2 n7 Sb7 (1 + (1 + (ns - 3)))%nat
                    with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hpriv
                          Hpath Hbsl [%] Hisl [%] Hop [Hslkc Hcslkd
                          Hcdep Hcidev Hciinum Hcivalid Hcdlnk2 Hcdiat Hcmeta
                          Hcmap Hcblocks Hcdview Hcfview Hctop Hcfrz Hckeep
                          Hruc]").
          { exact Hcsf. }
          { exact (cr_slots_3 _ ns eq_refl Hns). }
          { split_and!.
            - exact (cr_sub2 _ _ _
                       (cr_sub2 _ _ _
                          (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5)
                          (cr_sub2 _ _ _ Hsb6
                             (cr_sub_union_sing Sb6
                                (IBLOCK dind inodestart)))) Hsb7).
            - clear -Hn7 Hn6c Hn5c Hn4c Hn3u. lia.
            - intros _. rewrite (Hwf7c eq_refl) in Hn7.
              exact (cr_fail_ip_right (S u6) n7 Hipn6 (proj1 Hn7)). }
          iEval (rewrite /inode_map) in "Hcmap".
          iDestruct "Hcmap" as "[Hcaddrs2 Hcind2]".
          iDestruct (ic_mk_loaded fsc_fs γi fsc_cov fsc_logst kslot cinum dc2 bm2 dat2
                       Hc2iok Hc2rl Hc2dokn (Hc2ddix Ht162)
                       (dir_orphan_clean_of_only dc2 dat2 Hc2dots) Hc2duq
                       with "Hcdlnk2 Hcdiat Hcmeta Hcaddrs2 Hcind2 Hcblocks
                             Hcdview Hcfview Hctop")
            as "Hcloadf".
          iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
          { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
          iSplitR.
          { iPureIntro. split; [rewrite Ha0f; exact HT4s2 |].
            split; [exact Hkslt |].
            split; [split; [exact (proj1 Hcpos) | exact Hcinb] |].
            split; [exact Hc2ty |].
            split; [exact Hc2mj |].
            split; [exact Hc2mn |].
            split; [exact Hc2nlz |].
            intro Hnd. exfalso. exact (Hnd Htdir). }
          iApply (create_locked_mk γi
                    _ _ _ _ _ _ _ _ _ gil gisl
                    with "Hslkc Hcslkd Hcdep Hcidev Hciinum
                          Hcivalid Hcloadf Hcshot2 Hcfrz Hckeep Hruc").
        * (* =========================================================== *)
          (*  FAIL ENTRY 3 (+0x130 taken): the PARENT's own [dirlink]     *)
          (*  fell short.  This entry sits BEFORE the +0x134 [lhu], so    *)
          (*  the parent's count is still its entry one and its entry     *)
          (*  fragments go back unchanged -- available because dirlink's  *)
          (*  atomicity at [tot < 16] IS [tot = 0].                       *)
          (* =========================================================== *)
          assert (Htot30 : tot3 = 0%nat).
          { destruct Hatom3 as [Hz | H16];
              [exact Hz | exfalso; clear -H16 Htlt3; lia]. }
          subst tot3.
          (* THE ENTRY UNITS RIDE (durable-disk 2b-inode-5):
             nothing was written, so the entry map does not move. *)
          iDestruct (ent_toks_dirlink_nop (fs_gamma_L fsc_fs) (bv_unsigned dind)
                       dn dp3 bm bm3 data dat3
                       (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                                   (bname 14 nf)) !!! j)
                       (dir_nrec (bv_unsigned (di_size dn)))
                       (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                       0%nat D eq_refl (dir_slot_le _ _) eq_refl
                       Hp3ty Hp3nl Hp3szmax Hrng3
                       Hholes Hholes3 Hszcap (Hcap3 Hszcap)
                       with "Hetk") as "Hetk".
          assert (Heqentm := dir_entries_dirlink_nop_eq dn dp3 bm bm3 data dat3
                     (fun j => dirent_bytes (de_of_name (cr_low16 cinum)
                                 (bname 14 nf)) !!! j)
                     (dir_nrec (bv_unsigned (di_size dn)))
                     (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                     0%nat eq_refl (dir_slot_le _ _) eq_refl
                     Hp3ty Hp3szmax Hrng3
                     Hholes Hholes3 Hszcap (Hcap3 Hszcap)).
          assert (Hgrowm : forall s',
                     is_Some (dir_entries (era_node dn bm data) !! s')
                     -> is_Some (dir_entries (era_node dp3 bm3 dat3) !! s'))
            by (intros s' Hs'; rewrite Heqentm; exact Hs').
          iDestruct (dlinks_intro _ _ _ _ _ D
                       ltac:(exact (FsStateInode.ent_dset_ok_grow _ _ D
                                      Hgrowm Hdok0))
                       ltac:(exact (FsStateInode.node_exact_cong
                                      (era_node dn bm data)
                                      (era_node dp3 bm3 dat3) D
                                      ltac:(rewrite /fn_is_dir /fn_type
                                              !era_node_rec Hp3ty //)
                                      ltac:(rewrite /fn_nlink !era_node_rec
                                              Hp3nl //)
                                      Hxact0))
                       with "Hetk") as "Hdlnk".
          iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x130))
                    (mword_of_int 22 : mword 13) Ra0 md3 (K - 10)%nat b
                    ltac:(nz)
                    ltac:(rgne; rewrite Ha0m3; exact cr_bltz_m1)
                    ltac:(rewrite Htg146c; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cri_130 with "Htext"). }
          iIntros (CIDX3 HqX3). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg146c) in "Hpc".
          iDestruct (cpu_own_transport CIDd3 CIDX3 0%nat eb (proc_addr j) b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
          iEval (rewrite Hns3) in "Hislr".
          iAssert (ity_shot gd (di_type dp3)) as "#Hshotp3".
          { rewrite Hp3ty. iExact "Hshotl". }
          iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
          { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
          assert (Hipf3 : (iput_units <= n6)%nat)
            by exact (cr_mkdir_fail3 n5 n6 _ _ _ _ _ Hn5lo eq_refl Hspend3).
          (* THE MOVERS (namei-pinned-lookup.md §9 W3): the parent's append
             and the child's two interior links both moved bytes. *)
          (* THE PARENT'S RECORD-ONLY FACTS AT [dp3] (durable-disk
             2b-inode-3): the failing append is [tot = 0], so the record
             the entry re-parks is the walk's own, one MAX on.  They come
             BEFORE the retag now, because the retag owes the registry's
             row (durable-disk lane A). *)
          assert (Hp3rl : inode_rec_local dp3).
          { apply (inode_rec_local_same_type dn dp3 Hrl Hp3ty).
            - rewrite Hp3nl. exact (proj1 (proj2 Hrl)).
            - intros _. rewrite Hp3szmax. apply cr_max_div16.
              + apply (proj2 (proj2 Hrl)).
                rewrite Htydir. vm_compute. reflexivity.
              + exists (Z.of_nat (dir_slot data
                          (dir_nrec (bv_unsigned (di_size dn)))))%Z.
                rewrite Nat.add_0_r Nat2Z.inj_mul. lia. }
          iApply fupd_wp.
          iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (dv_of dp3 dat3)
                  ltac:(solve_ndisj) with "Hiregi Hdview") as "Hdview".
          iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (fv_of dp3 dat3)
                  ltac:(solve_ndisj) with "Hiregi Hfview") as "Hfview".
          iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dind)
                  (era_node dn bm data) (era_node dp3 bm3 dat3)
                  ltac:(solve_ndisj)
                  (inode_local_of_ok_rec (bv_unsigned dind) fsc_cov fsc_logst dp3
                     bm3 dat3 Hp3iok Hp3rl Hp3duq Hp3ddix)
                  with "[] Htop") as "Htop";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (dv_of dc2 dat2)
                  ltac:(solve_ndisj) with "Hiregi Hcdview") as "Hcdview".
          iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (fv_of dc2 dat2)
                  ltac:(solve_ndisj) with "Hiregi Hcfview") as "Hcfview".
          (* ...and the ERA's abstract value at that same record
             (durable-disk 2b-inode-3). *)
          iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
                  (era_node (cr_setf dnc major minor
                               (mword_of_int 1 : mword 16)) bmc datc)
                  (era_node dc2 bm2 dat2)
                  ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
            [iApply (ireg_inv_ftop with "Hiregi") |].
          iModIntro.
          (* THE ["."] UNIT COMES BACK OUT OF THE CHILD'S PAYLOAD (lane
             G5).  [cr_fail_mkdir_body] takes the child WITHOUT its
             [dlinks] and re-mints one itself, so this walk is the
             last holder of the child's own tokens -- and the
             [ip->nlink = 0] flush below still needs the WHOLE pile the
             fill minted, one of whose units this arm's
             [dirlink(ip, ".", ip)] filed in the child's ["."] entry.  The
             value comes off the sibling the walk still holds, by the
             register's own agreement. *)
          iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                       (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                       Hdot1c Horph1c with "Hcetk2") as "[(%vf1 & Hdotf1) _]".
          iApply fupd_wp.
          iMod (IregLinkNz.ireg_toks_agree ⊤ γi fsc_fs inodestart nib cinum _
                  vf1 (cr_ity ty (bv_unsigned dind))
                  ltac:(solve_ndisj) Hcinb
                  with "Hiregi Hcdiat Hdotf1 Htoken")
            as "([%Hvf1 _] & Hcdiat & Hdotf1 & Htoken)".
          iModIntro.
          iAssert (FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                     (FsStateLink.link_reps (cr_delta ty)
                        (cr_ity ty (bv_unsigned dind))))
            with "[Htoken Hdotf1]" as "Htoken".
          { rewrite (cr_delta_dir ty Htdirc) FsStateLink.link_toks_reps_S
              FsStateLink.link_reps_1.
            iSplitL "Htoken"; [iExact "Htoken" | rewrite -Hvf1; iExact "Hdotf1"]. }
          iPoseProof (cr_fail_mkdir_half γs j γl γu γd γk pd pav pu bn γ γi
                        gtl γa γf γpr bmapstart inodestart nib
                        ninodes size dev plen pfun pv ty major minor V u
                        Sb ns pidv dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                        kd qd gd γil γisl dind nf nsl t
                        HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                        Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                        with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                              Hprocs Hdevi Hgeom Hdlk") as "Hfl".
          iPoseProof ("Hfl" $! CIDX3) as "Hf".
          iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
          iApply ("Hf" $! md3 kslot q g gil gisl cinum dp3 bm3 dat3
                    dc2 bm2 dat2 n6 Sb6
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%]
                          Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14
                          Hnb2 Hslkd Hslkdd Hdep Hidev Hiinum Hivalid
                          Hdlnk Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop Hshotp3 Hfrzl Hkeep Hrud
                          Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
                          Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop Hcshot2 Hcfrz Hckeep Hruc
                          Htoken
                          Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                          Hislr Hop Hdirty Hcont").
          { exact Hmd3regs. }
          { exact Htdir. }
          { exact Hkdlt. }
          { exact Hdib. }
          { rewrite Hp3ty. exact Htydir. }
          { rewrite Hp3nl. exact Hnl0. }
          { exact Hp3iok. }
          { exact Hp3dok. }
          { exact Hp3ddix. }
          { exact Hp3duq. }
          { exact Hp3rl. }
          { exact Hkslt. }
          { exact Hcpos. }
          { exact Hcinb. }
          { exact Hc2ty. }
          { exact Hc2mj. }
          { exact Hc2mn. }
          { exact Hc2nl. }
          { exact Hc2iok. }
          { exact Hc2rl. }
          { exact Hc2dok. }
          { exact Hc2duq. }
          { exact Hc2dots. }
          { exact (cr_sub2 _ _ _
                     (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5) Hsb6). }
          { exact (Hsb6 _ (Hsb5 _ Hcmem4)). }
          { split; [exact Hipf3 | clear -Hn6c Hn5c Hn4c Hn3u; lia]. }
          { right. exact (Hsb6 _ Hbmem5). }
      + (* ============================================================= *)
        (*  FAIL ENTRY 2 (+0x11e taken): the [".."] link fell short.  The *)
        (*  parent is still untouched; the child is [dc2], one record on. *)
        (* ============================================================= *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x11e))
                  (mword_of_int 40 : mword 13) Ra0 md2 (K - 10)%nat b
                  ltac:(nz)
                  ltac:(rgne; rewrite Ha0m2; exact cr_bltz_m1)
                  ltac:(rewrite Htg146b; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (cri_11e with "Htext"). }
        iIntros (CIDX2 HqX2). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg146b) in "Hpc".
        iDestruct (cpu_own_transport CIDd2 CIDX2 0%nat eb (proc_addr j) b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
        iEval (rewrite Hns3) in "Hislr".
        iAssert (ity_shot g (di_type dc2)) as "#Hcshot2".
        { rewrite Hc2ty0 Hc1ty0 cr_setf_type. iExact "Hcshot". }
        destruct (cr_mkdir_fail2 n3 n4 n5 _ _ _ _ _ Hn3lo Hspend1 Hspend2
                    eq_refl) as [Hipf2 HipfS2].
        (* the failing [".."] is dirlink's atomicity again: [tot < 16] IS
           [tot = 0], so the child's size is still the ["."] record's 16 --
           which is what the record-only facts need (2b-inode-3). *)
        assert (Htot20 : tot2 = 0%nat).
        { destruct Hatom2 as [Hz | H16];
            [exact Hz | exfalso; clear -H16 Htlt2; lia]. }
        assert (Hc2rl : inode_rec_local dc2).
        { apply (inode_rec_local_same_type dnc dc2 Hrl_datc).
          - rewrite Hc2ty0 Hc1ty0 cr_setf_type. reflexivity.
          - rewrite Hc2nlz. lia.
          - intros _. rewrite Hc2szmax Hc1szmax Hcsz0 Ht161 Htot20.
            exists 1%Z. vm_compute. reflexivity. }
        (* THE MOVER (§9 W3): the child's two interior links moved its bytes;
           the parent's own append has not run on this entry. *)
        iApply fupd_wp.
        iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (dv_of dc2 dat2)
                  ltac:(solve_ndisj) with "Hiregi Hcdview") as "Hcdview".
        iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (fv_of dc2 dat2)
                ltac:(solve_ndisj) with "Hiregi Hcfview") as "Hcfview".
        (* ...and the ERA's abstract value at the same record. *)
        iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
                (era_node (cr_setf dnc major minor
                             (mword_of_int 1 : mword 16)) bmc datc)
                (era_node dc2 bm2 dat2)
                ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
          [iApply (ireg_inv_ftop with "Hiregi") |].
        iModIntro.
        (* THE ["."] UNIT COMES BACK OUT OF THE CHILD'S PAYLOAD (lane
           G5).  [cr_fail_mkdir_body] takes the child WITHOUT its
           [dlinks] and re-mints one itself, so this walk is the
           last holder of the child's own tokens -- and the
           [ip->nlink = 0] flush below still needs the WHOLE pile the
           fill minted, one of whose units this arm's
           [dirlink(ip, ".", ip)] filed in the child's ["."] entry.  The
           value comes off the sibling the walk still holds, by the
           register's own agreement. *)
        iDestruct (FsStateInode.ent_toks_dot_take (fs_gamma_L fsc_fs)
                     (bv_unsigned cinum) (era_node dc1 bm1 dat1) Dc1
                     Hdot1c Horph1c with "Hcetk2") as "[(%vf1 & Hdotf1) _]".
        iApply fupd_wp.
        iMod (IregLinkNz.ireg_toks_agree ⊤ γi fsc_fs inodestart nib cinum _
                vf1 (cr_ity ty (bv_unsigned dind))
                ltac:(solve_ndisj) Hcinb
                with "Hiregi Hcdiat Hdotf1 Htoken")
          as "([%Hvf1 _] & Hcdiat & Hdotf1 & Htoken)".
        iModIntro.
        iAssert (FsStateLink.link_toks (fs_gamma_L fsc_fs) (bv_unsigned cinum)
                   (FsStateLink.link_reps (cr_delta ty)
                      (cr_ity ty (bv_unsigned dind))))
          with "[Htoken Hdotf1]" as "Htoken".
        { rewrite (cr_delta_dir ty Htdirc) FsStateLink.link_toks_reps_S
            FsStateLink.link_reps_1.
          iSplitL "Htoken"; [iExact "Htoken" | rewrite -Hvf1; iExact "Hdotf1"]. }
        iPoseProof (cr_fail_mkdir_half γs j γl γu γd γk pd pav pu bn γ γi
                      gtl γa γf γpr bmapstart inodestart nib ninodes
                      size dev plen pfun pv ty major minor V u Sb ns pidv
                      dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                      kd qd gd γil γisl dind nf nsl t
                      HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                      Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                      with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                            Hprocs Hdevi Hgeom Hdlk") as "Hfl".
        iPoseProof ("Hfl" $! CIDX2) as "Hf".
        iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
        iApply ("Hf" $! md2 kslot q g gil gisl cinum dn bm data dc2 bm2 dat2
                  n5 Sb5
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
                        Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk
                        Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop Hshotl Hfrzl Hkeep Hrud
                        Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
                        Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop Hcshot2 Hcfrz Hckeep Hruc Htoken
                        Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                        Hislr Hop Hdirty Hcont").
        { exact Hmd2regs. }
        { exact Htdir. }
        { exact Hkdlt. }
        { exact Hdib. }
        { exact Htydir. }
        { exact Hnl0. }
        { exact Hiok. }
        { exact Hdok. }
        { exact Hddix. }
        { exact Hduq. }
        { exact Hrl. }
        { exact Hkslt. }
        { exact Hcpos. }
        { exact Hcinb. }
        { exact Hc2ty. }
        { exact Hc2mj. }
        { exact Hc2mn. }
        { exact Hc2nl. }
        { exact Hc2iok. }
        { exact Hc2rl. }
        { exact Hc2dok. }
        { exact Hc2duq. }
        { exact Hc2dots. }
        { exact (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb3 Hsb4) Hsb5). }
        { exact (Hsb5 _ Hcmem4). }
        { split; [exact Hipf2 | clear -Hn5c Hn4c Hn3u; lia]. }
        { left. exact HipfS2. }
    - (* =============================================================== *)
      (*  FAIL ENTRY 1 (+0x10a taken): the ["."] link fell short.  Both   *)
      (*  interior links are on the CHILD, so the parent goes over        *)
      (*  exactly as [cr_mkdir_body] handed it -- no re-park, no index    *)
      (*  description -- and the child is [dc1] at the record the failing *)
      (*  writei left.  The sibling's premises are all persistent, so     *)
      (*  this branch instantiates the lemma itself.                      *)
      (* =============================================================== *)
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0x10a))
                (mword_of_int 60 : mword 13) Ra0 md1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Ha0m1; exact cr_bltz_m1)
                ltac:(rewrite Htg146a; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cri_10a with "Htext"). }
      iIntros (CIDX1 HqX1). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg146a) in "Hpc".
      iDestruct (cpu_own_transport CIDd1 CIDX1 0%nat eb (proc_addr j) b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hislk Hislrr") as "Hislr".
      iEval (rewrite Hns3) in "Hislr".
      iAssert (ity_shot g (di_type dc1)) as "#Hcshot1".
      { rewrite Hc1ty0 cr_setf_type. iExact "Hcshot". }
      destruct (cr_mkdir_fail1 n3 n4 _ _ _ Hn3lo Hspend1) as [Hipf1 HipfS1].
      (* dirlink's atomicity once more: the failing ["."] is [tot = 0], so
         the child is still the fresh record's size (2b-inode-3). *)
      assert (Htot10 : tot1 = 0%nat).
      { destruct Hatom1 as [Hz | H16];
          [exact Hz | exfalso; clear -H16 Htlt1; lia]. }
      assert (Hc1rl : inode_rec_local dc1).
      { apply (inode_rec_local_same_type dnc dc1 Hrl_datc).
        - rewrite Hc1ty0 cr_setf_type. reflexivity.
        - rewrite Hc1nl. exact cr_nl_short_1.
        - intros _. rewrite Hc1szmax Hcsz0 Htot10.
          exists 0%Z. vm_compute. reflexivity. }
      (* THE MOVER (§9 W3): the child's first interior link moved its bytes. *)
      iApply fupd_wp.
      iMod (fv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (fv_of dc1 dat1)
              ltac:(solve_ndisj) with "Hiregi Hcfview") as "Hcfview".
      iMod (dv_set_rt ⊤ γi fsc_fs inodestart nib _ _ (dv_of dc1 dat1)
                  ltac:(solve_ndisj) with "Hiregi Hcdview") as "Hcdview".
      (* ...and the ERA's abstract value at the same record. *)
      iMod (cr_dirty_retag ⊤ t (bv_unsigned cinum)
              (era_node (cr_setf dnc major minor
                           (mword_of_int 1 : mword 16)) bmc datc)
              (era_node dc1 bm1 dat1)
              ltac:(solve_ndisj) with "[] Hdirty Hctop") as "[Hdirty Hctop]";
        [iApply (ireg_inv_ftop with "Hiregi") |].
      iModIntro.
      iPoseProof (cr_fail_mkdir_half γs j γl γu γd γk pd pav pu bn γ γi
                    gtl γa γf γpr bmapstart inodestart nib ninodes
                    size dev plen pfun pv ty major minor V u Sb ns pidv
                    dqb dqs dqbs dqn m sp0 ret_tgt K eb b lks
                    kd qd gd γil γisl dind nf nsl t
                    HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                    Hist0 Hcovb Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb
                    with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                          Hprocs Hdevi Hgeom Hdlk") as "Hfl".
      iPoseProof ("Hfl" $! CIDX1) as "Hf".
      iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
      iApply ("Hf" $! md1 kslot q g gil gisl cinum dn bm data dc1 bm1 dat1
                n4 Sb4
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                      Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
                      Hslkd Hslkdd Hdep Hidev Hiinum Hivalid Hdlnk
                      Hdiat Hmeta Hmap Hblocks Hdview Hfview Htop Hshotl Hfrzl Hkeep Hrud
                      Hslkc Hcslkd Hcdep Hcidev Hciinum Hcivalid
                      Hcdiat Hcmeta Hcmap Hcblocks Hcdview Hcfview Hctop Hcshot1 Hcfrz Hckeep Hruc Htoken
                      Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
                      Hislr Hop Hdirty Hcont").
      { exact Hmd1regs. }
      { exact Htdir. }
      { exact Hkdlt. }
      { exact Hdib. }
      { exact Htydir. }
      { exact Hnl0. }
      { exact Hiok. }
      { exact Hdok. }
      { exact Hddix. }
      { exact Hduq. }
      { exact Hrl. }
      { exact Hkslt. }
      { exact Hcpos. }
      { exact Hcinb. }
      { exact Hc1ty. }
      { exact Hc1mj. }
      { exact Hc1mn. }
      { exact Hc1nl. }
      { exact Hc1iok. }
      { exact Hc1rl. }
      { exact Hc1dok. }
      { exact Hc1duq. }
      { exact (Hc1dots Htlt1). }
      { exact (cr_sub2 _ _ _ Hsb3 Hsb4). }
      { exact (Hsb4 _ Hmem3). }
      { split; [exact Hipf1 | clear -Hn4c Hn3u; lia]. }
      { left. exact HipfS1. }
  Qed.

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
    iDestruct (word_pointsto_aligned_p with "H9") as %Ha9.
    iDestruct (word_pointsto_aligned_p with "H10") as %Ha10.
    iPureIntro. split; [exact Ha10 | exact Ha9].
  Qed.

  Lemma wp_create_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γi : gname)
      (gtl : gname)
      (γa γf γpr : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_create_sconf_body γs j γl γu γd γk pd pav pu bn γ γi gtl
                         γa γf γpr bmapstart inodestart nib
                         ninodes size dev plen pfun ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb b lks.
  Proof.
    rewrite /wp_create_sconf_body.
    intros HK Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc Hbmsl
           Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3 Hnib16
           Htynz Htyw Hpkc Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb.
    (* (L5) at the fresh record is (L5) at the type word (2b-inode-3). *)
    pose proof (InodeRegion.ireg_ty_ok_of_w (ialloc_fresh ty) Htyw) as Htyk.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    iIntros "Hcg Hcnt #Htext Hpc #Hkd #Hpk #Hbio #Hlogc #Hkenv
             #Hitb2 #Hitbl #Hesc #Hslks #Hiregi #Hiopen Hsbn Hsbi Hsbs Hsbb #Hbmr
             Hpriv Hpath #Hprocs #Hdevi #Hgeom #Hdlk Hbsl Hisl Hop Htx Hcont".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_cap_align m K b (proc_addr j) HK10 with "Hcg")
      as %[Hal10 Hal9].
    iApply (cr_found_half γs j γl γu γd γk pd pav pu bn γ γi gtl
              γa γf γpr bmapstart inodestart nib ninodes size
              dev plen pfun ty major minor V u Sb ns pidv
              dqb dqs dqbs dqn m K eb b lks
              HK Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc
              Hbmsl Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3
              Htynz Htyk Hpkc Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                    Hitb2 Hitbl Hesc Hslks Hiregi Hiopen Hsbn Hsbi Hsbs Hsbb Hbmr
                    Hpriv Hpath Hprocs Hdevi Hgeom Hdlk Hbsl Hisl Hop Htx
                    [] Hcont").
    iApply (cr_alloc_half γs j γl γu γd γk pd pav pu bn γ γi gtl
              γa γf γpr bmapstart inodestart nib ninodes size
              dev plen pfun (m !!! Regidx Ra0 : mword 64)
              ty major minor V u Sb ns pidv dqb dqs dqbs dqn m
              (m !!! Regidx csp_rs1 : mword 64)
              (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
              HK Hdev Hnib Hglog Hist Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl
              Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Htynz Htyk Hpkc
              Hu Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
              with "Htext Hkd Hpk Hbio Hlogc Hkenv Hitb2 Hitbl Hesc
                    Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk [] []").
    - iIntros (kd qd gd γil γisl dind dn bm data nf nsl t).
      iApply (cr_mkdir_half γs j γl γu γd γk pd pav pu bn γ γi gtl
                γa γf γpr bmapstart inodestart nib ninodes size
                dev plen pfun (m !!! Regidx Ra0 : mword 64)
                ty major minor V u Sb ns pidv dqb dqs dqbs dqn m
                (m !!! Regidx csp_rs1 : mword 64)
                (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
                kd qd gd γil γisl dind dn bm data nf nsl t
                HK Hdev Hnib Hglog Hist Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl
                Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Hpkc
                Hu Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
                with "Htext Hkd Hpk Hbio Hlogc Hkenv Hitb2 Hitbl
                      Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk").
    - iIntros (kd qd gd γil γisl dind dn bm data nf nsl t).
      iApply (cr_fail_half γs j γl γu γd γk pd pav pu bn γ γi gtl
                γa γf γpr bmapstart inodestart nib ninodes size
                dev plen pfun (m !!! Regidx Ra0 : mword 64)
                ty major minor V u Sb ns pidv dqb dqs dqbs dqn m
                (m !!! Regidx csp_rs1 : mword 64)
                (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
                kd qd gd γil γisl dind dn bm data nf nsl t
                HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                Hist0 Hcovb Hiregb Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
                with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                      Hprocs Hdevi Hgeom Hdlk").
  Qed.

End ProofCreateMain.

End CreateProof.
