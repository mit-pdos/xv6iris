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
   [SpecCreateFreshTy]), ARM A-FAIL (+0xec), the three metadata [sh]s, the
   LINK MINT at +0xc4 ([SpecIupdate.wp_iupdate_link]), the T_DIR branch at
   +0xca, the [dirlink(dp,name)] at +0xd8 and ARM C-OK-FILE (+0xe0..+0xea).
   Two of its branches leave through a PREMISE of their own -- the whole
   T_DIR sub-branch through [cr_mkdir_body] and the failing [dirlink]
   through [cr_fail_body] -- so its [Print Assumptions] is the standing six
   plus [create_fresh_ty] and nothing else.  Its conclusion is
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
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelText KernelDataInv.
Require Import KernelRvcDecode.
Require Import VcGen.
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
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import DinodeSlot.
Require Import DirentEnc.
Require Import PathElems.
Require Import DirView.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import PanicStub.
Require Import SpecPrintk.
Require Import SpecBmap SpecWritei.
Require Import SpecIput SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNamex SpecNameiparent.
Require Import SpecCreate.
(* the ONE assumed contract: the four-instruction span +0xa4..+0xb0 that
   pins [di_type dn = ty] across [ialloc]/[ilock].  Taken as a FUNCTOR
   ARGUMENT beside the seven real callees, so that this file names no
   [Axiom] and [Print Assumptions] reports it only where the functor is
   instantiated -- exactly as it reports the other seven. *)
Require Import SpecCreateFreshTy.
Require Import CreateBudget.
Require Import CodeCreate.
Require Import ProofDirlookupParts ProofNamexParts ProofCreateParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* claude-notes/durable-notes.md: a syscall-altitude goal carries
   [ProcInv.tf_page]'s 4096-conjunct big-op, and printing it turns a
   one-line mistake into a forty-minute non-answer. *)
Set Printing Depth 40.

Module CreateProof (NP : NAMEIPARENT) (IL : ILOCK) (IUP : IUNLOCKPUT)
                   (DL : DIRLOOKUP) (IA : IALLOC) (IU : IUPDATE)
                   (DLK : DIRLINK) (CFT : CREATE_FRESH_TY).
(* NOT ascribed [: CREATE] yet: the seal is [wp_create_sconf], which needs
   the allocate half.  [IA] / [IU] / [DLK] are the allocate half's callees
   and are taken here so that the functor's arity does not move when it
   lands. *)

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
   [SpecCreateFreshTy.cr_cs_but_s3], i.e. "callee-saved everywhere but s3",
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

(* the three slot figures the found half hands back, against [create_slots]:
   ARM N / ARM G return the ledger WHOLE, F-OK keeps one out for the inode
   it returns, F-BAD's second [iunlockput] gives that one back too. *)
Lemma cr_slots_ns (ns : nat) : (create_slots <= ns)%nat ->
  ((ns - create_slots)%nat <= ns)%nat /\ (ns <= ns)%nat.
Proof. unfold create_slots. lia. Qed.

Lemma cr_slots_1 (ns : nat) : (create_slots <= ns)%nat ->
  ((ns - create_slots)%nat <= (1 + (ns - 2))%nat)%nat
  /\ ((1 + (ns - 2))%nat <= ns)%nat.
Proof. unfold create_slots. lia. Qed.

Lemma cr_slots_2 (ns : nat) : (create_slots <= ns)%nat ->
  ((ns - create_slots)%nat <= (1 + (1 + (ns - 2)))%nat)%nat
  /\ ((1 + (1 + (ns - 2)))%nat <= ns)%nat.
Proof. unfold create_slots. lia. Qed.

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

(* ---- (vi) writei's RECORD AT THE SIZE [DirLinks.dir_links_dirlink] AND
   [DirView.dir_ok_dirlink] BOTH ASK FOR.  [SpecWritei.wi_dinode] installs
   [max(size, off+tot)] as a 32-bit literal; the two re-park lemmas want it
   read back over [Z].  The side condition is the only place the walk has to
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
Lemma cr_slots_3 (ns : nat) : (create_slots <= ns)%nat ->
  ((ns - create_slots)%nat <= (1 + (1 + (ns - 3)))%nat)%nat
  /\ ((1 + (1 + (ns - 3)))%nat <= ns)%nat.
Proof. unfold create_slots. lia. Qed.

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
(*  2.  THE PROOF                                                         *)
(* ===================================================================== *)

Section ProofCreateMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !irefslotG Σ, !iregG Σ}.
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
            live_gen_split inode_ident_split.
    iSplit.
    - iIntros "($ & [$ Hl2] & [$ Hi2])". iFrame.
    - iIntros "[($ & $ & $) [$ $]]".
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
    (pa_stk sp0 10) ↦₈ w1 -∗ (pa_stk sp0 9) ↦₈ w2 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16.
  Proof.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "H1 H2".
    iDestruct (slot_bytes_own with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own with "H2") as "[%Ha2 B2]".
    iSplitR; [done |].
    change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iSplitL "B1"; [iExact "B1" | iExact "B2"].
  Qed.

  Lemma cr_bytes_slots (sp0 : Arch.pa) :
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16 ⊢
    ∃ w1 w2 : bv 64, (pa_stk sp0 10) ↦₈ w1 ∗ (pa_stk sp0 9) ↦₈ w2.
  Proof.
    intros Ha1 Ha2.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "B". change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iDestruct "B" as "[B1 B2]".
    iDestruct (bytes_own_slot _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot _ Ha2 with "B2") as (w2) "H2".
    iExists w1, w2. iFrame.
  Qed.

  (* the sixteen-byte local is FOURTEEN bytes of [name] and two of slack;
     [nameiparent] and [dirlookup] both want exactly the fourteen. *)
  Lemma cr_split14 (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ f j) ⊣⊢
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ f j) ∗
    ([∗ list] j ∈ seq 14 2, pa_add a j ↦ₘ f j).
  Proof.
    change 16%nat with (14 + 2)%nat. rewrite seq_app big_sepL_app.
    reflexivity.
  Qed.

  (* ...and back: the fourteen bytes and the two of slack rejoin into the
     sixteen the frame slots are.  The two halves carry DIFFERENT byte
     functions ([nameiparent] rewrote only the fourteen), so the join has to
     produce the pointwise splice rather than reuse either. *)
  Lemma cr_join14 (a : Arch.pa) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 14 2, pa_add a j ↦ₘ g j) -∗
    ∃ h : nat -> bv 8, ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ h j).
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

  (* the two family accessors, at create's own persistent bundles *)
  Lemma cr_slk_acc (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (SpecDirlink.ic_sleeplocks cn -∗
     ∃ γil γisl : gname,
       is_sleeplock γil γisl (i_lock (ientry k)) "inode"%string (ic_tok cn k)
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /SpecDirlink.ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma cr_esc_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma cr_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* the p->cwd the walk lends and gets back untouched *)
  Lemma cr_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
  Proof. destruct V; reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE THREE NAMED BODIES (optimization.md, RULE ONE)                   *)
  (* ------------------------------------------------------------------- *)

  (* THE CONTRACT'S OWN CONTINUATION, named once so that the walk lemma's
     statement and the parked gate both speak of ONE term.  It is
     [SpecCreate.wp_create_sconf_body]'s [wp_next] callback verbatim; the
     seal (with the allocate half) closes by [iApply] straight through it. *)
  Definition cr_cont_body
      (γfs : fs_names) (γi : gname) (cn : ic_names) (γ : log_names)
      (γf : gname) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (j : nat) (ret_tgt : mword 64)
      (CIDc : CpuId) : iProp Σ :=
    (∀ (mf : regfile) (ok made : bool)
       (k : nat) (qi s : Qp) (g : gname) (inum : mword 32)
       (dn : dinode) (bm : blkmap)
       (u' : nat) (Sb' : gset Z) (ns' : nat) (used' : gset Z),
       ⌜callee_saved m mf⌝ -∗
       sie_cap_gpr mf K b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) C b -∗
       pc_is ret_tgt -∗
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used' -∗
       proc_priv γf (proc_addr j) pidv V -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
       bslots bn 3 -∗
       ⌜((ns - create_slots)%nat <= ns')%nat /\ (ns' <= ns)%nat⌝ -∗
       iref_slots ns' -∗
       ⌜Sb ⊆ Sb' /\ (u' <= u)%nat⌝ -∗
       log_opS γ u' Sb' -∗
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
          create_locked cn γfs γi cov logstart dev pidv k qi s g inum dn bm
        else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝) -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE EPILOGUE FUNNEL at +0x70: [mv a0,s2], the seven [c.ldsp]s, the
     pop, [c.ret].  FOUR arms of this half reach it and three more will,
     so the continuation is ABSTRACT and the body speaks only of the
     restored registers and the frame.  Slot 5 is s3's and this half never
     writes it, which is why [w5] is the one free slot value. *)
  Definition cr_tail_body
      (j : nat) (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (b : bool)
      (CIDt : CpuId) : iProp Σ :=
    (∀ (Mt : regfile) (w5 : mword 64) (dnew : nat -> bv 8),
       ⌜cr_tregs m sp0 Mt⌝ -∗
       sie_cap_gpr Mt (K - 10)%nat b (proc_addr j) -∗
       pc_is (mword_of_int (CK + 0x70)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ w5 -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ dnew jj) -∗
       wp_next (CID0 := CIDt) true (proc_addr j) (fun CIDf : CpuId =>
         ∀ mf : regfile,
           ⌜callee_saved m mf⌝ -∗
           ⌜mf !!! Regidx Ra0 = (Mt !!! Regidx Rs2 : mword 64)⌝ -∗
           sie_cap_gpr mf K b (proc_addr j) -∗
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
      (K : nat) (b : bool) :
    ((K - 10) + 10)%nat = K ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    kernel_text -∗
    □ wp_next (CID0 := CID) true (proc_addr j)
        (fun CIDt : CpuId => cr_tail_body j m sp0 ret_tgt K b CIDt).
  Proof.
    intros HKsum Hal10 Hal9 Hspm Hrt.
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext". iModIntro.
    iIntros (CIDt Hst Mt w5 dnew)
      "%HTr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb Hqc".
    destruct HTr as [HTsp HTthr].
    iPoseProof (cri_070 with "Htext") as "Hj62".
    iPoseProof (cri_072 with "Htext") as "Hj64".
    iPoseProof (cri_074 with "Htext") as "Hj66".
    iPoseProof (cri_076 with "Htext") as "Hj68".
    iPoseProof (cri_078 with "Htext") as "Hj6a".
    iPoseProof (cri_07a with "Htext") as "Hj6c".
    iPoseProof (cri_07c with "Htext") as "Hj6e".
    iPoseProof (cri_07e with "Htext") as "Hj70".
    iPoseProof (cri_080 with "Htext") as "Hj72".
    iPoseProof (cri_082 with "Htext") as "Hj74".
    (* +0x70 c.mv a0,s2 : the answer register *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x70)) Ra0 Rs2 Mt
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj62").
    iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mt !!! Regidx Rs2))]> Mt).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj64 Hb1").
    iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj66 Hb2").
    iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj68 Hb3").
    iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6a Hb4").
    iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6c Hb6").
    iIntros (CIDT5 HqT5) "Hcg Hpc Hb6".
    set (P5 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P4).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6e Hb7").
    iIntros (CIDT6 HqT6) "Hcg Hpc Hb7".
    set (P6 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P5).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj70 Hb8").
    iIntros (CIDT7 HqT7) "Hcg Hpc Hb8".
    set (P7 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P6).
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
    iAssert (stack_own sp0 10) with
      "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hc9 Hc10]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
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
              with "Hcg Hpc Hj72 Hstk").
    iIntros (CIDT8 HqT8) "Hcg Hpc".
    set (P8 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P7).
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
              ltac:(nz) with "Hcg Hpc Hj74").
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
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (b : bool)
      (CIDa : CpuId) : iProp Σ :=
    (∀ (Ma : regfile) (w5 : mword 64)
       (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf : nat -> bv 8) (nsl : nat -> bv 8)
       (n1 : nat) (Sb1 used1 : gset Z) (w : bool),
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
       ⌜inode_ok cov logstart dn bm data⌝ -∗
       ⌜dir_ok nib dn data⌝ -∗
       ⌜exists es e, nameiparent_of (bview plen pfun) es e
                     /\ bname 14 nf = e⌝ -∗
       ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn)))
                  (bname 14 nf) = None⌝ -∗
       (* the ledger, as the found half leaves it *)
       ⌜Sb ⊆ Sb1⌝ -∗
       ⌜w = true -> bmapstart ∈ Sb1⌝ -∗
       ⌜((u - (SpecNamex.walk_spend w + 0))%nat <= n1)%nat /\ (n1 <= u)%nat⌝ -∗
       ⌜used1 ⊆ used⌝ -∗
       (* the machine *)
       sie_cap_gpr Ma (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) C b -∗
       pc_is (mword_of_int (CK + 0xa2)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ w5 -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ nsl jj) -∗
       (* THE LOCKED PARENT, in pieces *)
       is_sleeplock γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok cn kd) -∗
       sleeplocked γisl -∗
       sl_pid (i_lock (ientry kd)) ↦₄ pidv -∗
       ic_deposit cn kd (DepShr (qd/2)%Qp dev dind gd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dir_links (bv_unsigned dind) dn data -∗
       dinode_at γi dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map γfs (ientry kd) bm -∗
       inode_blocks γfs bm data -∗
       ity_shot gd (di_type dn) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* everything the contract still owes back *)
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used1 -∗
       proc_priv γf (proc_addr j) pidv V -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
       bslots bn 3 -∗
       iref_slots (ns - 1) -∗
       log_opS γ n1 Sb1 -∗
       (* and the contract's own continuation, ANCHORED AT THE ENTRY HART
          (ProofDirlink's [dl_after_body]): the block's own proof does the
          retargeting, so this file hands over [Hcont] untouched. *)
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γfs γi cn γ γf bn cov logstart bmapstart inodestart
                         nib ninodes size dev used plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb C b j
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
  (*  child's [ilink] ticket is UNDEPOSITED -- +0xc4 minted it and the     *)
  (*  non-directory arm spends it at +0xd8, so on this branch it is still  *)
  (*  in hand and the mkdir arm's own [dirlink(dp,name)] at +0x12c is      *)
  (*  what spends it.                                                     *)
  (*                                                                       *)
  (*  [cr_fail_body] is +0x146, reached HERE only from the [bltz] at       *)
  (*  +0xdc (the other three entries are behind the T_DIR branch and       *)
  (*  therefore inside [cr_mkdir_body]), so a LINEAR premise is right and  *)
  (*  D0-b will re-shape it into the persistent four-entry form.  It is    *)
  (*  handed the parent's [dir_links] AT THE ENTRY INDICES together with   *)
  (*  the undeposited [ilink] and dirlink's own range clause, and NOT a    *)
  (*  re-parked payload: at [tot = 1] neither [DirLinks.dir_link_at_       *)
  (*  dirlink] (which wants [2 <= tot]) nor [dir_links_dirlink_nop] (which *)
  (*  wants [tot = 0]) applies, and that hole is DirLinks' own recorded    *)
  (*  S5i gap, not something this arm may paper over.                     *)
  (* ------------------------------------------------------------------- *)
  Definition cr_mkdir_body
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (b : bool)
      (* ---- what the found half froze, i.e. [cr_alloc_body]'s own binders *)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8)
      (CIDm : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname)
       (cinum : mword 32) (dnc : dinode) (bmc : blkmap)
       (datc : nat -> list (bv 8)) (n3 : nat) (Sb3 used3 : gset Z),
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
          hence the whole arm, since the [ilink dind] it mints is the only
          ticket for the [".."] written at +0x11a -- is unprovable. *)
       ⌜di_nlink dn <> (mword_of_int 32767 : mword 16)⌝ -∗
       ⌜inode_ok cov logstart dn bm data⌝ -∗
       ⌜dir_ok nib dn data⌝ -∗
       ⌜exists es e, nameiparent_of (bview plen pfun) es e
                     /\ bname 14 nf = e⌝ -∗
       ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn)))
                  (bname 14 nf) = None⌝ -∗
       (* the child, as the gate and the three [sh]s left it *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok cov logstart dnc bmc datc⌝ -∗
       ⌜dir_ok nib dnc datc⌝ -∗
       (* the ledger *)
       ⌜Sb ⊆ Sb3⌝ -∗
       ⌜IBLOCK cinum inodestart ∈ Sb3⌝ -∗
       ⌜(8 <= n3)%nat /\ (n3 <= u)%nat⌝ -∗
       ⌜used3 ⊆ used⌝ -∗
       (* the machine *)
       sie_cap_gpr Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) C b -∗
       pc_is (mword_of_int (CK + 0xf8)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ nsl jj) -∗
       (* THE LOCKED PARENT, in pieces *)
       is_sleeplock γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok cn kd) -∗
       sleeplocked γisl -∗
       sl_pid (i_lock (ientry kd)) ↦₄ pidv -∗
       ic_deposit cn kd (DepShr (qd/2)%Qp dev dind gd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dir_links (bv_unsigned dind) dn data -∗
       dinode_at γi dind dn -∗
       inode_meta (ientry kd) dn -∗
       inode_map γfs (ientry kd) bm -∗
       inode_blocks γfs bm data -∗
       ity_shot gd (di_type dn) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* THE LOCKED CHILD, in pieces, at the FLUSHED record *)
       is_sleeplock gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_tok cn kslot) -∗
       sleeplocked gisl -∗
       sl_pid (i_lock (ientry kslot)) ↦₄ pidv -∗
       ic_deposit cn kslot (DepShr (q/2)%Qp dev cinum g) -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dir_links (bv_unsigned cinum) dnc datc -∗
       dinode_at γi cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map γfs (ientry kslot) bmc -∗
       inode_blocks γfs bmc datc -∗
       ity_shot g (di_type dnc) -∗
       inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev cinum g -∗
       (* THE MINT, UNDEPOSITED *)
       ilink (bv_unsigned cinum) -∗
       (* everything the contract still owes back *)
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used3 -∗
       p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
       (p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
          proc_priv γf (proc_addr j) pidv V) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
       bslots bn 3 -∗
       iref_slots (ns - 2) -∗
       log_opS γ n3 Sb3 -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γfs γi cn γ γf bn cov logstart bmapstart inodestart
                         nib ninodes size dev used plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb C b j
                         ret_tgt CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition cr_fail_body
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (b : bool)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8)
      (CIDf : CpuId) : iProp Σ :=
    (∀ (Mx : regfile) (kslot : nat) (q : Qp) (g gil gisl : gname)
       (cinum : mword 32) (dnc : dinode) (bmc : blkmap)
       (datc : nat -> list (bv 8))
       (bm' : blkmap) (data' : nat -> list (bv 8)) (dn' dn0' : dinode)
       (tot : nat) (n4 : nat) (Sb4 used4 : gset Z),
       ⌜cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64) (ientry kslot)
          ty major minor Mx⌝ -∗
       ⌜ty <> SpecDirlookup.T_DIR⌝ -∗
       (* the parent's ENTRY facts *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
       ⌜inode_ok cov logstart dn bm data⌝ -∗
       ⌜dir_ok nib dn data⌝ -∗
       (* the child *)
       ⌜(kslot < NINODE)%nat⌝ -∗
       ⌜0 < bv_unsigned cinum < ninodes⌝ -∗
       ⌜bv_unsigned cinum < 16 * Z.of_nat nib⌝ -∗
       ⌜fresh_shape dnc⌝ -∗
       ⌜di_type dnc = ty⌝ -∗
       ⌜inode_ok cov logstart dnc bmc datc⌝ -∗
       ⌜dir_ok nib dnc datc⌝ -∗
       (* WHAT THE FAILING [dirlink(dp,name)] AT +0xd8 LEFT, verbatim from
          [SpecDirlink]'s append arm.  The [bltz] at +0xdc having fired says
          [tot < 16]; with dirlink's ATOMICITY clause (relayed from
          [SpecWritei.wi16_atomic], D0-c) that IS [tot = 0], and the arm
          needs the sharper form: it re-parks the parent's [dir_links] with
          [DirLinks.dir_links_dirlink_nop] before +0x158's [iunlockput(dp)],
          and at [0 < tot < 16] no re-park exists ([dir_link_at_dirlink]
          wants a ticket, and the one [ilink] in hand is what +0x14c
          spends).  The RE-PARK is still the body's own work, as before --
          what changed is that it is now possible. *)
       ⌜tot = 0%nat⌝ -∗
       (* NO CLAUSE RELATING [used4] TO [used].  Both directions were stated
          here when the body was written and NEITHER is suppliable: the
          bitmap set create's contract speaks of is its ENTRY one, the alloc
          half runs at [used1] with only [used1 ⊆ used] in hand, and the
          failing [dirlink]'s append arm reports [used1 ⊆ used4] -- so
          [used ⊆ used4] wants [used ⊆ used1] and [used4 ⊆ used] wants the
          append to have freed blocks.  Together they force [used4 = used].
          Nothing below needs either: [cr_cont_body] takes [bitmap_res] at
          an unconstrained [used'], which is what the fail tail hands it. *)
       ⌜blkmap_wf cov logstart bm'⌝ -∗
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
       sie_cap_gpr Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) C b -∗
       pc_is (mword_of_int (CK + 0x146)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nf jj) -∗
       ([∗ list] jj ∈ seq 14 2, pa_add (pa_stk sp0 10) jj ↦ₘ nsl jj) -∗
       (* THE LOCKED PARENT, in pieces, at the POST-dirlink indices --
          with [dir_links] still at the ENTRY ones and the ticket in hand *)
       is_sleeplock γil γisl (i_lock (ientry kd)) "inode"%string
                    (ic_tok cn kd) -∗
       sleeplocked γisl -∗
       sl_pid (i_lock (ientry kd)) ↦₄ pidv -∗
       ic_deposit cn kd (DepShr (qd/2)%Qp dev dind gd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dind -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dir_links (bv_unsigned dind) dn data -∗
       dinode_at γi dind dn0' -∗
       inode_meta (ientry kd) dn' -∗
       inode_map γfs (ientry kd) bm' -∗
       inode_blocks γfs bm' data' -∗
       ity_shot gd (di_type dn) -∗
       inode_ref_short_gen kd (qd/2 + qd/2)%Qp (qd/2)%Qp dev dind gd -∗
       (* THE LOCKED CHILD, at the flushed record *)
       is_sleeplock gil gisl (i_lock (ientry kslot)) "inode"%string
                    (ic_tok cn kslot) -∗
       sleeplocked gisl -∗
       sl_pid (i_lock (ientry kslot)) ↦₄ pidv -∗
       ic_deposit cn kslot (DepShr (q/2)%Qp dev cinum g) -∗
       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
       i_valid (ientry kslot) ↦₄ valid_word true -∗
       dir_links (bv_unsigned cinum) dnc datc -∗
       dinode_at γi cinum (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_meta (ientry kslot)
                  (cr_setf dnc major minor (mword_of_int 1 : mword 16)) -∗
       inode_map γfs (ientry kslot) bmc -∗
       inode_blocks γfs bmc datc -∗
       ity_shot g (di_type dnc) -∗
       inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev cinum g -∗
       (* THE MINT.  UNDEPOSITED: at [tot = 1] the written record is live at
          [cinum mod 256] and no ticket for that key exists anywhere, so the
          re-park is not available at this seam. *)
       ilink (bv_unsigned cinum) -∗
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used4 -∗
       p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
       (p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
          proc_priv γf (proc_addr j) pidv V) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
       bslots bn 3 -∗
       iref_slots (ns - 2) -∗
       log_opS γ n4 Sb4 -∗
       wp_next (CID0 := CID) true (proc_addr j)
         (fun CIDc : CpuId =>
            cr_cont_body γfs γi cn γ γf bn cov logstart bmapstart inodestart
                         nib ninodes size dev used plen pfun pv ty major minor
                         V u Sb ns pidv dqb dqs dqbs dqn m K eb C b j
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
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (V : pprivate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) :
    (K_create <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    bitmap_geom_ok cov logstart bmapstart size ->
    InodeInv.ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    bv_unsigned ty <> 0 ->
    printk_gen_contract γpr γu γd ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    m !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64) ->
    m !!! Regidx Ra2 = (sign_extend' 64 major : mword 64) ->
    m !!! Regidx Ra3 = (sign_extend' 64 minor : mword 64) ->
    eb = true ->
    sie_cap_gpr m K b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C b -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.create) -∗
    panic_wp_any -∗
    kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    kalloc_env γa None -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    SpecDirlink.ic_sleeplocks cn -∗
    ireg_inv γi γfs inodestart nib -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    proc_priv γf (proc_addr j) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen),
       pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ pfun i) -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    iref_slots ns -∗
    log_opS γ u Sb -∗
    (* ---- THE PARKED ALLOCATE HALF, as a HYPOTHESIS ---- *)
    wp_next true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γa γf γpr
                    cov logstart bmapstart inodestart nib ninodes size dev
                    used plen pfun (m !!! Regidx Ra0 : mword 64)
                    ty major minor V u Sb ns pidv dqb dqs dqbs dqn m
                    (m !!! Regidx csp_rs1 : mword 64)
                    (ret_pc (m !!! Regidx Rra : mword 64)) K eb C b CIDa) -∗
    (* ---- the contract's own continuation ---- *)
    wp_next true (proc_addr j) (fun CIDc : CpuId =>
      cr_cont_body γfs γi cn γ γf bn cov logstart bmapstart inodestart nib
                   ninodes size dev used plen pfun (m !!! Regidx Ra0 : mword 64)
                   ty major minor V u Sb ns pidv dqb dqs dqbs dqn m K eb C b j
                   (ret_pc (m !!! Regidx Rra : mword 64)) CIDc) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc Hbmsl
           Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3 Htynz Hpkc
           Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hkd #Hpk #Hbio #Hlogc #Hkenv
             #Hitb2 #Hitbl #Hesc #Hslks #Hiregi
             Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath #Hprocs #Hdevi #Hgeom #Hdlk
             Hbsl Hislots Hop Halloc Hcont".
    (* PIN THE INDEX: at level 0 [cpu_own_eb_agree] gives [eb = b], and the
       crossings below are the literal [true] (create parks everywhere). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    pose (ret_tgt := ret_pc (m !!! Regidx Rra : mword 64)).
    iPoseProof (cri_000 with "Htext") as "Hi000".
    iPoseProof (cri_002 with "Htext") as "Hi002".
    iPoseProof (cri_004 with "Htext") as "Hi004".
    iPoseProof (cri_006 with "Htext") as "Hi006".
    iPoseProof (cri_008 with "Htext") as "Hi008".
    iPoseProof (cri_00a with "Htext") as "Hi00a".
    iPoseProof (cri_00c with "Htext") as "Hi00c".
    iPoseProof (cri_00e with "Htext") as "Hi00e".
    iPoseProof (cri_010 with "Htext") as "Hi010".
    iPoseProof (cri_012 with "Htext") as "Hi012".
    iPoseProof (cri_014 with "Htext") as "Hi014".
    iPoseProof (cri_016 with "Htext") as "Hi016".
    iPoseProof (cri_018 with "Htext") as "Hi018".
    iPoseProof (cri_01c with "Htext") as "Hi01c".
    (* ===== +0x00 c.addi16sp sp,-80 : the 10-slot frame ================ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)
      by apply cr_push.
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.create)
              (mword_of_int 59 : mword 6) m K 10 b
              ltac:(exact HK10) Hpush with "Hcg Hpc Hi000").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R1 upd_eq; exact Hpush).
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
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
              Rra R1 (K - 10)%nat u1 b with "Hcg Hpc Hi002 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hp004 : add_vec_int (mword_of_int (CK + 0x02) : mword 64) 2
                    = mword_of_int (CK + 0x04)) by pcw.
    iEval (rewrite Hp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x04)) (mword_of_int 8 : mword 6)
              Rs0 R1 (K - 10)%nat u2 b with "Hcg Hpc Hi004 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hp006 : add_vec_int (mword_of_int (CK + 0x04) : mword 64) 2
                    = mword_of_int (CK + 0x06)) by pcw.
    iEval (rewrite Hp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x06)) (mword_of_int 7 : mword 6)
              Rs1 R1 (K - 10)%nat u3 b with "Hcg Hpc Hi006 Hb3").
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hp008 : add_vec_int (mword_of_int (CK + 0x06) : mword 64) 2
                    = mword_of_int (CK + 0x08)) by pcw.
    iEval (rewrite Hp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x08)) (mword_of_int 6 : mword 6)
              Rs2 R1 (K - 10)%nat u4 b with "Hcg Hpc Hi008 Hb4").
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hp00a : add_vec_int (mword_of_int (CK + 0x08) : mword 64) 2
                    = mword_of_int (CK + 0x0a)) by pcw.
    iEval (rewrite Hp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0a)) (mword_of_int 4 : mword 6)
              Rs4 R1 (K - 10)%nat u6 b with "Hcg Hpc Hi00a Hb6").
    iIntros (CID6 Hq6) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hp00c : add_vec_int (mword_of_int (CK + 0x0a) : mword 64) 2
                    = mword_of_int (CK + 0x0c)) by pcw.
    iEval (rewrite Hp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0c)) (mword_of_int 3 : mword 6)
              Rs5 R1 (K - 10)%nat u7 b with "Hcg Hpc Hi00c Hb7").
    iIntros (CID7 Hq7) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hp00e : add_vec_int (mword_of_int (CK + 0x0c) : mword 64) 2
                    = mword_of_int (CK + 0x0e)) by pcw.
    iEval (rewrite Hp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0x0e)) (mword_of_int 2 : mword 6)
              Rs6 R1 (K - 10)%nat u8 b with "Hcg Hpc Hi00e Hb8").
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
              with "Hcg Hpc Hi010").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi012").
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra1))]> R2).
    assert (HR3s4 : R3 !!! Regidx Rs4 = (sign_extend' 64 ty : mword 64)).
    { rewrite /R3 upd_eq. rewrite (HR2o Ra1 ltac:(nz) ltac:(nz)) Ha1.
      apply add_vec_zero_l. }
    assert (Hp014 : add_vec_int (mword_of_int (CK + 0x12) : mword 64) 2
                    = mword_of_int (CK + 0x14)) by pcw.
    iEval (rewrite Hp014) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x14)) Rs5 Ra2 R3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi014").
    iIntros (CID11 Hq11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra2))]> R3).
    assert (HR4s5 : R4 !!! Regidx Rs5 = (sign_extend' 64 major : mword 64)).
    { rewrite /R4 upd_eq. rewrite /R3 upd_ne; [| nz].
      rewrite (HR2o Ra2 ltac:(nz) ltac:(nz)) Ha2. apply add_vec_zero_l. }
    assert (Hp016 : add_vec_int (mword_of_int (CK + 0x14) : mword 64) 2
                    = mword_of_int (CK + 0x16)) by pcw.
    iEval (rewrite Hp016) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x16)) Rs6 Ra3 R4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi016").
    iIntros (CID12 Hq12) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra3))]> R4).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi018").
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (R6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R5 Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R5).
    assert (HR6a1 : R6 !!! Regidx Ra1 = pa_stk sp0 10).
    { rewrite /R6 upd_eq. rewrite rget_ne;
        [| intro Hq1'; injection Hq1' as Hq2'; vm_compute in Hq2'; congruence ].
      rewrite HR5s0. apply cr_name_addr. }
    assert (Hp01c : add_vec_int (mword_of_int (CK + 0x18) : mword 64) 4
                    = mword_of_int (CK + 0x1c)) by pcw.
    iEval (rewrite Hp01c) in "Hpc".
    (* ===== +0x1c jal nameiparent ===================================== *)
    assert (Htgnp : add_vec (mword_of_int (CK + 0x1c) : mword 64)
              (sign_extend' 64 (mword_of_int 2092774 : mword 21))
              = mword_of_int KernelSyms.nameiparent) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x1c)) Rra
              (mword_of_int 2092774 : mword 21) R6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi01c").
    iIntros (CID14 Hq14) "Hcg Hpc".
    iEval (rewrite Htgnp) in "Hpc".
    set (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x1c) : mword 64) 4)]> R6).
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
    (* ---- the running process: cwd + the pid quarter ---- *)
    iDestruct (proc_priv_cwd_pid γf (proc_addr j) pidv V with "Hpriv")
      as "(Hpcwd & Hcref & Hppid & Hpclose)".
    iDestruct (cwd_ref_held with "Hcref") as "Hcref".
    iEval (rewrite -HR7a0) in "Hpath".
    iEval (rewrite -HR7a1) in "Hnb14".
    iDestruct (cpu_own_transport CID CID14 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (NP.wp_nameiparent_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
              γa γf cov logstart bmapstart inodestart nib size dev used
              (pv_cwd V) plen pfun nf0 u Sb pidv (DfracOwn (1/4)) dqb dqs
              (DfracOwn 1) R7 (K - 10)%nat eb C b
              ltac:(exact HKnp) Hdev Hnib Hglog Hist Hroot Hnib0 Hlg Hsize
              Hbms0 Hbmsc Hbmsl Hist0 Hcovb Hiregb Hcstr Hplen31
              ltac:(exact (cr_walk_need _ u Hu)) Hj Hgs Heb
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hiregi Hprocs Hdevi Hgeom Hdlk Hsbb Hsbi Hbmr
                    Hppid Hpcwd Hcref Hpath Hnb14 Hbsl Hisl2 Hop").
    iIntros (CIDnp Hsnp mnp n1 used1 Sb1 okp nfp ipv w)
      "%Hcsnp Hcg Hcnt Hpc Hsbb Hsbi %Husd1 Hbmr Hppid Hpcwd Hcref Hpath Hnb14
       Hbsl %Hsb1 %Hwmem %Hnp1 Hop Hres".
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
    iDestruct ("Hpclose" $! (pv_cwd V) with "Hpcwd Hcref Hppid") as "Hpriv".
    iEval (rewrite cr_upd_cwd_id) in "Hpriv".
    iPoseProof (cri_020 with "Htext") as "Hi020".
    iPoseProof (cri_022 with "Htext") as "Hi022".
    (* ===== +0x20 c.mv s1,a0 : s1 = dp ================================ *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x20)) Rs1 Ra0 mnp (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi020").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0))]> mnp).
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
    iDestruct (cr_tail_half j m sp0 ret_tgt K b HKsum Hal10 Hal9
                 eq_refl eq_refl with "Htext") as "#Htail".
    destruct okp.
    - (* ============================================================== *)
      (*  nameiparent SUCCEEDED -- the parent is a LOCKED-ABLE DIRECTORY  *)
      (* ============================================================== *)
      iDestruct "Hres" as "((%Hnpa0 & %Hnpname) & Hipty & Hisl1)".
      iDestruct "Hipty" as (kd qd dind gd) "(%Hie & %Hkd & %Hdib & Href & #Hshotd)".
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
                with "Hcg Hpc Hi022").
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
      iDestruct (cr_esc_acc cn γfs γi cov logstart kd Hkd with "Hesc") as "#Hescd".
      iDestruct (cr_slk_acc cn kd Hkd with "Hslks") as (gild gisld) "#Hslkd".
      iDestruct (cr_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (proc_priv_pid γf (proc_addr j) pidv V with "Hpriv")
        as "[Hppid Hppback]".
      iPoseProof (cri_026 with "Htext") as "Hi026".
      iPoseProof (cri_02a with "Htext") as "Hi02a".
      iPoseProof (cri_02e with "Htext") as "Hi02e".
      (* ===== +0x26 jal ilock (a0 is STILL dp -- not reloaded) ========= *)
      assert (Htgil : add_vec (mword_of_int (CK + 0x26) : mword 64)
                (sign_extend' 64 (mword_of_int 2090622 : mword 21))
                = mword_of_int KernelSyms.ilock) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0x26)) Rra
                (mword_of_int 2090622 : mword 21) Q1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi026").
      iIntros (CID17 Hq17) "Hcg Hpc".
      iEval (rewrite Htgil) in "Hpc".
      set (Q2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)]> Q1).
      assert (HQ2ra : Q2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CK + 0x26) : mword 64) 4)
        by (rewrite /Q2; apply upd_eq).
      assert (HQ2a0 : Q2 !!! Regidx Ra0 = ientry kd).
      { rewrite /Q2 upd_ne; [| nz]. rewrite HQ1a0 Hnpa0. exact Hie. }
      assert (HQ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                          ty major minor Q2)
        by (rewrite /Q2; apply cr_regs_caller; [exact Hcsra | exact HQ1regs]).
      iDestruct (cpu_own_transport CIDnp CID17 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IL.wp_ilock_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn
                gild gisld cov logstart inodestart nib kd (qd/2)%Qp gd dev dind
                pidv (DfracOwn (1/4)) dqs Q2 (K - 10)%nat eb C b
                ltac:(exact HKil) Hkd Hlg Hist0 Hdblk Hdib' Hj Hgs HQ2a0
                with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hitbl Hescd Hiregi
                      Hslkd Hshr Hsbi Hppid Hprocs Hdevi Hgeom Hdlk Hbs1").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iIntros (CIDil Hqil mil dnl bml fld)
        "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hslkdd Hslpid Hdep
         Hidev Hiinum Hivalid Hload #Hshotl %Hfrd".
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
      iDestruct "Hload" as (datl)
        "(%Hiok & %Hdok & Hdlnk & Hdiat & Hmeta & Haddrs & Hind & Hblocks)".
      iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
      iEval (rewrite /i_nlink) in "Hinl".
      (* ===== +0x2a lh a5,74(s1) : dp->nlink -- THE GUARD (9da28f5) ==== *)
      iApply (wp_lh_s_sconf (mword_of_int (CK + 0x2a)) Ra5 Rs1
                (mword_of_int 74 : mword 12) mil (K - 10)%nat
                (di_nlink dnl : mword 16) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi02a [Hinl]").
      { iEval (rgne; rewrite Y9 Hie). iExact "Hinl". }
      iIntros (CID18 Hq18) "Hcg Hpc Hinl".
      iEval (rgne; rewrite Y9 Hie) in "Hinl".
      set (Q3 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (di_nlink dnl : mword 16) : mword 64)]> mil).
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
                  with "Hcg Hpc Hi02e").
        iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg084) in "Hpc".
        iPoseProof (cri_084 with "Htext") as "Hi084".
        iPoseProof (cri_086 with "Htext") as "Hi086".
        iPoseProof (cri_08a with "Htext") as "Hi08a".
        iPoseProof (cri_08c with "Htext") as "Hi08c".
        iAssert (ic_loaded γfs γi cov logstart kd dind dnl bml)
          with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind Hblocks Hdlnk]"
          as "Hload".
        { rewrite /ic_loaded. iExists datl.
          iSplitR; [iPureIntro; exact Hiok |].
          iSplitR; [iPureIntro; exact Hdok |].
          iSplitL "Hdlnk"; [iExact "Hdlnk" |].
          iFrame "Hdiat".
          iSplitL "Hity Himaj Himin Hinl Hisz".
          - rewrite /inode_meta /i_type /i_nlink. iFrame.
          - iFrame. }
        iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x84 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x84)) Ra0 Rs1 Q3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi084").
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3).
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
                  (sign_extend' 64 (mword_of_int 2091050 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x86)) Rra
                  (mword_of_int 2091050 : mword 21) G1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi086").
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite Htgup) in "Hpc".
        set (G2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)]> G1).
        assert (HG2ra : G2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x86) : mword 64) 4)
          by (rewrite /G2; apply upd_eq).
        assert (HG2a0 : G2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /G2 upd_ne; [exact HG1a0 | nz]).
        assert (HG2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G2)
          by (rewrite /G2; apply cr_regs_caller; [exact Hcsra | exact HG1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
        iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
                  gtl gild gisld cov logstart bmapstart inodestart nib size dev
                  used1 kd (qd/2)%Qp (qd/2)%Qp gd dind dnl bml n1 Sb1
                  false false false e0 pidv (DfracOwn (1/4)) dqb dqs
                  G2 (K - 10)%nat eb C b
                  ltac:(exact HKiup) Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HG2a0
                  with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                        Hivalid Hload Hshotl Hkeep2 Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 used2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd2 Hbmr Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl".
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
                  with "Hcg Hpc Hi08a").
        iIntros (CID22 Hq22) "Hcg Hpc".
        set (G3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
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
                  with "Hcg Hpc Hi08c").
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070g) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! G3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor G3 HG3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns used2
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [%]").
        { exact Hcsf. }
        { exact (cr_slots_ns ns Hns). }
        { exact (conj (cr_sub2 _ _ _ Hsb1 Hsb2)
                   (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))). }
        { rewrite Ha0f. exact HG3s2. }
      + (* ====== THE GUARD FALLS THROUGH: dp->nlink <> 0 ============== *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 43 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_ne _ Hnl0))
                  with "Hcg Hpc Hi02e").
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
                    sie_cap_gpr (CID := CIDj) Mj (K - 10)%nat b (proc_addr j) -∗
                    pc_is (CID := CIDj) (mword_of_int (CK + 0x3e)) -∗
                    WP (Loop : expr riscv_lang)))
                 ∧ (wp_next (CID0 := CID19) b (proc_addr j) (fun CIDg : CpuId =>
                    ∀ Mg : regfile,
                    ⌜cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                       ty major minor Mg⌝ -∗
                    sie_cap_gpr (CID := CIDg) Mg (K - 10)%nat b (proc_addr j) -∗
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
        assert (Hbmwf : blkmap_wf cov logstart bml) by exact (proj1 Hiok).
        assert (Hbmcov : bm_covers bml (bv_unsigned (di_size dnl)))
          by exact (proj1 (proj2 Hiok)).
        assert (Hszcap : bv_unsigned (di_size dnl)
                         <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
          by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hiok))))).
        assert (Hdz : bv_unsigned (di_type dnl) = T_DIR_z)
          by (rewrite Htydir; vm_compute; reflexivity).
        iPoseProof (cri_03e with "Htext") as "Hi03e".
        iPoseProof (cri_040 with "Htext") as "Hi040".
        iPoseProof (cri_044 with "Htext") as "Hi044".
        iPoseProof (cri_046 with "Htext") as "Hi046".
        iPoseProof (cri_04a with "Htext") as "Hi04a".
        iPoseProof (cri_04c with "Htext") as "Hi04c".
        (* ===== +0x3e c.li a2,0 : dirlookup's [poff] is NOT wanted ===== *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x3e)) Ra2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  Mj (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi03e").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (D1 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Mj).
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
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi040").
        iIntros (CID21 Hq21) "Hcg Hpc".
        set (D2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget D1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> D1).
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
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi044").
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (D3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (D2 !!! Regidx Rs1))]> D2).
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
                  (sign_extend' 64 (mword_of_int 2092030 : mword 21))
                  = mword_of_int KernelSyms.dirlookup) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x46)) Rra
                  (mword_of_int 2092030 : mword 21) D3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi046").
        iIntros (CID23 Hq23) "Hcg Hpc".
        iEval (rewrite Htgdl) in "Hpc".
        set (D4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x46) : mword 64) 4)]> D3).
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
        iAssert (inode_map γfs (ientry kd) bml) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        iEval (rewrite -HD4a1) in "Hnb14".
        iDestruct (cpu_own_transport CIDil CID23 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (DL.wp_dirlookup_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn
                  gtl γa γf cov logstart nib dev (ientry kd) bml datl dnl nfp
                  false (mword_of_int 0 : mword 32)
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  D4 (K - 10)%nat eb C b
                  ltac:(exact HKdlu) Htydir Hlg Hbmwf Hbmcov Hszcap
                  ltac:(rewrite Hnib; exact (Hdok Hdz)) Hj Hgs HD4a0
                  ltac:(cbn [negb]; rewrite HD4a2 dlk_zero_moi;
                        exact (eq_vec_refl _))
                  Heb
                  with "Hcg Hcnt Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta Hmap
                        Hblocks Hnb14 [] Hppid Hprocs Hdevi Hgeom Hdlk Hbs1
                        Hitb2 Hitbl Hesc Hisl1").
        { done. }
        iIntros (CIDdl Hsdl mdl found kk kslot qq)
          "%Hcsdl Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hnb14 Hppid Hbs1 Hres2".
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
          iDestruct "Hres2" as "((%Hfst & %Hkslot & %Hdla0) & Hchild & _)".
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
          iPoseProof (cri_04e with "Htext") as "Hi04e".
          iPoseProof (cri_050 with "Htext") as "Hi050".
          iPoseProof (cri_054 with "Htext") as "Hi054".
          iPoseProof (cri_056 with "Htext") as "Hi056".
          iPoseProof (cri_05a with "Htext") as "Hi05a".
          iPoseProof (cri_05c with "Htext") as "Hi05c".
          (* ===== +0x4a c.mv s2,a0 : s2 = ip ========================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04a").
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (F1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
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
                    with "Hcg Hpc Hi04c").
          iIntros (CID25 Hq25) "Hcg Hpc".
          assert (Hp04e : add_vec_int (mword_of_int (CK + 0x4c) : mword 64) 2
                          = mword_of_int (CK + 0x4e)) by pcw.
          iEval (rewrite Hp04e) in "Hpc".
          (* ===== +0x4e c.mv a0,s1 : the PARENT, for iunlockput ======== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4e)) Ra0 Rs1 F1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04e").
          iIntros (CID26 Hq26) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (F2 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (F1 !!! Regidx Rs1))]> F1).
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
                    (sign_extend' 64 (mword_of_int 2091104 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x50)) Rra
                    (mword_of_int 2091104 : mword 21) F2 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi050").
          iIntros (CID27 Hq27) "Hcg Hpc".
          iEval (rewrite Htgup1) in "Hpc".
          set (F3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)]> F2).
          assert (HF3ra : F3 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x50) : mword 64) 4)
            by (rewrite /F3; apply upd_eq).
          assert (HF3a0 : F3 !!! Regidx Ra0 = ientry kd)
            by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
          assert (HF3regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F3)
            by (rewrite /F3; apply cr_regs_caller; [exact Hcsra | exact HF2regs]).
          iAssert (ic_loaded γfs γi cov logstart kd dind dnl bml)
            with "[Hdiat Hmeta Hmap Hblocks Hdlnk]" as "Hload".
          { rewrite /ic_loaded. iExists datl.
            iSplitR; [iPureIntro; exact Hiok |].
            iSplitR; [iPureIntro; exact Hdok |].
            iSplitL "Hdlnk"; [iExact "Hdlnk" |].
            iFrame "Hdiat". rewrite /inode_map. iFrame. }
          iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (cpu_own_transport CIDdl CID27 0%nat eb (proc_addr j) C b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (log_opS_named with "Hop") as (e0) "Hop".
          iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
          iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi
                    cn gtl gild gisld cov logstart bmapstart inodestart nib size
                    dev used1 kd (qd/2)%Qp (qd/2)%Qp gd dind dnl bml n1 Sb1
                    false false false e0 pidv (DfracOwn (1/4)) dqb dqs
                    F3 (K - 10)%nat eb C b
                    ltac:(exact HKiup) Hkd ltac:(discriminate) ltac:(discriminate)
                    Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                    ltac:(exact Hn1ip) Hj Hgs HF3a0
                    with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                          Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                          Hivalid Hload Hshotl Hkeep2 Hsbb Hsbi Hbmr Hppid
                          Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iEval (cbn beta iota). iEmpIntro. }
          iIntros (CIDu1 Hqu1 mu1 n2 used2 Sb2 wf1)
            "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd2 Hbmr Hbsl
             %Hsb2 %Hwf1 %Hwf1c %Hn2 Hop Hisl".
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
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi054").
          iIntros (CID28 Hq28) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (F4 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mu1 !!! Regidx Rs2))]> mu1).
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
                    (sign_extend' 64 (mword_of_int 2090574 : mword 21))
                    = mword_of_int KernelSyms.ilock) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x56)) Rra
                    (mword_of_int 2090574 : mword 21) F4 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi056").
          iIntros (CID29 Hq29) "Hcg Hpc".
          iEval (rewrite Htgil2) in "Hpc".
          set (F5 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x56) : mword 64) 4)]> F4).
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
          iDestruct (cr_esc_acc cn γfs γi cov logstart kslot Hkslot with "Hesc")
            as "#Hescc".
          iDestruct (cr_slk_acc cn kslot Hkslot with "Hslks")
            as (gilc gislc) "#Hslkc".
          iDestruct (cr_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
          iDestruct (cpu_own_transport CIDu1 CID29 0%nat eb (proc_addr j) C b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (IL.wp_ilock_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn
                    gilc gislc cov logstart inodestart nib kslot (qq/2)%Qp gc
                    dev cinum pidv (DfracOwn (1/4)) dqs F5 (K - 10)%nat eb C b
                    ltac:(exact HKil) Hkslot Hlg Hist0 Hcblk Hcinb Hj Hgs HF5a0
                    with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hitbl Hescc
                          Hiregi Hslkc Hcshr Hsbi Hppid Hprocs Hdevi Hgeom
                          Hdlk Hbs1").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          iIntros (CIDic Hqic mic dnc bmc flc)
            "%Hcsic Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hcslkd Hcslpid Hcdep
             Hcidev Hciinum Hcivalid Hcload #Hcshot %Hfrc".
          assert (Hpcic : ret_pc (F5 !!! Regidx Rra : mword 64)
                          = mword_of_int (CK + 0x5a)) by (rewrite HF5ra; pcw).
          iEval (rewrite Hpcic) in "Hpc".
          assert (Hmicregs : cr_regs m sp0 ipv (ientry kslot) ty major minor mic)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F5 mic Hcsic HF5regs).
          pose proof Hmicregs as HmicR.
          destruct HmicR as (Z2 & Z8 & Z9 & Z18 & Z20 & Z21 & Z22 & Zthr).
          iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
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
                       sie_cap_gpr Mb (K - 10)%nat b (proc_addr j) -∗
                       cpu_own 0 eb (proc_addr j) C b -∗
                       pc_is (mword_of_int (CK + 0x98)) -∗
                       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
                       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
                       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
                       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
                       (pa_stk sp0 5) ↦₈ u5 -∗
                       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
                       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
                       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
                       ([∗ list] jj ∈ seq 0 14,
                          pa_add (pa_stk sp0 10) jj ↦ₘ nfp jj) -∗
                       ([∗ list] jj ∈ seq 14 2,
                          pa_add (pa_stk sp0 10) jj ↦ₘ nf0 jj) -∗
                       sleeplocked gislc -∗
                       sl_pid (i_lock (ientry kslot)) ↦₄ pidv -∗
                       ic_deposit cn kslot (DepShr (qq/2)%Qp dev cinum gc) -∗
                       i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev -∗
                       i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} cinum -∗
                       i_valid (ientry kslot) ↦₄ valid_word true -∗
                       ic_loaded γfs γi cov logstart kslot cinum dnc bmc -∗
                       ity_shot gc (di_type dnc) -∗
                       inode_ref_short_gen kslot (qq/2 + qq/2)%Qp (qq/2)%Qp
                                           dev cinum gc -∗
                       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
                       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
                       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                       bitmap_res γfs bmapstart cov logstart size used2 -∗
                       p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
                       (p_pid (proc_addr j) ↦₄{DfracOwn (1/4)} pidv -∗
                          proc_priv γf (proc_addr j) pidv V) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add (m !!! Regidx Ra0 : mword 64) i ↦ₘ pfun i) -∗
                       bslots bn 3 -∗
                       iref_slots 1 -∗ iref_slots (ns - 2) -∗
                       log_opS γ n2 Sb2 -∗
                       wp_next (CID0 := CID) true (proc_addr j)
                         (fun CIDc : CpuId =>
                            cr_cont_body γfs γi cn γ γf bn cov logstart bmapstart
                              inodestart nib ninodes size dev used plen pfun
                              (m !!! Regidx Ra0 : mword 64) ty major minor V u Sb
                              ns pidv dqb dqs dqbs dqn m K eb C b j ret_tgt
                              CIDc) -∗
                       WP (Loop : expr riscv_lang)))%I
            with "[]" as "#Hfbad".
          { iModIntro.
            iIntros (CIDb Hsb Mb)
              "%HBr Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
               Hcslkd Hcslpid Hcdep Hcidev Hciinum Hcivalid Hcload Hcshotb
               Hckeep Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl
               Hisl Hislr Hop Hcontb".
            iPoseProof (cri_098 with "Htext") as "Hi098".
            iPoseProof (cri_09a with "Htext") as "Hi09a".
            iPoseProof (cri_09e with "Htext") as "Hi09e".
            iPoseProof (cri_0a0 with "Htext") as "Hi0a0".
            pose proof HBr as HBr2.
            destruct HBr2 as (X2 & X8 & X9 & X18 & X20 & X21 & X22 & Xthr).
            (* +0x98 c.mv a0,s2 : the CHILD *)
            iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x98)) Ra0 Rs2 Mb
                      (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi098").
            iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
            set (B1 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb).
            assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kslot).
            { rewrite /B1 upd_eq. rewrite X18. apply add_vec_zero_l. }
            assert (HB1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B1)
              by (rewrite /B1; apply cr_regs_caller; [exact Hcsa0 | exact HBr]).
            assert (Hq09a : add_vec_int (mword_of_int (CK + 0x98) : mword 64) 2
                            = mword_of_int (CK + 0x9a)) by pcw.
            iEval (rewrite Hq09a) in "Hpc".
            (* +0x9a jal iunlockput (ip), at crb = cru = crz = false *)
            assert (Htgup2 : add_vec (mword_of_int (CK + 0x9a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091030 : mword 21))
                      = mword_of_int KernelSyms.iunlockput) by pcw.
            iApply (wp_jal_s_sconf (mword_of_int (CK + 0x9a)) Rra
                      (mword_of_int 2091030 : mword 21) B1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi09a").
            iIntros (CIDB2 HqB2) "Hcg Hpc".
            iEval (rewrite Htgup2) in "Hpc".
            set (B2 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)]> B1).
            assert (HB2ra : B2 !!! Regidx Rra
                            = add_vec_int (mword_of_int (CK + 0x9a) : mword 64) 4)
              by (rewrite /B2; apply upd_eq).
            assert (HB2a0 : B2 !!! Regidx Ra0 = ientry kslot)
              by (rewrite /B2 upd_ne; [exact HB1a0 | nz]).
            assert (HB2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B2)
              by (rewrite /B2; apply cr_regs_caller; [exact Hcsra | exact HB1regs]).
            iDestruct (cpu_own_transport CIDb CIDB2 0%nat eb (proc_addr j) C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (log_opS_named with "Hop") as (ec) "Hop".
            iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckeep2".
            iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi
                      cn gtl gilc gislc cov logstart bmapstart inodestart nib
                      size dev used2 kslot (qq/2)%Qp (qq/2)%Qp gc cinum dnc bmc
                      n2 Sb2 false false false ec pidv (DfracOwn (1/4)) dqb dqs
                      B2 (K - 10)%nat eb C b
                      ltac:(exact HKiup) Hkslot ltac:(discriminate)
                      ltac:(discriminate)
                      Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
                      ltac:(exact Hn2ip) Hj Hgs HB2a0
                      with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2
                            Hitbl Hescc Hiregi Hslkc Hcslkd Hcslpid Hcdep
                            Hcidev Hciinum Hcivalid Hcload Hcshotb Hckeep2 Hsbb
                            Hsbi Hbmr Hppid Hprocs Hdevi Hgeom Hdlk Hbsl []
                            Hop").
            { rewrite Heb /trap_csrs_ext. done. }
            { rewrite Heb /cpu_claim_ext. done. }
            { iEval (cbn beta iota). iEmpIntro. }
            iIntros (CIDU2 HqU2 mu2 n3 used3 Sb3 wf2)
              "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd3 Hbmr Hbsl
               %Hsb3 %Hwf2 %Hwf2c %Hn3 Hop Hisl2".
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
                      with "Hcg Hpc Hi09e").
            iIntros (CIDB3 HqB3) "Hcg Hpc".
            set (B3 := <[Regidx Rs2 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> mu2).
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
                      with "Hcg Hpc Hi0a0").
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
            iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iDestruct (iref_slots_combine with "Hisl2 Hisl") as "Hisl".
            iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
            iSpecialize ("Hcontb" $! CIDf with "[%]"); [wp_next_chain |].
            iApply ("Hcontb" $! mf false false 0%nat 1%Qp 1%Qp γf
                      (mword_of_int 0 : mword 32) dnc bmc n3 Sb3
                      (1 + (1 + (ns - 2)))%nat used3
                      with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv
                            Hpath Hbsl [%] Hisl [%] Hop [%]").
            { exact Hcsf. }
            { exact (cr_slots_2 ns Hns). }
            { exact (conj (cr_sub3 _ _ _ _ Hsb1 Hsb2 Hsb3)
                       (cr_le3 _ _ _ _ (proj2 Hn3) (proj2 Hn2) (proj2 Hnp1))). }
            { rewrite Ha0f. exact HB3s2. } }
          (* ===== +0x5a c.li a5,2 ===================================== *)
          iApply (wp_cli_s_sconf (mword_of_int (CK + 0x5a)) Ra5
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    mic (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hi05a").
          iIntros (CID30 Hq30) "Hcg Hpc".
          set (F6 := <[Regidx Ra5 := regval_into_reg
                        (mword_of_int 2 : mword 64)]> mic).
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
                       with "Hcg Hpc Hi05c").
             iIntros (CID31 Hq31) "Hcg Hpc".
             assert (Hp060 : add_vec_int (mword_of_int (CK + 0x5c) : mword 64) 4
                             = mword_of_int (CK + 0x60)) by pcw.
             iEval (rewrite Hp060) in "Hpc".
             iPoseProof (cri_060 with "Htext") as "Hi060".
             iPoseProof (cri_064 with "Htext") as "Hi064".
             iPoseProof (cri_066 with "Htext") as "Hi066".
             iPoseProof (cri_068 with "Htext") as "Hi068".
             iPoseProof (cri_06a with "Htext") as "Hi06a".
             iPoseProof (cri_06c with "Htext") as "Hi06c".
             iDestruct "Hcload" as (datc)
               "(%Hciok & %Hcdok & Hcdlnk & Hcdiat & Hcmeta & Hcaddrs & Hcind &
                 Hcblocks)".
             iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
             iEval (rewrite /i_type) in "Hcity".
             (* ===== +0x60 lhu a5,68(s2) : ip->type, ZERO-extended ==== *)
             iApply (wp_lhu_s_sconf (mword_of_int (CK + 0x60)) Ra5 Rs2
                       (mword_of_int 68 : mword 12) F6 (K - 10)%nat
                       (di_type dnc : mword 16) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi060 [Hcity]").
             { iEval (rgne; rewrite HF6s2). iExact "Hcity". }
             iIntros (CID32 Hq32) "Hcg Hpc Hcity".
             iEval (rgne; rewrite HF6s2) in "Hcity".
             set (F7 := <[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6).
             assert (HF7regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F7)
               by (rewrite /F7; apply cr_regs_caller; [exact Hcsa5 | exact HF6regs]).
             assert (Hp064 : add_vec_int (mword_of_int (CK + 0x60) : mword 64) 4
                             = mword_of_int (CK + 0x64)) by pcw.
             iEval (rewrite Hp064) in "Hpc".
             (* ===== +0x64 c.addiw a5,-2 ============================== *)
             iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x64)) Ra5
                       (mword_of_int 62 : mword 6) F7 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi064").
             iIntros (CID33 Hq33) "Hcg Hpc".
             set (F8 := <[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64
                              (subrange_vec_dec
                                 (add_vec (rget F7 Ra5)
                                    (sign_extend' 64
                                       (sign_extend' 12
                                          (mword_of_int 62 : mword 6))))
                                 31 0))]> F7).
             assert (HF8regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F8)
               by (rewrite /F8; apply cr_regs_caller; [exact Hcsa5 | exact HF7regs]).
             assert (Hp066 : add_vec_int (mword_of_int (CK + 0x64) : mword 64) 2
                             = mword_of_int (CK + 0x66)) by pcw.
             iEval (rewrite Hp066) in "Hpc".
             (* ===== +0x66 c.slli a5,48 / +0x68 c.srli a5,48 ========== *)
             iApply (wp_cslli_s_sconf (mword_of_int (CK + 0x66))
                       (Regidx Ra5) Ra5 (mword_of_int 48 : mword 6)
                       F8 (K - 10)%nat b eq_refl ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi066").
             iIntros (CID34 Hq34) "Hcg Hpc".
             set (F9 := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8).
             assert (HF9regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F9)
               by (rewrite /F9; apply cr_regs_caller; [exact Hcsa5 | exact HF8regs]).
             assert (Hp068 : add_vec_int (mword_of_int (CK + 0x66) : mword 64) 2
                             = mword_of_int (CK + 0x68)) by pcw.
             iEval (rewrite Hp068) in "Hpc".
             iApply (wp_csrli_s_sconf (mword_of_int (CK + 0x68))
                       (Cregidx (mword_of_int 7)) Ra5 (mword_of_int 48 : mword 6)
                       F9 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi068").
             iIntros (CID35 Hq35) "Hcg Hpc".
             set (FA := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_right (rget F9 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F9).
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
                       with "Hcg Hpc Hi06a").
             iIntros (CID36 Hq36) "Hcg Hpc".
             set (FB := <[Regidx Ra4 := regval_into_reg
                           (mword_of_int 1 : mword 64)]> FA).
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
             iAssert (ic_loaded γfs γi cov logstart kslot cinum dnc bmc)
               with "[Hcdiat Hcity Hcimaj Hcimin Hcinl Hcisz Hcaddrs Hcind
                      Hcblocks Hcdlnk]" as "Hcload".
             { rewrite /ic_loaded. iExists datc.
               iSplitR; [iPureIntro; exact Hciok |].
               iSplitR; [iPureIntro; exact Hcdok |].
               iSplitL "Hcdlnk"; [iExact "Hcdlnk" |].
               iFrame "Hcdiat".
               iSplitL "Hcity Hcimaj Hcimin Hcinl Hcisz".
               - rewrite /inode_meta /i_type. iFrame.
               - iFrame. }
             destruct (zopz0zI_u (mword_of_int 1 : mword 64)
                         (cr_trange (di_type dnc))) eqn:Hrng.
             ++ (* ===== ARM F-BAD (second entry): the type is out of
                    range, so the found inode is a directory or free ==== *)
                iApply (wp_bltu_taken_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          ltac:(rewrite Htg098b; vm_compute; reflexivity)
                          with "Hcg Hpc Hi06c").
                iIntros (CID37 Hq37). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htg098b) in "Hpc".
                iDestruct (cpu_own_transport CIDic CID37 0%nat eb
                             (proc_addr j) C b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
                  as "Hcnt".
                iPoseProof ("Hfbad" $! CID37) as "Hfb".
                iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
                iApply ("Hfb" $! FB with
                          "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                           Hnb14 Hnb2 Hcslkd Hcslpid Hcdep Hcidev Hciinum
                           Hcivalid Hcload Hcshot Hckeep Hsbn Hsbi Hsbs Hsbb
                           Hbmr Hppid Hppback Hpath Hbsl Hisl Hislr Hop Hcont").
                { exact HFBregs. }
             ++ (* ===== ARM F-OK: the found inode is a file or a device *)
                iApply (wp_bltu_fall_s_sconf (mword_of_int (CK + 0x6c))
                          (mword_of_int 44 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          with "Hcg Hpc Hi06c").
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
                iDestruct (cpu_own_transport CIDic CIDf 0%nat eb (proc_addr j) C b
                             ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
                iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
                iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
                iApply ("Hcont" $! mf true false kslot (qq/2)%Qp (qq/2)%Qp gc
                          cinum dnc bmc n2 Sb2 (1 + (ns - 2))%nat used2
                          with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv
                                Hpath Hbsl [%] Hisl [%] Hop [Hcslkd Hcslpid Hcdep
                                Hcidev Hciinum Hcivalid Hcload Hckeep]").
                { exact Hcsf. }
                { exact (cr_slots_1 ns Hns). }
                { exact (conj (cr_sub2 _ _ _ Hsb1 Hsb2)
                           (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))). }
                iSplitR.
                { iPureIntro. split; [rewrite Ha0f; exact HFBs2 |].
                  split; [exact Hkslot |].
                  split; [split; [exact Hcpos | exact Hcinb] |].
                  split; [exact Htyf |].
                  exact (cr_trange_in (di_type dnc) Hrng). }
                rewrite /create_locked. iExists gilc, gislc.
                iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckp".
                iFrame "Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum Hcivalid
                        Hcload Hcshot Hckp".
          -- (* ===== ARM F-BAD (first entry): type != T_FILE ========== *)
             iApply (wp_bne_taken_s_sconf (mword_of_int (CK + 0x5c))
                       (mword_of_int 60 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_ne _ Htyf))
                       ltac:(rewrite Htg098; vm_compute; reflexivity)
                       with "Hcg Hpc Hi05c").
             iIntros (CID31 Hq31). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg098) in "Hpc".
             iDestruct (cpu_own_transport CIDic CID31 0%nat eb
                          (proc_addr j) C b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt")
               as "Hcnt".
             iPoseProof ("Hfbad" $! CID31) as "Hfb".
             iSpecialize ("Hfb" with "[%]"); [wp_next_chain |].
             iApply ("Hfb" $! F6 with
                       "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hcslkd Hcslpid Hcdep Hcidev Hciinum
                        Hcivalid Hcload Hcshot Hckeep Hsbn Hsbi Hsbs Hsbb
                        Hbmr Hppid Hppback Hpath Hbsl Hisl Hislr Hop Hcont").
             { exact HF6regs. }
        * (* ========================================================== *)
          (*  THE NAME IS NOT THERE -- the ALLOCATE half, PARKED         *)
          (* ========================================================== *)
          iDestruct "Hres2" as "((%Hnone & %Hdla0) & Hisl1 & _)".
          (* +0x4a c.mv s2,a0 : s2 := 0, and it STAYS 0 all the way to
             +0xe6 / +0xf2 -- the live invariant the failure arms use. *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x4a)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04a").
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (A1 := <[Regidx Rs2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (mdl !!! Regidx Ra0))]> mdl).
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
                    with "Hcg Hpc Hi04c").
          iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg0a2) in "Hpc".
          iDestruct ("Hppback" with "Hppid") as "Hpriv".
          iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          iDestruct (iref_slots_combine with "Hisl1 Hislr") as "Hisl".
          assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat)
            by exact (cr_ns_1 ns Hns).
          iEval (rewrite Hns1) in "Hisl".
          iDestruct (cpu_own_transport CIDdl CID25 0%nat eb (proc_addr j) C b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iPoseProof ("Halloc" $! CID25) as "Ha".
          iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
          iApply ("Ha" $! A1 u5 kd qd gd gild gisld dind dnl bml datl nfp nf0
                    n1 Sb1 used1 w
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                          [%]
                          Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                          Hnb14 Hnb2 Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                          Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hshotl Hkeep
                          Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath Hbsl Hisl Hop
                          Hcont").
          { rewrite -Hie. exact HA1regs. }
          { exact Hkd. }
          { exact Hdib'. }
          { exact Htydir. }
          { exact Hnl0. }
          { exact Hnlmax. }
          { exact Hiok. }
          { rewrite Hnib. exact Hdok. }
          { exact Hnpname. }
          { exact Hnone. }
          { exact Hsb1. }
          { exact Hwmem. }
          { exact Hnp1. }
          { exact Husd1. }
          - (* ===== ARM G2: the guard FIRES -- the parent is a full ====
               directory and the caller asked for another one.  The block
               is ARM G's, at +0x8e, and it closes the same way: the
               [iunlockput(dp)] runs uncredited and the answer is 0.  What
               differs is only the hypothesis it is under -- [nlink] is
               32767 here rather than 0 -- and no step below reads it. *)
            iIntros (CIDg) "%Hqg". iIntros (Mg) "%HMgregs Hcg Hpc".
            pose proof HMgregs as HMgR.
            destruct HMgR as (V2 & V8 & V9 & V18 & V20 & V21 & V22 & Vthr).
        iPoseProof (cri_08e with "Htext") as "Hi08e".
        iPoseProof (cri_090 with "Htext") as "Hi090".
        iPoseProof (cri_094 with "Htext") as "Hi094".
        iPoseProof (cri_096 with "Htext") as "Hi096".
        iAssert (ic_loaded γfs γi cov logstart kd dind dnl bml)
          with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind Hblocks Hdlnk]"
          as "Hload".
        { rewrite /ic_loaded. iExists datl.
          iSplitR; [iPureIntro; exact Hiok |].
          iSplitR; [iPureIntro; exact Hdok |].
          iSplitL "Hdlnk"; [iExact "Hdlnk" |].
          iFrame "Hdiat".
          iSplitL "Hity Himaj Himin Hinl Hisz".
          - rewrite /inode_meta /i_type /i_nlink. iFrame.
          - iFrame. }
        iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        (* +0x8e c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x8e)) Ra0 Rs1 Mg
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi08e").
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (J1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Mg !!! Regidx Rs1))]> Mg).
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
                  (sign_extend' 64 (mword_of_int 2091040 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x90)) Rra
                  (mword_of_int 2091040 : mword 21) J1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi090").
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite HtgupG) in "Hpc".
        set (J2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)]> J1).
        assert (HJ2ra : J2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x90) : mword 64) 4)
          by (rewrite /J2; apply upd_eq).
        assert (HJ2a0 : J2 !!! Regidx Ra0 = ientry kd)
          by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
        assert (HJ2regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor J2)
          by (rewrite /J2; apply cr_regs_caller; [exact Hcsra | exact HJ1regs]).
        iDestruct (cpu_own_transport CIDil CID21 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (log_opS_named with "Hop") as (e0) "Hop".
        iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
        iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
                  gtl gild gisld cov logstart bmapstart inodestart nib size dev
                  used1 kd (qd/2)%Qp (qd/2)%Qp gd dind dnl bml n1 Sb1
                  false false false e0 pidv (DfracOwn (1/4)) dqb dqs
                  J2 (K - 10)%nat eb C b
                  ltac:(exact HKiup) Hkd ltac:(discriminate) ltac:(discriminate)
                  Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib' Hcovb
                  ltac:(exact Hn1ip) Hj Hgs HJ2a0
                  with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                        Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                        Hivalid Hload Hshotl Hkeep2 Hsbb Hsbi Hbmr Hppid
                        Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iEval (cbn beta iota). iEmpIntro. }
        iIntros (CIDup Hqup mup n2 used2 Sb2 wg)
          "%Hcsup Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd2 Hbmr Hbsl
           %Hsb2 %Hwg %Hwgc %Hn2 Hop Hisl".
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
                  with "Hcg Hpc Hi094").
        iIntros (CID22 Hq22) "Hcg Hpc".
        set (J3 := <[Regidx Rs2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> mup).
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
                  with "Hcg Hpc Hi096").
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg070h) in "Hpc".
        iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
        iPoseProof ("Htail" $! CID23) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! J3 u5 nfj with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
        { exact (cr_tregs_of_regs m sp0 ipv _ ty major minor J3 HJ3regs). }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDup CIDf 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        (* the slot ledger comes back whole: nameiparent took two and gave
           one back, and this [iunlockput] gave the other. *)
        iDestruct (iref_slots_combine with "Hisl1 Hisl") as "Hisl".
        iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
        iEval (rewrite -Hnsplit) in "Hisl".
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                  (mword_of_int 0 : mword 32) dnl bml n2 Sb2 ns used2
                  with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath
                        Hbsl [%] Hisl [%] Hop [%]").
        { exact Hcsf. }
        { exact (cr_slots_ns ns Hns). }
        { exact (conj (cr_sub2 _ _ _ Hsb1 Hsb2)
                   (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))). }
        { rewrite Ha0f. exact HJ3s2. }
        }
        iPoseProof (cri_030 with "Htext") as "Hi030".
        iPoseProof (cri_032 with "Htext") as "Hi032".
        iPoseProof (cri_034 with "Htext") as "Hi034".
        iPoseProof (cri_036 with "Htext") as "Hi036".
        iPoseProof (cri_038 with "Htext") as "Hi038".
        iPoseProof (cri_03c with "Htext") as "Hi03c".
        (* ===== +0x30 c.lui a4,0xffff8 ================================= *)
        iApply (wp_clui_s_sconf (mword_of_int (CK + 0x30)) Ra4
                  (sign_extend' 20 (mword_of_int 56 : mword 6))
                  (mword_of_int (-32768) : mword 64) Q3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi030").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (N1 := <[Regidx Ra4 := regval_into_reg
                      (mword_of_int (-32768) : mword 64)]> Q3).
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
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi032").
        iIntros (CID21 Hq21) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (N2 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (N1 !!! Regidx Ra4)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 1 : mword 6))))]> N1).
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
                  N2 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi034").
        iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
        set (N3 := <[Regidx Ra5 := regval_into_reg
                      (add_vec (N2 !!! Regidx Ra5) (N2 !!! Regidx Ra4))]> N2).
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
                    with "Hcg Hpc Hi036").
          iIntros (CID23 Hq23) "Hcg Hpc".
          assert (Hp038 : add_vec_int (mword_of_int (CK + 0x36) : mword 64) 2
                          = mword_of_int (CK + 0x38)) by pcw.
          iEval (rewrite Hp038) in "Hpc".
          (* ===== +0x38 addi a5,s4,-1 : a5 = type - T_DIR ============== *)
          iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x38)) Ra5 Rs4
                    (mword_of_int 4095 : mword 12) N3 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi038").
          iIntros (CID24 Hq24) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (N4 := <[Regidx Ra5 := regval_into_reg
                        (add_vec (N3 !!! Regidx Rs4)
                           (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> N3).
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
                       with "Hcg Hpc Hi03c").
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
                       with "Hcg Hpc Hi03c").
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
                    with "Hcg Hpc Hi036").
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
                with "Hcg Hpc Hi022").
      iIntros (CID16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg160) in "Hpc".
      iPoseProof (cri_160 with "Htext") as "Hi160".
      iPoseProof (cri_162 with "Htext") as "Hi162".
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
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi160").
      iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (N1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q1 !!! Regidx Ra0))]> Q1).
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
                with "Hcg Hpc Hi162").
      iIntros (CID18 Hq18). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg070n) in "Hpc".
      iDestruct (cr_join14 (pa_stk sp0 10) with "Hnb14 Hnb2") as (nfj) "Hnb16".
      iPoseProof ("Htail" $! CID18) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! N1 u5 nfj with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb16").
      { exact (cr_tregs_of_regs m sp0 _ _ ty major minor N1 HN1regs). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDnp CIDf 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hisl2 Hislr") as "Hisl".
      iEval (rewrite -Hnsplit) in "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32)
                (MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
                          (replicate 13 (bv_0 32)))
                bm_empty n1 Sb1 ns used1
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [%]").
      { exact Hcsf. }
      { exact (cr_slots_ns ns Hns). }
      { exact (conj Hsb1 (proj2 Hnp1)). }
      { rewrite Ha0f. exact HN1s2. }
  Qed.



  (* =================================================================== *)
  (*  4.  THE ALLOCATE HALF, +0xa2 .. +0xea                               *)
  (*                                                                      *)
  (*  [cr_alloc_half] discharges [cr_alloc_body]: the eighth save, the     *)
  (*  fresh-type gate span, ARM A-FAIL, the three metadata [sh]s, the      *)
  (*  MINT at +0xc4, the T_DIR branch and ARM C-OK-FILE.  Two branches     *)
  (*  leave through a PREMISE -- the T_DIR sub-branch through              *)
  (*  [cr_mkdir_body] and the failing [dirlink] through [cr_fail_body] --  *)
  (*  so [Print Assumptions] sees the standing six plus [create_fresh_ty]  *)
  (*  and nothing else.                                                   *)
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
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (b : bool) :
    (K_create <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    bitmap_geom_ok cov logstart bmapstart size ->
    InodeInv.ireg_blocks_ok inodestart nib cov logstart ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    (* mkfs's own [ushort] geometry, carried as a premise rather than as a
       slot widening (D0-a, the eleventh stop's item-2 ruling): it is what
       makes the [lw a2,4(s3)] at +0xce agree with dirlink's ZERO-extended
       halfword argument. *)
    16 * Z.of_nat nib <= 2 ^ 16 ->
    bv_unsigned ty <> 0 ->
    printk_gen_contract γpr γu γd ->
    (create_units <= u)%nat ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ panic_wp_any -∗ kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    kalloc_env γa None -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    SpecDirlink.ic_sleeplocks cn -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    (* ---- THE T_DIR SUB-BRANCH, PARKED (D0-b consumes it) ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDm : CpuId =>
         cr_mkdir_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γa γf γpr
                       cov logstart bmapstart inodestart nib ninodes size dev
                       used plen pfun pv ty major minor V u Sb ns pidv
                       dqb dqs dqbs dqn m sp0 ret_tgt K eb C b
                       kd qd gd γil γisl dind dn bm data nf nsl CIDm)) -∗
    (* ---- ARM FAIL's NON-DIRECTORY ENTRY, PARKED ---- *)
    (∀ (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
       (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
       (nf nsl : nat -> bv 8),
       wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
         cr_fail_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γa γf γpr
                      cov logstart bmapstart inodestart nib ninodes size dev
                      used plen pfun pv ty major minor V u Sb ns pidv
                      dqb dqs dqbs dqn m sp0 ret_tgt K eb C b
                      kd qd gd γil γisl dind dn bm data nf nsl CIDf)) -∗
    (* THE CONCLUSION IS [wp_next]-WRAPPED, and it has to be.  The two parked
       bodies and [cr_alloc_body]'s own [Hcont] are all anchored at the
       SECTION hart, while the allocate half's resources arrive at whatever
       hart the [c.beqz] at +0x4c rebound to -- so the walk needs that hart's
       own chain link, which is exactly what [wp_next]'s guard is.  Stated at
       a bare [CIDa : CpuId] parameter the lemma is UNPROVABLE (nothing
       relates [CIDa] to [CID]), and this is also the shape [cr_found_half]
       takes its premise in, so the seal is one [iApply]. *)
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDa : CpuId =>
      cr_alloc_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γa γf γpr
                    cov logstart bmapstart inodestart nib ninodes size dev used
                    plen pfun pv ty major minor V u Sb ns pidv dqb dqs dqbs dqn
                    m sp0 ret_tgt K eb C b CIDa).
  Proof.
    intros HK Hdev Hnib Hglog Hist Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
           Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Htynz Hpkc Hu Hns Hj Hgs
           Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hpanic #Hkd #Hpk #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl #Hesc
             #Hslks #Hiregi #Hprocs #Hdevi #Hgeom #Hdlk Hmk Hfl".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDa Hsa).
    iIntros (Ma w5 kd qd gd γil γisl dind dn bm data nf nsl n1 Sb1 used1 w).
    iIntros "%HAregs %Hkdlt %Hdib %Htydir %Hnl0 %Hnlmax %Hiok %Hdok %Hnpname
             %Hnone %Hsb1 %Hwmem %Hnp1 %Husd1".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hslpid Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks #Hshotl Hkeep
             Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath Hbsl Hisl Hop Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
    pose proof HAregs as HAr.
    destruct HAr as (A2 & A8 & A9 & A18 & A20 & A21 & A22 & Athr).
    (* the ledger row [CreateBudget.cr_budget_found_w] is stated at *)
    assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
    assert (Hn1u : (n1 <= u)%nat) by exact (proj2 Hnp1).
    destruct n1 as [| q1]; [exfalso; lia |].
    assert (Hq1 : (8 <= q1)%nat) by lia.
    assert (Hn1ip : (iput_units <= S q1)%nat) by exact (cr_ip_of9 _ Hn1lo).
    destruct (Hiregb dind Hdib) as [Hdblk Hdblog].
    iDestruct (cr_esc_acc cn γfs γi cov logstart kd Hkdlt with "Hesc") as "#Hescd".
    (* ===== +0xa2 c.sdsp s3,40(sp) : THE EIGHTH SAVE ================== *)
    iPoseProof (cri_0a2 with "Htext") as "Hi0a2".
    assert (HAs3 : (Ma !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (Athr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)
                     ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
    assert (Hf5 : add_vec (Ma !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite A2; apply cr_frm5).
    iEval (rewrite -Hf5) in "Hb5".
    iApply (wp_csdsp_s_sconf (mword_of_int (CK + 0xa2)) (mword_of_int 5 : mword 6)
              Rs3 Ma (K - 10)%nat w5 b with "Hcg Hpc Hi0a2 Hb5").
    iIntros (CIDA1 HqA1) "Hcg Hpc Hb5".
    iEval (rgne; rewrite HAs3 Hf5) in "Hb5".
    assert (Hq0a4 : add_vec_int (mword_of_int (CK + 0xa2) : mword 64) 2
                    = mword_of_int (CK + 0xa4)) by pcw.
    iEval (rewrite Hq0a4) in "Hpc".
    (* ---- the ledger, split for the gate ---- *)
    assert (Hns1 : (1 + (ns - 2))%nat = (ns - 1)%nat) by exact (cr_ns_1 ns Hns).
    iEval (rewrite -Hns1 iref_slots_op) in "Hisl".
    iDestruct "Hisl" as "[Hisl1 Hislr]".
    iDestruct (proc_priv_pid γf (proc_addr j) pidv V with "Hpriv")
      as "[Hppid Hppback]".
    iDestruct (cpu_own_transport CIDa CIDA1 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    (* ===== +0xa4 .. +0xb0 : THE FRESH-TYPE GATE SPAN ================= *)
    iApply (CFT.create_fresh_ty γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
              γpr cov logstart inodestart ninodes nib dev ty kd (DfracOwn (1/2))
              q1 Sb1 pidv (DfracOwn (1/4)) dqs dqn Ma (K - 10)%nat eb C b
              ltac:(exact HKia) ltac:(exact HKil) Hlg Hist0 Hiregb Hni1 Hni2
              Hni3 Htynz Hpkc Hj Hgs Hroot A20 A9 Hkdlt Heb
              (fun CIDx : CpuId => IA.wp_ialloc_gen (CID := CIDx))
              (fun CIDx : CpuId => IL.wp_ilock_sconf (CID := CIDx))
              with "Hcg Hcnt Htext Hpc Hpanic Hkd Hpk Hbio Hlogc Hitb2 Hitbl
                    Hesc Hslks Hiregi Hprocs Hdevi Hgeom Hdlk Hsbn Hsbi Hppid
                    Hbsl Hisl1 Hidev Hop").
    iIntros (CIDo Hso Mo alloc kslot q g cinum gil gisl dnc bmc)
      "%Hcs3 Hcg Hcnt Hsbn Hsbi Hppid Hbsl Hidev Hres".
    destruct alloc.
    - (* ============================================================== *)
      (*  THE INODE WAS CLAIMED, LOCKED AND FILLED -- control at +0xb4   *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hpure & Hpc & #Hslkc & Hcslkd & Hcslpid & Hcdep &
                            Hcidev & Hciinum & Hcivalid & Hcload & #Hcshot &
                            Hckeep & Hop)".
      destruct Hpure as (Hs3 & Hkslt & Hcpos & Hcinb & Htyc & Hfresh).
      destruct (Hiregb cinum Hcinb) as [Hcblk Hcblog].
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (ientry kslot) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor Ma Mo Hcs3 Hs3 HAregs).
      pose proof HMoregs as HMoR.
      destruct HMoR as (M2 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & Mthr).
      iDestruct "Hcload" as (datc)
        "(%Hciok & %Hcdok & Hcdlnk & Hcdiat & Hcmeta & Hcaddrs & Hcind &
          Hcblocks)".
      iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
      iEval (rewrite /i_major) in "Hcimaj".
      iEval (rewrite /i_minor) in "Hcimin".
      iEval (rewrite /i_nlink) in "Hcinl".
      iPoseProof (cri_0b4 with "Htext") as "Hi0b4".
      iPoseProof (cri_0b8 with "Htext") as "Hi0b8".
      iPoseProof (cri_0bc with "Htext") as "Hi0bc".
      iPoseProof (cri_0be with "Htext") as "Hi0be".
      iPoseProof (cri_0c2 with "Htext") as "Hi0c2".
      iPoseProof (cri_0c4 with "Htext") as "Hi0c4".
      iPoseProof (cri_0c8 with "Htext") as "Hi0c8".
      iPoseProof (cri_0ca with "Htext") as "Hi0ca".
      (* ===== +0xb4 sh s5,70(s3) : ip->major = major ================== *)
      iApply (wp_sh_s_sconf (mword_of_int (CK + 0xb4)) Rs5 Rs3
                (mword_of_int 70 : mword 12) Mo (K - 10)%nat (di_major dnc) b
                with "Hcg Hpc Hi0b4 [Hcimaj]").
      { iEval (rgne; rewrite M19). iExact "Hcimaj". }
      iIntros (CIDB1 HqB1) "Hcg Hpc Hcimaj".
      iEval (rgne; rgne; rewrite M19 M21 trunc16_sext64) in "Hcimaj".
      assert (Hq0b8 : add_vec_int (mword_of_int (CK + 0xb4) : mword 64) 4
                      = mword_of_int (CK + 0xb8)) by pcw.
      iEval (rewrite Hq0b8) in "Hpc".
      (* ===== +0xb8 sh s6,72(s3) : ip->minor = minor ================== *)
      iApply (wp_sh_s_sconf (mword_of_int (CK + 0xb8)) Rs6 Rs3
                (mword_of_int 72 : mword 12) Mo (K - 10)%nat (di_minor dnc) b
                with "Hcg Hpc Hi0b8 [Hcimin]").
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
                with "Hcg Hpc Hi0bc").
      iIntros (CIDB3 HqB3) "Hcg Hpc".
      set (W1 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> Mo).
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
      iApply (wp_sh_s_sconf (mword_of_int (CK + 0xbe)) Ra4 Rs3
                (mword_of_int 74 : mword 12) W1 (K - 10)%nat (di_nlink dnc) b
                with "Hcg Hpc Hi0be [Hcinl]").
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
      iAssert (inode_map γfs (ientry kslot) bmc)
        with "[Hcaddrs Hcind]" as "Hcmap".
      { rewrite /inode_map. iFrame. }
      (* ===== +0xc2 c.mv a0,s3 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xc2)) Ra0 Rs3 W1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c2").
      iIntros (CIDB5 HqB5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (W2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs3))]> W1).
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
                (sign_extend' 64 (mword_of_int 2090284 : mword 21))
                = mword_of_int KernelSyms.iupdate) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xc4)) Rra
                (mword_of_int 2090284 : mword 21) W2 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c4").
      iIntros (CIDB6 HqB6) "Hcg Hpc".
      iEval (rewrite Htgiu) in "Hpc".
      set (W3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xc4) : mword 64) 4)]> W2).
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
        by exact (blkmap_wf_dir_len cov logstart bmc (proj1 Hciok)).
      destruct q1 as [| q2]; [exfalso; lia |].
      iDestruct (cr_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
      iDestruct (cpu_own_transport CIDo CIDB6 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IU.wp_iupdate_link γs j γl γu γd γk pd pav pu bn γ γfs γi
                cov logstart inodestart nib dev (ientry kslot) cinum
                (cr_setf dnc major minor (mword_of_int 1 : mword 16)) dnc bmc
                q2 (Sb1 ∪ {[IBLOCK cinum inodestart]}) true pidv
                (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
                W3 (K - 10)%nat eb C b
                ltac:(exact HKiu)
                ltac:(intros _; exact (cr_in_union_sing Sb1 _))
                Hlg Hist0 Hcblk Hcblog Hcinb
                ltac:(exact (di_type_stable_eq _ _
                        (cr_setf_type dnc major minor _)))
                ltac:(exact (cr_setf_type_nz dnc major minor _ Htyz))
                Hbump Hgrd Hcadd Hcdirlen Hj Hgs HW3a0 Heb
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlogc Hcidev Hciinum
                      Hcmeta Hcmap Hsbi Hiregi Hcdiat Hppid Hprocs Hdevi
                      Hgeom Hdlk Hbs2 Hop").
      iIntros (CIDiu Hsiu miu)
        "%Hcsiu Hcg Hcnt Hpc Hppid Hcidev Hciinum Hcmeta Hcmap Hsbi Hcdiat
         Hilink Hbs2 Hop".
      assert (Hpciu : ret_pc (W3 !!! Regidx Rra : mword 64)
                      = mword_of_int (CK + 0xc8)) by (rewrite HW3ra; pcw).
      iEval (rewrite Hpciu) in "Hpc".
      assert (Hmiuregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                           (ientry kslot) ty major minor miu)
        by exact (cr_regs3_cs m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (ientry kslot) ty major minor W3 miu Hcsiu HW3regs).
      pose proof Hmiuregs as HmiuR.
      destruct HmiuR as (N2 & N8 & N9 & N18 & N19 & N20 & N21 & N22 & Nthr).
      iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
        [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
      (* ===== +0xc8 c.li a4,1 ====================================== *)
      iApply (wp_cli_s_sconf (mword_of_int (CK + 0xc8)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                miu (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi0c8").
      iIntros (CIDB7 HqB7) "Hcg Hpc".
      set (W4 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int 1 : mword 64)]> miu).
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
        (*  [ilink] is UNDEPOSITED here -- +0xc4 minted it and this arm's  *)
        (*  own [dirlink(dp,name)] at +0x12c is what spends it.            *)
        (* ============================================================ *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_eq ty Htdir))
                  ltac:(rewrite Htg0f8; vm_compute; reflexivity)
                  with "Hcg Hpc Hi0ca").
        iIntros (CIDB8 HqB8). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg0f8) in "Hpc".
        iDestruct (cpu_own_transport CIDiu CIDB8 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hmk" $! kd qd gd γil γisl dind dn bm data nf nsl).
        iPoseProof ("Hmk" $! CIDB8) as "Hm".
        iSpecialize ("Hm" with "[%]"); [wp_next_chain |].
        iApply ("Hm" $! W4 kslot q g gil gisl cinum dnc bmc datc
                  (S q2) (Sb1 ∪ {[IBLOCK cinum inodestart]}
                          ∪ {[IBLOCK cinum inodestart]}) used1
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                        Hnb14 Hnb2 Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                        Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hshotl Hkeep
                        Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum Hcivalid
                        Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks Hcshot Hckeep
                        Hilink Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath
                        Hbsl Hislr Hop Hcont").
        { exact HW4regs. }
        { exact Htdir. }
        { exact Hkdlt. }
        { exact Hdib. }
        { exact Htydir. }
        { exact Hnl0. }
        { exact (Hnlmax Htdir). }
        { exact Hiok. }
        { exact Hdok. }
        { exact Hnpname. }
        { exact Hnone. }
        { exact Hkslt. }
        { exact Hcpos. }
        { exact Hcinb. }
        { exact Hfresh. }
        { exact Htyc. }
        { exact Hciok. }
        { rewrite Hnib. exact Hcdok. }
        { exact (cr_sub2 _ _ _ (cr_sub2 _ _ _ Hsb1 (cr_sub_union_sing Sb1 _))
                   (cr_sub_union_sing _ _)). }
        { exact (cr_in_union_sing _ _). }
        { split; [lia | lia]. }
        { exact Husd1. }
      + (* ============================================================ *)
        (*  +0xca FALLS THROUGH: the non-directory path                  *)
        (* ============================================================ *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (CK + 0xca))
                  (mword_of_int 46 : mword 13) Ra4 Rs4 W4 (K - 10)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HW4s4 HW4a4;
                        exact (cr_tdir_ne ty Htdir))
                  with "Hcg Hpc Hi0ca").
        iIntros (CIDB8 HqB8) "Hcg Hpc".
        assert (Htdirz : bv_unsigned (di_type dnc) <> T_DIR_z).
        { rewrite Htyc. intro Hc. apply Htdir.
          apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
        assert (Hq0ce : add_vec_int (mword_of_int (CK + 0xca) : mword 64) 4
                        = mword_of_int (CK + 0xce)) by pcw.
        iEval (rewrite Hq0ce) in "Hpc".
        iPoseProof (cri_0ce with "Htext") as "Hi0ce".
        iPoseProof (cri_0d2 with "Htext") as "Hi0d2".
        iPoseProof (cri_0d6 with "Htext") as "Hi0d6".
        iPoseProof (cri_0d8 with "Htext") as "Hi0d8".
        iPoseProof (cri_0dc with "Htext") as "Hi0dc".
        (* ===== +0xce lw a2,4(s3) : the child's inum ================ *)
        iApply (wp_lw_s_sconf (mword_of_int (CK + 0xce)) Ra2 Rs3
                  (mword_of_int 4 : mword 12) W4 (K - 10)%nat cinum b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0ce [Hciinum]").
        { iEval (rgne; rewrite HW4s3). iExact "Hciinum". }
        iIntros (CIDC1 HqC1) "Hcg Hpc Hciinum".
        iEval (rgne; rewrite HW4s3) in "Hciinum".
        set (X1 := <[Regidx Ra2 := regval_into_reg
                      (sign_extend' 64 cinum : mword 64)]> W4).
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
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d2").
        iIntros (CIDC2 HqC2) "Hcg Hpc".
        set (X2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (rget X1 Rs0)
                         (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> X1).
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
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0d6").
        iIntros (CIDC3 HqC3) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (X3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64)
                         (X2 !!! Regidx Rs1))]> X2).
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
                  (sign_extend' 64 (mword_of_int 2092390 : mword 21))
                  = mword_of_int KernelSyms.dirlink) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0xd8)) Rra
                  (mword_of_int 2092390 : mword 21) X3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0d8").
        iIntros (CIDC4 HqC4) "Hcg Hpc".
        iEval (rewrite Htgdlk) in "Hpc".
        set (X4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0xd8) : mword 64) 4)]> X3).
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
        assert (Hbmwf : blkmap_wf cov logstart bm) by exact (proj1 Hiok).
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
        iAssert (inode_map γfs (ientry kd) bm) with "[Haddrs Hind]" as "Hmap".
        { rewrite /inode_map. iFrame. }
        assert (Hns2 : (1 + (ns - 3))%nat = (ns - 2)%nat)
          by exact (cr_ns_2 ns Hns).
        iEval (rewrite -Hns2 iref_slots_op) in "Hislr".
        iDestruct "Hislr" as "[Hislk Hislrr]".
        iDestruct (cpu_own_transport CIDiu CIDC4 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (DLK.wp_dirlink_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
                  gtl γa γf γpr cov logstart inodestart nib bmapstart size dev
                  used1 (ientry kd) dind bm data dn dn nf (cr_low16 cinum)
                  (S q2) (Sb1 ∪ {[IBLOCK cinum inodestart]}
                          ∪ {[IBLOCK cinum inodestart]})
                  pidv (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1) dqs
                  dqb dqbs (DfracOwn (1/2))
                  X4 (K - 10)%nat eb C b
                  ltac:(exact HKdlk) Htydir Hbmcov Hszcap
                  ltac:(exact (Hdok Hdz))
                  ltac:(exact (di_type_stable_refl dn))
                  ltac:(exact (di_nlink_stable_refl dn Htynzd))
                  Hlg Hbmwf Hholes Hdaddr Hsz31 Hist0 Hdblk Hdblog Hdib
                  Hcl16b Hbmgeo Hpkc Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb
                  ltac:(exact (cr_alloc_dlneed (S q2) _ _ ltac:(lia)))
                  Hj Hgs HX4a0 HX4a2 Heb
                  with "Hcg Hcnt Htext Hpc Hpanic Hkd Hpk Hbio Hlogc Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs Hsbb
                        Hbmr Hiregi Hdiat Hppid Hprocs Hdevi Hgeom Hdlk Hbsl
                        Hitb2 Hitbl Hesc Hslks Hislk Hop").
        iIntros (CIDdl Hsdl mdl found bm' data' dn' dn0' n' used' Sb' tot)
          "%Hcsdl Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnb14 Hsbi Hsbs
           Hsbb Hbmr Hdiat Hppid Hbsl Hislk %Hn' %Hsb' %Hdl16 Hop %Hcapp
           %Hsizedp %Harm".
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
        * destruct Harm as (_ & Husd' & Hwf' & Hholes' & Haddr' & Hsz31' &
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
                            <= 16 * dir_nrec (bv_unsigned (di_size dn)) + 16)%nat)
            by lia.
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
          { rewrite Hmb in Hszcap. change (2 ^ 32)%Z with 4294967296%Z. lia. }
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
             iPoseProof (cri_0e0 with "Htext") as "Hi0e0".
             iPoseProof (cri_0e2 with "Htext") as "Hi0e2".
             iPoseProof (cri_0e6 with "Htext") as "Hi0e6".
             iPoseProof (cri_0e8 with "Htext") as "Hi0e8".
             iPoseProof (cri_0ea with "Htext") as "Hi0ea".
             (* ===== +0xdc bltz a0 : FALLS THROUGH ================== *)
             iApply (wp_blt_x0_fall_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0z; exact cr_bltz_zero)
                       with "Hcg Hpc Hi0dc").
             iIntros (CIDD1 HqD1) "Hcg Hpc".
             assert (Hq0e0 : add_vec_int (mword_of_int (CK + 0xdc) : mword 64) 4
                             = mword_of_int (CK + 0xe0)) by pcw.
             iEval (rewrite Hq0e0) in "Hpc".
             (* the PARENT'S RE-PARK: the [ilink] the mint made goes into
                the record the append just wrote. *)
             iEval (rewrite -Hcl16) in "Hilink".
             iDestruct (dir_link_at_dirlink (bv_unsigned dind) dn' data data'
                          (cr_low16 cinum) (bname 14 nf)
                          (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                          tot ltac:(lia) Hrng with "Hilink") as "Hk0".
             iDestruct (dir_links_dirlink (bv_unsigned dind) dn dn' data data'
                          (cr_low16 cinum) (bname 14 nf)
                          (dir_nrec (bv_unsigned (di_size dn)))
                          (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                          tot eq_refl eq_refl Htot16 Hty' Hnl' Hszmax Hrng
                          with "Hk0 Hdlnk") as "Hdlnk".
             assert (Hiok' : inode_ok cov logstart dn' bm' data').
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
             iAssert (ic_loaded γfs γi cov logstart kd dind dn' bm')
               with "[Hdlnk Hdiat Hmeta Hmap Hblocks]" as "Hload".
             { rewrite /ic_loaded. iExists data'.
               iSplitR; [iPureIntro; exact Hiok' |].
               iSplitR; [iPureIntro; rewrite -Hnib; exact Hdok' |].
               iSplitL "Hdlnk"; [iExact "Hdlnk" |].
               rewrite (Hdn0' eq_refl). iFrame "Hdiat Hmeta".
               iEval (rewrite /inode_map) in "Hmap".
               iDestruct "Hmap" as "[Haddrs Hind]". iFrame. }
             (* ===== +0xe0 c.mv a0,s1 ============================== *)
             iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xe0)) Ra0 Rs1 mdl
                       (K - 10)%nat b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi0e0").
             iIntros (CIDD2 HqD2) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (Y1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mdl !!! Regidx Rs1))]> mdl).
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
                       (sign_extend' 64 (mword_of_int 2090958 : mword 21))
                       = mword_of_int KernelSyms.iunlockput) by pcw.
             iApply (wp_jal_s_sconf (mword_of_int (CK + 0xe2)) Rra
                       (mword_of_int 2090958 : mword 21) Y1 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc Hi0e2").
             iIntros (CIDD3 HqD3) "Hcg Hpc".
             iEval (rewrite Htgu2) in "Hpc".
             set (Y2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (CK + 0xe2) : mword 64) 4)]> Y1).
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
             iDestruct (cpu_own_transport CIDdl CIDD3 0%nat eb (proc_addr j) C b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (log_opS_named with "Hop") as (e0) "Hop".
             iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
             iAssert (ity_shot gd (di_type dn')) as "#Hshotl'".
             { rewrite Hty'. iExact "Hshotl". }
             iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs
                       γi cn gtl γil γisl cov logstart bmapstart inodestart nib
                       size dev used' kd (qd/2)%Qp (qd/2)%Qp gd dind dn' bm'
                       n' Sb' false false false e0 pidv (DfracOwn (1/4)) dqb dqs
                       Y2 (K - 10)%nat eb C b
                       ltac:(exact HKiup) Hkdlt ltac:(discriminate)
                       ltac:(discriminate)
                       Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                       ltac:(exact Hipn') Hj Hgs HY2a0
                       with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2
                             Hitbl Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev
                             Hiinum Hivalid Hload Hshotl' Hkeep2 Hsbb Hsbi Hbmr
                             Hppid Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             { iEval (cbn beta iota). iEmpIntro. }
             iIntros (CIDU2 HqU2 mu2 n2 used2 Sb2 wf2)
               "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd2 Hbmr Hbsl
                %Hsb2 %Hwf2 %Hwf2c %Hn2 Hop Hisl2".
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
                       with "Hcg Hpc Hi0e6").
             iIntros (CIDD4 HqD4) "Hcg Hpc". iEval (rgne) in "Hcg".
             assert (Hy2v : add_vec (zero_reg : mword 64) (mu2 !!! Regidx Rs3)
                            = ientry kslot).
             { destruct Hmu2regs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
               apply add_vec_zero_l. }
             set (Y3 := <[Regidx Rs2 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (mu2 !!! Regidx Rs3))]> mu2).
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
                       with "Hcg Hpc Hi0e8 Hb5").
             iIntros (CIDD5 HqD5) "Hcg Hpc Hb5".
             iEval (rewrite HT5) in "Hb5".
             set (Y4 := <[Regidx Rs3 := regval_into_reg
                           (m !!! Regidx Rs3 : mword 64)]> Y3).
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
                       with "Hcg Hpc Hi0ea").
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
             iDestruct (cpu_own_transport CIDU2 CIDf 0%nat eb (proc_addr j) C b
                          ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (iref_slots_combine with "Hislk Hisl2") as "Hisl".
             iDestruct (iref_slots_combine with "Hisl Hislrr") as "Hisl".
             iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
             iApply ("Hcont" $! mf true true kslot (q/2)%Qp (q/2)%Qp g cinum
                       (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc
                       n2 Sb2 (1 + (1 + (ns - 3)))%nat used2
                       with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv
                             Hpath Hbsl [%] Hisl [%] Hop [Hslkc Hcslkd Hcslpid
                             Hcdep Hcidev Hciinum Hcivalid Hcdlnk Hcdiat Hcmeta
                             Hcmap Hcblocks Hckeep]").
             { exact Hcsf. }
             { exact (cr_slots_3 ns Hns). }
             { split.
               - exact (cr_sub3 _ _ _ _ Hsb1
                          (cr_sub2 _ _ _ (cr_sub_union_sing Sb1 _)
                             (cr_sub_union_sing _ _))
                          (cr_sub2 _ _ _ Hsb' Hsb2)).
               - pose proof (proj2 Hn2) as HB1. pose proof (proj2 Hn') as HB2.
                 lia. }
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
             rewrite /create_locked. iExists gil, gisl.
             iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckp".
             iAssert (ic_loaded γfs γi cov logstart kslot cinum
                        (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc)
               with "[Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks]" as "Hcload".
             { rewrite /ic_loaded. iExists datc.
               iSplitR; [iPureIntro; exact (cr_setf_inode_ok cov logstart dnc
                                              bmc datc major minor _ Hciok) |].
               iSplitR; [iPureIntro;
                         exact (cr_setf_dir_ok icfg_nib dnc datc major minor _ Hcdok) |].
               (* the CHILD is not a directory on this arm, so its record
                  ledger is [emp] at either dinode and the flush's [nlink]
                  bump -- which would break [dir_link_at]'s grey disjunct on
                  a real directory -- is invisible here. *)
               iSplitR.
               { rewrite /dir_links.
                 destruct (decide (bv_unsigned (di_type (cr_setf dnc major minor
                             (mword_of_int 1 : mword 16))) = T_DIR_z))
                   as [Hchdir | Hchdir].
                 - exfalso. apply Htdirz.
                   rewrite -(cr_setf_type dnc major minor
                               (mword_of_int 1 : mword 16)).
                   exact Hchdir.
                 - done. }
               iFrame "Hcdiat Hcmeta".
               iEval (rewrite /inode_map) in "Hcmap".
               iDestruct "Hcmap" as "[Hca Hci]". iFrame. }
             rewrite cr_setf_type.
             iFrame "Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum Hcivalid
                     Hcload Hcshot Hckp".
          -- (* ======================================================== *)
             (*  ARM FAIL's non-directory entry: the append fell short    *)
             (* ======================================================== *)
             iApply (wp_blt_x0_taken_s_sconf (mword_of_int (CK + 0xdc))
                       (mword_of_int 106 : mword 13) Ra0 mdl (K - 10)%nat b
                       ltac:(nz)
                       ltac:(rgne; rewrite Ha0m; exact cr_bltz_m1)
                       ltac:(rewrite Htg146; vm_compute; reflexivity)
                       with "Hcg Hpc Hi0dc").
             iIntros (CIDE1 HqE1). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg146) in "Hpc".
             iDestruct (cpu_own_transport CIDdl CIDE1 0%nat eb (proc_addr j) C b
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
             iSpecialize ("Hfl" $! kd qd gd γil γisl dind dn bm data nf nsl).
             iPoseProof ("Hfl" $! CIDE1) as "Hf".
             iSpecialize ("Hf" with "[%]"); [wp_next_chain |].
             iApply ("Hf" $! mdl kslot q g gil gisl cinum dnc bmc datc
                       bm' data' dn' dn0' tot n' Sb' used'
                       with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                             [%] [%] [%] [%] [%] [%]
                             Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                             Hnb14 Hnb2 Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                             Hivalid Hdlnk Hdiat Hmeta Hmap Hblocks Hshotl
                             Hkeep Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum
                             Hcivalid Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks
                             Hcshot Hckeep Hilink Hsbn Hsbi Hsbs Hsbb Hbmr
                             Hppid Hppback Hpath Hbsl Hislr Hop Hcont").
             { exact Hmdlregs. }
             { exact Htdir. }
             { exact Hkdlt. }
             { exact Hdib. }
             { exact Htydir. }
             { exact Hnl0. }
             { exact Hiok. }
             { exact Hdok. }
             { exact Hkslt. }
             { exact Hcpos. }
             { exact Hcinb. }
             { exact Hfresh. }
             { exact Htyc. }
             { exact Hciok. }
             { rewrite Hnib. exact Hcdok. }
             (* [tot < 16] AND dirlink's atomicity IS [tot = 0]: the shape
                the fail body's re-park needs. *)
             { destruct Hatom as [Hz | H16]; [exact Hz | exfalso; lia]. }
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
               pose proof (proj2 Hn') as HB2. lia. }
             (* the LEFT disjunct, and this entry has it unconditionally:
                eight into the dirlink and [wi16_spend <= 4] out. *)
             { left.
               exact (cr_alloc_ip4 (S q2) n' _ _ _ _ _ ltac:(lia) Hspend). }
    - (* ============================================================== *)
      (*  ARM A-FAIL (+0xec): ialloc returned 0, nothing was claimed     *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hs3z & Hpc & Hislg & Hop)".
      iPoseProof (cri_0ec with "Htext") as "Hi0ec".
      iPoseProof (cri_0ee with "Htext") as "Hi0ee".
      iPoseProof (cri_0f2 with "Htext") as "Hi0f2".
      iPoseProof (cri_0f4 with "Htext") as "Hi0f4".
      iPoseProof (cri_0f6 with "Htext") as "Hi0f6".
      assert (HMoregs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                          (mword_of_int 0 : mword 64) ty major minor Mo)
        by exact (cr_regs3_of_span m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                    (mword_of_int 0 : mword 64) ty major minor Ma Mo Hcs3 Hs3z
                    HAregs).
      (* ===== +0xec c.mv a0,s1 ====================================== *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xec)) Ra0 Rs1 Mo
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0ec").
      iIntros (CIDF1 HqF1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Z1 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mo !!! Regidx Rs1))]> Mo).
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
                (sign_extend' 64 (mword_of_int 2090946 : mword 21))
                = mword_of_int KernelSyms.iunlockput) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (CK + 0xee)) Rra
                (mword_of_int 2090946 : mword 21) Z1 (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0ee").
      iIntros (CIDF2 HqF2) "Hcg Hpc".
      iEval (rewrite Htgu) in "Hpc".
      set (Z2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CK + 0xee) : mword 64) 4)]> Z1).
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
      iAssert (ic_loaded γfs γi cov logstart kd dind dn bm)
        with "[Hdlnk Hdiat Hmeta Haddrs Hind Hblocks]" as "Hload".
      { rewrite /ic_loaded. iExists data.
        iSplitR; [iPureIntro; exact Hiok |].
        iSplitR; [iPureIntro; rewrite -Hnib; exact Hdok |].
        iFrame. }
      iDestruct (cpu_own_transport CIDo CIDF2 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (log_opS_named with "Hop") as (e0) "Hop".
      iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
      iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
                gtl γil γisl cov logstart bmapstart inodestart nib size dev
                used1 kd (qd/2)%Qp (qd/2)%Qp gd dind dn bm (S q1) Sb1
                false false false e0 pidv (DfracOwn (1/4)) dqb dqs
                Z2 (K - 10)%nat eb C b
                ltac:(exact HKiup) Hkdlt ltac:(discriminate) ltac:(discriminate)
                Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
                ltac:(exact Hn1ip) Hj Hgs HZ2a0
                with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                      Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                      Hivalid Hload Hshotl Hkeep2 Hsbb Hsbi Hbmr Hppid
                      Hprocs Hdevi Hgeom Hdlk Hbsl [] Hop").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { iEval (cbn beta iota). iEmpIntro. }
      iIntros (CIDU HqU mu n2 used2 Sb2 wf)
        "%Hcsu Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd2 Hbmr Hbsl
         %Hsb2 %Hwf %Hwfc %Hn2 Hop Hisl".
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
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0f2").
      iIntros (CIDF3 HqF3) "Hcg Hpc". iEval (rgne) in "Hcg".
      assert (Hz2v : add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3)
                     = (mword_of_int 0 : mword 64)).
      { destruct Hmuregs as (_ & _ & _ & _ & Hd19 & _). rewrite Hd19.
        apply add_vec_zero_l. }
      set (Z3 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mu !!! Regidx Rs3))]> mu).
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
                with "Hcg Hpc Hi0f4 Hb5").
      iIntros (CIDF4 HqF4) "Hcg Hpc Hb5".
      iEval (rewrite HT5) in "Hb5".
      set (Z4 := <[Regidx Rs3 := regval_into_reg
                    (m !!! Regidx Rs3 : mword 64)]> Z3).
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
                with "Hcg Hpc Hi0f6").
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
      iDestruct (cpu_own_transport CIDU CIDf 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (iref_slots_combine with "Hislg Hisl") as "Hisl".
      iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
                (mword_of_int 0 : mword 32) dn bm n2 Sb2
                (1 + (1 + (ns - 2)))%nat used2
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath
                      Hbsl [%] Hisl [%] Hop [%]").
      { exact Hcsf. }
      { exact (cr_slots_2 ns Hns). }
      { exact (conj (cr_sub2 _ _ _ Hsb1 Hsb2)
                 (cr_le2 _ _ _ (proj2 Hn2) (proj2 Hnp1))). }
      { rewrite Ha0f. exact HZ4s2. }
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
  (*      [ilink] the +0xc4 mint made is what pays for the decrement --   *)
  (*      it is consumed here, which is why the parent's re-park below    *)
  (*      may not want a ticket.                                          *)
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
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32) (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8) (pv : mword 64)
      (ty major minor : mword 16) (V : pprivate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (sp0 ret_tgt : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (b : bool)
      (kd : nat) (qd : Qp) (gd γil γisl : gname) (dind : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (nf nsl : nat -> bv 8) :
    (K_create <= K)%nat ->
    γ = icfg_log ->
    inodestart = icfg_ist ->
    nib = icfg_nib ->
    16 * Z.of_nat nib <= 2 ^ 16 ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    InodeInv.ireg_blocks_ok inodestart nib cov logstart ->
    (create_slots <= ns)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (m !!! Regidx csp_rs1 : mword 64) = sp0 ->
    ret_pc (m !!! Regidx Rra : mword 64) = ret_tgt ->
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    eb = true ->
    kernel_text -∗ panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wp_next (CID0 := CID) true (proc_addr j) (fun CIDf : CpuId =>
      cr_fail_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γa γf γpr
                   cov logstart bmapstart inodestart nib ninodes size dev
                   used plen pfun pv ty major minor V u Sb ns pidv
                   dqb dqs dqbs dqn m sp0 ret_tgt K eb C b
                   kd qd gd γil γisl dind dn bm data nf nsl CIDf).
  Proof.
    intros HK Hglog Hist Hnib Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcovb
           Hiregb Hns Hj Hgs Hspm Hrt Hal10 Hal9 Heb.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iIntros "#Htext #Hpanic #Hbio #Hlogc #Hitb2 #Hitbl #Hesc #Hiregi
             #Hprocs #Hdevi #Hgeom #Hdlk".
    iDestruct (cr_tail_half j m sp0 ret_tgt K b HKsum Hal10 Hal9 Hspm Hrt
                 with "Htext") as "#Htail".
    iIntros (CIDf Hsf).
    iIntros (Mx kslot q g gil gisl cinum dnc bmc datc bm' data' dn' dn0'
             tot n4 Sb4 used4).
    iIntros "%HXregs %Htdir %Hkdlt %Hdib %Htydir %Hnl0 %Hiok %Hdok %Hkslt
             %Hcpos %Hcinb %Hfresh %Htyc %Hciok %Hcdok %Htot0 %Hwf' %Hholes'
             %Haddr' %Hsz31' %Hcov' %Hszcap' %Hsized' %Hdn' %Hdn0' %Hrng
             %Hsb4 %Hmem4 %Hn4 %Hledge".
    iIntros "Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hnb14 Hnb2
             #Hslkd Hslkdd Hslpid Hdep Hidev Hiinum Hivalid Hdlnk Hdiat
             Hmeta Hmap Hblocks #Hshotl Hkeep
             #Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum Hcivalid Hcdlnk
             Hcdiat Hcmeta Hcmap Hcblocks #Hcshot Hckeep Hilink
             Hsbn Hsbi Hsbs Hsbb Hbmr Hppid Hppback Hpath Hbsl Hislr Hop
             Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
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
      by exact (blkmap_wf_dir_len cov logstart bmc (proj1 Hciok)).
    assert (Hcdok' : dir_ok icfg_nib dnc datc) by (rewrite -Hnib; exact Hcdok).
    iPoseProof (cri_146 with "Htext") as "Hi146".
    iPoseProof (cri_14a with "Htext") as "Hi14a".
    iPoseProof (cri_14c with "Htext") as "Hi14c".
    iPoseProof (cri_150 with "Htext") as "Hi150".
    iPoseProof (cri_152 with "Htext") as "Hi152".
    iPoseProof (cri_156 with "Htext") as "Hi156".
    iPoseProof (cri_158 with "Htext") as "Hi158".
    iPoseProof (cri_15c with "Htext") as "Hi15c".
    iPoseProof (cri_15e with "Htext") as "Hi15e".
    (* ===== +0x146 sh zero,74(s3) : ip->nlink = 0 ===================== *)
    iEval (rewrite /inode_meta cr_setf_type cr_setf_major cr_setf_minor
                   cr_setf_nlink cr_setf_size) in "Hcmeta".
    iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
    iEval (rewrite /i_nlink) in "Hcinl".
    iDestruct (sie_cap_gpr_x0 Mx (K - 10)%nat b (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iApply (wp_sh_s_sconf (mword_of_int (CK + 0x146)) Rz Rs3
              (mword_of_int 74 : mword 12) Mx (K - 10)%nat
              (mword_of_int 1 : mword 16) b
              with "Hcg Hpc Hi146 [Hcinl]").
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
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14a").
    iIntros (CIDG2 HqG2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mx !!! Regidx Rs3))]> Mx).
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
              (sign_extend' 64 (mword_of_int 2090148 : mword 21))
              = mword_of_int KernelSyms.iupdate) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x14c)) Rra
              (mword_of_int 2090148 : mword 21) G1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14c").
    iIntros (CIDG3 HqG3) "Hcg Hpc".
    iEval (rewrite Htgiu) in "Hpc".
    set (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x14c) : mword 64) 4)]> G1).
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
    iDestruct (cr_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CIDf CIDG3 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IU.wp_iupdate_unlink γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart inodestart nib dev (ientry kslot) cinum
              (cr_setf dnc major minor (mword_of_int 0 : mword 16))
              (cr_setf dnc major minor (mword_of_int 1 : mword 16)) bmc
              u0 Sb4 true pidv
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G2 (K - 10)%nat eb C b
              ltac:(exact HKiu) ltac:(intros _; exact Hmem4)
              Hlg Hist0 Hcblk Hcblog Hcinb Hstab
              ltac:(exact (cr_setf_type_nz dnc major minor _ Htyz))
              Hdec Hcadd0 Hcdirlen Hj Hgs HG2a0 Heb
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlogc Hcidev Hciinum
                    Hcmeta Hcmap Hsbi Hiregi Hcdiat Hilink [] Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbs2 Hop").
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
    iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    (* ===== +0x150 c.mv a0,s3 ========================================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x150)) Ra0 Rs3 mfl
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi150").
    iIntros (CIDG5 HqG5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mfl !!! Regidx Rs3))]> mfl).
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
              (sign_extend' 64 (mword_of_int 2090846 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x152)) Rra
              (mword_of_int 2090846 : mword 21) G3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi152").
    iIntros (CIDG6 HqG6) "Hcg Hpc".
    iEval (rewrite Htgu1) in "Hpc".
    set (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)]> G3).
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x152) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a0 : G4 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G4)
      by (rewrite /G4; apply cr_regs3_caller; [exact Hcsra | exact HG3regs]).
    (* the child's payload, at the ZEROED record: its own [dir_links] is
       [emp] (it is not a directory -- this is the non-T_DIR arm), and the
       flush handed the region's fragment back retagged. *)
    iAssert (ic_loaded γfs γi cov logstart kslot cinum
               (cr_setf dnc major minor (mword_of_int 0 : mword 16)) bmc)
      with "[Hcdlnk Hcdiat Hcmeta Hcmap Hcblocks]" as "Hcload".
    { rewrite /ic_loaded. iExists datc.
      iSplitR; [iPureIntro;
                exact (cr_setf_inode_ok cov logstart dnc bmc datc major minor
                         _ Hciok) |].
      iSplitR; [iPureIntro;
                exact (cr_setf_dir_ok icfg_nib dnc datc major minor
                         _ Hcdok') |].
      iSplitR.
      { rewrite /dir_links.
        destruct (decide (bv_unsigned (di_type (cr_setf dnc major minor
                    (mword_of_int 0 : mword 16))) = T_DIR_z)) as [Hchd | Hchd].
        - exfalso. apply Htdirz.
          rewrite -(cr_setf_type dnc major minor
                      (mword_of_int 0 : mword 16)).
          exact Hchd.
        - done. }
      iFrame "Hcdiat Hcmeta".
      iEval (rewrite /inode_map) in "Hcmap".
      iDestruct "Hcmap" as "[Hca Hci]". iFrame. }
    iAssert (ity_shot g (di_type (cr_setf dnc major minor
                                    (mword_of_int 0 : mword 16))))
      as "#Hcshot'". { rewrite cr_setf_type. iExact "Hcshot". }
    iPoseProof (cr_esc_acc cn γfs γi cov logstart kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (inode_ref_short_gen_forget with "Hckeep") as "Hckp".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iDestruct (cpu_own_transport CIDG4 CIDG6 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
              gtl gil gisl cov logstart bmapstart inodestart nib size dev
              used4 kslot (q/2)%Qp (q/2)%Qp g cinum
              (cr_setf dnc major minor (mword_of_int 0 : mword 16)) bmc
              (S u0) (Sb4 ∪ {[IBLOCK cinum inodestart]})
              (bool_decide (bmapstart ∈ (Sb4 ∪ {[IBLOCK cinum inodestart]})))
              true false e0 pidv (DfracOwn (1/4)) dqb dqs
              G4 (K - 10)%nat eb C b
              ltac:(exact HKiup) Hkslt
              ltac:(exact (cr_crb_honest (Sb4 ∪ {[IBLOCK cinum inodestart]})
                             bmapstart))
              ltac:(intros _; exact (cr_in_union_sing Sb4
                                       (IBLOCK cinum inodestart)))
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hcblk Hcblog Hcinb Hcovb
              ltac:(exact (proj1 Hn4)) Hj Hgs HG4a0
              with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                    Hescc Hiregi Hslkc Hcslkd Hcslpid Hcdep Hcidev Hciinum
                    Hcivalid Hcload Hcshot' Hckp Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDG7 HqG7 mu1 n5 used5 Sb5 w1)
      "%Hcsu1 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd5 Hbmr Hbsl
       %Hsb5 %Hw5 %Hw5c %Hn5 Hop Hisl1".
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
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi156").
    iIntros (CIDG8 HqG8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mu1 !!! Regidx Rs1))]> mu1).
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
              (sign_extend' 64 (mword_of_int 2090840 : mword 21))
              = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0x158)) Rra
              (mword_of_int 2090840 : mword 21) G5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi158").
    iIntros (CIDG9 HqG9) "Hcg Hpc".
    iEval (rewrite Htgu2) in "Hpc".
    set (G6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)]> G5).
    assert (HG6ra : G6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0x158) : mword 64) 4)
      by (rewrite /G6; apply upd_eq).
    assert (HG6a0 : G6 !!! Regidx Ra0 = ientry kd)
      by (rewrite /G6 upd_ne; [exact HG5a0 | nz]).
    assert (HG6regs : cr_regs3 m sp0 (ientry kd) (mword_of_int 0 : mword 64)
                        (ientry kslot) ty major minor G6)
      by (rewrite /G6; apply cr_regs3_caller; [exact Hcsra | exact HG5regs]).
    (* THE PARENT'S RE-PARK.  [tot = 0]: no byte and no record moved, so
       the whole big-op rides ([DirLinks.dir_links_dirlink_nop]) and no
       ticket is wanted -- which is the only reason this arm exists, since
       the one [ilink] it had was spent by the flush at +0x14c. *)
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
    iDestruct (dir_links_dirlink_nop (bv_unsigned dind) dn dn' data data'
                 (cr_low16 cinum) (bname 14 nf)
                 (dir_nrec (bv_unsigned (di_size dn)))
                 (dir_slot data (dir_nrec (bv_unsigned (di_size dn))))
                 eq_refl eq_refl Hty' Hnl' Hszmax Hrng with "Hdlnk")
      as "Hdlnk".
    assert (Hiok' : inode_ok cov logstart dn' bm' data').
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
    iAssert (ic_loaded γfs γi cov logstart kd dind dn' bm')
      with "[Hdlnk Hdiat Hmeta Hmap Hblocks]" as "Hload".
    { rewrite /ic_loaded. iExists data'.
      iSplitR; [iPureIntro; exact Hiok' |].
      iSplitR; [iPureIntro; exact Hdok' |].
      iSplitL "Hdlnk"; [iExact "Hdlnk" |].
      iFrame "Hdiat Hmeta".
      iEval (rewrite /inode_map) in "Hmap".
      iDestruct "Hmap" as "[Haddrs Hind]". iFrame. }
    iAssert (ity_shot gd (di_type dn')) as "#Hshotl'".
    { rewrite Hty'. iExact "Hshotl". }
    iPoseProof (cr_esc_acc cn γfs γi cov logstart kd Hkdlt with "Hesc")
      as "#Hescd".
    iDestruct (inode_ref_short_gen_forget with "Hkeep") as "Hkeep2".
    iDestruct (log_opS_named with "Hop") as (e1) "Hop".
    iDestruct (cpu_own_transport CIDG7 CIDG9 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (IUP.wp_iunlockput_gen γs j γl γu γd γk pd pav pu bn γ γfs γi cn
              gtl γil γisl cov logstart bmapstart inodestart nib size dev
              used5 kd (qd/2)%Qp (qd/2)%Qp gd dind dn' bm'
              n5 Sb5 false false false e1 pidv (DfracOwn (1/4)) dqb dqs
              G6 (K - 10)%nat eb C b
              ltac:(exact HKiup) Hkdlt ltac:(discriminate) ltac:(discriminate)
              Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0 Hdblk Hdblog Hdib Hcovb
              ltac:(exact Hipn5) Hj Hgs HG6a0
              with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hlogc Hitb2 Hitbl
                    Hescd Hiregi Hslkd Hslkdd Hslpid Hdep Hidev Hiinum
                    Hivalid Hload Hshotl' Hkeep2 Hsbb Hsbi Hbmr Hppid Hprocs
                    Hdevi Hgeom Hdlk Hbsl [] Hop").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (CIDGA HqGA mu2 n6 used6 Sb6 w2)
      "%Hcsu2 Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi %Husd6 Hbmr Hbsl
       %Hsb6 %Hw6 %Hw6c %Hn6 Hop Hisl2".
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
              with "Hcg Hpc Hi15c Hb5").
    iIntros (CIDGB HqGB) "Hcg Hpc Hb5".
    iEval (rewrite HT5) in "Hb5".
    set (G7 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> mu2).
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
              with "Hcg Hpc Hi15e").
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
    iDestruct (cpu_own_transport CIDGA CIDfin 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (iref_slots_combine with "Hisl1 Hisl2") as "Hisl".
    iDestruct (iref_slots_combine with "Hisl Hislr") as "Hisl".
    iSpecialize ("Hcont" $! CIDfin with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf false false 0%nat 1%Qp 1%Qp γf
              (mword_of_int 0 : mword 32) dn bm n6 Sb6
              (1 + (1 + (ns - 2)))%nat used6
              with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbs Hsbb Hbmr Hpriv Hpath
                    Hbsl [%] Hisl [%] Hop [%]").
    { exact Hcsf. }
    { exact (cr_slots_2 ns Hns). }
    { split.
      - exact (cr_sub3 _ _ _ _ Hsb4
                 (cr_sub_union_sing Sb4 (IBLOCK cinum inodestart))
                 (cr_sub2 _ _ _ Hsb5 Hsb6)).
      - pose proof (proj2 Hn6) as HB1. pose proof (proj2 Hn5) as HB2.
        pose proof (proj2 Hn4) as HB3. lia. }
    { rewrite Ha0f. exact HG7s2. }
  Qed.

End ProofCreateMain.

End CreateProof.
