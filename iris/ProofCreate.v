(* ProofCreate.v -- the walk of xv6's create (fs.c), FOUND HALF.

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
   whole ALLOCATE half (+0x8a onward, reached by the [c.beqz] at +0x3e
   being TAKEN) parked behind ONE HYPOTHESIS, [cr_alloc_body].  That
   hypothesis is a PREMISE of the lemma, not an axiom and not an [admit]:
   [Print Assumptions cr_found_half] shows the standing platform six and
   nothing else, and the parked half appears in the STATEMENT.

   The cut is at +0x3e rather than at the failure family because the
   family's ARM FAIL is reached only through ialloc / ilock(ip) / three
   [sh]s / iupdate / dirlink -- i.e. through more code than everything
   before it.  The found half is the increment that stands alone.

   ---- THE PIECES ------------------------------------------------------

   [cr_tail_body]  -- the epilogue funnel at +0x62 ([mv a0,s2], the seven
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
Require Import SpecPrintkGen.
Require Import SpecBmap SpecWritei.
Require Import SpecIput SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNamex SpecNameiparent.
Require Import SpecCreate.
(* the ONE assumed contract: the four-instruction span +0x8c..+0x98 that
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

(* what the epilogue funnel at +0x62 needs, and what all four arms have *)
Definition cr_tregs (m : regfile) (sp0 : mword 64) (Mt : regfile) : Prop :=
  Mt !!! Regidx csp_rs1 = pa_stk sp0 10 /\ cr_thr m Mt.

(* the walk's bundle: [dpv] is s1 and [ansv] is s2, both as parameters
   because both are written mid-walk ([mv s1,a0] at +0x20, [mv s2,a0] at
   +0x3c, [li s2,0] at +0x7c / +0x86 / the [mv s2,a0] at +0x148). *)
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

(* the three writes of s2: [mv s2,a0] at +0x3c and +0x148, [li s2,0] at
   +0x7c / +0x86 *)
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

   The [c.mv s3,a0] at +0x94 (inside the gate span) writes the EIGHTH
   callee-saved register, so [cr_thr]'s claim "s3 still holds the caller's
   value" is false from +0x94 until the [c.ldsp s3,40(sp)] at +0xd0 /
   +0xdc puts it back.  [cr_thr3] is [cr_thr] with s3 removed from the
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

(* the [c.mv s2,s3] at +0xce (ARM C-OK) and +0xda (ARM A-FAIL) *)
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

(* the [c.ldsp s3,40(sp)] at +0xd0 / +0xdc *)
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
(*  Three things the walk from +0x8a to +0xd2 needs and nothing else in   *)
(*  the tree has: the HALFWORD BRIDGE at +0xb6, the record identity the   *)
(*  three [sh]s produce, and the arm's ledger readings.                    *)
(* ===================================================================== *)

(* ---- (i) THE HALFWORD BRIDGE.  The [lw a2,4(s3)] at +0xb6 loads the
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

(* the [c.li a4,1] at +0xa4 stores a SIXTEEN-bit one through the [sh] at
   +0xa6: [trunc16] of the 64-bit literal. *)
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
   is the theorem; these are it at the two figures the CONTRACTS state,
   exactly as [cr_n1_lo] / [cr_after_ip] are for the found half.  The
   walk reaches its [dirlink] with [q1 >= 8] ([cr_uw w - ia_spend -
   iu_spend true] is 8 or 7... at [w = false] it is nine minus one), and
   [dl_need] is at most six, [wi16_spend] at most five. *)
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

Lemma cr_alloc_ip0 (nc n' : nat) :
  (8 <= nc)%nat -> ((nc - SpecDirlink.dl0_spend)%nat <= n')%nat ->
  (iput_units <= n')%nat.
Proof.
  intros Hnc Hn'. unfold SpecDirlink.dl0_spend, iput_units in *. lia.
Qed.

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

  (* THE EPILOGUE FUNNEL at +0x62: [mv a0,s2], the seven [c.ldsp]s, the
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
       pc_is (mword_of_int (CK + 0x62)) -∗
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
  (*  -- which reaches +0x62 through TWO more arms -- could not see it.    *)
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
    iPoseProof (cri_062 with "Htext") as "Hj62".
    iPoseProof (cri_064 with "Htext") as "Hj64".
    iPoseProof (cri_066 with "Htext") as "Hj66".
    iPoseProof (cri_068 with "Htext") as "Hj68".
    iPoseProof (cri_06a with "Htext") as "Hj6a".
    iPoseProof (cri_06c with "Htext") as "Hj6c".
    iPoseProof (cri_06e with "Htext") as "Hj6e".
    iPoseProof (cri_070 with "Htext") as "Hj70".
    iPoseProof (cri_072 with "Htext") as "Hj72".
    iPoseProof (cri_074 with "Htext") as "Hj74".
    (* +0x62 c.mv a0,s2 : the answer register *)
    iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x62)) Ra0 Rs2 Mt
              (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj62").
    iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (Mt !!! Regidx Rs2))]> Mt).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P0 upd_ne; [exact HTsp | nz]).
    assert (Hq064 : add_vec_int (mword_of_int (CK + 0x62) : mword 64) 2
                    = mword_of_int (CK + 0x64)) by pcw.
    iEval (rewrite Hq064) in "Hpc".
    (* +0x64 .. +0x70 : the seven restores *)
    assert (HT1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HP0sp; apply cr_frm1).
    iEval (rewrite -HT1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x64)) (mword_of_int 9 : mword 6)
              Rra P0 (K - 10)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj64 Hb1").
    iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P1 upd_ne; [exact HP0sp | nz]).
    assert (Hq066 : add_vec_int (mword_of_int (CK + 0x64) : mword 64) 2
                    = mword_of_int (CK + 0x66)) by pcw.
    iEval (rewrite Hq066) in "Hpc".
    assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HP1sp; apply cr_frm2).
    iEval (rewrite -HT2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x66)) (mword_of_int 8 : mword 6)
              Rs0 P1 (K - 10)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj66 Hb2").
    iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hq068 : add_vec_int (mword_of_int (CK + 0x66) : mword 64) 2
                    = mword_of_int (CK + 0x68)) by pcw.
    iEval (rewrite Hq068) in "Hpc".
    assert (HT3 : add_vec (P2 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HP2sp; apply cr_frm3).
    iEval (rewrite -HT3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x68)) (mword_of_int 7 : mword 6)
              Rs1 P2 (K - 10)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj68 Hb3").
    iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hq06a : add_vec_int (mword_of_int (CK + 0x68) : mword 64) 2
                    = mword_of_int (CK + 0x6a)) by pcw.
    iEval (rewrite Hq06a) in "Hpc".
    assert (HT4 : add_vec (P3 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HP3sp; apply cr_frm4).
    iEval (rewrite -HT4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x6a)) (mword_of_int 6 : mword 6)
              Rs2 P3 (K - 10)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6a Hb4").
    iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hq06c : add_vec_int (mword_of_int (CK + 0x6a) : mword 64) 2
                    = mword_of_int (CK + 0x6c)) by pcw.
    iEval (rewrite Hq06c) in "Hpc".
    assert (HT6 : add_vec (P4 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HP4sp; apply cr_frm6).
    iEval (rewrite -HT6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x6c)) (mword_of_int 4 : mword 6)
              Rs4 P4 (K - 10)%nat (m !!! Regidx Rs4 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6c Hb6").
    iIntros (CIDT5 HqT5) "Hcg Hpc Hb6".
    set (P5 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P4).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hq06e : add_vec_int (mword_of_int (CK + 0x6c) : mword 64) 2
                    = mword_of_int (CK + 0x6e)) by pcw.
    iEval (rewrite Hq06e) in "Hpc".
    assert (HT7 : add_vec (P5 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HP5sp; apply cr_frm7).
    iEval (rewrite -HT7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x6e)) (mword_of_int 3 : mword 6)
              Rs5 P5 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6e Hb7").
    iIntros (CIDT6 HqT6) "Hcg Hpc Hb7".
    set (P6 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P5).
    assert (HP6sp : P6 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hq070 : add_vec_int (mword_of_int (CK + 0x6e) : mword 64) 2
                    = mword_of_int (CK + 0x70)) by pcw.
    iEval (rewrite Hq070) in "Hpc".
    assert (HT8 : add_vec (P6 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HP6sp; apply cr_frm8).
    iEval (rewrite -HT8) in "Hb8".
    iApply (wp_cldsp_s_sconf (mword_of_int (CK + 0x70)) (mword_of_int 2 : mword 6)
              Rs6 P6 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj70 Hb8").
    iIntros (CIDT7 HqT7) "Hcg Hpc Hb8".
    set (P7 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P6).
    assert (HP7sp : P7 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hq072 : add_vec_int (mword_of_int (CK + 0x70) : mword 64) 2
                    = mword_of_int (CK + 0x72)) by pcw.
    iEval (rewrite Hq072) in "Hpc".
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
    (* ===== +0x72 c.addi16sp sp,80 : the pop ===== *)
    assert (Hwv : add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                  = sp0) by (rewrite HP7sp; apply cr_pop).
    assert (Hpop : (P7 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
      by (rewrite Hwv; exact HP7sp).
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CK + 0x72))
              (mword_of_int 5 : mword 6) P7 (K - 10)%nat 10 b Hpop
              with "Hcg Hpc Hj72 Hstk").
    iIntros (CIDT8 HqT8) "Hcg Hpc".
    set (P8 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P7).
    iEval (rewrite HKsum) in "Hcg".
    assert (Hq074 : add_vec_int (mword_of_int (CK + 0x72) : mword 64) 2
                    = mword_of_int (CK + 0x74)) by pcw.
    iEval (rewrite Hq074) in "Hpc".
    (* ===== +0x74 c.ret ===== *)
    assert (CPra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (CK + 0x74)) Rra P8 K b
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
  (*  THE PARKED GATE: the whole ALLOCATE half, +0x8a onward               *)
  (*                                                                       *)
  (*  Reached ONLY by the [c.beqz a0] at +0x3e being TAKEN, i.e. by        *)
  (*  dirlookup missing.  At that point s2 = a0 = 0 (the [mv s2,a0] at     *)
  (*  +0x3c stored dirlookup's zero), the parent is LOCKED and LOADED, and *)
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
       pc_is (mword_of_int (CK + 0x8a)) -∗
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
  (*  [cr_mkdir_body] is the [beq s4,a4] at +0xb2 TAKEN, i.e. the whole    *)
  (*  T_DIR sub-branch (+0xe0..+0x12c: the two interior [dirlink]s on the  *)
  (*  child, the parent's [dirlink], its [nlink++] and its [iupdate]).     *)
  (*  D0-b consumes it.  Note what it is handed and what it is NOT: the    *)
  (*  child's [ilink] ticket is UNDEPOSITED -- +0xac minted it and the     *)
  (*  non-directory arm spends it at +0xc0, so on this branch it is still  *)
  (*  in hand and the mkdir arm's own [dirlink(dp,name)] at +0x114 is      *)
  (*  what spends it.                                                     *)
  (*                                                                       *)
  (*  [cr_fail_body] is +0x12e, reached HERE only from the [bltz] at       *)
  (*  +0xc4 (the other three entries are behind the T_DIR branch and       *)
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
       (* THE BRANCH ITSELF: +0xb2 is taken exactly on [ty = T_DIR] *)
       ⌜ty = SpecDirlookup.T_DIR⌝ -∗
       (* the parent, as the found half left it *)
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dind < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dn = SpecDirlookup.T_DIR⌝ -∗
       ⌜di_nlink dn <> (mword_of_int 0 : mword 16)⌝ -∗
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
       pc_is (mword_of_int (CK + 0xe0)) -∗
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
       (* WHAT THE FAILING [dirlink(dp,name)] AT +0xc0 LEFT, verbatim from
          [SpecDirlink]'s append arm.  [tot < 16] is the [bltz] at +0xc4
          having fired; the RE-PARK of [dir_links] is deliberately NOT done
          here (see the header). *)
       ⌜(tot < 16)%nat⌝ -∗
       ⌜used ⊆ used4⌝ -∗
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
       ⌜used4 ⊆ used⌝ -∗
       (* the machine *)
       sie_cap_gpr Mx (K - 10)%nat b (proc_addr j) -∗
       cpu_own 0 eb (proc_addr j) C b -∗
       pc_is (mword_of_int (CK + 0x12e)) -∗
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
    assert (Htg148 : add_vec (mword_of_int (CK + 0x22) : mword 64)
              (sign_extend' 64 (mword_of_int 294 : mword 13))
              = mword_of_int (CK + 0x148)) by pcw.
    (* ================================================================== *)
    (*  THE EPILOGUE FUNNEL at +0x62 -- SIX arms reach it, so the          *)
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
                (mword_of_int 294 : mword 13) Ra0 Q1 (K - 10)%nat b
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
      assert (Htg076 : add_vec (mword_of_int (CK + 0x2e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 36 : mword 8) ('b"0"))))
                = mword_of_int (CK + 0x76)) by pcw.
      (* the ledger, as [CreateBudget.cr_budget_found_w]'s first row *)
      assert (Hn1lo : (9 <= n1)%nat) by exact (cr_n1_lo u n1 w Hu (proj1 Hnp1)).
      assert (Hn1ip : (iput_units <= n1)%nat) by exact (cr_ip_of9 n1 Hn1lo).
      destruct (decide (di_nlink dnl = (mword_of_int 0 : mword 16))) as [Hnl0 | Hnl0].
      + (* ========== ARM G: the guard FIRES -- nlink == 0 ============= *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x2e))
                  (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_eq _ Hnl0))
                  ltac:(rewrite Htg076; vm_compute; reflexivity)
                  with "Hcg Hpc Hi02e").
        iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg076) in "Hpc".
        iPoseProof (cri_076 with "Htext") as "Hi076".
        iPoseProof (cri_078 with "Htext") as "Hi078".
        iPoseProof (cri_07c with "Htext") as "Hi07c".
        iPoseProof (cri_07e with "Htext") as "Hi07e".
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
        (* +0x76 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x76)) Ra0 Rs1 Q3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi076").
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Q3 !!! Regidx Rs1))]> Q3).
        assert (HG1a0 : G1 !!! Regidx Ra0 = ientry kd).
        { rewrite /G1 upd_eq. rewrite /Q3 upd_ne; [| nz].
          rewrite Y9 Hie. apply add_vec_zero_l. }
        assert (HG1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor G1)
          by (rewrite /G1; apply cr_regs_caller; [exact Hcsa0 | exact HQ3regs]).
        assert (Hp078 : add_vec_int (mword_of_int (CK + 0x76) : mword 64) 2
                        = mword_of_int (CK + 0x78)) by pcw.
        iEval (rewrite Hp078) in "Hpc".
        (* +0x78 jal iunlockput (dp) -- AT crb = cru = crz = false.
           [crz] is unavailable BY CONSTRUCTION on this arm: it is bought
           with [InodeRegion.nlz_obs], minted only at a NONZERO nlink
           observation, and this arm IS the zero observation. *)
        assert (Htgup : add_vec (mword_of_int (CK + 0x78) : mword 64)
                  (sign_extend' 64 (mword_of_int 2091064 : mword 21))
                  = mword_of_int KernelSyms.iunlockput) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x78)) Rra
                  (mword_of_int 2091064 : mword 21) G1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi078").
        iIntros (CID21 Hq21) "Hcg Hpc".
        iEval (rewrite Htgup) in "Hpc".
        set (G2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x78) : mword 64) 4)]> G1).
        assert (HG2ra : G2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x78) : mword 64) 4)
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
                        = mword_of_int (CK + 0x7c)) by (rewrite HG2ra; pcw).
        iEval (rewrite Hpcup) in "Hpc".
        assert (Hmupregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mup)
          by exact (cr_regs_cs m sp0 _ _ ty major minor G2 mup Hcsup HG2regs).
        iDestruct ("Hppback" with "Hppid") as "Hpriv".
        (* +0x7c c.li s2,0 *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x7c)) Rs2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mup (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi07c").
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
        assert (Hp07e : add_vec_int (mword_of_int (CK + 0x7c) : mword 64) 2
                        = mword_of_int (CK + 0x7e)) by pcw.
        iEval (rewrite Hp07e) in "Hpc".
        (* +0x7e c.j +0x62 *)
        assert (Htg062g : add_vec (mword_of_int (CK + 0x7e) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                  = mword_of_int (CK + 0x62)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (CK + 0x7e))
                  (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                  G3 (K - 10)%nat b
                  ltac:(rewrite Htg062g; vm_compute; reflexivity)
                  with "Hcg Hpc Hi07e").
        iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htg062g) in "Hpc".
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
                  (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Q3 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ3a5; exact (nx_nlz_ne _ Hnl0))
                  with "Hcg Hpc Hi02e").
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hp030 : add_vec_int (mword_of_int (CK + 0x2e) : mword 64) 2
                        = mword_of_int (CK + 0x30)) by pcw.
        iEval (rewrite Hp030) in "Hpc".
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
        iPoseProof (cri_030 with "Htext") as "Hi030".
        iPoseProof (cri_032 with "Htext") as "Hi032".
        iPoseProof (cri_036 with "Htext") as "Hi036".
        iPoseProof (cri_038 with "Htext") as "Hi038".
        iPoseProof (cri_03c with "Htext") as "Hi03c".
        iPoseProof (cri_03e with "Htext") as "Hi03e".
        (* ===== +0x30 c.li a2,0 : dirlookup's [poff] is NOT wanted ===== *)
        iApply (wp_cli_s_sconf (mword_of_int (CK + 0x30)) Ra2
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  Q3 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi030").
        iIntros (CID20 Hq20) "Hcg Hpc".
        set (D1 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> Q3).
        assert (HD1a2 : D1 !!! Regidx Ra2 = (mword_of_int 0 : mword 64))
          by (rewrite /D1; apply upd_eq).
        assert (HD1s0 : D1 !!! Regidx Rs0 = sp0).
        { rewrite /D1 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact Y8 | nz]. }
        assert (HD1s1 : D1 !!! Regidx Rs1 = ipv).
        { rewrite /D1 upd_ne; [| nz]. rewrite /Q3 upd_ne; [exact Y9 | nz]. }
        assert (HD1regs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                            ty major minor D1)
          by (rewrite /D1; apply cr_regs_caller; [exact Hcsa2 | exact HQ3regs]).
        assert (Hp032 : add_vec_int (mword_of_int (CK + 0x30) : mword 64) 2
                        = mword_of_int (CK + 0x32)) by pcw.
        iEval (rewrite Hp032) in "Hpc".
        (* ===== +0x32 addi a1,s0,-80 : a1 = &name ====================== *)
        iApply (wp_addi4_s_sconf (mword_of_int (CK + 0x32)) Ra1 Rs0
                  (mword_of_int 4016 : mword 12) D1 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi032").
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
        assert (Hp036 : add_vec_int (mword_of_int (CK + 0x32) : mword 64) 4
                        = mword_of_int (CK + 0x36)) by pcw.
        iEval (rewrite Hp036) in "Hpc".
        (* ===== +0x36 c.mv a0,s1 ======================================= *)
        iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x36)) Ra0 Rs1 D2
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi036").
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
        assert (Hp038 : add_vec_int (mword_of_int (CK + 0x36) : mword 64) 2
                        = mword_of_int (CK + 0x38)) by pcw.
        iEval (rewrite Hp038) in "Hpc".
        (* ===== +0x38 jal dirlookup(dp, name, 0) ======================= *)
        assert (Htgdl : add_vec (mword_of_int (CK + 0x38) : mword 64)
                  (sign_extend' 64 (mword_of_int 2092044 : mword 21))
                  = mword_of_int KernelSyms.dirlookup) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (CK + 0x38)) Rra
                  (mword_of_int 2092044 : mword 21) D3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi038").
        iIntros (CID23 Hq23) "Hcg Hpc".
        iEval (rewrite Htgdl) in "Hpc".
        set (D4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CK + 0x38) : mword 64) 4)]> D3).
        assert (HD4ra : D4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CK + 0x38) : mword 64) 4)
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
                        = mword_of_int (CK + 0x3c)) by (rewrite HD4ra; pcw).
        iEval (rewrite Hpcdl) in "Hpc".
        assert (Hmdlregs : cr_regs m sp0 ipv (m !!! Regidx Rs2 : mword 64)
                             ty major minor mdl)
          by exact (cr_regs_cs m sp0 _ _ ty major minor D4 mdl Hcsdl HD4regs).
        assert (Htg08a : add_vec (mword_of_int (CK + 0x3e) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 38 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0x8a)) by pcw.
        assert (Hp03e : add_vec_int (mword_of_int (CK + 0x3c) : mword 64) 2
                        = mword_of_int (CK + 0x3e)) by pcw.
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
          iPoseProof (cri_040 with "Htext") as "Hi040".
          iPoseProof (cri_042 with "Htext") as "Hi042".
          iPoseProof (cri_046 with "Htext") as "Hi046".
          iPoseProof (cri_048 with "Htext") as "Hi048".
          iPoseProof (cri_04c with "Htext") as "Hi04c".
          iPoseProof (cri_04e with "Htext") as "Hi04e".
          (* ===== +0x3c c.mv s2,a0 : s2 = ip ========================== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x3c)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi03c").
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
          iEval (rewrite Hp03e) in "Hpc".
          (* ===== +0x3e c.beqz a0 : FALLS THROUGH (a hit is an entry) == *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0x3e))
                    (mword_of_int 38 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    F1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HF1a0 Hdla0;
                          apply (proj2 (eq_vec_false_iff _ _));
                          exact (ientry_ne_zero kslot
                                   (Nat.lt_le_incl _ _ Hkslot)))
                    with "Hcg Hpc Hi03e").
          iIntros (CID25 Hq25) "Hcg Hpc".
          assert (Hp040 : add_vec_int (mword_of_int (CK + 0x3e) : mword 64) 2
                          = mword_of_int (CK + 0x40)) by pcw.
          iEval (rewrite Hp040) in "Hpc".
          (* ===== +0x40 c.mv a0,s1 : the PARENT, for iunlockput ======== *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x40)) Ra0 Rs1 F1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi040").
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
          assert (Hp042 : add_vec_int (mword_of_int (CK + 0x40) : mword 64) 2
                          = mword_of_int (CK + 0x42)) by pcw.
          iEval (rewrite Hp042) in "Hpc".
          (* ===== +0x42 jal iunlockput (dp), UNCREDITED ================ *)
          assert (Htgup1 : add_vec (mword_of_int (CK + 0x42) : mword 64)
                    (sign_extend' 64 (mword_of_int 2091118 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x42)) Rra
                    (mword_of_int 2091118 : mword 21) F2 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi042").
          iIntros (CID27 Hq27) "Hcg Hpc".
          iEval (rewrite Htgup1) in "Hpc".
          set (F3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x42) : mword 64) 4)]> F2).
          assert (HF3ra : F3 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x42) : mword 64) 4)
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
                          = mword_of_int (CK + 0x46)) by (rewrite HF3ra; pcw).
          iEval (rewrite Hpcu1) in "Hpc".
          assert (Hmu1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu1)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F3 mu1 Hcsu1 HF3regs).
          (* GR-2c FINDING 5: the credited bound is STRONGER than the row
             the ledger cites; weaken ONCE, keeping the name. *)
          destruct (cr_after_ip n1 n2 wf1 Hn1lo (proj1 Hn2)) as [Hn2ip Hn2lo].
          (* ===== +0x46 c.mv a0,s2 : the CHILD ========================= *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x46)) Ra0 Rs2 mu1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi046").
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
          assert (Hp048 : add_vec_int (mword_of_int (CK + 0x46) : mword 64) 2
                          = mword_of_int (CK + 0x48)) by pcw.
          iEval (rewrite Hp048) in "Hpc".
          (* ===== +0x48 jal ilock (ip) ================================= *)
          assert (Htgil2 : add_vec (mword_of_int (CK + 0x48) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090588 : mword 21))
                    = mword_of_int KernelSyms.ilock) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (CK + 0x48)) Rra
                    (mword_of_int 2090588 : mword 21) F4 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi048").
          iIntros (CID29 Hq29) "Hcg Hpc".
          iEval (rewrite Htgil2) in "Hpc".
          set (F5 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (CK + 0x48) : mword 64) 4)]> F4).
          assert (HF5ra : F5 !!! Regidx Rra
                          = add_vec_int (mword_of_int (CK + 0x48) : mword 64) 4)
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
                          = mword_of_int (CK + 0x4c)) by (rewrite HF5ra; pcw).
          iEval (rewrite Hpcic) in "Hpc".
          assert (Hmicregs : cr_regs m sp0 ipv (ientry kslot) ty major minor mic)
            by exact (cr_regs_cs m sp0 _ _ ty major minor F5 mic Hcsic HF5regs).
          pose proof Hmicregs as HmicR.
          destruct HmicR as (Z2 & Z8 & Z9 & Z18 & Z20 & Z21 & Z22 & Zthr).
          iDestruct (cr_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
            [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
          (* ============================================================ *)
          (*  ARM F-BAD (+0x80), reached from BOTH type tests -- so it is  *)
          (*  a [□]-persistent block that takes every linear resource,     *)
          (*  the contract's own continuation included, as an ARGUMENT.    *)
          (*  ONE [iunlockput], on the CHILD: the parent was released at   *)
          (*  +0x42, which is shared with F-OK.  Both are uncredited, and  *)
          (*  [CreateBudget.cr_budget_found_w]'s third conjunct is the     *)
          (*  row that closes it.                                          *)
          (* ============================================================ *)
          iAssert (□ wp_next (CID0 := CID) true (proc_addr j) (fun CIDb : CpuId =>
                     ∀ Mb : regfile,
                       ⌜cr_regs m sp0 ipv (ientry kslot) ty major minor Mb⌝ -∗
                       sie_cap_gpr Mb (K - 10)%nat b (proc_addr j) -∗
                       cpu_own 0 eb (proc_addr j) C b -∗
                       pc_is (mword_of_int (CK + 0x80)) -∗
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
            iPoseProof (cri_080 with "Htext") as "Hi080".
            iPoseProof (cri_082 with "Htext") as "Hi082".
            iPoseProof (cri_086 with "Htext") as "Hi086".
            iPoseProof (cri_088 with "Htext") as "Hi088".
            pose proof HBr as HBr2.
            destruct HBr2 as (X2 & X8 & X9 & X18 & X20 & X21 & X22 & Xthr).
            (* +0x80 c.mv a0,s2 : the CHILD *)
            iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x80)) Ra0 Rs2 Mb
                      (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi080").
            iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
            set (B1 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (zero_reg : mword 64)
                             (Mb !!! Regidx Rs2))]> Mb).
            assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kslot).
            { rewrite /B1 upd_eq. rewrite X18. apply add_vec_zero_l. }
            assert (HB1regs : cr_regs m sp0 ipv (ientry kslot) ty major minor B1)
              by (rewrite /B1; apply cr_regs_caller; [exact Hcsa0 | exact HBr]).
            assert (Hq082 : add_vec_int (mword_of_int (CK + 0x80) : mword 64) 2
                            = mword_of_int (CK + 0x82)) by pcw.
            iEval (rewrite Hq082) in "Hpc".
            (* +0x82 jal iunlockput (ip), at crb = cru = crz = false *)
            assert (Htgup2 : add_vec (mword_of_int (CK + 0x82) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091054 : mword 21))
                      = mword_of_int KernelSyms.iunlockput) by pcw.
            iApply (wp_jal_s_sconf (mword_of_int (CK + 0x82)) Rra
                      (mword_of_int 2091054 : mword 21) B1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi082").
            iIntros (CIDB2 HqB2) "Hcg Hpc".
            iEval (rewrite Htgup2) in "Hpc".
            set (B2 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (CK + 0x82) : mword 64) 4)]> B1).
            assert (HB2ra : B2 !!! Regidx Rra
                            = add_vec_int (mword_of_int (CK + 0x82) : mword 64) 4)
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
                            = mword_of_int (CK + 0x86)) by (rewrite HB2ra; pcw).
            iEval (rewrite Hpcu2) in "Hpc".
            assert (Hmu2regs : cr_regs m sp0 ipv (ientry kslot) ty major minor mu2)
              by exact (cr_regs_cs m sp0 _ _ ty major minor B2 mu2 Hcsu2 HB2regs).
            iDestruct ("Hppback" with "Hppid") as "Hpriv".
            (* +0x86 c.li s2,0 *)
            iApply (wp_cli_s_sconf (mword_of_int (CK + 0x86)) Rs2
                      (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                      mu2 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                      with "Hcg Hpc Hi086").
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
            assert (Hq088 : add_vec_int (mword_of_int (CK + 0x86) : mword 64) 2
                            = mword_of_int (CK + 0x88)) by pcw.
            iEval (rewrite Hq088) in "Hpc".
            (* +0x88 c.j +0x62 *)
            assert (Htg062b : add_vec (mword_of_int (CK + 0x88) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
                      = mword_of_int (CK + 0x62)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (CK + 0x88))
                      (sign_extend' 21
                         (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
                      B3 (K - 10)%nat b
                      ltac:(rewrite Htg062b; vm_compute; reflexivity)
                      with "Hcg Hpc Hi088").
            iIntros (CIDB4 HqB4). iApply bi.later_intro. iIntros "Hcg Hpc".
            iEval (rewrite Htg062b) in "Hpc".
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
          (* ===== +0x4c c.li a5,2 ===================================== *)
          iApply (wp_cli_s_sconf (mword_of_int (CK + 0x4c)) Ra5
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    mic (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hi04c").
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
          assert (Hp04e : add_vec_int (mword_of_int (CK + 0x4c) : mword 64) 2
                          = mword_of_int (CK + 0x4e)) by pcw.
          iEval (rewrite Hp04e) in "Hpc".
          assert (Htg080 : add_vec (mword_of_int (CK + 0x4e) : mword 64)
                    (sign_extend' 64 (mword_of_int 50 : mword 13))
                    = mword_of_int (CK + 0x80)) by pcw.
          destruct (decide (ty = T_FILE)) as [Htyf | Htyf].
          -- (* the requested type IS T_FILE: the second test decides *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (CK + 0x4e))
                       (mword_of_int 50 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_eq _ Htyf))
                       with "Hcg Hpc Hi04e").
             iIntros (CID31 Hq31) "Hcg Hpc".
             assert (Hp052 : add_vec_int (mword_of_int (CK + 0x4e) : mword 64) 4
                             = mword_of_int (CK + 0x52)) by pcw.
             iEval (rewrite Hp052) in "Hpc".
             iPoseProof (cri_052 with "Htext") as "Hi052".
             iPoseProof (cri_056 with "Htext") as "Hi056".
             iPoseProof (cri_058 with "Htext") as "Hi058".
             iPoseProof (cri_05a with "Htext") as "Hi05a".
             iPoseProof (cri_05c with "Htext") as "Hi05c".
             iPoseProof (cri_05e with "Htext") as "Hi05e".
             iDestruct "Hcload" as (datc)
               "(%Hciok & %Hcdok & Hcdlnk & Hcdiat & Hcmeta & Hcaddrs & Hcind &
                 Hcblocks)".
             iDestruct "Hcmeta" as "(Hcity & Hcimaj & Hcimin & Hcinl & Hcisz)".
             iEval (rewrite /i_type) in "Hcity".
             (* ===== +0x52 lhu a5,68(s2) : ip->type, ZERO-extended ==== *)
             iApply (wp_lhu_s_sconf (mword_of_int (CK + 0x52)) Ra5 Rs2
                       (mword_of_int 68 : mword 12) F6 (K - 10)%nat
                       (di_type dnc : mword 16) b ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi052 [Hcity]").
             { iEval (rgne; rewrite HF6s2). iExact "Hcity". }
             iIntros (CID32 Hq32) "Hcg Hpc Hcity".
             iEval (rgne; rewrite HF6s2) in "Hcity".
             set (F7 := <[Regidx Ra5 := regval_into_reg
                           (zero_extend' 64 (di_type dnc : mword 16))]> F6).
             assert (HF7regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F7)
               by (rewrite /F7; apply cr_regs_caller; [exact Hcsa5 | exact HF6regs]).
             assert (Hp056 : add_vec_int (mword_of_int (CK + 0x52) : mword 64) 4
                             = mword_of_int (CK + 0x56)) by pcw.
             iEval (rewrite Hp056) in "Hpc".
             (* ===== +0x56 c.addiw a5,-2 ============================== *)
             iApply (wp_caddiw_s_sconf (mword_of_int (CK + 0x56)) Ra5
                       (mword_of_int 62 : mword 6) F7 (K - 10)%nat b
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi056").
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
             assert (Hp058 : add_vec_int (mword_of_int (CK + 0x56) : mword 64) 2
                             = mword_of_int (CK + 0x58)) by pcw.
             iEval (rewrite Hp058) in "Hpc".
             (* ===== +0x58 c.slli a5,48 / +0x5a c.srli a5,48 ========== *)
             iApply (wp_cslli_s_sconf (mword_of_int (CK + 0x58))
                       (Regidx Ra5) Ra5 (mword_of_int 48 : mword 6)
                       F8 (K - 10)%nat b eq_refl ltac:(nz) ltac:(rdok)
                       with "Hcg Hpc Hi058").
             iIntros (CID34 Hq34) "Hcg Hpc".
             set (F9 := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget F8 Ra5)
                              (subrange_vec_dec (mword_of_int 48 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> F8).
             assert (HF9regs : cr_regs m sp0 ipv (ientry kslot) ty major minor F9)
               by (rewrite /F9; apply cr_regs_caller; [exact Hcsa5 | exact HF8regs]).
             assert (Hp05a : add_vec_int (mword_of_int (CK + 0x58) : mword 64) 2
                             = mword_of_int (CK + 0x5a)) by pcw.
             iEval (rewrite Hp05a) in "Hpc".
             iApply (wp_csrli_s_sconf (mword_of_int (CK + 0x5a))
                       (Cregidx (mword_of_int 7)) Ra5 (mword_of_int 48 : mword 6)
                       F9 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                       ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi05a").
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
             assert (Hp05c : add_vec_int (mword_of_int (CK + 0x5a) : mword 64) 2
                             = mword_of_int (CK + 0x5c)) by pcw.
             iEval (rewrite Hp05c) in "Hpc".
             (* ===== +0x5c c.li a4,1 ================================== *)
             iApply (wp_cli_s_sconf (mword_of_int (CK + 0x5c)) Ra4
                       (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                       FA (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                       with "Hcg Hpc Hi05c").
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
             assert (Hp05e : add_vec_int (mword_of_int (CK + 0x5c) : mword 64) 2
                             = mword_of_int (CK + 0x5e)) by pcw.
             iEval (rewrite Hp05e) in "Hpc".
             assert (Htg080b : add_vec (mword_of_int (CK + 0x5e) : mword 64)
                       (sign_extend' 64 (mword_of_int 34 : mword 13))
                       = mword_of_int (CK + 0x80)) by pcw.
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
                iApply (wp_bltu_taken_s_sconf (mword_of_int (CK + 0x5e))
                          (mword_of_int 34 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          ltac:(rewrite Htg080b; vm_compute; reflexivity)
                          with "Hcg Hpc Hi05e").
                iIntros (CID37 Hq37). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htg080b) in "Hpc".
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
                iApply (wp_bltu_fall_s_sconf (mword_of_int (CK + 0x5e))
                          (mword_of_int 34 : mword 13) Ra5 Ra4 FB (K - 10)%nat b
                          ltac:(nz) ltac:(nz)
                          ltac:(rgne; rgne; rewrite HFBa4 HFBa5; exact Hrng)
                          with "Hcg Hpc Hi05e").
                iIntros (CID37 Hq37) "Hcg Hpc".
                assert (Hp062 : add_vec_int (mword_of_int (CK + 0x5e) : mword 64) 4
                                = mword_of_int (CK + 0x62)) by pcw.
                iEval (rewrite Hp062) in "Hpc".
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
             iApply (wp_bne_taken_s_sconf (mword_of_int (CK + 0x4e))
                       (mword_of_int 50 : mword 13) Ra5 Rs4 F6 (K - 10)%nat b
                       ltac:(nz) ltac:(nz)
                       ltac:(rgne; rgne; rewrite HF6a5 HF6s4;
                             exact (cr_tfile_ne _ Htyf))
                       ltac:(rewrite Htg080; vm_compute; reflexivity)
                       with "Hcg Hpc Hi04e").
             iIntros (CID31 Hq31). iApply bi.later_intro. iIntros "Hcg Hpc".
             iEval (rewrite Htg080) in "Hpc".
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
          (* +0x3c c.mv s2,a0 : s2 := 0, and it STAYS 0 all the way to
             +0xce / +0xda -- the live invariant the failure arms use. *)
          iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x3c)) Rs2 Ra0 mdl
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi03c").
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
          iEval (rewrite Hp03e) in "Hpc".
          (* ===== +0x3e c.beqz a0 : TAKEN -> the allocate half ======== *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0x3e))
                    (mword_of_int 38 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                    A1 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HA1a0 Hdla0;
                          apply (proj2 (eq_vec_true_iff _ _));
                          exact dlk_zero_moi)
                    ltac:(rewrite Htg08a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi03e").
          iIntros (CID25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htg08a) in "Hpc".
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
          { exact Hiok. }
          { rewrite Hnib. exact Hdok. }
          { exact Hnpname. }
          { exact Hnone. }
          { exact Hsb1. }
          { exact Hwmem. }
          { exact Hnp1. }
          { exact Husd1. }
    - (* ============================================================== *)
      (*  ARM N: nameiparent returned 0                                  *)
      (* ============================================================== *)
      iDestruct "Hres" as "(%Hnpa0 & Hisl2)".
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (CK + 0x22))
                (mword_of_int 294 : mword 13) Ra0 Q1 (K - 10)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HQ1a0 Hnpa0;
                      apply (proj2 (eq_vec_true_iff _ _)); exact dlk_zero_moi)
                ltac:(rewrite Htg148; vm_compute; reflexivity)
                with "Hcg Hpc Hi022").
      iIntros (CID16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg148) in "Hpc".
      iPoseProof (cri_148 with "Htext") as "Hi148".
      iPoseProof (cri_14a with "Htext") as "Hi14a".
      assert (Hs1v : add_vec (zero_reg : mword 64) (mnp !!! Regidx Ra0)
                     = (mword_of_int 0 : mword 64))
        by (rewrite Hnpa0; apply add_vec_zero_l).
      assert (HQ1regs : cr_regs m sp0 (mword_of_int 0 : mword 64)
                          (m !!! Regidx Rs2 : mword 64) ty major minor Q1)
        by exact (cr_regs_s1 m sp0 (m !!! Regidx Rs1 : mword 64)
                    (mword_of_int 0 : mword 64) (m !!! Regidx Rs2 : mword 64)
                    ty major minor mnp _ Hs1v Hmnpregs).
      (* +0x148 c.mv s2,a0 (a0 = 0) *)
      iApply (wp_cmv_s_sconf (mword_of_int (CK + 0x148)) Rs2 Ra0 Q1
                (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi148").
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
      assert (Hp14a : add_vec_int (mword_of_int (CK + 0x148) : mword 64) 2
                      = mword_of_int (CK + 0x14a)) by pcw.
      iEval (rewrite Hp14a) in "Hpc".
      (* +0x14a c.j +0x62 *)
      assert (Htg062n : add_vec (mword_of_int (CK + 0x14a) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 1932 : mword 11) ('b"0"))))
                = mword_of_int (CK + 0x62)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CK + 0x14a))
                (sign_extend' 21 (concat_vec (mword_of_int 1932 : mword 11) ('b"0")))
                N1 (K - 10)%nat b
                ltac:(rewrite Htg062n; vm_compute; reflexivity)
                with "Hcg Hpc Hi14a").
      iIntros (CID18 Hq18). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htg062n) in "Hpc".
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


End ProofCreateMain.

End CreateProof.
