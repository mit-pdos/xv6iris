(* fs-namei-ialloc-wip.v -- PARKED WIP for stage N5c (ialloc).
   ====================================================================
   HOW TO RESUME
   ====================================================================
   Copy this file to [iris/ProofIalloc.v] and add the two rows

       ProofIalloc.v
       LinkIalloc.v

   after the (already landed) [SpecIalloc.v] row in [iris/_CoqProject].
   It compiles GREEN as it stands -- verified on the EC2 mirror with

       coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel \
            -R ../user-rocq User -w -notation-overridden ProofIalloc.v

   -- carrying exactly ONE axiom, the [cheat_] stub, which stands for the
   FIVE block lemmas' proofs and for nothing else.  Everything that is not
   a block lemma is PROVEN and [Print Assumptions] reports each of
   [ia_msg_bytes], [ia_dzero_bytes], [ia_win_acc] (and SpecIalloc's
   [ialloc_fresh_shape] / [ialloc_fresh_wf]) as "Closed under the global
   context".

   IT IS NOT IN THE BUILD.  No [iris/ProofIalloc.v], no [iris/LinkIalloc.v]
   and no [_CoqProject] row for either, so nothing in the tree depends on
   the axiom.  [iris/SpecIalloc.v] DID land, is axiom-free, and is FROZEN:
   every premise and every resource below fitted it exactly and no
   counterexample goal was found while the five interfaces were being cut.

   WHAT IS OWED, in the order to do it (each is a [Proof. exact (cheat_ _).
   Qed.] to replace, and each already has its full, TYPECHECKED interface):

     1. [ia_epilogue]  +0x80..+0x86.  The cheapest: ProofIupdate's
        +0x72..+0x7c verbatim at two pops instead of four, then discharge
        [ia_cont] off [ia_arms]'s two arms.
     2. [ia_out]       +0x66..+0x7e.  ProofBalloc's [ba_out] verbatim at
        SIX pops instead of seven, with [ia_msg]/[ia_msg_addr]/[ia_msg_bytes]
        /[ia_msg_fmt] already proven here, then [c.li a0,0] and fall (NOT
        jump -- ialloc's dry arm falls straight into +0x80).
     3. [ia_claim]     +0x88..+0xba.  The one with new content; see the
        block's own comment.  [ia_win_acc] + [DinodeSlot.dislot_acc_gen] +
        [ia_dzero_bytes] + [ia_fresh_of_zero] are the whole byte story, and
        [InodeRegion.ireg_claim_au] plugged into [LW.wp_log_write_au] at
        [Efs := (⊤ ∖ ↑iregN)], [Φfsb := True] is the whole ghost story.
     4. [ia_scan]      +0x30..+0x64.  ProofDirlookup's loop skeleton;
        [InodeRegion.ireg_read_blk] + [ireg_blk_slot] for the decode and
        [ProofIupdate.iu_held_L]'s shape for the machinery half.
     5. [wp_ialloc_sconf] +0x00..+0x2e.  The 8-slot prologue, the DEAD
        [bgeu] at +0x12 (refuted from [1 < ninodes]), and the entry into
        [ia_scan] at fuel [Z.to_nat (ninodes - 1)].
   ====================================================================  *)

(* ProofIalloc.v -- ialloc over the SIE-agnostic sconf world.

     struct inode* ialloc(uint dev, short type) {
       int inum;  struct buf *bp;  struct dinode *dip;
       for(inum = 1; inum < sb.ninodes; inum++){
         bp = bread(dev, IBLOCK(inum, sb));
         dip = (struct dinode * )bp->data + inum % IPB;
         if(dip->type == 0){
           memset(dip, 0, 64);   dip->type = type;
           log_write(bp);        brelse(bp);
           return iget(dev, inum);
         }
         brelse(bp);
       }
       printf("ialloc: no inodes\n");
       return 0;
     }

   *** STATUS: PARKED GREEN, ONE FRONTIER.  See the ledger entry for
   fs-namei N5c.  The five block lemmas below carry their FULL, TYPECHECKED
   statements and their proofs are [exact (cheat_ _)]; the vocabulary, the
   two arms, the format-string lemmas and the three byte-level bridges the
   claim needs are PROVEN.  This file is NOT in [iris/_CoqProject] and no
   [LinkIalloc.v] instantiates it -- nothing in the build depends on the
   axiom.  ***

   THE SHAPE OF THE PROOF.  Four block lemmas entered strictly right to
   left, plus one induction, exactly ProofBalloc's layout:

     [ia_epilogue]  +0x80 .. +0x86   pop ra/s0, pop the frame, ret, and
                                     discharge the contract.  BOTH arms land
                                     here, each carrying its half of
                                     [ia_arms] as one resource, and a0 is
                                     ALREADY set by the arm (the dry arm's
                                     [c.li a0,0] is at +0x7e, the claim's a0
                                     is iget's return value).
     [ia_out]       +0x66 .. +0x7e   pop s1..s6, printk("ialloc: no
                                     inodes"), [c.li a0,0], fall into
                                     +0x80.
     [ia_claim]     +0x88 .. +0xba   memset(dip,0,64), [sh s6,0(s3)],
                                     log_write (THE CLAIM), brelse, iget,
                                     pop s1..s6, [c.j +0x80].
     [ia_scan]      +0x30 .. +0x64   THE ONLY LOOP, by induction on the fuel
                                     [Z.to_nat (ninodes - inum)]: bread, the
                                     slot arithmetic, [lh a5,0(s3)], and the
                                     two-way branch at +0x52.
     [wp_ialloc_sconf] +0x00 .. +0x2e

   THE +0x12 ARM IS DEAD, and the contract's [1 < ninodes] is what kills it
   -- balloc's [0 < size] at the very same offset, killing the very same
   shape of arm: [bgeu a5,a4] with a5 = 1 would jump to the printk WITHOUT
   having pushed s1..s6, i.e. into a SECOND epilogue shape rather than a
   second behaviour.

   THE CLAIM IS ONE ATOMIC UPDATE AND NO RESOURCE (fs-icache.md §16.5).
   [InodeRegion.ireg_claim_au] IS [SpecLogWrite.wp_log_write_au_body]'s fupd
   premise at [Efs := ⊤ ∖ ↑iregN] and [Φfsb := True]; it takes no [dinode_at]
   from anybody, because a free inum's fragment lives in the region and the
   BUFFER is the serialiser.  So the claim block plugs it in at +0x9a the
   way [ProofIupdate] plugs in [ireg_write_au], and pays nothing out.

   THE BYTES.  The scan's per-block decode is
   [InodeRegion.ireg_read_blk] (fragment-free, mask-preserving) against the
   machinery half [ProofIupdate.iu_held_L] extracts from the handle; the
   record the claim installs is [SpecIalloc.ialloc_fresh ty] and the three
   bridges between "memset wrote 64 zero bytes" and
   "[diblk_bytes (<[islot inum := ialloc_fresh ty]> ds)]" are
   [ia_dzero_bytes], [ia_fresh_of_zero] and [ia_win_acc] below.        *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers dfrac.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSmodeHalf.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSconfSrliw.
Require Import ByteBuf.
Require Import PrintintArith.
Require Import PrintkFmt.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import CodeIalloc.
Require Import SpecPanic.
Require Import SpecPrintkGen.
Require Import SpecBread SpecBrelse SpecLogWrite SpecMemset SpecIget.
Require Import SpecIalloc.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* THE ONE FRONTIER.  Unlike [Admitted] this still runs [Qed], so the five
   block lemmas below are really typechecked -- their statements, their
   premise lists and their resource lists are all verified, which is the
   whole point of parking here rather than in a scratch file.  See
   claude-notes/optimization.md. *)
Axiom cheat_ : forall (A : Type), A.

(* ===================================================================== *)
(*  The no-inodes format string, in .rodata just above etext.             *)
(*  [auipc a0,0x4 / addi a0,a0,850] at +0x72 resolves to 0x80007430.      *)
(*  Hoisted as NAMED pure lemmas -- never an inline [ltac:] argument to    *)
(*  [kernel_data_string] (claude-notes/optimization.md).                   *)
(* ===================================================================== *)
Definition ia_msg : string :=
  ("ialloc: no inodes" ++ String (Ascii.ascii_of_nat 10) EmptyString)%string.
Definition ia_msg_addr : Z := 0x80007430.

Lemma ia_msg_bytes : forall j b, cstring_bytes ia_msg !! j = Some b ->
  KernelData.kernel_data !! (ia_msg_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 19 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma ia_msg_fmt : pk_kinds ia_msg = [] /\ nonul ia_msg = true /\
                   (Z.of_nat (String.length ia_msg) < 2147483645)%Z.
Proof.
  split_and!; [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity].
Qed.

(* ===================================================================== *)
(*  THE ZERO RECORD, AND THE THREE BRIDGES THE CLAIM NEEDS.               *)
(*                                                                        *)
(*  [memset(dip, 0, 64)] leaves 64 zero BYTES; [sh s6,0(s3)] then writes  *)
(*  the type halfword.  What [ireg_claim_au] wants is the block's bytes   *)
(*  at [diblk_bytes (<[islot inum := ialloc_fresh ty]> ds)].  The route   *)
(*  is: zero bytes  =  [dinode_bytes ia_dzero]  (ia_dzero_bytes), then    *)
(*  [DinodeSlot.dislot_acc_gen] turns the window into the six typed cells *)
(*  the [sh] writes one of, and [ia_win_acc] puts the slot back into the  *)
(*  block at the new record.                                             *)
(* ===================================================================== *)
Definition ia_dzero : dinode :=
  MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
           (replicate 13 (bv_0 32)).

Lemma ia_dzero_wf : dinode_wf ia_dzero.
Proof. rewrite /dinode_wf /ia_dzero /=. reflexivity. Qed.

(* the 64 bytes of the all-zero record ARE 64 zero bytes *)
Lemma ia_dzero_bytes (j : nat) :
  (j < 64)%nat -> dinode_bytes ia_dzero !!! j = bv_0 8.
Proof.
  intros Hj.
  (* [vm_compute; reflexivity] does NOT close these: the two [bv 8]s differ
     in their (proof-irrelevant) well-formedness component, and the error
     reads "Unable to unify 0%bv with 0%bv".  Go through [bv_eq] -- the
     [pcw] idiom used all over this tree. *)
  do 64 (destruct j as [|j]; [apply bv_eq; vm_compute; reflexivity |]).
  exfalso; lia.
Qed.

(* [ialloc_fresh ty] IS [ia_dzero] with the type halfword replaced -- which
   is exactly what the [sh] does to [dislot]'s first cell. *)
Lemma ia_fresh_of_zero (ty : mword 16) :
  ialloc_fresh ty
  = MkDinode ty (di_major ia_dzero) (di_minor ia_dzero) (di_nlink ia_dzero)
             (di_size ia_dzero) (di_addrs ia_dzero).
Proof. reflexivity. Qed.

Section IallocBytes.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !fsLogG Σ, !bioG Σ}.

  (* THE RAW 64-BYTE WINDOW of slot [k], borrowed out of the block's byte
     image and given back AT A NEW RECORD.  [DinodeSlot.diblk_slot_acc] is
     this composed with [dislot_acc_gen]; ialloc needs the RAW form too,
     because [SpecMemset] takes and returns a byte window and not the six
     typed cells. *)
  Lemma ia_win_acc (a : mword 64) (ds : list dinode) (k : nat) :
    diblk_wf ds -> (k < 16)%nat ->
    bb_bytes a 1024 (fun j => diblk_bytes ds !!! j) -∗
      ([∗ list] j ∈ seq 0 64,
         pa_add (pa_add a (64 * k)%nat) j ↦ₘ (dinode_bytes (ds !!! k) !!! j)) ∗
      (∀ d : dinode, ⌜dinode_wf d⌝ -∗
         ([∗ list] j ∈ seq 0 64,
            pa_add (pa_add a (64 * k)%nat) j ↦ₘ (dinode_bytes d !!! j)) -∗
         bb_bytes a 1024 (fun j => diblk_bytes (<[k := d]> ds) !!! j)).
  Proof.
    intros [Hlen Hall] Hk.
    assert (Hklen : (k < length ds)%nat) by (rewrite Hlen; exact Hk).
    iIntros "H". rewrite /bb_bytes.
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes ds !!! j) ltac:(lia)).
    iDestruct "H" as "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_lookup_t ds k i Hall Hklen ltac:(lia)).
      reflexivity. }
    iIntros (d) "%Hd Hmid".
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes (<[k := d]> ds) !!! j) ltac:(lia)).
    iSplitL "Hpre".
    { iApply (big_sepL_mono with "Hpre"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_insert_other_t ds k d i Hall Hd Hklen
                 ltac:(left; lia)).
      reflexivity. }
    iSplitL "Hmid".
    { iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_insert_same_t ds k d i Hall Hd Hklen ltac:(lia)).
      reflexivity. }
    iApply (big_sepL_mono with "Hsuf"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (diblk_bytes_insert_other_t ds k d (64 * k + (64 + i))%nat
               Hall Hd Hklen ltac:(right; lia)).
    reflexivity.
  Qed.

End IallocBytes.

Module IallocProof (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE)
                   (MS : MEMSET) (IG : IGET) : IALLOC.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

(* ===================================================================== *)
(*  Vocabulary: the frame, the threading invariants, the two arms, the    *)
(*  continuation.                                                         *)
(* ===================================================================== *)
Section IallocDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  (* ialloc's 64-byte frame: ra@56 s0@48 s1@40 s2@32 s3@24 s4@16 s5@8 s6@0.
     [pa_stk sp j] counts DOWN from the entry sp, so slot j holds the
     register saved at (newsp + 64 - 8j). *)
  Definition ia_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ (m !!! Regidx Rs6 : mword 64))%I.

  (* THE TWO ARMS, as ONE resource: what each of ialloc's two exits carries
     into the shared epilogue at +0x80.  [av] is the value in a0 there --
     which each arm has ALREADY set (the dry arm at +0x7e, the claim arm as
     iget's return value at +0xaa).

     Note what is NOT here: no region resource of any kind.  The claimed
     fragment stayed inside [InodeRegion.ireg_inv] at its [fresh_shape] arm
     (fs-icache.md §16.5) and nothing crosses back to the caller. *)
  Definition ia_arms (γ : log_names) (dev : mword 32)
      (ninodes : Z) (nib : nat) (u : nat) (av : mword 64) : iProp Σ :=
    ((* NO INODES: a0 = 0, the iget ledger unit unspent, the reservation
        untouched *)
     (⌜av = (mword_of_int 0 : mword 64)⌝ ∗ iref_slot ∗ log_op γ (S u))
     ∨
     (* THE CLAIM: iget's postcondition verbatim, and one unit gone *)
     (∃ (kslot : nat) (q : Qp) (inum : mword 32),
        ⌜av = ientry kslot
         /\ (kslot < NINODE)%nat
         /\ 0 < bv_unsigned inum < ninodes
         /\ bv_unsigned inum < 16 * Z.of_nat nib⌝ ∗
        inode_ref kslot q dev inum ∗
        log_op γ u))%I.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition ia_cont `{GEN : GenId} `{CID0 : CpuId}
      (γ : log_names) (bn : bio_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat) (pidv : mword 32) (dq dqs dqn : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (alloc : bool) (kslot : nat) (q : Qp) (inum : mword 32)
        (dn' : dinode),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        bslots bn 2 -∗
        (if alloc
         then ⌜mf !!! Regidx Ra0 = ientry kslot
               /\ (kslot < NINODE)%nat
               /\ 0 < bv_unsigned inum < ninodes
               /\ bv_unsigned inum < 16 * Z.of_nat nib
               /\ dn' = ialloc_fresh ty
               /\ di_type dn' = ty
               /\ fresh_shape dn'⌝ ∗
              inode_ref kslot q dev inum ∗
              log_op γ u
         else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗
              iref_slot ∗
              log_op γ (S u)) -∗
        WP (Loop : expr riscv_lang))%I.

End IallocDefs.

(* the two register-threading invariants.  [ia_thr2] excludes only the two
   registers still un-restored at the epilogue; [ia_thr8] also excludes
   s1..s6, which are live across the whole body. *)
Definition ia_thr2 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ia_thr8 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ia_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))).

(* ===================================================================== *)
(*  +0x80 .. +0x86 : THE JOIN.  restore ra/s0, pop the frame, return.     *)
(*  a0 already carries the arm's return value.                            *)
(* ===================================================================== *)
Section IallocEpilogue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  Local Lemma ia_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γ : log_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_ialloc <= K)%nat ->
    ia_sp m M ->
    ia_thr2 m M ->
    sie_cap_gpr M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x80) : mword 64) -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    ia_arms γ dev ninodes nib u (M !!! Regidx Ra0 : mword 64) -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u
            pidv dq dqs dqn j m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (cheat_ _). Qed.

End IallocEpilogue.

(* ===================================================================== *)
(*  +0x66 .. +0x7e : THE SCAN CAME UP EMPTY.  Restore s1..s6, printk the  *)
(*  message, [c.li a0,0], and fall into the epilogue.                     *)
(*                                                                        *)
(*  This is the GENERAL printk path, not the panic path: at ialloc time   *)
(*  [panicking] is 0.  The contract carries printk's own contract as a    *)
(*  PURE hypothesis (SpecIalloc.v's header) so that [Print Assumptions]   *)
(*  stays at the standing six.                                           *)
(* ===================================================================== *)
Section IallocOut.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  Local Lemma ia_out `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γ : log_names)
      (γpr : gname) (γu : uart_names) (γd : disk_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_ialloc <= K)%nat ->
    printk_gen_contract γpr γu γd ->
    ia_sp m M ->
    ia_thr8 m M ->
    sie_cap_gpr M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x66) : mword 64) -∗
    panic_wp_any -∗
    printk_env γpr γu γd -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    iref_slot -∗
    log_op γ (S u) -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u
            pidv dq dqs dqn j m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (cheat_ _). Qed.

End IallocOut.

(* ===================================================================== *)
(*  +0x88 .. +0xba : THE CLAIM.  memset(dip,0,64) / [sh s6,0(s3)] /       *)
(*  log_write / brelse / iget / pop s1..s6 / [c.j +0x80].                 *)
(*                                                                        *)
(*  Entered from the scan's [c.beqz a5,+54] at +0x52 with the buffer      *)
(*  still HELD, s1 = bp, s3 = &dip, s2 = inum, s5 = dev, s6 = type, and   *)
(*  the decoded [ds] whose slot [islot inum] has type 0.                  *)
(*                                                                        *)
(*  The log_write at +0x9a is the ONLY ghost step, and its fupd premise   *)
(*  is [InodeRegion.ireg_claim_au ⊤ γi γfs inodestart nib inum            *)
(*  (ialloc_fresh ty) ds] -- no resource in, [True] out.                  *)
(* ===================================================================== *)
Section IallocClaim.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  Local Lemma ia_claim `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart inodestart ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (inum : mword 32) (ds : list dinode) (u : nat)
      (kk : nat) (bno : mword 32) (bsd : list (bv 8)) (d0 : bool)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_ialloc <= K)%nat ->
    log_geom_ok cov logstart ->
    (* the scan's state at +0x88 *)
    ia_sp m M ->
    ia_thr8 m M ->
    M !!! Regidx Rs1 = bnode kk ->
    M !!! Regidx Rs3 = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat ->
    M !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64) ->
    M !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64) ->
    M !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64) ->
    (kk < NBUF)%nat ->
    uint bno = IBLOCK inum inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    (* the claim's own premises, all four of [ireg_claim_au]'s *)
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    bv_unsigned (di_type (ds !!! DinodeEnc.islot inum)) = 0 ->
    bv_unsigned ty <> 0 ->
    (* and iget's, plus what the arms promise *)
    0 < bv_unsigned inum < ninodes ->
    dislot_align (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) ->
    sie_cap_gpr M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x88) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    iref_slot -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 1 -∗
    log_op γ (S u) -∗
    bio_held bn (fs_view γfs γd dev cov) kk pidv dev bno
       (diblk_bytes ds) (diblk_bytes ds) bsd d0 -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u
            pidv dq dqs dqn j m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (cheat_ _). Qed.

End IallocClaim.

(* ===================================================================== *)
(*  +0x30 .. +0x64 : THE SCAN.  bread, the slot arithmetic, [lh], and the *)
(*  two-way branch -- by induction on the fuel [Z.to_nat (ninodes - inum)].*)
(*                                                                        *)
(*  bread SLEEPS, so the invariant is under a [∀ fuel, wp_next ...] the   *)
(*  way ProofDirlookup's scan is: every turn re-enters at +0x30 with a    *)
(*  fresh [CpuId] and the whole bundle.                                   *)
(* ===================================================================== *)
Section IallocScan.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  Local Lemma ia_scan `{GEN : GenId} `{CIDe : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart inodestart ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16) (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_ialloc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    ireg_blocks_ok inodestart nib cov logstart ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    bv_unsigned ty <> 0 ->
    printk_gen_contract γpr γu γd ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    kernel_text -∗ kernel_data -∗
    panic_wp_any -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    (* ONE turn of the loop, at any surviving [inum], under any fuel that
       bounds what is left to scan.  Everything else is re-supplied by the
       caller of this wand at every re-entry. *)
    (∀ fuel : nat, wp_next (CID0 := CIDe) b (proc_addr j) (fun (CIDl : CpuId) =>
       ∀ (Ml : regfile) (inum : mword 32) (CIDc : CpuId),
         ⌜(Z.to_nat (ninodes - bv_unsigned inum) <= fuel)%nat⌝ -∗
         ⌜0 < bv_unsigned inum < ninodes⌝ -∗
         ⌜ia_sp m Ml⌝ -∗
         ⌜ia_thr8 m Ml⌝ -∗
         ⌜Ml !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64)⌝ -∗
         sie_cap_gpr Ml (K - 8)%nat b (proc_addr j) -∗
         cpu_own 0 true (proc_addr j) C b -∗
         pc_is (mword_of_int (KernelSyms.ialloc + 0x30) : mword 64) -∗
         ia_frame m -∗
         p_pid (proc_addr j) ↦₄{dq} pidv -∗
         sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
         bslots bn 2 -∗
         iref_slot -∗
         log_op γ (S u) -∗
         ia_cont (CID0 := CIDc) γ bn inodestart ninodes nib dev ty u
                 pidv dq dqs dqn j m K C b -∗
         WP (Loop : expr riscv_lang))).
  Proof. exact (cheat_ _). Qed.

End IallocScan.

(* ===================================================================== *)
(*  +0x00 .. +0x2e : THE PROLOGUE, and the contract.                      *)
(* ===================================================================== *)
Section IallocMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

  Lemma wp_ialloc_sconf `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) :
      wp_ialloc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty u
                           pidv dq dqs dqn m K eb C b.
  Proof. exact (cheat_ _). Qed.

End IallocMain.

End IallocProof.
