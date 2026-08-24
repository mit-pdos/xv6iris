(* ProofSysUnlink.v -- sys_unlink's WALK.

   The contract is [SpecSysUnlink.v] (its header carries the arm graph and
   the frame map), the pure/frame/register layer is
   [ProofSysUnlinkParts.v], every EXIT block is [ProofSysUnlinkTails.v] and
   the op-wide log ledger is [SysUnlinkBudget.v].  This file is the walk
   itself, decomposed exactly as projects/fs-sysfile.md's S7-unlink entry
   decomposes it:

     W1  +0x00 .. +0x2e   the prologue, argstr, begin_op, nameiparent
                          (ARM A at +0x16, ARM B at +0x2e)
     W2  +0x30 .. +0x6e   ilock(dp), the two namecmp refusals, dirlookup
     W3  +0x72 .. +0x88   ilock(ip), the blez guard, the T_DIR test
     W4  +0xf8 .. +0x12c  the inlined isdirempty loop
     W5  +0x8a .. +0xd8   the zeroing writei and the two tails

   SEALED.  The functor is ascribed [: SYSUNLINK] and
   [wp_sys_unlink_sconf] at the bottom of this file composes
   W1 ∘ W2 ∘ W3 ∘ {W5-FILE, W5-DIR}; [LinkSysUnlink.v] instantiates it
   against the twelve callees' proofs and its [Axiom] is gone.  The two
   pure facts the T_DIR half used to stop on -- the child's [".."] naming
   the parent, and a directory with a live subdirectory entry having two
   links -- are DERIVED inside [su_w5_dir] from the ledger's parent
   register and its count clauses (projects/fs-fragments-campaign.md, V4
   and V5'; projects/fs-sysfile.md, S7-unlink).

   ==== HOW THE BLOCKS CHAIN ============================================

   A single [wp_next] exit continuation is LINEAR, so a block that owns an
   exit arm cannot ALSO be handed the caller's continuation twice.  The
   shape every block here uses is durable-notes' "the exit must be handed
   back": the block's FALL-THROUGH argument is a continuation that receives
   the seam AND the caller's own [wp_next] back, so whichever arm runs
   consumes the one copy.

   The [(CID0 := CIDs)] annotation on a [wp_next] written inside a binder
   is MANDATORY -- written bare, instance resolution anchors it at the
   innermost [CpuId] and the guard degrades to a tautology. *)
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
Require Import W32Arith.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SpecPanic.
Require Import SpecPrintk.
Require Import WpUart.
Require Import ByteBuf.
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
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import DirLinks.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IregDirBit.
Require Import IregLinkNz.   (* V5' increment W: the root refutation at a
                                released TOKEN ([ireg_tok_root_min2]) and the
                                [dl_root]/[ireg_root] bridge, which is what
                                opens [dir_links_dotdot_out]'s tie leg *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIput.
Require Import SpecIupdate.
Require Import SpecIunlockput.
Require Import SpecNamecmp.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecMemset.
Require Import SpecReadi.
Require Import SpecWritei.
Require Import SpecNamex.
Require Import SpecNameiparent.
Require Import CodeSysUnlink.
Require Import SysUnlinkBudget.
Require Import SpecSysUnlink.
Require Import ProofSysUnlinkParts.
Require Import ProofSysUnlinkTails.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

(* ===================================================================== *)
(*  THE RECORD-SHAPE IDENTITIES the process block needs across argstr     *)
(*  and the walk.  Restated here rather than imported: a whole-function   *)
(*  proof file is not a dependency any other one may take.                *)
(* ===================================================================== *)

Lemma su_upd_upt_idem (V : pprivate) (P1 P2 : uptd) :
  upd_upt (upd_upt V P1) P2 = upd_upt V P2.
Proof. reflexivity. Qed.

Lemma su_cwd_upt (V : pprivate) (P : uptd) : pv_cwd (upd_upt V P) = pv_cwd V.
Proof. reflexivity. Qed.

Lemma su_upd_cwd_upt (V : pprivate) (P : uptd) :
  upd_cwd (upd_upt V P) (pv_cwd V) = upd_upt V P.
Proof. destruct V; reflexivity. Qed.

(* [SysUnlinkBudget] and [SpecSysUnlink] both define [sys_unlink_slots];
   this file imports both, so every mention of the allowance is spelled at
   the CONTRACT's copy and this is the bridge to the literal the callees
   want. *)
Lemma su_slots2 : SpecSysUnlink.sys_unlink_slots = 2%nat.
Proof. reflexivity. Qed.

(* argstr's [noff] premise at the walk's own depth, which is zero. *)
Lemma su_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* nameiparent's counter report, read into the ledger's own name.  [ok]
   fixes the second summand at zero, which is the only difference between
   this and [su_u1f]. *)
Lemma su_cnt_ok (w1 : bool) (n1 : nat) :
  ((MAXOPBLOCKS - (walk_spend w1 + 0))%nat <= n1)%nat -> (su_u1 w1 <= n1)%nat.
Proof.
  intro H. unfold su_u1, su_u0. rewrite Nat.add_0_r in H. exact H.
Qed.

(* ===================================================================== *)
(*  THE TWO NAME LITERALS the two [namecmp] refusals compare against.     *)
(*                                                                        *)
(*  The [auipc a1,2] / [addi a1,a1,1656] pair at +0x34..+0x38 computes    *)
(*  0x800075e0 and the pair at +0x48..+0x4c computes 0x800075e8 -- the    *)
(*  SAME two .rodata addresses create's [dirlink(ip,".")] /               *)
(*  [dirlink(ip,"..")] use, which is why the byte lists below are         *)
(*  [ProofCreateParts]'s verbatim.  RESTATED rather than imported: a      *)
(*  whole-function proof's parts file is not a dependency this one may    *)
(*  take.                                                                 *)
(*                                                                        *)
(*  OWNERSHIP IS OF ALL FOURTEEN BYTES, so the functions have to be       *)
(*  honest about what follows the NUL: "." 's window runs into ".."       *)
(*  (bytes 8 and 9) and ".." 's into "unlink" (bytes 8..13).  [bname]     *)
(*  cuts at the first NUL, so neither reaches the comparison.            *)
(* ===================================================================== *)

Definition su_dot_addr : Z := 0x800075e0.
Definition su_dotdot_addr : Z := 0x800075e8.

Definition su_dot_list : list (bv 8) :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0x2e; Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0].

Definition su_dotdot_list : list (bv 8) :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0x75; Z_to_bv 8 0x6e; Z_to_bv 8 0x6c; Z_to_bv 8 0x69;
   Z_to_bv 8 0x6e; Z_to_bv 8 0x6b].

Definition su_dot_f (j : nat) : bv 8 := su_dot_list !!! j.
Definition su_dotdot_f (j : nat) : bv 8 := su_dotdot_list !!! j.

(* what [namecmp]'s boolean is stated against: the canonical name views *)
Lemma su_dot_name : bname 14 su_dot_f = dot_name.
Proof. vm_compute. reflexivity. Qed.

Lemma su_dotdot_name : bname 14 su_dotdot_f = dotdot_name.
Proof. vm_compute. reflexivity. Qed.

(* the two [auipc]/[addi] pairs, computed.  CLOSED terms -- no free
   address -- so [vm_compute] is safe here (contrast [su_offcell]). *)
Lemma su_dotaddr :
  add_vec (add_vec (mword_of_int (SU + 0x34) : mword 64)
                   (auipc_off (mword_of_int 2 : mword 20)))
          (sign_extend' 64 (mword_of_int 1554 : mword 12))
  = (mword_of_int su_dot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_dotdotaddr :
  add_vec (add_vec (mword_of_int (SU + 0x48) : mword 64)
                   (auipc_off (mword_of_int 2 : mword 20)))
          (sign_extend' 64 (mword_of_int 1542 : mword 12))
  = (mword_of_int su_dotdot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [di_type dn = T_DIR] at the sixteen-bit width, read as the Z-level
   equality [DirView] / [DirLinks] state their type tests at.  The
   [ity_shot] agreement gives the left form and every payload clause wants
   the right one. *)
Lemma su_tdir_zof (t : mword 16) :
  t = SpecDirlookup.T_DIR -> bv_unsigned t = T_DIR_z.
Proof. intros ->. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  W4's PURE LAYER -- the isdirempty loop's index arithmetic and the      *)
(*  dots-only harvest at its empty exit.                                  *)
(* ===================================================================== *)

(* 8-alignment weakens to the [lhu]'s 2 (ProofDirlookupParts' shape,
   restated: a whole-function proof's parts file is not a dependency this
   one may take). *)
Lemma su_rem8_2 (x : Z) : 0 <= x -> Z.rem x 8 = 0 -> Z.rem x 2 = 0.
Proof.
  intros H0 H8.
  rewrite Z.rem_mod_nonneg in H8; [| exact H0 | lia].
  rewrite Z.rem_mod_nonneg; [| exact H0 | lia].
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in H8; [| lia].
  destruct H8 as [c Hc]. exists (4 * c). lia.
Qed.

Lemma su_align_8_2 (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true ->
  is_aligned_paddr (Physaddr a) 2 = true.
Proof.
  unfold is_aligned_paddr. intro H. apply Z.eqb_eq in H. apply Z.eqb_eq.
  apply su_rem8_2; [| exact H].
  rewrite uint_unsigned. exact (proj1 (bv_unsigned_in_range 64 (a : mword 64))).
Qed.

(* THE LOOP'S HARVEST.  Records 0 and 1 are the two dots ([dir_dots_ix],
   whose guards are the kernel's own type test and [blez]), and the scan
   found everything above them dead -- so every live record is a dot, which
   is [DirView.dir_dots_only] verbatim. *)
Lemma su_dots_only_scan (self : Z) (dn : dinode) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z ->
  bv_unsigned (di_nlink dn) <> 0 ->
  dir_dots_ix self dn data ->
  (forall k : nat, (2 <= k)%nat ->
     (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
     dir_inum data k = bv_0 16) ->
  dir_dots_only dn data.
Proof.
  intros Hty Hnl Hdd Hdead k Hk Hlive.
  destruct (Hdd Hty Hnl) as (_ & _ & _ & Hn0 & _ & Hn1).
  destruct k as [| [| k']].
  - left. exact Hn0.
  - right. exact Hn1.
  - exfalso. apply Hlive. apply Hdead; lia.
Qed.

(* [mword_of_int] of a 32-bit word's own value is the word *)
Lemma su_moi32_id (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  apply Z_to_bv_bv_unsigned.
Qed.

(* the [lw] of ip->size, read at the literal the loop's compares want *)
Lemma su_size_sext (w : mword 32) :
  bv_unsigned w < 2 ^ 31 ->
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_unsigned w).
Proof.
  intro Hw. rewrite -{1}(su_moi32_id w). apply w32_sext_moi.
  pose proof (proj1 (bv_unsigned_in_range _ w)). lia.
Qed.

(* [rd_clamp] at n = 16: never more; and 16 exactly means the whole record
   sits inside the file *)
Lemma su_clamp_le16 (szw : bv 32) (off : nat) :
  (rd_clamp szw off 16 <= 16)%nat.
Proof. unfold rd_clamp. case_decide; lia. Qed.

Lemma su_clamp16_in (szw : bv 32) (off : nat) :
  rd_clamp szw off 16 = 16%nat ->
  (off + 16 <= Z.to_nat (bv_unsigned szw))%nat.
Proof. unfold rd_clamp. case_decide; lia. Qed.

(* [dir_nrec] against the byte bound, both directions *)
Lemma su_nrec_le (sz : Z) (j : nat) :
  0 <= sz -> sz <= 16 * Z.of_nat j -> (dir_nrec sz <= j)%nat.
Proof.
  intros H0 Hj. unfold dir_nrec.
  assert (Hd : sz `div` 16 <= Z.of_nat j) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma su_nrec16 (sz : Z) :
  0 <= sz -> (16 * dir_nrec sz <= Z.to_nat sz)%nat.
Proof.
  intro H0. unfold dir_nrec.
  pose proof (Z.mul_div_le sz 16 ltac:(lia)) as Hle.
  pose proof (Z.div_pos sz 16 H0 ltac:(lia)) as Hp. lia.
Qed.

(* [neq_vec] off the [eq_vec] facts the parts file states *)
Lemma su_neq_of_eq_true (x y : mword 64) :
  eq_vec x y = true -> neq_vec x y = false.
Proof. intro H. unfold neq_vec. rewrite H. reflexivity. Qed.

Lemma su_neq_of_eq_false (x y : mword 64) :
  eq_vec x y = false -> neq_vec x y = true.
Proof. intro H. unfold neq_vec. rewrite H. reflexivity. Qed.

(* the two inum bytes of a record, and its fourteen name bytes
   ([ProofDirlookupParts]' shapes, restated) *)
Lemma su_half_bytes_eq (data : nat -> list (bv 8)) (i j : nat) :
  (j < 2)%nat -> nth_byte (dir_inum data i) j = file_byte data (16 * i + j)%nat.
Proof.
  intro Hj. destruct j as [| [| j]]; [| | exfalso; lia].
  - rewrite dir_inum_byte0. f_equal; lia.
  - rewrite dir_inum_byte1. f_equal; lia.
Qed.

Lemma su_name_shift (data : nat -> list (bv 8)) (i j : nat) :
  file_byte data (16 * i + (2 + j))%nat = dir_name data i j.
Proof. unfold dir_name. f_equal; lia. Qed.

(* the [zero_extend' 32] dirlookup's iget wraps the halfword inum in is
   unsigned-transparent -- W3 reads the region bound through it *)
Lemma su_zext32_unsigned (w : mword 16) :
  bv_unsigned (zero_extend' 32 w : mword 32) = bv_unsigned w.
Proof.
  exact (bv_zero_extend_unsigned 32 w ltac:(vm_compute; discriminate)).
Qed.

(* the [V] slot of readi's contract is dead on the kernel arm *)
(* [su_dummyV] IS DEAD: readi's and writei's [V] slot used to be unread on
   the kernel arm, which took a bare quarter of [p->pid].  Both take
   [proc_priv_bare pj pidv V] now, so the slot is live and sys_unlink passes
   its own block's [V] straight through.  Kept only until the last reference
   goes. *)
Definition su_dummyV : pprivate :=
  MkPPriv (mword_of_int 0)
          (UPTD (mword_of_int 0) (mword_of_int 0) ∅ ∅)
          [] [] (mword_of_int 0) [].

(* readi's delivered byte at [tot = 16] is the file's byte *)
Lemma su_rdd_eq (data : nat -> list (bv 8)) (olds : nat -> bv 8)
    (off jj : nat) :
  (jj < 16)%nat ->
  rd_delivered data olds off 16 jj = file_byte data (off + jj)%nat.
Proof.
  intro Hj. unfold rd_delivered. rewrite decide_True; [reflexivity | exact Hj].
Qed.

(* ===================================================================== *)
(*  W5'S PURE LAYER: the zeroing writei's cost figures (restated from      *)
(*  ProofDirlink, the walk-file-restates rule), the zero record's bytes,   *)
(*  and the decrement arithmetic packaged over plain [Z] ([lia] under the  *)
(*  bitvector zify hook cannot handle atoms that are [bv_unsigned] of      *)
(*  large terms -- ProofMemmove.mm_overlap_arith's recipe).               *)
(* ===================================================================== *)

(* sixteen bytes at a 16-aligned offset straddle exactly ONE block *)
Lemma su_wi_blocks (k : nat) : wi_blocks (16 * k) 16 = 1%nat.
Proof.
  unfold wi_blocks.
  assert (HB : BSIZE = 1024%nat) by reflexivity.
  rewrite HB.
  assert (Hm : ((16 * k) mod 1024)%nat = (16 * (k mod 64))%nat).
  { change 1024%nat with (16 * 64)%nat. apply Nat.Div0.mul_mod_distr_l. }
  rewrite Hm.
  assert (Hlt : (k mod 64 < 64)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hd : (16 * (k mod 64) + 16 + 1024 - 1)%nat
               = (1024 * 1 + (16 * (k mod 64) + 15))%nat) by lia.
  rewrite Hd.
  rewrite (Nat.div_add_l 1 1024 (16 * (k mod 64) + 15)%nat ltac:(lia)).
  rewrite (Nat.div_small (16 * (k mod 64) + 15)%nat 1024 ltac:(lia)).
  reflexivity.
Qed.

Lemma su_wi_cost (k : nat) : wi_cost_bmonly (16 * k) 16 = 4%nat.
Proof. unfold wi_cost_bmonly. rewrite (su_wi_blocks k). reflexivity. Qed.

(* [iunlockput] can report at most one bitmap unit spent on this credited
   call.  Keep that arithmetic out of the whole-function Iris context. *)
Lemma su_iunlockput_from5 (w : bool) (n n' : nat) :
  (5 <= n)%nat ->
  ((n - ip_spend_w w true false)%nat <= n')%nat ->
  (4 <= n')%nat.
Proof. unfold ip_spend_w, ip_bm. destruct w; cbn; lia. Qed.

(* the zero record: its inum field and each of its sixteen bytes *)
Lemma su_dz_inum : de_inum dirent_zero = bv_0 16.
Proof. reflexivity. Qed.

Lemma su_dz_byte (j : nat) :
  (j < 16)%nat -> dirent_bytes dirent_zero !!! j = NUL.
Proof.
  intro Hj. rewrite dirent_bytes_zero.
  do 16 (destruct j as [| j]; [reflexivity |]). exfalso. lia.
Qed.

(* the decrement arithmetic, mword-free *)
Lemma su_decr_pay (x y : Z) (bb : bool) :
  y = x + 1 -> x + (if bb then 1 else 0) <= y.
Proof. intro H. destruct bb; lia. Qed.

(* the decrement stays short, over plain [Z] (durable-disk 2b-inode-3):
   [lia]'s zify hook does not come back with [bv_unsigned] in the goal. *)
Lemma su_dec_short (a c : Z) : c = a + 1 -> c <= 32767 -> a <= 32767.
Proof. lia. Qed.

Lemma su_decr_pos (x y z : Z) : y = x + 1 -> y = z -> 2 <= z -> x <> 0.
Proof. intros. lia. Qed.

Lemma su_le1_nz_eq1 (x : Z) : 0 <= x -> x <= 1 -> x <> 0 -> x = 1.
Proof. intros. lia. Qed.

Lemma su_decr_zero (x y : Z) : y = x + 1 -> y = 1 -> x = 0.
Proof. intros. lia. Qed.

(* panic's side conditions as CLOSED lemmas over plain nat/gset -- never an
   inline [ltac:] in the application (see claude-notes/projects/panic.md). *)
Lemma su_pn_K (K : nat) : (K_sys_unlink <= K)%nat -> (panic_stack <= K - 30)%nat.
Proof. lia. Qed.

Lemma su_pn_K_readi (K : nat) :
  (K_readi <= K - 30)%nat -> (panic_stack <= K - 30)%nat.
Proof. lia. Qed.

Lemma su_pn_noff : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma su_pn_below (lks : gset string) :
  locks_below lks "log" -> locks_below lks "pr".
Proof. intros H. apply (locks_below_mono lks "log" "pr" H). vm_compute; lia. Qed.

Module SysUnlinkProof (Argstr : ARGSTR) (BeginOp : BEGIN_OP)
                      (Nameiparent : NAMEIPARENT) (Ilock : ILOCK)
                      (Namecmp : NAMECMP) (Dirlookup : DIRLOOKUP)
                      (Memset : MEMSET) (Readi : READI) (Writei : WRITEI)
                      (Iupdate : IUPDATE) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP) (PN : PANIC) : SYSUNLINK.

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkBody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* ================================================================== *)
  (*  THE FOUR SPLITS AND THE TWO PER-SLOT PROJECTIONS W2 NEEDS          *)
  (* ================================================================== *)

  (* the two per-slot projections out of the boot families, at the copies
     THIS contract names ([ic_escrows] is IcacheEscrow's, [ic_sleeplocks]
     SpecDirlink's). *)
  Lemma su_esc_acc `{GEN : GenId} (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma su_slk_acc `{GEN : GenId} (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (ic_sleeplocks cn -∗
     ∃ gil gisl : gname,
       is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string
                        (ic_tok cn k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma su_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* THE GENERATION-NAMED SHED.  [IcacheRef.inode_ref_shed] loses the
     generation, and nameiparent's [inode_held_ty] payout is exactly the
     claim that the share handed to ilock names the SAME generation as the
     type one-shot beside it -- which is what turns the parent's promised
     T_DIR into [di_type dnd = T_DIR] at the record ilock returns.  Pure
     resource algebra; its home is [IcacheRef.v] and it is here for that
     file's rebuild-cone reason. *)
  Lemma su_carve_gen (k : nat) (q s : Qp) (dv inum : mword 32) (gy : gname) :
    inode_ref_gen k (q + s)%Qp dv inum gy ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q dv inum gy ∗ inode_shr_gen k s dv inum gy.
  Proof.
    rewrite /inode_ref_gen /inode_ref_short_gen /inode_shr_gen
            live_gen_split inode_ident_split SleepLock.slh_tok_split.
    iSplit.
    - iIntros "($ & [$ Hl2] & [$ Hi2] & [$ Hs2])". iFrame.
    - iIntros "[($ & $ & $ & $) ($ & $ & $)]".
  Qed.

  Lemma su_shed_gen (k : nat) (q : Qp) (dv inum : mword 32) (gy : gname) :
    inode_ref_gen k q dv inum gy ⊣⊢
    inode_ref_short_gen k (q/2 + q/2)%Qp (q/2)%Qp dv inum gy ∗
    inode_shr_gen k (q/2)%Qp dv inum gy.
  Proof.
    pose proof (su_carve_gen k (q/2)%Qp (q/2)%Qp dv inum gy) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

  Lemma su_dot_window `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dot_f j).
  Proof.
    intros ->. iApply (kernel_data_bytes su_dot_addr 14 su_dot_f _ eq_refl
                         ltac:(unfold text_end, su_dot_addr; lia)
                         ltac:(vm_compute; discriminate)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  Lemma su_dotdot_window `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dotdot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dotdot_f j).
  Proof.
    intros ->. iApply (kernel_data_bytes su_dotdot_addr 14 su_dotdot_f _ eq_refl
                         ltac:(unfold text_end, su_dotdot_addr; lia)
                         ltac:(vm_compute; discriminate)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  (* ================================================================== *)
  (*  THE isdirempty [de] RECORD'S BYTE VIEWS -- two bytes as the [lhu]'s *)
  (*  halfword, fourteen riding.  [ProofDirlookupParts]' shapes, restated *)
  (*  for that file's whole-function reason.                             *)
  (* ================================================================== *)

  Lemma su_del_split (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ[KT1] f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ[KT1] f j)
       ∗ ([∗ list] j ∈ seq 0 14, pa_add (pa_add a 2) j ↦ₘ[KT1] f (2 + j)%nat).
  Proof. exact (bb_split a 2 14 f). Qed.

  Lemma su_half_acc (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ[KT1] file_byte data (16 * i + j)%nat)
    ⊣⊢ a ↦₂[KT1] dir_inum data i.
  Proof.
    intro Hal.
    rewrite (bb_ext (KTR := KT1) a 2 (fun j => file_byte data (16 * i + j)%nat)
                        (fun j => nth_byte (dir_inum data i) j)
               (fun j Hj => eq_sym (su_half_bytes_eq data i j Hj))).
    iSplit.
    - iIntros "H".
      iApply (word2_pointsto_intro (KTR := KT1) a (DfracOwn 1) (dir_inum data i) Hal).
      iExact "H".
    - iIntros "H". iApply (word2_pointsto_bytes (KTR := KT1) with "H").
  Qed.

  Lemma su_name_acc (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] file_byte data (16 * i + (2 + j))%nat)
    ⊣⊢ ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ[KT1] dir_name data i j).
  Proof.
    apply (bb_ext (KTR := KT1) a 14 (fun j => file_byte data (16 * i + (2 + j))%nat)
                       (dir_name data i)
             (fun j _ => su_name_shift data i j)).
  Qed.

  (* the whole record, split for the [lhu] and put back *)
  Lemma su_de_view (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] jj ∈ seq 0 16, pa_add a jj ↦ₘ[KT1] file_byte data (16 * i + jj)%nat)
    ⊣⊢ a ↦₂[KT1] dir_inum data i
       ∗ ([∗ list] jj ∈ seq 0 14, pa_add (pa_add a 2) jj ↦ₘ[KT1] dir_name data i jj).
  Proof.
    intro Hal.
    rewrite -(su_half_acc data i a Hal).
    rewrite -(su_name_acc data i (pa_add a 2)).
    exact (su_del_split a (fun jj => file_byte data (16 * i + jj)%nat)).
  Qed.

  (* readi's sixteen delivered bytes ARE the record's bytes at [tot = 16] *)
  Lemma su_rdd_view (data : nat -> list (bv 8)) (olds : nat -> bv 8)
      (i : nat) (a : Arch.pa) :
    ([∗ list] jj ∈ seq 0 16,
       pa_add a jj ↦ₘ[KT1] rd_delivered data olds (16 * i)%nat 16 jj)
    ⊣⊢ ([∗ list] jj ∈ seq 0 16,
          pa_add a jj ↦ₘ[KT1] file_byte data (16 * i + jj)%nat).
  Proof.
    apply (bb_ext (KTR := KT1) a 16
             (fun jj => rd_delivered data olds (16 * i)%nat 16 jj)
             (fun jj => file_byte data (16 * i + jj)%nat)
             (fun jj Hj => su_rdd_eq data olds (16 * i)%nat jj Hj)).
  Qed.


  (* ================================================================== *)
  (*  W1: +0x00 .. +0x2e -- the prologue, argstr, begin_op, nameiparent  *)
  (*                                                                     *)
  (*    +0x00 c.addi16sp sp,-240 ; +0x02 c.sdsp ra ; +0x04 c.sdsp s0     *)
  (*    +0x06 c.addi4spn s0,sp,240                                       *)
  (*    +0x08 li a2,128 ; +0x0c addi a1,s0,-208 ; +0x10 c.li a0,0        *)
  (*    +0x12 jal argstr ; +0x16 bltz a0 -> ARM A                        *)
  (*    +0x1a c.sdsp s1,216(sp)  (the FIRST shrink-wrapped save)         *)
  (*    +0x1c jal begin_op                                               *)
  (*    +0x20 addi a1,s0,-80 ; +0x24 addi a0,s0,-208                     *)
  (*    +0x28 jal nameiparent ; +0x2c c.mv s1,a0                          *)
  (*    +0x2e c.beqz a0 -> ARM B                                          *)
  (*                                                                     *)
  (*  THE SAVE AT +0x1a IS BELOW THE ARGSTR BRANCH, so ARM A owns no      *)
  (*  callee-saved slot at all and slot 3 is still the caller's junk      *)
  (*  there; ARM B, which is below it, restores s1 from slot 3.          *)
  (*                                                                     *)
  (*  nameiparent is applied at its GEN (set-form) contract, for the      *)
  (*  [w] pay-bit the zeroing's writei needs downstream; the [ok = false] *)
  (*  arm hands the whole allowance back and ARM B retires the op.        *)
  (* ================================================================== *)
  Lemma su_w1 `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64) (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    g = icfg_log ->
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
    ireg_blocks_ok inodestart nib cov logstart ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    pv_tf V !! tf_arg_idx 0 = Some v0 ->
    sie_cap_gpr KT1 m K b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int KernelSyms.sys_unlink) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    iref_slots SpecSysUnlink.sys_unlink_slots -∗
    proc_priv gf (proc_addr jx) pid V -∗
    (* ---- THE SEAM: the fall-through, at +0x30 with [dp] resolved ---- *)
    (∀ (CIDs : CpuId) (Ms : regfile) (P1 : uptd)
       (n1 : nat) (Sb1 : gset Z) (w1 : bool) (dpv : mword 64)
       (nf bp1 bnm0 bd0 be0 : nat -> bv 8)
       (w4 w5 w6 w27 w30 : mword 64),
       ⌜su_al (m !!! Regidx csp_rs1 : mword 64)⌝ -∗
       ⌜su_regs m (m !!! Regidx csp_rs1 : mword 64) dpv
                (m !!! Regidx Rs2 : mword 64) (m !!! Regidx Rs3 : mword 64) Ms⌝ -∗
       (* [a0] STILL HOLDS [dp] AT THE SEAM, and it has to be said: [su_regs]
          pins the five CALLEE-SAVED registers and [a0] is not one of them,
          so the [c.mv s1,a0] at +0x2c leaves the fact true and unexported.
          W2's [ilock(dp)] reads [a0], so this is its first premise.  (Found
          by the seal, which is the first consumer to compose W1 with W2.) *)
       ⌜(Ms !!! Regidx Ra0 : mword 64) = dpv⌝ -∗
       ⌜uptd_ext (pv_upt V) P1⌝ -∗
       ⌜(su_u1 w1 <= n1)%nat⌝ -∗
       ⌜w1 = true -> bmapstart ∈ Sb1⌝ -∗
       ⌜dpv <> (zero_reg : mword 64)⌝ -∗
       sie_cap_gpr KT1 Ms (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x30)) -∗
       fs_crash_seam cov logstart -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
       iref_slots 1 -∗
       inode_held_ty dpv T_DIR -∗
       log_opS g n1 Sb1 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 4) ↦₈[KT1] w4 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 5) ↦₈[KT1] w5 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 6) ↦₈[KT1] w6 -∗
       ([∗ list] jj ∈ seq 0 16,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 8) jj ↦ₘ[KT1] bd0 jj) -∗
       ([∗ list] jj ∈ seq 0 14,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 0 2,
          pa_add (pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10) 14) jj
            ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
       ([∗ list] jj ∈ seq 0 128,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 26) jj ↦ₘ[KT1] bp1 jj) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 27) ↦₈[KT1] w27 -∗
       ([∗ list] jj ∈ seq 0 16,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 29) jj ↦ₘ[KT1] be0 jj) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 30) ↦₈[KT1] w30 -∗
       (* the caller's own exit, handed BACK *)
       wp_next (CID0 := CIDs) true (proc_addr jx) (fun (CIDx : CpuId) =>
         ∀ (mf : regfile) (P' : uptd),
             ⌜callee_saved m mf⌝ -∗
             ⌜uptd_ext (pv_upt V) P'⌝ -∗
             sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
             cpu_own 0 eb (proc_addr jx) b lks -∗
             trap_csrs_ext KT1 eb -∗
             cpu_claim_ext eb (proc_addr jx) -∗
             pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
             bslots 3 -∗
             sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
             sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
             sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
             iref_slots SpecSysUnlink.sys_unlink_slots -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
             ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
             WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb Harg0.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1 : mword 64).
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpenv2 #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv Hseamk Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    (* ===== +0x00 c.addi16sp sp,-240 ===== *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.sys_unlink)
              (mword_of_int 49 : mword 6) m K 30 b ltac:(exact K30)
              (su_push sp0) with "Hcg Hpc []").
    { iApply (suli_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 49 : mword 6))))]> m).
    assert (HM1sp : su_sp sp0 M1).
    { unfold su_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply su_push ]. }
    assert (HM1thr : su_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19.
      rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.sys_unlink : mword 64) 2
                    = mword_of_int (SU + 0x2)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (su_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%u3 Hf3] & [%u4 Hf4] & [%u5 Hf5] &
           [%u6 Hf6] & HbD & HbN & HbP & [%u27 H27] & HbE & [%u30 H30])".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply su_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply su_frm2).
    (* ===== +0x02 c.sdsp ra,232(sp) ===== *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SU + 0x2))
              (mword_of_int 29 : mword 6) Rra M1 (K - 30)%nat u1 b
              with "Hcg Hpc [] Hf1").
    { iApply (suli_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SU + 0x2) : mword 64) 2
                    = mword_of_int (SU + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,224(sp) ===== *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SU + 0x4))
              (mword_of_int 28 : mword 6) Rs0 M1 (K - 30)%nat u2 b
              with "Hcg Hpc [] Hf2").
    { iApply (suli_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (SU + 0x4) : mword 64) 2
                    = mword_of_int (SU + 0x6)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ===== +0x06 c.addi4spn s0,sp,240 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SU + 0x6))
              (Cregidx (mword_of_int 0)) (mword_of_int 60 : mword 8) Rs0
              M1 (K - 30)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (suli_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 60 : mword 8))))]> M1).
    assert (HM2regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) M2).
    { unfold su_regs. split_and!.
      - rewrite /M2 upd_ne; [exact HM1sp | nz].
      - etransitivity; [ rewrite /M2; apply upd_eq |].
        rewrite HM1sp. apply su_fp.
      - rewrite /M2 upd_ne; [exact HM1s1 | nz].
      - rewrite /M2 upd_ne; [exact HM1s2 | nz].
      - rewrite /M2 upd_ne; [exact HM1s3 | nz].
      - intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
        exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp08 : add_vec_int (mword_of_int (SU + 0x6) : mword 64) 2
                    = mword_of_int (SU + 0x8)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 li a2,128 ===== *)
    iApply (wp_li4_s_sconf (CID := CID4) (mword_of_int (SU + 0x8)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) M2 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (suli_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> M2).
    assert (HM3a2 : (M3 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (HM3regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) M3)
      by (rewrite /M3; apply su_regs_caller; [exact Hcsa2 | exact HM2regs]).
    assert (Hpp0c : add_vec_int (mword_of_int (SU + 0x8) : mword 64) 4
                    = mword_of_int (SU + 0xc)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c addi a1,s0,-208 -- [path] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID5) (mword_of_int (SU + 0xc)) Ra1 Rs0
              (mword_of_int 3888 : mword 12) M3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_00c with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3888 : mword 12)))]> M3).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26).
    { etransitivity; [ rewrite /M4; apply upd_eq |].
      rewrite (su_regs_s0 _ _ _ _ _ _ HM3regs). apply su_bufpath. }
    assert (HM4a2 : (M4 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3a2 | nz]).
    assert (HM4regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) M4)
      by (rewrite /M4; apply su_regs_caller; [exact Hcsa1 | exact HM3regs]).
    assert (Hpp10 : add_vec_int (mword_of_int (SU + 0xc) : mword 64) 4
                    = mword_of_int (SU + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 c.li a0,0 ===== *)
    iApply (wp_cli_s_sconf (CID := CID6) (mword_of_int (SU + 0x10)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (suli_010 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M5 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M4).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5a2 : (M5 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a2 | nz]).
    assert (HM5regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) M5)
      by (rewrite /M5; apply su_regs_caller; [exact Hcsa0 | exact HM4regs]).
    assert (Hpp12 : add_vec_int (mword_of_int (SU + 0x10) : mword 64) 2
                    = mword_of_int (SU + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 jal ra,argstr ===== *)
    iApply (wp_jal_s_sconf (CID := CID7) (mword_of_int (SU + 0x12)) Rra
              (mword_of_int 2087096 : mword 21) M5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_012 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)]> M5).
    assert (Hjas : add_vec (mword_of_int (SU + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087096 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM6ra : (M6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)
      by (rewrite /M6; apply upd_eq).
    assert (HM6a0 : (M6 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a0 | nz]).
    assert (HM6a1 : (M6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26)
      by (rewrite /M6 upd_ne; [exact HM5a1 | nz]).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5a2 | nz]).
    assert (HM6regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) M6)
      by (rewrite /M6; apply su_regs_caller; [exact Hcsra | exact HM5regs]).
    iDestruct (su_bytes_name (pa_stk sp0 26) 128 with "HbP") as (bp0) "HbP".
    iDestruct (cpu_own_transport CID0 CID8 0 eb (proc_addr jx) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID8) ga gf M6 (K - 30)%nat 0%nat eb
              (proc_addr jx) 0%nat v0 pid V 128%nat bp0 b lks
              su_arg0_lt HM6a0 Harg0 su_noff0 ltac:(exact Kar) HM6a2
              su_maxpath_lt (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [HbP]").
    { iEval (rewrite HM6a1). iExact "HbP". }
    iIntros (CID9 Hq9 mas P1 bp1) "%Hcsas %Hupt1 Hcg Hown Hpc Hpriv HbP %Hfsr1".
    iEval (rewrite HM6a1) in "HbP".
    assert (Hpc16 : ret_pc (M6 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x16)) by (rewrite HM6ra; pcw).
    iEval (rewrite Hpc16) in "Hpc".
    assert (Hasregs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) mas)
      by exact (su_regs_cs m sp0 _ _ _ M6 mas Hcsas HM6regs).
    assert (Hassp : su_sp sp0 mas) by exact (su_regs_sp _ _ _ _ _ _ Hasregs).
    assert (Hasthr : su_thr m mas) by exact (su_regs_thr _ _ _ _ _ _ Hasregs).
    assert (Hass1 : (mas !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by exact (su_regs_s1 _ _ _ _ _ _ Hasregs).
    assert (Hass2 : (mas !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by exact (su_regs_s2 _ _ _ _ _ _ Hasregs).
    assert (Hass3 : (mas !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (su_regs_s3 _ _ _ _ _ _ Hasregs).
    (* ===== +0x16 bltz a0 -> ARM A (+0x170) ===== *)
    destruct Hfsr1 as [(pk1 & Hpk1 & Hpcstr1 & Hpr1) | Hpr1].
    - (* ---------------- the path fetched: fall through ---------------- *)
      iApply (wp_blt_x0_fall_s_sconf (CID := CID9) (mword_of_int (SU + 0x16))
                (mword_of_int 346 : mword 13) Ra0 mas (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr1;
                      exact (su_nonneg _ (su_len_range pk1 Hpk1)))
                with "Hcg Hpc []").
      { iApply (suli_016 with "Htext"). }
      iIntros (CID10 Hq10) "Hcg Hpc".
      assert (Hpp1a : add_vec_int (mword_of_int (SU + 0x16) : mword 64) 4
                      = mword_of_int (SU + 0x1a)) by pcw.
      iEval (rewrite Hpp1a) in "Hpc".
      (* ===== +0x1a c.sdsp s1,216(sp) -- slot 3, saved LATE ===== *)
      assert (Hd3 : add_vec (mas !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64
                         (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite Hassp; apply su_frm3).
      iEval (rewrite -Hd3) in "Hf3".
      iApply (wp_csdsp_s_sconf (CID := CID10) (mword_of_int (SU + 0x1a))
                (mword_of_int 27 : mword 6) Rs1 mas (K - 30)%nat u3 b
                with "Hcg Hpc [] Hf3").
      { iApply (suli_01a with "Htext"). }
      iIntros (CID11 Hq11) "Hcg Hpc Hf3".
      iEval (rgne; rewrite Hd3 Hass1) in "Hf3".
      assert (Hpp1c : add_vec_int (mword_of_int (SU + 0x1a) : mword 64) 2
                      = mword_of_int (SU + 0x1c)) by pcw.
      iEval (rewrite Hpp1c) in "Hpc".
      (* THE PROCESS BLOCK, OPENED for the walk. *)
      (* three-way now: [FirstTok.first_tok] parks beside the reference and
         is handed straight back at the rejoins below. *)
      iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1) with "Hpriv")
        as "[Hpnc [Href Hftok]]".
      iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
      iDestruct "Hpnc" as "[Hpidq Hofiles]".
      iDestruct (cwd_ref_held with "Href") as "Hcwdref".
      iEval (cbn [upd_upt pv_cwd]) in "Hcwdref".
      (* ===== +0x1c jal ra,begin_op ===== *)
      iApply (wp_jal_s_sconf (CID := CID11) (mword_of_int (SU + 0x1c)) Rra
                (mword_of_int 2092218 : mword 21) mas (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_01c with "Htext"). }
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (N0 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x1c) : mword 64) 4)]> mas).
      assert (Hjbo : add_vec (mword_of_int (SU + 0x1c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092218 : mword 21))
                     = mword_of_int KernelSyms.begin_op) by pcw.
      iEval (rewrite Hjbo) in "Hpc".
      assert (HN0ra : (N0 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (SU + 0x1c) : mword 64) 4)
        by (rewrite /N0; apply upd_eq).
      assert (HN0regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) N0)
        by (rewrite /N0; apply su_regs_caller; [exact Hcsra | exact Hasregs]).
      iDestruct (cpu_own_transport CID9 CID12 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (BeginOp.wp_begin_op_sconf (CID := CID12) gs jx gl bn g gfs cov
                logstart dev pid (DfracOwn (1/4)) N0 (K - 30)%nat eb b lks
                (upd_upt V P1) ltac:(exact Kbo) Hj Hgl (Hlb "log"%string)
                with "Hcg Hown [] [] Htext Hpc Hlog Hpidq Hprocs").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iIntros (CID13 Hq13 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpidq Hop".
      assert (Hpc20 : ret_pc (N0 !!! Regidx Rra : mword 64)
                      = mword_of_int (SU + 0x20)) by (rewrite HN0ra; pcw).
      iEval (rewrite Hpc20) in "Hpc".
      assert (Hboregs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) mbo)
        by exact (su_regs_cs m sp0 _ _ _ N0 mbo Hcsbo HN0regs).
      (* ===== +0x20 addi a1,s0,-80 -- [name] ===== *)
      iApply (wp_addi4_s_sconf (CID := CID13) (mword_of_int (SU + 0x20)) Ra1 Rs0
                (mword_of_int 4016 : mword 12) mbo (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_020 with "Htext"). }
      iIntros (CID14 Hq14) "Hcg Hpc".
      set (N1 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (mbo !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> mbo).
      assert (HN1a1 : (N1 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10).
      { etransitivity; [ rewrite /N1; apply upd_eq |].
        rewrite (su_regs_s0 _ _ _ _ _ _ Hboregs). apply su_bufname. }
      assert (HN1regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) N1)
        by (rewrite /N1; apply su_regs_caller; [exact Hcsa1 | exact Hboregs]).
      assert (Hpp24 : add_vec_int (mword_of_int (SU + 0x20) : mword 64) 4
                      = mword_of_int (SU + 0x24)) by pcw.
      iEval (rewrite Hpp24) in "Hpc".
      (* ===== +0x24 addi a0,s0,-208 -- [path] ===== *)
      iApply (wp_addi4_s_sconf (CID := CID14) (mword_of_int (SU + 0x24)) Ra0 Rs0
                (mword_of_int 3888 : mword 12) N1 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_024 with "Htext"). }
      iIntros (CID15 Hq15) "Hcg Hpc".
      set (N2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (N1 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 3888 : mword 12)))]> N1).
      assert (HN2a0 : (N2 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26).
      { etransitivity; [ rewrite /N2; apply upd_eq |].
        rewrite (su_regs_s0 _ _ _ _ _ _ HN1regs). apply su_bufpath. }
      assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10)
        by (rewrite /N2 upd_ne; [exact HN1a1 | nz]).
      assert (HN2regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) N2)
        by (rewrite /N2; apply su_regs_caller; [exact Hcsa0 | exact HN1regs]).
      assert (Hpp28 : add_vec_int (mword_of_int (SU + 0x24) : mword 64) 4
                      = mword_of_int (SU + 0x28)) by pcw.
      iEval (rewrite Hpp28) in "Hpc".
      (* ===== +0x28 jal ra,nameiparent ===== *)
      iApply (wp_jal_s_sconf (CID := CID15) (mword_of_int (SU + 0x28)) Rra
                (mword_of_int 2091754 : mword 21) N2 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_028 with "Htext"). }
      iIntros (CID16 Hq16) "Hcg Hpc".
      set (N3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)]> N2).
      assert (Hjnp : add_vec (mword_of_int (SU + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2091754 : mword 21))
                     = mword_of_int KernelSyms.nameiparent) by pcw.
      iEval (rewrite Hjnp) in "Hpc".
      assert (HN3ra : (N3 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)
        by (rewrite /N3; apply upd_eq).
      assert (HN3a0 : (N3 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26)
        by (rewrite /N3 upd_ne; [exact HN2a0 | nz]).
      assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10)
        by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
      assert (HN3regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) N3)
        by (rewrite /N3; apply su_regs_caller; [exact Hcsra | exact HN2regs]).
      iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbN") as (bnm0) "HbN".
      iDestruct (su_nm_split (pa_stk sp0 10) bnm0 with "HbN") as "[Hnm14 Hnm2]".
      iDestruct (su_buf_split (pa_stk sp0 26) bp1 pk1 Hpk1 with "HbP")
        as "[Hbufp Hbufpr]".
      iDestruct "Hop" as (Sb0) "HopS".
      iEval (rewrite su_slots2) in "Hir".
      iDestruct (cpu_own_transport CID13 CID16 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Nameiparent.wp_nameiparent_gen (CID := CID16) gs jx gl gu gd gk
                pd pav pu bn g gfs gi cn gtl ga gf cov logstart bmapstart
                inodestart nib size dev pk1 bp1 bnm0
                MAXOPBLOCKS Sb0 pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                N3 (K - 30)%nat eb b lks
                (upd_upt V P1) ltac:(exact Knp) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
                Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hpcstr1
                (proj2 (su_len_range pk1 Hpk1))
                ltac:(exact (su_walk_need_closes _)) Hj Hgl
                with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hkenv Hitab Hitinv
                      Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                      Hbmres Hpidq Hcwdref [Hbufp] [Hnm14] Hbsl Hir
                      HopS").
      (* nameiparent is eb-generic now; sys_unlink is at [eb = true]. *)
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { iEval (rewrite HN3a0). iExact "Hbufp". }
      { iEval (rewrite HN3a1). iExact "Hnm14". }
      iIntros (CID17 Hq17 mnp n1 Sb1 ok1 nf dpv w1)
        "%Hcsnp Hcg Hown _ _ Hpc Hsbb Hsbi Hpidq Hcwdref
         Hbufp Hnm14 Hbsl %HSb1 %Hw1 %Hn1 HopS Hres1".
      iEval (rewrite HN3a0) in "Hbufp".
      iEval (rewrite HN3a1) in "Hnm14".
      assert (Hpc2c : ret_pc (N3 !!! Regidx Rra : mword 64)
                      = mword_of_int (SU + 0x2c)) by (rewrite HN3ra; pcw).
      iEval (rewrite Hpc2c) in "Hpc".
      assert (Hnpregs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) mnp)
        by exact (su_regs_cs m sp0 _ _ _ N3 mnp Hcsnp HN3regs).
      (* ===== +0x2c c.mv s1,a0 -- s1 = dp ===== *)
      iApply (wp_cmv_s_sconf (CID := CID17) (mword_of_int (SU + 0x2c))
                Rs1 Ra0 mnp (K - 30)%nat b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (suli_02c with "Htext"). }
      iIntros (CID18 Hq18) "Hcg Hpc".
      set (N4 := <[Regidx Rs1 := regval_into_reg
                    (add_vec zero_reg (mnp !!! Regidx Ra0))]> mnp).
      assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64)
                      = (mnp !!! Regidx Ra0 : mword 64))
        by (rewrite /N4 upd_ne; [reflexivity | nz]).
      assert (HN4regs : su_regs m sp0 (mnp !!! Regidx Ra0 : mword 64)
                          (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) N4).
      { rewrite /N4.
        exact (su_regs_wr_s1 m sp0 _ _ _ _ mnp _ (add_vec_zero_l _) Hnpregs). }
      assert (Hpp2e : add_vec_int (mword_of_int (SU + 0x2c) : mword 64) 2
                      = mword_of_int (SU + 0x2e)) by pcw.
      iEval (rewrite Hpp2e) in "Hpc".
      assert (Htge2 : add_vec (mword_of_int (SU + 0x2e) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13
                              (concat_vec (mword_of_int 90 : mword 8) ('b"0"))))
                      = mword_of_int (SU + 0xe2)) by pcw.
      (* ===== +0x2e c.beqz a0 -> ARM B (+0xe2) ===== *)
      destruct ok1.
      + (* ---------- the parent RESOLVED: the SEAM ---------- *)
        iDestruct "Hres1" as "(%Hnp & Hhelddp & Hir1)".
        iDestruct "Hhelddp" as (kd qd dinum gyd)
          "(%Hdpe & %Hkd & %Hdinumc & Hrefdp & #Hshotd & Hrud)".
        assert (Hdpnz : dpv <> (zero_reg : mword 64))
          by (rewrite Hdpe; apply ientry_ne_zero; lia).
        iAssert (inode_held_ty dpv T_DIR) with "[Hrefdp Hrud]" as "Hhelddp".
        { iExists kd, qd, dinum, gyd. iSplitR; [done |]. iSplitR; [done |].
          iSplitR; [done |]. iFrame "Hrefdp Hrud". iExact "Hshotd". }
        iApply (wp_cbeqz_fall_s_sconf (CID := CID18)
                  (mword_of_int (SU + 0x2e)) (mword_of_int 90 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 N4 (K - 30)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HN4a0 (proj1 Hnp);
                        apply (proj2 (eq_vec_false_iff _ _)); exact Hdpnz)
                  with "Hcg Hpc []").
        { iApply (suli_02e with "Htext"). }
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hpp30 : add_vec_int (mword_of_int (SU + 0x2e) : mword 64) 2
                        = mword_of_int (SU + 0x30)) by pcw.
        iEval (rewrite Hpp30) in "Hpc".
        (* the process block, rebuilt whole for the seam *)
        iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
        iCombine "Hpidq Hofiles" as "Hpnc".
        iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                     with "[Hpnc Href Hftok]") as "Hpriv";
          [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
        (* the path buffer, rejoined and renamed *)
        iDestruct (su_buf_join (pa_stk sp0 26) bp1 pk1 Hpk1
                     with "Hbufp Hbufpr") as "HbPj".
        iDestruct (su_bytes_name (pa_stk sp0 26) 128 with "HbPj") as (bpf) "HbPj".
        iDestruct (su_bytes_name (pa_stk sp0 8) 16 with "HbD") as (bd0) "HbD".
        iDestruct (su_bytes_name (pa_stk sp0 29) 16 with "HbE") as (be0) "HbE".
        iDestruct (cpu_own_transport CID17 CID19 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        rewrite (proj1 Hnp) in HN4regs.
        iApply ("Hseamk" $! CID19 N4 P1 n1 Sb1 w1 dpv nf bpf bnm0 bd0 be0
                  u4 u5 u6 u27 u30 with "[%] [%] [%] [%] [%] [%] [%]
                  Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
                  Hir1 Hhelddp HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2
                  HbPj H27 HbE H30 [Hcont]").
        { exact Hal. }
        { exact HN4regs. }
        { exact (eq_trans HN4a0 (proj1 Hnp)). }
        { exact Hupt1. }
        { exact (su_cnt_ok w1 n1 (proj1 Hn1)). }
        { exact Hw1. }
        { exact Hdpnz. }
        { iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID19)
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          iExact "Hcont". }
      + (* ---------- ARM B: nameiparent returned 0 ---------- *)
        iDestruct "Hres1" as "(%Hnpz & Hir2)".
        iApply (wp_cbeqz_taken_s_sconf (CID := CID18)
                  (mword_of_int (SU + 0x2e)) (mword_of_int 90 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 N4 (K - 30)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HN4a0 Hnpz; vm_compute; reflexivity)
                  ltac:(rewrite Htge2; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_02e with "Htext"). }
        iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htge2) in "Hpc".
        (* the buffers, rejoined and renamed for the tail *)
        iDestruct (su_buf_join (pa_stk sp0 26) bp1 pk1 Hpk1
                     with "Hbufp Hbufpr") as "HbPj".
        iDestruct (su_bytes_name (pa_stk sp0 26) 128 with "HbPj") as (bpf) "HbPj".
        iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
          as "HbNj".
        iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
        iDestruct (su_bytes_name (pa_stk sp0 8) 16 with "HbD") as (bd0) "HbD".
        iDestruct (su_bytes_name (pa_stk sp0 29) 16 with "HbE") as (be0) "HbE".
        assert (HN4sp : su_sp sp0 N4) by exact (su_regs_sp _ _ _ _ _ _ HN4regs).
        assert (HN4thr : su_thr m N4) by exact (su_regs_thr _ _ _ _ _ _ HN4regs).
        assert (HN4s2 : (N4 !!! Regidx Rs2 : mword 64)
                        = (m !!! Regidx Rs2 : mword 64))
          by exact (su_regs_s2 _ _ _ _ _ _ HN4regs).
        assert (HN4s3 : (N4 !!! Regidx Rs3 : mword 64)
                        = (m !!! Regidx Rs3 : mword 64))
          by exact (su_regs_s3 _ _ _ _ _ _ HN4regs).
        iDestruct (cpu_own_transport CID17 CID19 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Tails.su_tail_b (CID0 := CID19) gs jx gl gu gd gk pd pav pu bn
                  g gfs cov logstart dev n1 pid (DfracOwn (1/4))
                  m N4 sp0 K eb b lks u4 u5 u6 u27 u30 bd0 bnf bpf be0
                  (upd_upt V P1) ltac:(exact Keo) K30 Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) HN4sp HN4thr HN4s2 HN4s3 Hal
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk [HopS] Hf1 Hf2 Hf3 Hf4
                        Hf5 Hf6 HbD HbNj HbPj H27 HbE H30
                        [Hcont Hbsl Hsbb Hsbi Hsbs Hir2 Hofiles
                         Hcwdref Hftok]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { rewrite /log_op. iExists Sb1. iExact "HopS". }
        iEval (rewrite /wp_next).
        iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                             Hpc Hpidq".
        iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
        iCombine "Hpidq Hofiles" as "Hpnc".
        iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                     with "[Hpnc Href Hftok]") as "Hpriv";
          [iSplitL "Hpnc"; [iExact "Hpnc" | iFrame "Href Hftok"] |].
        iEval (rewrite -su_slots2) in "Hir2".
        iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hbsl Hsbb Hsbi Hsbs Hir2 Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt1. }
        { left. rewrite Ha0f. reflexivity. }
    - (* ---------------- ARM A: argstr returned -1 ---------------- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID9) (mword_of_int (SU + 0x16))
                (mword_of_int 346 : mword 13) Ra0 mas (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr1; exact su_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_016 with "Htext"). }
      iNext. iIntros (CID10 Hq10) "Hcg Hpc".
      assert (Htga : add_vec (mword_of_int (SU + 0x16) : mword 64)
                       (sign_extend' 64 (mword_of_int 346 : mword 13))
                     = mword_of_int (SU + 0x170)) by pcw.
      iEval (rewrite Htga) in "Hpc".
      iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbN") as (bnf) "HbN".
      iDestruct (su_bytes_name (pa_stk sp0 8) 16 with "HbD") as (bd0) "HbD".
      iDestruct (su_bytes_name (pa_stk sp0 29) 16 with "HbE") as (be0) "HbE".
      iApply (Tails.su_tail_a (CID0 := CID10) m mas sp0 K b (proc_addr jx)
                u3 u4 u5 u6 u27 u30 bd0 bnf bp1 be0
                K30 Kpop ltac:(reflexivity) Hassp Hasthr Hass1 Hass2 Hass3 Hal
                with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbN HbP H27
                      HbE H30
                      [Hcont Hown Hbsl Hsbb Hsbi Hsbs Hir Hpriv]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CID9 CIDy 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown [] [] Hpc
                Hbsl Hsbb Hsbi Hsbs Hir Hpriv [%]").
      { exact Hcsf. }
      { exact Hupt1. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { left. rewrite Ha0f. reflexivity. }
  Qed.

  (* the [&off] argument's address, re-based on the PUSHED sp so that
     [StackOwn.stack_off_nonzero] applies: slot 27's upper word is
     [sp + 28] once the frame is down.  NEVER [vm_compute] this goal whole
     ([su_offcell]'s warning); compose the shifts symbolically first. *)
  Lemma su_offcell_sp `{GEN : GenId} (X : mword 64) :
    pa_add (pa_stk X 27) 4 = pa_add (pa_stk X 30) 28.
  Proof.
    unfold pa_add, pa_stk. rewrite !avi_assoc. unfold add_vec_int.
    f_equal; try (apply bv_eq; vm_compute; reflexivity).
  Qed.

  (* the sp bound the capability underwrites, [ProofSysClose.sc_sp_bounds]'
     shape.  [0 < k] is mandatory: [trap_res false] is nothing, so at the
     interrupts-off arm the caller's own slots are all that bound sp. *)
  Lemma su_sp_bounds `{GEN : GenId} `{CIDh : CpuId} (M : regfile) (k : nat)
      (b : bool) (pp : mword 64) :
    (0 < k)%nat ->
    sie_cap_gpr KT1 M k b pp -∗
    ⌜(8 <= uint (M !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds (KTR := KT1) _ (trap_res b + k)%nat with "Hstk").
    destruct b; unfold trap_res; lia.
  Qed.

  (* ================================================================== *)
  (*  THE TWO namecmp REFUSALS' ENTRY INTO [bad:], as ONE lemma.          *)
  (*                                                                     *)
  (*  ARMS C (+0x44) and C' (+0x58) arrive at +0x15a holding exactly the  *)
  (*  same things -- neither has saved s2 or s3, neither has run          *)
  (*  dirlookup, so [ic_loaded] is still PACKED and the reference         *)
  (*  allowance is still whole -- so unlike ARM D and ARM E they are ONE  *)
  (*  entry written twice, not two.  The process block travels as the     *)
  (*  pid quarter plus its CLOSER, which is what keeps the cwd half out   *)
  (*  of this interface entirely.                                        *)
  (* ================================================================== *)
  Lemma su_w2_bad `{GEN : GenId} `{CID0 : CpuId}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (kk : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dqb dqs dqbs : dfrac)
      (V : pprivate) (P1 : uptd)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string)
      (w4 w5 w6 w27 w30 : mword 64) (bd nfx bnm0 bp be : nat -> bv 8) :
    (K_iunlockput <= K - 30)%nat -> (K_end_op <= K - 30)%nat ->
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= u)%nat ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_sp sp0 M -> su_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = ientry kk ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    su_al sp0 ->
    eb = true ->
    uptd_ext (pv_upt V) P1 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0x15a)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string
                     (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [su_tail_bad]'s iunlockput *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    proc_priv_bare (proc_addr jx) pidv (upd_upt V P1) -∗
    (proc_priv_bare (proc_addr jx) pidv (upd_upt V P1) -∗
       proc_priv gf (proc_addr jx) pidv (upd_upt V P1)) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    iref_slots 1 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nfx jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pidv (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 HMs2
           HMs3 Hal Heb Hupt1.
    iIntros "Hcg Hown #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
             #Hesck #Hireg #Hropen #Hslkk Hslkd Hdep Hidev Hiinum Hivalid Hload
             #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hsbs #Hbmres Hpidq Hpre #Hprocs #Hdev
             #Hgeo
             #Hdlk Hbsl Hir Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27
             HbE H30 Hcont".
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nfx with "Hnm14 Hnm2") as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iApply (Tails.su_tail_bad (CID0 := CID0) gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib size
              dev kk qi s gy inum dn bm u pidv (DfracOwn (1/4)) dqb dqs
              m M sp0 K eb b lks w4 w5 w6 w27 w30 bd bnf bp be
              (upd_upt V P1) HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs2 HMs3 Hal
              with "Hcg Hown [] [] Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen Hitab
                    Hitinv Hesck Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum
                    Hivalid Hload Hshot Hfrz Hkeep Hru Hsbb Hsbi Hbmres Hpidq
                    Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj
                    HbP H27 HbE H30 [Hcont Hpre Hsbs Hir]").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                     Hpc Hpidq Hsbb Hsbi Hbsl Hislot".
    iDestruct ("Hpre" with "Hpidq") as "Hpriv".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hbsl Hsbb Hsbi Hsbs [Hir Hislot] Hpriv [%]").
    { exact Hcsf. }
    { exact Hupt1. }
    { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
      rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
    { left. rewrite Ha0f. reflexivity. }
  Qed.

  (* ================================================================== *)
  (*  W2: +0x30 .. +0x6e -- ilock(dp), the two namecmp refusals,         *)
  (*                        dirlookup(dp, name, &off)                    *)
  (*                                                                     *)
  (*    +0x30 jal ilock                                                  *)
  (*    +0x34 auipc a1,2 ; +0x38 addi a1,a1,1656   ("." @ 0x800075e0)    *)
  (*    +0x3c addi a0,s0,-80 ; +0x40 jal namecmp                          *)
  (*    +0x44 beq a0,x0 -> +0x15a                        [ARM C]         *)
  (*    +0x48 auipc a1,2 ; +0x4c addi a1,a1,1644   (".." @ 0x800075e8)   *)
  (*    +0x50 addi a0,s0,-80 ; +0x54 jal namecmp                          *)
  (*    +0x58 beq a0,x0 -> +0x15a                        [ARM C']        *)
  (*    +0x5c c.sdsp s2,208(sp)      (the SECOND shrink-wrapped save)    *)
  (*    +0x5e addi a2,s0,-212        (&off -- slot 27's UPPER word)      *)
  (*    +0x62 addi a1,s0,-80 ; +0x66 c.mv a0,s1                           *)
  (*    +0x68 jal dirlookup ; +0x6c c.mv s2,a0                            *)
  (*    +0x6e beq a0,x0 -> +0x158                        [ARM D]         *)
  (*                                                                     *)
  (*  THE TWO REFUSALS ARE WHERE FINDING 1 IS PAID FOR.  Their FALL-      *)
  (*  THROUGH is what says the name dirlookup then matches is neither     *)
  (*  dot, and that -- against [DirView.dir_orphan_clean], which rides in *)
  (*  [ic_loaded] -- is what forces [di_nlink dp <> 0] at the zeroing.    *)
  (*  Both facts therefore cross the seam; nothing in W2 spends them.     *)
  (*                                                                     *)
  (*  ARM C and ARM C' HOLD [ic_loaded] PACKED: neither has run           *)
  (*  dirlookup, so the bundle ilock returned has never been opened and   *)
  (*  [su_tail_bad] takes it as it stands.  ARM D has, and repacks.       *)
  (* ================================================================== *)
  Lemma su_w2 `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (V : pprivate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (dpv : mword 64)
      (nf bnm0 bp bd be : nat -> bv 8)
      (w4 w5 w6 w27 w30 : mword 64)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    inodestart = icfg_ist ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
            (m !!! Regidx Rs3 : mword 64) M ->
    (M !!! Regidx Ra0 : mword 64) = dpv ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext (pv_upt V) P1 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (SU + 0x30)) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    iref_slots 1 -∗
    proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
    inode_held_ty dpv T_DIR -∗
    log_opS g n1 Sb1 -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] w4 -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₈[KT1] w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    (* ---- THE SEAM: the fall-through, at +0x72 with [ip] resolved ---- *)
    (∀ (CIDs : CpuId) (M2 : regfile)
       (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
       (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
       (datd : nat -> list (bv 8)) (lo : bv 32),
       ⌜su_regs m sp0 (ientry kd) (ientry ks)
                (m !!! Regidx Rs3 : mword 64) M2⌝ -∗
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜(ks < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dinum < 16 * Z.of_nat nib⌝ -∗
       ⌜di_type dnd = SpecDirlookup.T_DIR⌝ -∗
       ⌜inode_ok cov logstart dnd bmd datd⌝ -∗
       (* durable-disk 2b-inode-3: the payload's record-only facts *)
       ⌜inode_rec_local dnd⌝ -∗
       ⌜dir_ok icfg_nib dnd datd⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dinum) dnd datd⌝ -∗
       ⌜dir_orphan_clean dnd datd⌝ -∗
       ⌜dir_uniq dnd datd⌝ -∗
       ⌜bname 14 nf <> dot_name⌝ -∗
       ⌜bname 14 nf <> dotdot_name⌝ -∗
       ⌜dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
                  (bname 14 nf) = Some kk⌝ -∗
       (* the [a0 = ip] W3's [ilock] call reads, and slot 27's own
          alignment (taken off the points-to at the split; the join at the
          epilogue needs it back) *)
       ⌜(M2 !!! Regidx Ra0 : mword 64) = ientry ks⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true⌝ -∗
       sie_cap_gpr KT1 M2 (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x72)) -∗
       fs_crash_seam cov logstart -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
       (* ---- [dp], LOCKED and OPEN ---- *)
       is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                        (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
       ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks gfs (bv_unsigned dinum) dnd bmd datd -∗
       dinode_at gi dinum dnd -∗
       inode_meta (ientry kd) dnd -∗
       inode_addrs (ientry kd) (bm_cells bmd) -∗
       ind_res gfs bmd -∗
       inode_blocks gfs bmd datd -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dinum) (dv_of dnd datd) -∗
       fv_ride (bv_unsigned dinum) (fv_of dnd datd) -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L gfs) (bv_unsigned dinum)
                (era_node dnd bmd datd) -∗
       ity_shot gyd (di_type dnd) -∗
       (* the payload's freeze token (§3.9, RULING A-prime) *)
       ifreeze_off (bv_unsigned dinum) -∗
       inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
       (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
       runit_any (bv_unsigned dinum) -∗
       (* ---- [ip], REFERENCED (dirlookup's iget) ---- *)
       inode_ref ks qs dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       (* ...with the unit that iget minted with it (item 7a-wire) *)
       runit_any
         (bv_unsigned
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
       log_opS g n1 Sb1 -∗
       (* ---- the frame, with slot 4 filled and slot 27 SPLIT ---- *)
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] w5 -∗
       (pa_stk sp0 6) ↦₈[KT1] w6 -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 0 2,
          pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
       ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
       (pa_stk sp0 27) ↦₄[KT1] lo -∗
       (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
         (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
       (pa_stk sp0 30) ↦₈[KT1] w30 -∗
       (* the caller's own exit, handed BACK *)
       wp_next (CID0 := CIDs) true (proc_addr jx) (fun (CIDx : CpuId) =>
         ∀ (mf : regfile) (P' : uptd),
             ⌜callee_saved m mf⌝ -∗
             ⌜uptd_ext (pv_upt V) P'⌝ -∗
             sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
             cpu_own 0 eb (proc_addr jx) b lks -∗
             trap_csrs_ext KT1 eb -∗
             cpu_claim_ext eb (proc_addr jx) -∗
             pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
             bslots 3 -∗
             sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
             sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
             sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
             iref_slots SpecSysUnlink.sys_unlink_slots -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
             ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
             WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hregs Hma0 Hn1 Hupt1.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpenv2 #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv Hheld HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE H30
             Hseamk Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hiu : (iput_units <= n1)%nat).
    { pose proof (su_u1_ge9 w1) as H9. unfold iput_units. lia. }
    (* ---- dp's reference: unpacked, and shed AT THE GENERATION the type
       one-shot names.  That is what lets [ity_shot_agree] below turn
       nameiparent's promise into [di_type dnd = T_DIR] at ilock's own
       record, which is dirlookup's first premise. ---- *)
    iDestruct "Hheld" as (kd qd dinum gyd)
      "(%Hdpe & %Hkd & %Hdinumc & Hrefdp & #Hshotd & Hrud)".
    assert (Hdinb : bv_unsigned dinum < 16 * Z.of_nat nib)
      by (rewrite Hcnib; exact Hdinumc).
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    iEval (rewrite -Hcdev) in "Hrefdp".
    iEval (rewrite su_shed_gen) in "Hrefdp".
    iDestruct "Hrefdp" as "[Hkeepd Hshrd]".
    iDestruct (inode_ref_short_gen_forget with "Hkeepd") as "Hkeepd".
    iDestruct (su_esc_acc cn gfs gi cov logstart kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (su_slk_acc cn kd Hkd with "Hslks") as (gild gisld) "#Hslkd0".
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* the process block, opened for the callees' pid fraction *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    (* THE CLOSER, built once: every arm below hands the BLOCK back and wants
       [proc_priv] whole, and nothing between here and the seam touches the
       fd table or the cwd reference. *)
    iAssert (proc_priv_bare (proc_addr jx) pid (upd_upt V P1) -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* the register facts the whole block rides on *)
    assert (HMs1 : (M !!! Regidx Rs1 : mword 64) = dpv)
      by exact (su_regs_s1 _ _ _ _ _ _ Hregs).
    assert (HMsp : su_sp sp0 M) by exact (su_regs_sp _ _ _ _ _ _ Hregs).
    (* ===== +0x30 jal ra,ilock ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SU + 0x30)) Rra
              (mword_of_int 2089532 : mword 21) M (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_030 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x30) : mword 64) 4)]> M).
    assert (Hjil : add_vec (mword_of_int (SU + 0x30) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089532 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Hjil) in "Hpc".
    assert (HR0ra : (R0 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x30) : mword 64) 4)
      by (rewrite /R0; apply upd_eq).
    assert (HR0a0 : (R0 !!! Regidx Ra0 : mword 64) = ientry kd).
    { rewrite /R0 upd_ne; [| nz]. rewrite Hma0. exact Hdpe. }
    assert (HR0regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) R0)
      by (rewrite /R0; apply su_regs_caller; [exact Hcsra | exact Hregs]).
    iDestruct (cpu_own_transport CID0 CID1 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Ilock.wp_ilock_sconf (CID := CID1) gs jx gl gu gd gk pd pav pu bn
              gfs gi cn gild gisld cov logstart inodestart nib kd (qd/2)%Qp
              gyd PlainK dev dinum pid (DfracOwn (1/4)) dqs R0 (K - 30)%nat eb b
              lks
              (upd_upt V P1) ltac:(exact Kil) Hkd Hgeom Hist0 Hdiblk Hdinb Hj Hgl HR0a0
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hitinv Hescd Hireg
                    Hslkd0 Hshrd Hrud Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID2 Hq2 mil dnd bmd fld)
      "%Hcsil Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkdd Hdep
       Hidev Hiinum Hivalid Hload #Hshotl Hfrz %Hfld Hrud %Hilkpd".
    assert (Hpc34 : ret_pc (R0 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x34)) by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc34) in "Hpc".
    assert (Hilregs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) mil)
      by exact (su_regs_cs m sp0 _ _ _ R0 mil Hcsil HR0regs).
    (* THE PARENT IS A DIRECTORY, and nameiparent said so.  [ity_shot] is a
       one-shot per generation, so the two readings agree. *)
    iDestruct (ity_shot_agree with "Hshotd Hshotl") as %Htyd.
    assert (Htydir : di_type dnd = SpecDirlookup.T_DIR) by (symmetry; exact Htyd).
    assert (Htydz : bv_unsigned (di_type dnd) = T_DIR_z)
      by exact (su_tdir_zof _ Htydir).
    (* ===== +0x34 auipc a1,2 ===== *)
    iApply (wp_auipc_s_sconf (CID := CID2) (mword_of_int (SU + 0x34)) Ra1
              (mword_of_int 2 : mword 20) mil (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_034 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (R1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (SU + 0x34) : mword 64)
                     (auipc_off (mword_of_int 2 : mword 20)))]> mil).
    assert (HR1a1 : (R1 !!! Regidx Ra1 : mword 64)
                    = add_vec (mword_of_int (SU + 0x34) : mword 64)
                        (auipc_off (mword_of_int 2 : mword 20)))
      by (rewrite /R1; apply upd_eq).
    assert (HR1regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) R1)
      by (rewrite /R1; apply su_regs_caller; [exact Hcsa1 | exact Hilregs]).
    assert (Hpp38 : add_vec_int (mword_of_int (SU + 0x34) : mword 64) 4
                    = mword_of_int (SU + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x38 addi a1,a1,1656 -- the "." literal ===== *)
    iApply (wp_addi4_s_sconf (CID := CID3) (mword_of_int (SU + 0x38)) Ra1 Ra1
              (mword_of_int 1554 : mword 12) R1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_038 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (R1 !!! Regidx Ra1)
                     (sign_extend' 64 (mword_of_int 1554 : mword 12)))]> R1).
    assert (HR2a1 : (R2 !!! Regidx Ra1 : mword 64)
                    = (mword_of_int su_dot_addr : mword 64)).
    { etransitivity; [ rewrite /R2; apply upd_eq |].
      rewrite HR1a1. apply su_dotaddr. }
    assert (HR2regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) R2)
      by (rewrite /R2; apply su_regs_caller; [exact Hcsa1 | exact HR1regs]).
    assert (Hpp3c : add_vec_int (mword_of_int (SU + 0x38) : mword 64) 4
                    = mword_of_int (SU + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c addi a0,s0,-80 -- [name] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID4) (mword_of_int (SU + 0x3c)) Ra0 Rs0
              (mword_of_int 4016 : mword 12) R2 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_03c with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R2 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R2).
    assert (HR3a0 : (R3 !!! Regidx Ra0 : mword 64) = pa_stk sp0 10).
    { etransitivity; [ rewrite /R3; apply upd_eq |].
      rewrite (su_regs_s0 _ _ _ _ _ _ HR2regs). apply su_bufname. }
    assert (HR3a1 : (R3 !!! Regidx Ra1 : mword 64)
                    = (mword_of_int su_dot_addr : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR3regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) R3)
      by (rewrite /R3; apply su_regs_caller; [exact Hcsa0 | exact HR2regs]).
    assert (Hpp40 : add_vec_int (mword_of_int (SU + 0x3c) : mword 64) 4
                    = mword_of_int (SU + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 jal ra,namecmp ===== *)
    iApply (wp_jal_s_sconf (CID := CID5) (mword_of_int (SU + 0x40)) Rra
              (mword_of_int 2091006 : mword 21) R3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_040 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x40) : mword 64) 4)]> R3).
    assert (Hjnc1 : add_vec (mword_of_int (SU + 0x40) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091006 : mword 21))
                    = mword_of_int KernelSyms.namecmp) by pcw.
    iEval (rewrite Hjnc1) in "Hpc".
    assert (HR4ra : (R4 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x40) : mword 64) 4)
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : (R4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 10)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4a1 : (R4 !!! Regidx Ra1 : mword 64)
                    = (mword_of_int su_dot_addr : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a1 | nz]).
    assert (HR4regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) R4)
      by (rewrite /R4; apply su_regs_caller; [exact Hcsra | exact HR3regs]).
    iPoseProof (su_dot_window (mword_of_int su_dot_addr) eq_refl with "Hdata")
      as "Hdotw".
    iApply (Namecmp.wp_namecmp_sconf (CID := CID6) KT1 KT0 R4 nf su_dot_f
              (K - 30)%nat (DfracOwn 1) DfracDiscarded b (proc_addr jx)
              ltac:(exact Knc) with "Hcg Htext Hpc [Hnm14] [Hdotw]").
    { iEval (rewrite HR4a0). iExact "Hnm14". }
    { iEval (rewrite HR4a1). iExact "Hdotw". }
    iIntros (CID7 Hq7 mn1) "%Hcsn1 Hcg Hpc Hnm14 _ %Hnc1".
    iEval (rewrite HR4a0) in "Hnm14".
    assert (Hpc44 : ret_pc (R4 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x44)) by (rewrite HR4ra; pcw).
    iEval (rewrite Hpc44) in "Hpc".
    assert (Hn1regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) mn1)
      by exact (su_regs_cs m sp0 _ _ _ R4 mn1 Hcsn1 HR4regs).
    iDestruct (cpu_own_transport CID2 CID7 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    assert (Htgbad1 : add_vec (mword_of_int (SU + 0x44) : mword 64)
                        (sign_extend' 64 (mword_of_int 278 : mword 13))
                      = mword_of_int (SU + 0x15a)) by pcw.
    (* ===== +0x44 beq a0,x0 -> [bad:] ===== *)
    destruct (decide (bname 14 nf = dot_name)) as [Hisdot | Hnotdot].
    - (* ---------------- ARM C: the name IS "." ---------------- *)
      iApply (wp_beqz_x0_taken_s_sconf (CID := CID7) (mword_of_int (SU + 0x44))
                (mword_of_int 278 : mword 13) Ra0 mn1 (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne;
                      rewrite (proj2 Hnc1
                        ltac:(rewrite Hisdot su_dot_name; reflexivity));
                      vm_compute; reflexivity)
                ltac:(rewrite Htgbad1; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_044 with "Htext"). }
      iIntros (CID8 Hq8). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgbad1) in "Hpc".
      iDestruct (cpu_own_transport CID7 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (su_w2_bad (CID0 := CID8) gf gs jx gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gild gisld cov logstart bmapstart inodestart nib size
                dev kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd n1 pid
                dqb dqs dqbs V P1 m mn1 sp0 K eb b lks w4 w5 w6 w27 w30
                bd nf bnm0 bp be
                Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                (su_regs_sp _ _ _ _ _ _ Hn1regs) (su_regs_thr _ _ _ _ _ _ Hn1regs)
                ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn1regs); exact Hdpe)
                (su_regs_s2 _ _ _ _ _ _ Hn1regs)
                (su_regs_s3 _ _ _ _ _ _ Hn1regs) Hal Heb Hupt1
                with "Hcg Hown Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen Hitab
                      Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd Hdep Hidev
                      Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb Hsbi Hsbs
                      Hbmres Hpidq Hpre Hprocs Hdev Hgeo Hdlk
                      [Hbs1 Hbs2] Hir [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD
                      Hnm14 Hnm2 HbP H27 HbE H30 Hcont").
      { iApply su_bs3. iFrame "Hbs1 Hbs2". }
      { rewrite /log_op. iExists Sb1. iExact "HopS". }
    - (* ---------------- the name is not "." : fall through ---------------- *)
      iApply (wp_beqz_x0_fall_s_sconf (CID := CID7) (mword_of_int (SU + 0x44))
                (mword_of_int 278 : mword 13) Ra0 mn1 (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne; apply (proj2 (eq_vec_false_iff _ _));
                      intro Hc; apply Hnotdot; rewrite -su_dot_name;
                      apply (proj1 Hnc1);
                      rewrite Hc; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_044 with "Htext"). }
      iIntros (CID8 Hq8) "Hcg Hpc".
      assert (Hpp48 : add_vec_int (mword_of_int (SU + 0x44) : mword 64) 4
                      = mword_of_int (SU + 0x48)) by pcw.
      iEval (rewrite Hpp48) in "Hpc".
      (* ===== +0x48 auipc a1,2 ===== *)
      iApply (wp_auipc_s_sconf (CID := CID8) (mword_of_int (SU + 0x48)) Ra1
                (mword_of_int 2 : mword 20) mn1 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_048 with "Htext"). }
      iIntros (CID9 Hq9) "Hcg Hpc".
      set (R5 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (mword_of_int (SU + 0x48) : mword 64)
                       (auipc_off (mword_of_int 2 : mword 20)))]> mn1).
      assert (HR5a1 : (R5 !!! Regidx Ra1 : mword 64)
                      = add_vec (mword_of_int (SU + 0x48) : mword 64)
                          (auipc_off (mword_of_int 2 : mword 20)))
        by (rewrite /R5; apply upd_eq).
      assert (HR5regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) R5)
        by (rewrite /R5; apply su_regs_caller; [exact Hcsa1 | exact Hn1regs]).
      assert (Hpp4c : add_vec_int (mword_of_int (SU + 0x48) : mword 64) 4
                      = mword_of_int (SU + 0x4c)) by pcw.
      iEval (rewrite Hpp4c) in "Hpc".
      (* ===== +0x4c addi a1,a1,1644 -- the ".." literal ===== *)
      iApply (wp_addi4_s_sconf (CID := CID9) (mword_of_int (SU + 0x4c)) Ra1 Ra1
                (mword_of_int 1542 : mword 12) R5 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_04c with "Htext"). }
      iIntros (CID10 Hq10) "Hcg Hpc".
      set (R6 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (R5 !!! Regidx Ra1)
                       (sign_extend' 64 (mword_of_int 1542 : mword 12)))]> R5).
      assert (HR6a1 : (R6 !!! Regidx Ra1 : mword 64)
                      = (mword_of_int su_dotdot_addr : mword 64)).
      { etransitivity; [ rewrite /R6; apply upd_eq |].
        rewrite HR5a1. apply su_dotdotaddr. }
      assert (HR6regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) R6)
        by (rewrite /R6; apply su_regs_caller; [exact Hcsa1 | exact HR5regs]).
      assert (Hpp50 : add_vec_int (mword_of_int (SU + 0x4c) : mword 64) 4
                      = mword_of_int (SU + 0x50)) by pcw.
      iEval (rewrite Hpp50) in "Hpc".
      (* ===== +0x50 addi a0,s0,-80 ===== *)
      iApply (wp_addi4_s_sconf (CID := CID10) (mword_of_int (SU + 0x50)) Ra0 Rs0
                (mword_of_int 4016 : mword 12) R6 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_050 with "Htext"). }
      iIntros (CID11 Hq11) "Hcg Hpc".
      set (R7 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (R6 !!! Regidx Rs0)
                       (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R6).
      assert (HR7a0 : (R7 !!! Regidx Ra0 : mword 64) = pa_stk sp0 10).
      { etransitivity; [ rewrite /R7; apply upd_eq |].
        rewrite (su_regs_s0 _ _ _ _ _ _ HR6regs). apply su_bufname. }
      assert (HR7a1 : (R7 !!! Regidx Ra1 : mword 64)
                      = (mword_of_int su_dotdot_addr : mword 64))
        by (rewrite /R7 upd_ne; [exact HR6a1 | nz]).
      assert (HR7regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) R7)
        by (rewrite /R7; apply su_regs_caller; [exact Hcsa0 | exact HR6regs]).
      assert (Hpp54 : add_vec_int (mword_of_int (SU + 0x50) : mword 64) 4
                      = mword_of_int (SU + 0x54)) by pcw.
      iEval (rewrite Hpp54) in "Hpc".
      (* ===== +0x54 jal ra,namecmp ===== *)
      iApply (wp_jal_s_sconf (CID := CID11) (mword_of_int (SU + 0x54)) Rra
                (mword_of_int 2090986 : mword 21) R7 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_054 with "Htext"). }
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (R8 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x54) : mword 64) 4)]> R7).
      assert (Hjnc2 : add_vec (mword_of_int (SU + 0x54) : mword 64)
                        (sign_extend' 64 (mword_of_int 2090986 : mword 21))
                      = mword_of_int KernelSyms.namecmp) by pcw.
      iEval (rewrite Hjnc2) in "Hpc".
      assert (HR8ra : (R8 !!! Regidx Rra : mword 64)
                      = add_vec_int (mword_of_int (SU + 0x54) : mword 64) 4)
        by (rewrite /R8; apply upd_eq).
      assert (HR8a0 : (R8 !!! Regidx Ra0 : mword 64) = pa_stk sp0 10)
        by (rewrite /R8 upd_ne; [exact HR7a0 | nz]).
      assert (HR8a1 : (R8 !!! Regidx Ra1 : mword 64)
                      = (mword_of_int su_dotdot_addr : mword 64))
        by (rewrite /R8 upd_ne; [exact HR7a1 | nz]).
      assert (HR8regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) R8)
        by (rewrite /R8; apply su_regs_caller; [exact Hcsra | exact HR7regs]).
      iPoseProof (su_dotdot_window (mword_of_int su_dotdot_addr) eq_refl
                    with "Hdata") as "Hddw".
      iApply (Namecmp.wp_namecmp_sconf (CID := CID12) KT1 KT0 R8 nf su_dotdot_f
                (K - 30)%nat (DfracOwn 1) DfracDiscarded b (proc_addr jx)
                ltac:(exact Knc) with "Hcg Htext Hpc [Hnm14] [Hddw]").
      { iEval (rewrite HR8a0). iExact "Hnm14". }
      { iEval (rewrite HR8a1). iExact "Hddw". }
      iIntros (CID13 Hq13 mn2) "%Hcsn2 Hcg Hpc Hnm14 _ %Hnc2".
      iEval (rewrite HR8a0) in "Hnm14".
      assert (Hpc58 : ret_pc (R8 !!! Regidx Rra : mword 64)
                      = mword_of_int (SU + 0x58)) by (rewrite HR8ra; pcw).
      iEval (rewrite Hpc58) in "Hpc".
      assert (Hn2regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                          (m !!! Regidx Rs3 : mword 64) mn2)
        by exact (su_regs_cs m sp0 _ _ _ R8 mn2 Hcsn2 HR8regs).
      iDestruct (cpu_own_transport CID7 CID13 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      assert (Htgbad2 : add_vec (mword_of_int (SU + 0x58) : mword 64)
                          (sign_extend' 64 (mword_of_int 258 : mword 13))
                        = mword_of_int (SU + 0x15a)) by pcw.
      (* ===== +0x58 beq a0,x0 -> [bad:] ===== *)
      destruct (decide (bname 14 nf = dotdot_name)) as [Hisdd | Hnotdd].
      + (* ---------------- ARM C': the name IS ".." ---------------- *)
        iApply (wp_beqz_x0_taken_s_sconf (CID := CID13)
                  (mword_of_int (SU + 0x58)) (mword_of_int 258 : mword 13) Ra0
                  mn2 (K - 30)%nat b ltac:(nz)
                  ltac:(rgne;
                        rewrite (proj2 Hnc2
                          ltac:(rewrite Hisdd su_dotdot_name; reflexivity));
                        vm_compute; reflexivity)
                  ltac:(rewrite Htgbad2; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_058 with "Htext"). }
        iIntros (CID14 Hq14). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgbad2) in "Hpc".
        iDestruct (cpu_own_transport CID13 CID14 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID14)
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (su_w2_bad (CID0 := CID14) gf gs jx gl gu gd gk pd pav pu bn g
                  gfs gi cn gtl gild gisld cov logstart bmapstart inodestart
                  nib size dev kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd
                  n1 pid dqb dqs dqbs V P1 m mn2 sp0 K eb b lks
                  w4 w5 w6 w27 w30 bd nf bnm0 bp be
                  Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                  Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                  (su_regs_sp _ _ _ _ _ _ Hn2regs)
                  (su_regs_thr _ _ _ _ _ _ Hn2regs)
                  ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn2regs); exact Hdpe)
                  (su_regs_s2 _ _ _ _ _ _ Hn2regs)
                  (su_regs_s3 _ _ _ _ _ _ Hn2regs) Hal Heb Hupt1
                  with "Hcg Hown Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen Hitab
                        Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd Hdep Hidev
                        Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb Hsbi Hsbs
                        Hbmres Hpidq Hpre Hprocs Hdev Hgeo Hdlk
                        [Hbs1 Hbs2] Hir [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD
                        Hnm14 Hnm2 HbP H27 HbE H30 Hcont").
        { iApply su_bs3. iFrame "Hbs1 Hbs2". }
        { rewrite /log_op. iExists Sb1. iExact "HopS". }
      + (* -------- the name is neither dot: on to dirlookup -------- *)
        iApply (wp_beqz_x0_fall_s_sconf (CID := CID13)
                  (mword_of_int (SU + 0x58)) (mword_of_int 258 : mword 13) Ra0
                  mn2 (K - 30)%nat b ltac:(nz)
                  ltac:(rgne; apply (proj2 (eq_vec_false_iff _ _));
                        intro Hc; apply Hnotdd; rewrite -su_dotdot_name;
                        apply (proj1 Hnc2);
                        rewrite Hc; apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_058 with "Htext"). }
        iIntros (CID14 Hq14) "Hcg Hpc".
        assert (Hpp5c : add_vec_int (mword_of_int (SU + 0x58) : mword 64) 4
                        = mword_of_int (SU + 0x5c)) by pcw.
        iEval (rewrite Hpp5c) in "Hpc".
        (* ===== +0x5c c.sdsp s2,208(sp) -- slot 4, saved LATER ===== *)
        assert (Hd4 : add_vec (mn2 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64
                           (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                      = pa_stk sp0 4)
          by (rewrite (su_regs_sp _ _ _ _ _ _ Hn2regs); apply su_frm4).
        iEval (rewrite -Hd4) in "Hf4".
        iApply (wp_csdsp_s_sconf (CID := CID14) (mword_of_int (SU + 0x5c))
                  (mword_of_int 26 : mword 6) Rs2 mn2 (K - 30)%nat w4 b
                  with "Hcg Hpc [] Hf4").
        { iApply (suli_05c with "Htext"). }
        iIntros (CID15 Hq15) "Hcg Hpc Hf4".
        iEval (rgne; rewrite Hd4 (su_regs_s2 _ _ _ _ _ _ Hn2regs)) in "Hf4".
        assert (Hpp5e : add_vec_int (mword_of_int (SU + 0x5c) : mword 64) 2
                        = mword_of_int (SU + 0x5e)) by pcw.
        iEval (rewrite Hpp5e) in "Hpc".
        (* the [off] cell, carved out of slot 27's UPPER word *)
        iDestruct (word_pointsto_aligned_p with "H27") as %Hal27.
        iDestruct (su_off_split sp0 w27 with "H27") as "[H27lo H27hi]".
        (* ===== +0x5e addi a2,s0,-212 -- &off ===== *)
        iApply (wp_addi4_s_sconf (CID := CID15) (mword_of_int (SU + 0x5e)) Ra2
                  Rs0 (mword_of_int 3884 : mword 12) mn2 (K - 30)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (suli_05e with "Htext"). }
        iIntros (CID16 Hq16) "Hcg Hpc".
        set (R9 := <[Regidx Ra2 := regval_into_reg
                      (add_vec (mn2 !!! Regidx Rs0)
                         (sign_extend' 64 (mword_of_int 3884 : mword 12)))]> mn2).
        assert (HR9a2 : (R9 !!! Regidx Ra2 : mword 64)
                        = pa_add (pa_stk sp0 27) 4).
        { etransitivity; [ rewrite /R9; apply upd_eq |].
          rewrite (su_regs_s0 _ _ _ _ _ _ Hn2regs). apply su_offcell. }
        assert (HR9regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                            (m !!! Regidx Rs3 : mword 64) R9)
          by (rewrite /R9; apply su_regs_caller; [exact Hcsa2 | exact Hn2regs]).
        assert (Hpp62 : add_vec_int (mword_of_int (SU + 0x5e) : mword 64) 4
                        = mword_of_int (SU + 0x62)) by pcw.
        iEval (rewrite Hpp62) in "Hpc".
        (* ===== +0x62 addi a1,s0,-80 ===== *)
        iApply (wp_addi4_s_sconf (CID := CID16) (mword_of_int (SU + 0x62)) Ra1
                  Rs0 (mword_of_int 4016 : mword 12) R9 (K - 30)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (suli_062 with "Htext"). }
        iIntros (CID17 Hq17) "Hcg Hpc".
        set (R10 := <[Regidx Ra1 := regval_into_reg
                       (add_vec (R9 !!! Regidx Rs0)
                          (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> R9).
        assert (HR10a1 : (R10 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10).
        { etransitivity; [ rewrite /R10; apply upd_eq |].
          rewrite (su_regs_s0 _ _ _ _ _ _ HR9regs). apply su_bufname. }
        assert (HR10a2 : (R10 !!! Regidx Ra2 : mword 64)
                         = pa_add (pa_stk sp0 27) 4)
          by (rewrite /R10 upd_ne; [exact HR9a2 | nz]).
        assert (HR10regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                             (m !!! Regidx Rs3 : mword 64) R10)
          by (rewrite /R10; apply su_regs_caller; [exact Hcsa1 | exact HR9regs]).
        assert (Hpp66 : add_vec_int (mword_of_int (SU + 0x62) : mword 64) 4
                        = mword_of_int (SU + 0x66)) by pcw.
        iEval (rewrite Hpp66) in "Hpc".
        (* ===== +0x66 c.mv a0,s1 -- a0 = dp ===== *)
        iApply (wp_cmv_s_sconf (CID := CID17) (mword_of_int (SU + 0x66))
                  Ra0 Rs1 R10 (K - 30)%nat b ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (suli_066 with "Htext"). }
        iIntros (CID18 Hq18) "Hcg Hpc".
        set (R11 := <[Regidx Ra0 := regval_into_reg
                       (add_vec zero_reg (R10 !!! Regidx Rs1))]> R10).
        assert (HR11a0 : (R11 !!! Regidx Ra0 : mword 64) = ientry kd).
        { etransitivity; [ rewrite /R11; apply upd_eq |].
          rewrite add_vec_zero_l (su_regs_s1 _ _ _ _ _ _ HR10regs). exact Hdpe. }
        assert (HR11a1 : (R11 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10)
          by (rewrite /R11 upd_ne; [exact HR10a1 | nz]).
        assert (HR11a2 : (R11 !!! Regidx Ra2 : mword 64)
                         = pa_add (pa_stk sp0 27) 4)
          by (rewrite /R11 upd_ne; [exact HR10a2 | nz]).
        assert (HR11regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                             (m !!! Regidx Rs3 : mword 64) R11)
          by (rewrite /R11; apply su_regs_caller; [exact Hcsa0 | exact HR10regs]).
        assert (Hpp68 : add_vec_int (mword_of_int (SU + 0x66) : mword 64) 2
                        = mword_of_int (SU + 0x68)) by pcw.
        iEval (rewrite Hpp68) in "Hpc".
        (* ===== +0x68 jal ra,dirlookup ===== *)
        iApply (wp_jal_s_sconf (CID := CID18) (mword_of_int (SU + 0x68)) Rra
                  (mword_of_int 2090988 : mword 21) R11 (K - 30)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_068 with "Htext"). }
        iIntros (CID19 Hq19) "Hcg Hpc".
        set (R12 := <[Regidx Rra := regval_into_reg
                       (add_vec_int (mword_of_int (SU + 0x68) : mword 64) 4)]> R11).
        assert (Hjdl : add_vec (mword_of_int (SU + 0x68) : mword 64)
                         (sign_extend' 64 (mword_of_int 2090988 : mword 21))
                       = mword_of_int KernelSyms.dirlookup) by pcw.
        iEval (rewrite Hjdl) in "Hpc".
        assert (HR12ra : (R12 !!! Regidx Rra : mword 64)
                         = add_vec_int (mword_of_int (SU + 0x68) : mword 64) 4)
          by (rewrite /R12; apply upd_eq).
        assert (HR12a0 : (R12 !!! Regidx Ra0 : mword 64) = ientry kd)
          by (rewrite /R12 upd_ne; [exact HR11a0 | nz]).
        assert (HR12a1 : (R12 !!! Regidx Ra1 : mword 64) = pa_stk sp0 10)
          by (rewrite /R12 upd_ne; [exact HR11a1 | nz]).
        assert (HR12a2 : (R12 !!! Regidx Ra2 : mword 64)
                         = pa_add (pa_stk sp0 27) 4)
          by (rewrite /R12 upd_ne; [exact HR11a2 | nz]).
        assert (HR12regs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                             (m !!! Regidx Rs3 : mword 64) R12)
          by (rewrite /R12; apply su_regs_caller; [exact Hcsra | exact HR11regs]).
        (* [&off] is not null: the frame's own geometry, off the PUSHED sp *)
        iDestruct (su_sp_bounds (CIDh := CID19) R12 (K - 30)%nat b
                     (proc_addr jx) ltac:(lia) with "Hcg") as %Hspb.
        rewrite (su_regs_sp _ _ _ _ _ _ HR12regs) in Hspb.
        assert (Hoffnz : (R12 !!! Regidx Ra2 : mword 64) <> (zero_reg : mword 64)).
        { rewrite HR12a2 su_offcell_sp. unfold pa_add.
          apply stack_off_nonzero; [exact Hspb | lia]. }
        (* the locked directory, opened for readi's bundle *)
        iDestruct (ic_loaded_open with "Hload") as (datd)"(%Hiok & %Hrl_datd & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind & Hblocks & Hdview & Hfview & Htop)".
        pose proof Hiok as Hiok0.
        destruct Hiok as (Hbmwf & Hbmcv & Hbmc & Htynz & Hszcap & Hiokrest).
        assert (Hinums : dir_inums_ok datd
                           (dir_nrec (bv_unsigned (di_size dnd))) nib)
          by (rewrite Hcnib; exact (Hdok Htydz)).
        iAssert (iref_slot) with "[Hir]" as "Hislot".
        { rewrite /iref_slot. iExact "Hir". }
        iDestruct (cpu_own_transport CID13 CID19 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        (* THE LICENCE PREMISE (fs-fragments §7.5.6, last row of the supplier
           table).  THIS is the site the disjunction exists for: sys_unlink
           runs nameiparent -> ilock(dp) -> dirlookup(dp,name,&off) with NO
           [dp->nlink == 0] re-check anywhere, so the LEFT disjunct -- a live
           home -- is UNSUPPLIABLE here and no reordering of this walk makes
           it suppliable.  What sys_unlink has instead is the pair of
           [namecmp] refusals at sysfile.c:220-221
             if(namecmp(name, ".") == 0 || namecmp(name, "..") == 0) goto bad;
           whose fall-through arms are the two [decide]s at +0x44 and +0x58
           above; they left [Hnotdot]/[Hnotdd], which IS the RIGHT disjunct.
           Under [dir_orphan_clean] an orphaned home's live records are all
           dot records, so a non-dot match cannot be live and the borrowed
           ticket is only ever cashed under a live home. *)
        (* dirlookup borrows the LEDGER half alone (durable-disk
           2b-inode-5); the counting RA's tokens stay in this walk's hand
           and go back into the payload with the same node. *)
        assert (Hholesd : blk_holes_zero bmd datd)
          by (destruct Hiok0 as (_ & _ & _ & _ & _ & Hq & _); exact Hq).
        iApply (Dirlookup.wp_dirlookup_sconf (CID := CID19) gs jx gl gu gd gk
                  pd pav pu bn gfs gi cn gtl ga gf cov logstart inodestart nib dev
                  (ientry kd) dinum bmd datd dnd dnd nf true (word_hi w27) pid
                  (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  R12 (K - 30)%nat eb b lks
                  (upd_upt V P1) ltac:(exact Kdl) Htydir Hgeom Hbmwf Hbmcv Hszcap Hholesd Hinums
                  ltac:(right; exact (conj Hnotdot Hnotdd)) Hdoc Htynz
                  (* premise (6'), iclaim-ledger.md §3.3: region record = the
                     in-core one here (both slots take [dnd]). *)
                  eq_refl
                  Hj Hgl HR12a0
                  ltac:(cbn [negb]; apply (proj2 (eq_vec_false_iff _ _));
                        exact Hoffnz)
                  (Hlb "bcache"%string)
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hkenv Hidev Hmeta
                        [Haddrs Hind] Hblocks [Hnm14] [H27hi] Hpidq Hprocs
                        Hdev Hgeo Hdlk Hbs1 Hitab Hitinv Hescrows Hireg Hislot
                        Hdlnk Hdiat").
        (* dirlookup is eb-generic now; sys_unlink is still at [eb = true],
           where the complement is [emp]. *)
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { rewrite /inode_map. iFrame "Haddrs Hind". }
        { iEval (rewrite HR12a1). iExact "Hnm14". }
        { cbn [negb]. iEval (rewrite HR12a2). iExact "H27hi". }
        (* ...and the borrow comes straight back, on both arms, verbatim *)
        iIntros (CID20 Hq20 mdl found kk kslot qs)
          "%Hcsdl Hcg Hown _ _ Hpc Hidev Hmeta Hmap Hblocks Hnm14 Hpidq Hbs1
           Hdlnk Hdiat Hres".
        iEval (rewrite HR12a1) in "Hnm14".
        assert (Hpc6c : ret_pc (R12 !!! Regidx Rra : mword 64)
                        = mword_of_int (SU + 0x6c)) by (rewrite HR12ra; pcw).
        iEval (rewrite Hpc6c) in "Hpc".
        assert (Hdlregs : su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                            (m !!! Regidx Rs3 : mword 64) mdl)
          by exact (su_regs_cs m sp0 _ _ _ R12 mdl Hcsdl HR12regs).
        iDestruct "Hmap" as "[Haddrs Hind]".
        assert (Htgargd : add_vec (mword_of_int (SU + 0x6e) : mword 64)
                            (sign_extend' 64 (mword_of_int 234 : mword 13))
                          = mword_of_int (SU + 0x158)) by pcw.
        destruct found.
        * (* ============ THE RECORD IS THERE: the SEAM ============ *)
          iDestruct "Hres" as "((%Hfst & %Hkslot & %Hdla0) & Hchild & Hruc & H27hi)".
          iEval (rewrite HR12a2) in "H27hi".
          (* ===== +0x6c c.mv s2,a0 -- s2 = ip ===== *)
          iApply (wp_cmv_s_sconf (CID := CID20) (mword_of_int (SU + 0x6c))
                    Rs2 Ra0 mdl (K - 30)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (suli_06c with "Htext"). }
          iIntros (CID21 Hq21) "Hcg Hpc".
          set (R13 := <[Regidx Rs2 := regval_into_reg
                         (add_vec zero_reg (mdl !!! Regidx Ra0))]> mdl).
          assert (HR13a0 : (R13 !!! Regidx Ra0 : mword 64)
                           = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /R13 upd_ne; [reflexivity | nz]).
          assert (HR13regs : su_regs m sp0 dpv (ientry kslot)
                               (m !!! Regidx Rs3 : mword 64) R13).
          { rewrite /R13.
            apply (su_regs_wr_s2 m sp0 dpv (m !!! Regidx Rs2 : mword 64)
                     (ientry kslot) (m !!! Regidx Rs3 : mword 64) mdl _);
              [ rewrite add_vec_zero_l; exact Hdla0 | exact Hdlregs ]. }
          assert (Hpp6e : add_vec_int (mword_of_int (SU + 0x6c) : mword 64) 2
                          = mword_of_int (SU + 0x6e)) by pcw.
          iEval (rewrite Hpp6e) in "Hpc".
          (* ===== +0x6e beq a0,x0 : FALLS THROUGH (a hit is an entry) ===== *)
          iApply (wp_beqz_x0_fall_s_sconf (CID := CID21)
                    (mword_of_int (SU + 0x6e)) (mword_of_int 234 : mword 13)
                    Ra0 R13 (K - 30)%nat b ltac:(nz)
                    ltac:(rgne; rewrite HR13a0 Hdla0;
                          apply (proj2 (eq_vec_false_iff _ _));
                          exact (ientry_ne_zero kslot
                                   (Nat.lt_le_incl _ _ Hkslot)))
                    with "Hcg Hpc []").
          { iApply (suli_06e with "Htext"). }
          iIntros (CID22 Hq22) "Hcg Hpc".
          assert (Hpp72 : add_vec_int (mword_of_int (SU + 0x6e) : mword 64) 4
                          = mword_of_int (SU + 0x72)) by pcw.
          iEval (rewrite Hpp72) in "Hpc".
          (* the process block, rebuilt whole for the seam *)
          iDestruct ("Hpre" with "Hpidq") as "Hpriv".
          iDestruct (cpu_own_transport CID20 CID22 0 eb (proc_addr jx) b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          rewrite Hdpe in HR13regs.
          iApply ("Hseamk" $! CID22 R13 kd kslot kk gild gisld gyd (qd/2)%Qp
                    (qd/2)%Qp qs dinum dnd bmd datd (word_lo w27)
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    [%] [%]
                    Hcg Hown Hpc Hseam Hgen [Hbs1 Hbs2] Hsbb Hsbi Hsbs
                    Hpriv Hslkd0 Hslkdd Hdep Hidev Hiinum Hivalid
                    Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview Htop Hshotl Hfrz Hkeepd Hrud
                    Hchild Hruc HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP
                    H27lo H27hi HbE H30 [Hcont]").
          { exact HR13regs. }
          { exact Hkd. }
          { exact Hkslot. }
          { exact Hdinb. }
          { exact Htydir. }
          { exact Hiok0. }
          { exact Hrl_datd. }
          { exact Hdok. }
          { exact Hddix. }
          { exact Hdoc. }
          { exact Hduq. }
          { exact Hnotdot. }
          { exact Hnotdd. }
          { exact Hfst. }
          { rewrite HR13a0. exact Hdla0. }
          { exact Hal27. }
          { iApply su_bs3. iFrame "Hbs1 Hbs2". }
          { iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID22)
                         ltac:(wp_next_chain) with "Hcont") as "Hcont".
            iExact "Hcont". }
        * (* ============ ARM D: dirlookup returned 0 ============ *)
          iDestruct "Hres" as "((%Hfst & %Hdla0) & Hislot & H27hi)".
          iEval (rewrite HR12a2) in "H27hi".
          (* ===== +0x6c c.mv s2,a0 ===== *)
          iApply (wp_cmv_s_sconf (CID := CID20) (mword_of_int (SU + 0x6c))
                    Rs2 Ra0 mdl (K - 30)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (suli_06c with "Htext"). }
          iIntros (CID21 Hq21) "Hcg Hpc".
          set (R13 := <[Regidx Rs2 := regval_into_reg
                         (add_vec zero_reg (mdl !!! Regidx Ra0))]> mdl).
          assert (HR13a0 : (R13 !!! Regidx Ra0 : mword 64)
                           = (mdl !!! Regidx Ra0 : mword 64))
            by (rewrite /R13 upd_ne; [reflexivity | nz]).
          assert (HR13sp : su_sp sp0 R13)
            by (rewrite /su_sp /R13 upd_ne;
                [exact (su_regs_sp _ _ _ _ _ _ Hdlregs) | nz]).
          assert (HR13s1 : (R13 !!! Regidx Rs1 : mword 64) = ientry kd).
          { rewrite /R13 upd_ne; [| nz].
            rewrite (su_regs_s1 _ _ _ _ _ _ Hdlregs). exact Hdpe. }
          assert (HR13s3 : (R13 !!! Regidx Rs3 : mword 64)
                           = (m !!! Regidx Rs3 : mword 64))
            by (rewrite /R13 upd_ne;
                [exact (su_regs_s3 _ _ _ _ _ _ Hdlregs) | nz]).
          assert (HR13thr : su_thr m R13).
          { intros c Hc N2 N8 N9 N18 N19. rewrite /R13 upd_ne; [| congruence].
            exact (su_regs_thr _ _ _ _ _ _ Hdlregs c Hc N2 N8 N9 N18 N19). }
          assert (Hpp6e : add_vec_int (mword_of_int (SU + 0x6c) : mword 64) 2
                          = mword_of_int (SU + 0x6e)) by pcw.
          iEval (rewrite Hpp6e) in "Hpc".
          (* ===== +0x6e beq a0,x0 -> +0x158 ===== *)
          iApply (wp_beqz_x0_taken_s_sconf (CID := CID21)
                    (mword_of_int (SU + 0x6e)) (mword_of_int 234 : mword 13)
                    Ra0 R13 (K - 30)%nat b ltac:(nz)
                    ltac:(rgne; rewrite HR13a0 Hdla0; vm_compute; reflexivity)
                    ltac:(rewrite Htgargd; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (suli_06e with "Htext"). }
          iIntros (CID22 Hq22). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgargd) in "Hpc".
          (* the buffers and the bundle, put back for the tail *)
          iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
            as "HbNj".
          iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
          iDestruct (su_off_join sp0 (word_lo w27) (word_hi w27) Hal27
                       with "H27lo H27hi") as "H27".
          iAssert (ic_loaded gfs gi cov logstart kd dinum dnd bmd)
            with "[Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview Htop]"
            as "Hload".
          { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
            iExists datd. iFrame "Hdlnk Hdiat Hmeta
              Haddrs Hind Hblocks Hdview Hfview Htop". iPureIntro. split_and!;
              [ exact Hiok0 | exact Hrl_datd | exact Hdok | exact Hddix
              | exact Hdoc | exact Hduq ]. }
          iDestruct (cpu_own_transport CID20 CID22 0 eb (proc_addr jx) b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (Tails.su_tail_d (CID0 := CID22) gs jx gl gu gd gk pd pav pu
                    bn g gfs gi cn gtl gild gisld cov logstart bmapstart
                    inodestart nib size dev kd (qd/2)%Qp (qd/2)%Qp gyd
                    dinum dnd bmd n1 pid (DfracOwn (1/4)) dqb dqs
                    m R13 sp0 K eb b lks w5 w6 (word_of_words (word_lo w27)
                    (word_hi w27)) w30 bd bnf bp be
                    (upd_upt V P1) Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog
                    Hist0 Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty
                    Hsp0 HR13sp HR13thr HR13s1 HR13s3 Hal
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen
                          Hitab Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd Hdep
                          Hidev Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb
                          Hsbi
                          Hbmres Hpidq Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2]
                          [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                          HbE H30
                          [Hcont Hpre Hsbs Hislot]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iApply su_bs3. iFrame "Hbs1 Hbs2". }
          { rewrite /log_op. iExists Sb1. iExact "HopS". }
          iEval (rewrite /wp_next).
          iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce
                                           Hcce Hpc Hpidq Hsbb Hsbi
                                           Hbsl Hislot2".
          iDestruct ("Hpre" with "Hpidq") as "Hpriv".
          iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                    Hbsl Hsbb Hsbi Hsbs [Hislot Hislot2] Hpriv [%]").
          { exact Hcsf. }
          { exact Hupt1. }
          { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
            rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
          { left. rewrite Ha0f. reflexivity. }
  Qed.

  (* ================================================================== *)
  (*  W4: +0xf8 .. +0x12c -- the inlined isdirempty loop.                *)
  (*                                                                     *)
  (*    +0xf8  lw a4,76(s2)          (a4 = ip->size)                     *)
  (*    +0xfc  li a5,32                                                  *)
  (*    +0x100 bgeu a5,a4 -> +0x8a   (size <= 32: EMPTY, exit)           *)
  (*    +0x104 c.mv s3,a5            (off = 32)                          *)
  (*    +0x106 c.li a4,16 ; +0x108 c.mv a3,s3 ; +0x10a addi a2,s0,-232   *)
  (*    +0x10e c.li a1,0  ; +0x110 c.mv a0,s2                            *)
  (*    +0x112 jal readi(ip, 0, &de, off, 16)                            *)
  (*    +0x116 c.li a5,16 ; +0x118 bne a0,a5 -> +0x12e  [panic readi]    *)
  (*    +0x11c lhu a5,-232(s0) ; +0x120 c.bnez a5 -> +0x174  [ARM E]     *)
  (*    +0x122 c.addiw s3,s3,16 ; +0x124 lw a5,76(s2)                    *)
  (*    +0x128 bltu s3,a5 -> +0x106  (the back edge)                     *)
  (*    +0x12c c.j +0x8a             (EMPTY, exit)                       *)
  (*                                                                     *)
  (*  THE INTERFACE IS ip's LOCKED CONTENT PLUS TWO CONTINUATIONS -- the  *)
  (*  ARM E entry at +0x174 and the empty exit at +0x8a -- and an OPAQUE  *)
  (*  frame [X] the caller threads through: dp's twelve-component bundle, *)
  (*  the frame slots, the ledger and the caller's own exit all live in   *)
  (*  [X], never in the loop.  Both exits hand [X] back, which is what    *)
  (*  lets ONE linear packet serve two ∗-separated continuations.         *)
  (*                                                                     *)
  (*  THE LOOP SPENDS NO LOG BUDGET: readi takes no [log_op] at all       *)
  (*  (SpecReadi's "READI MODIFIES NOTHING"), so no ledger resource       *)
  (*  appears below.  The short-read arm is [Tails.su_panic_readi] and    *)
  (*  never returns.                                                     *)
  (*                                                                     *)
  (*  THE INVARIANT IS THE DEAD PREFIX: every scanned record (indices     *)
  (*  2 .. jj-1) has a zero inum.  The empty exit turns it into           *)
  (*  [DirView.dir_dots_only] against [dir_dots_ix]'s two dots            *)
  (*  ([su_dots_only_scan]) -- the payload W5-DIR's re-park reads.        *)
  (* ================================================================== *)

  (* ARM E's continuation: a live record was found, the loop leaves for
     +0x174 with ip's content intact and the answer discarded.  [dp]'s
     bundle and the exit ride in [X]. *)
  Definition su_w4_exitE `{GEN : GenId}
      (gfs : fs_names) (jx ki : nat)
      (dev : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac) (bn : bio_names)
      (m : regfile) (sp0 dpv ipv : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Vpr : pprivate) : iProp Σ :=
    (∀ (CIDx : CpuId) (Mx : regfile) (s3x : mword 64) (bex : nat -> bv 8),
       ⌜su_regs m sp0 dpv ipv s3x Mx⌝ -∗
       sie_cap_gpr KT1 Mx (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x174)) -∗
       i_dev (ientry ki) ↦₄{DfracOwn (1/2)} dev -∗
       inode_meta (ientry ki) dni -∗
       inode_map gfs (ientry ki) bmi -∗
       inode_blocks gfs bmi dati -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
       proc_priv_bare (proc_addr jx) pidv Vpr -∗
       bslot -∗
       X -∗
       WP (Loop : expr riscv_lang))%I.

  (* the EMPTY exit: every record past the dots is dead, and the payload
     clause is [dir_dots_only] -- exactly what W5-DIR's re-park
     ([su_dir_links_orphan]) reads, stated at the loop's own [dati]. *)
  Definition su_w4_exitD `{GEN : GenId}
      (gfs : fs_names) (jx ki : nat)
      (dev : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac) (bn : bio_names)
      (m : regfile) (sp0 dpv ipv : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Vpr : pprivate) : iProp Σ :=
    (∀ (CIDx : CpuId) (Mx : regfile) (s3x : mword 64) (bex : nat -> bv 8),
       ⌜su_regs m sp0 dpv ipv s3x Mx⌝ -∗
       ⌜dir_dots_only dni dati⌝ -∗
       ⌜forall k : nat, (2 <= k)%nat ->
          (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
          dir_inum dati k = bv_0 16⌝ -∗
       sie_cap_gpr KT1 Mx (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x8a)) -∗
       i_dev (ientry ki) ↦₄{DfracOwn (1/2)} dev -∗
       inode_meta (ientry ki) dni -∗
       inode_map gfs (ientry ki) bmi -∗
       inode_blocks gfs bmi dati -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
       proc_priv_bare (proc_addr jx) pidv Vpr -∗
       bslot -∗
       X -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE ITERATION, by fuel over the remaining bytes.  Entry at +0x106
     with s3 = 16*jj, records 2..jj-1 known dead. *)
  Local Lemma su_w4_loop `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ki : nat) (inumi : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (dpv ipv : mword 64)
      (m : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Vpr : pprivate) :
    (K_readi <= K - 30)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true -> lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    ipv = ientry ki ->
    inode_ok cov logstart dni bmi dati ->
    (* durable-disk 2b-inode-3: the child's record-only facts *)
    inode_rec_local dni ->
    bv_unsigned (di_type dni) = T_DIR_z ->
    bv_unsigned (di_nlink dni) <> 0 ->
    dir_dots_ix (bv_unsigned inumi) dni dati ->
    forall (W jj : nat) (M : regfile) (bcur : nat -> bv 8),
    (2 <= jj)%nat ->
    (16 * jj < Z.to_nat (bv_unsigned (di_size dni)))%nat ->
    (Z.to_nat (bv_unsigned (di_size dni)) <= 16 * jj + 16 * W)%nat ->
    (forall k : nat, (2 <= k)%nat -> (k < jj)%nat ->
       dir_inum dati k = bv_0 16) ->
    su_regs m sp0 dpv ipv (mword_of_int (Z.of_nat (16 * jj))) M ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    panic_env -∗
    pc_is (mword_of_int (SU + 0x106)) -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    (* the byte view's row, for readi's crossing (durable-disk 1c-flip) *)
    fs_bytes_any gfs -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    i_dev (ientry ki) ↦₄{DfracOwn (1/2)} dev -∗
    inode_meta (ientry ki) dni -∗
    inode_map gfs (ientry ki) bmi -∗
    inode_blocks gfs bmi dati -∗
    ([∗ list] jj0 ∈ seq 0 16, pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] bcur jj0) -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    bslot -∗
    su_w4_exitE gfs jx ki dev dni bmi dati pidv dq bn
                m sp0 dpv ipv K eb b lks X Vpr -∗
    su_w4_exitD gfs jx ki dev dni bmi dati pidv dq bn
                m sp0 dpv ipv K eb b lks X Vpr -∗
    X -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal Hipv Hiok Hrl_dati Htyz
           Hnlz Hddix.
    pose proof Hiok as Hiok0.
    destruct Hiok as (Hbmwf & Hbmcv & Hbmc & Htynz & Hszcap & Hiokrest).
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dni))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dni))).
    assert (Hszlt : bv_unsigned (di_size dni) < 2 ^ 31)
      by (assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity);
          lia).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa3 : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hal29 : is_aligned_paddr (Physaddr (pa_stk sp0 29)) 2 = true).
    { apply su_align_8_2.
      destruct Hal as (_ & _ & _ & Hal29w).
      exact (Hal29w 0%nat ltac:(lia)). }
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 jj M bcur Hjj2 Hjlt Hfuel Hdead Hregs;
      [exfalso; lia |].
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (H16jj : Z.of_nat (16 * jj) < 2 ^ 31)
      by (assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity);
          lia).
    iIntros "Hcg Hown #Htext #Hkd #Hpe Hpc #Hbio #Hrow #Hkenv #Hprocs #Hdev #Hgeo
             #Hdlk Hidev Hmeta Hmap Hblocks Hbuf Hpidq Hbslot HcE HcD HX".
    (* ===== +0x106 c.li a4,16 ===== *)
    iApply (wp_cli_s_sconf (CID := CID0) (mword_of_int (SU + 0x106)) Ra4
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64) M
              (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_106 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> M).
    assert (HN1a4 : (N1 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N1; apply upd_eq).
    assert (HN1regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N1)
      by (rewrite /N1; apply su_regs_caller; [exact Hcsa4 | exact Hregs]).
    assert (Hpp108 : add_vec_int (mword_of_int (SU + 0x106) : mword 64) 2
                     = mword_of_int (SU + 0x108)) by pcw.
    iEval (rewrite Hpp108) in "Hpc".
    (* ===== +0x108 c.mv a3,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID1) (mword_of_int (SU + 0x108)) Ra3 Rs3
              N1 (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_108 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (N2 := <[Regidx Ra3 := regval_into_reg
                  (add_vec zero_reg (N1 !!! Regidx Rs3))]> N1).
    assert (HN2a3 : (N2 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * jj)) : mword 64)).
    { etransitivity; [ rewrite /N2; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HN1regs). }
    assert (HN2a4 : (N2 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1a4 | nz]).
    assert (HN2regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N2)
      by (rewrite /N2; apply su_regs_caller; [exact Hcsa3 | exact HN1regs]).
    assert (Hpp10a : add_vec_int (mword_of_int (SU + 0x108) : mword 64) 2
                     = mword_of_int (SU + 0x10a)) by pcw.
    iEval (rewrite Hpp10a) in "Hpc".
    (* ===== +0x10a addi a2,s0,-232 -- isdirempty's [&de] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID2) (mword_of_int (SU + 0x10a)) Ra2 Rs0
              (mword_of_int 3864 : mword 12) N2 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_10a with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (N3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (N2 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3864 : mword 12)))]> N2).
    assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64) = pa_stk sp0 29).
    { etransitivity; [ rewrite /N3; apply upd_eq |].
      rewrite (su_regs_s0 _ _ _ _ _ _ HN2regs). apply su_bufdel. }
    assert (HN3a3 : (N3 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * jj)) : mword 64))
      by (rewrite /N3 upd_ne; [exact HN2a3 | nz]).
    assert (HN3a4 : (N3 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N3 upd_ne; [exact HN2a4 | nz]).
    assert (HN3regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N3)
      by (rewrite /N3; apply su_regs_caller; [exact Hcsa2 | exact HN2regs]).
    assert (Hpp10e : add_vec_int (mword_of_int (SU + 0x10a) : mword 64) 4
                     = mword_of_int (SU + 0x10e)) by pcw.
    iEval (rewrite Hpp10e) in "Hpc".
    (* ===== +0x10e c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := CID3) (mword_of_int (SU + 0x10e)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) N3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_10e with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (N4 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> N3).
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N4; apply upd_eq).
    assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64) = pa_stk sp0 29)
      by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
    assert (HN4a3 : (N4 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * jj)) : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3a3 | nz]).
    assert (HN4a4 : (N4 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3a4 | nz]).
    assert (HN4regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N4)
      by (rewrite /N4; apply su_regs_caller; [exact Hcsa1 | exact HN3regs]).
    assert (Hpp110 : add_vec_int (mword_of_int (SU + 0x10e) : mword 64) 2
                     = mword_of_int (SU + 0x110)) by pcw.
    iEval (rewrite Hpp110) in "Hpc".
    (* ===== +0x110 c.mv a0,s2 -- a0 = ip ===== *)
    iApply (wp_cmv_s_sconf (CID := CID4) (mword_of_int (SU + 0x110)) Ra0 Rs2
              N4 (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_110 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (N5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N4 !!! Regidx Rs2))]> N4).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = ientry ki).
    { etransitivity; [ rewrite /N5; apply upd_eq |].
      rewrite add_vec_zero_l (su_regs_s2 _ _ _ _ _ _ HN4regs). exact Hipv. }
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5a2 : (N5 !!! Regidx Ra2 : mword 64) = pa_stk sp0 29)
      by (rewrite /N5 upd_ne; [exact HN4a2 | nz]).
    assert (HN5a3 : (N5 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * jj)) : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a3 | nz]).
    assert (HN5a4 : (N5 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a4 | nz]).
    assert (HN5regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N5)
      by (rewrite /N5; apply su_regs_caller; [exact Hcsa0 | exact HN4regs]).
    assert (Hpp112 : add_vec_int (mword_of_int (SU + 0x110) : mword 64) 2
                     = mword_of_int (SU + 0x112)) by pcw.
    iEval (rewrite Hpp112) in "Hpc".
    (* ===== +0x112 jal ra,readi ===== *)
    iApply (wp_jal_s_sconf (CID := CID5) (mword_of_int (SU + 0x112)) Rra
              (mword_of_int 2090292 : mword 21) N5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_112 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (N6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x112) : mword 64) 4)]> N5).
    assert (Hjrd : add_vec (mword_of_int (SU + 0x112) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090292 : mword 21))
                   = mword_of_int KernelSyms.readi) by pcw.
    iEval (rewrite Hjrd) in "Hpc".
    assert (HN6ra : (N6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x112) : mword 64) 4)
      by (rewrite /N6; apply upd_eq).
    assert (HN6a0 : (N6 !!! Regidx Ra0 : mword 64) = ientry ki)
      by (rewrite /N6 upd_ne; [exact HN5a0 | nz]).
    assert (HN6a1 : (N6 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N6 upd_ne; [exact HN5a1 | nz]).
    assert (HN6a2 : (N6 !!! Regidx Ra2 : mword 64) = pa_stk sp0 29)
      by (rewrite /N6 upd_ne; [exact HN5a2 | nz]).
    assert (HN6a3 : (N6 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * jj)) : mword 64))
      by (rewrite /N6 upd_ne; [exact HN5a3 | nz]).
    assert (HN6a4 : (N6 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N6 upd_ne; [exact HN5a4 | nz]).
    assert (HN6regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N6)
      by (rewrite /N6; apply su_regs_caller; [exact Hcsra | exact HN5regs]).
    iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Readi.wp_readi_sconf KT1 (CID := CID6) gs jx gl gu gd gk pd pav pu bn
              gfs ga gf cov logstart dev (ientry ki) bmi dati dni false
              (16 * jj)%nat 16%nat bcur Vpr pidv dq (DfracOwn (1/2))
              N6 (K - 30)%nat eb b lks
              ltac:(exact Kre) Hgeom Hbmwf Hbmcv Hszcap
              ltac:(assert (E32 : (2 ^ 32 = 4294967296)%Z)
                      by (vm_compute; reflexivity); lia)
              ltac:(intros _;
                    assert (E32 : (2 ^ 32 = 4294967296)%Z)
                      by (vm_compute; reflexivity); lia)
              Hj Hgl HN6a0
              ltac:(rewrite HN6a1; cbn [negb]; vm_compute; reflexivity)
              ltac:(rewrite HN6a3; apply rd_arg32_small; exact H16jj)
              ltac:(rewrite HN6a4;
                    apply (rd_arg32_small 16); vm_compute; reflexivity)
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hkd Hpc Hpe Hbio Hrow Hkenv Hidev Hmeta
                    Hmap Hblocks [Hbuf Hpidq] Hprocs Hdev Hgeo Hdlk Hbslot").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iSplitL "Hbuf"; [| iExact "Hpidq"].
      iEval (rewrite HN6a2). iExact "Hbuf". }
    iIntros (CID7 Hq7 mrd tot P')
      "%Hcsrd %Hupt' %Htotle %Harm Hcg Hown _ _ Hpc Hidev Hmeta Hmap Hblocks
       [Hbuf Hpidq] Hbslot".
    iEval (rewrite HN6a2) in "Hbuf".
    assert (Hpc116 : ret_pc (N6 !!! Regidx Rra : mword 64)
                     = mword_of_int (SU + 0x116)) by (rewrite HN6ra; pcw).
    iEval (rewrite Hpc116) in "Hpc".
    assert (Hrdregs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) mrd)
      by exact (su_regs_cs m sp0 _ _ _ N6 mrd Hcsrd HN6regs).
    destruct Harm as [[_ Hfalse] | [Ha0 Htoteq]]; [discriminate Hfalse |].
    (* ===== +0x116 c.li a5,16 ===== *)
    iApply (wp_cli_s_sconf (CID := CID7) (mword_of_int (SU + 0x116)) Ra5
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64) mrd
              (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_116 with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (N7 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mrd).
    assert (HN7a5 : (N7 !!! Regidx Ra5 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /N7; apply upd_eq).
    assert (HN7a0 : (N7 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat tot) : mword 64)).
    { rewrite /N7 upd_ne; [| nz]. exact Ha0. }
    assert (HN7regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N7)
      by (rewrite /N7; apply su_regs_caller; [exact Hcsa5 | exact Hrdregs]).
    assert (Hpp118 : add_vec_int (mword_of_int (SU + 0x116) : mword 64) 2
                     = mword_of_int (SU + 0x118)) by pcw.
    iEval (rewrite Hpp118) in "Hpc".
    assert (Htot16b : (tot <= 16)%nat)
      by (pose proof (su_clamp_le16 (di_size dni) (16 * jj)%nat); lia).
    (* ===== +0x118 bne a0,a5 -> [panic "isdirempty: readi"] ===== *)
    destruct (decide (tot = 16%nat)) as [-> | Hne16].
    2:{ (* the SHORT READ: taken, and the panic never returns *)
      iApply (wp_bne_taken_s_sconf (CID := CID8) (mword_of_int (SU + 0x118))
                (mword_of_int 22 : mword 13) Ra5 Ra0 N7 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HN7a0 HN7a5;
                      exact (su_neq_of_eq_false _ _
                               (su_tot16_ne tot Htot16b Hne16)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_118 with "Htext"). }
      iIntros (CID9 Hq9). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg12e : add_vec (mword_of_int (SU + 0x118) : mword 64)
                         (sign_extend' 64 (mword_of_int 22 : mword 13))
                       = mword_of_int (SU + 0x12e)) by pcw.
      iEval (rewrite Htg12e) in "Hpc".
      iDestruct (cpu_own_transport CID7 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (cpu_own_transport CID8 CID9 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_readi (CID0 := CID9) N7 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K_readi K Kre) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hkd Hpe Hpc"). }
    (* the read was FULL: sixteen bytes, and they are the record's *)
    assert (Hin16 : (16 * jj + 16 <= Z.to_nat (bv_unsigned (di_size dni)))%nat)
      by (apply su_clamp16_in; symmetry; exact Htoteq).
    iApply (wp_bne_fall_s_sconf (CID := CID8) (mword_of_int (SU + 0x118))
              (mword_of_int 22 : mword 13) Ra5 Ra0 N7 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HN7a0 HN7a5;
                    apply su_neq_of_eq_true;
                    apply (proj2 (eq_vec_true_iff _ _)); reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_118 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    assert (Hpp11c : add_vec_int (mword_of_int (SU + 0x118) : mword 64) 4
                     = mword_of_int (SU + 0x11c)) by pcw.
    iEval (rewrite Hpp11c) in "Hpc".
    (* the buffer holds record jj's sixteen bytes; carve the halfword *)
    iEval (rewrite su_rdd_view (su_de_view dati jj (pa_stk sp0 29) Hal29))
      in "Hbuf".
    iDestruct "Hbuf" as "[Hhalf Hname]".
    (* ===== +0x11c lhu a5,-232(s0) -- de.inum ===== *)
    iApply (wp_lhu_s_sconf (CID := CID9) (kt := KT1) (ktd := KT1) (mword_of_int (SU + 0x11c)) Ra5 Rs0
              (mword_of_int 3864 : mword 12) N7 (K - 30)%nat
              (dir_inum dati jj : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hhalf]").
    { iApply (suli_11c with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HN7regs) su_bufdel).
      iExact "Hhalf". }
    iIntros (CID10 Hq10) "Hcg Hpc Hhalf".
    iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HN7regs) su_bufdel) in "Hhalf".
    set (N8 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (dir_inum dati jj : mword 16))]> N7).
    assert (HN8a5 : (N8 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (dir_inum dati jj : mword 16) : mword 64))
      by (rewrite /N8; apply upd_eq).
    assert (HN8regs : su_regs m sp0 dpv ipv
                        (mword_of_int (Z.of_nat (16 * jj))) N8)
      by (rewrite /N8; apply su_regs_caller; [exact Hcsa5 | exact HN7regs]).
    assert (Hpp120 : add_vec_int (mword_of_int (SU + 0x11c) : mword 64) 4
                     = mword_of_int (SU + 0x120)) by pcw.
    iEval (rewrite Hpp120) in "Hpc".
    (* ===== +0x120 c.bnez a5 -> +0x174 [ARM E] ===== *)
    destruct (decide (bv_unsigned (dir_inum dati jj) = 0)) as [Hz | Hnz].
    - (* -------- record jj is DEAD: fall through, keep scanning -------- *)
      iApply (wp_cbnez_fall_s_sconf (CID := CID10) (mword_of_int (SU + 0x120))
                (mword_of_int 42 : mword 8) (Cregidx (mword_of_int 7)) Ra5 N8
                (K - 30)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HN8a5;
                      exact (su_neq_of_eq_true _ _ (su_inum_zero _ Hz)))
                with "Hcg Hpc []").
      { iApply (suli_120 with "Htext"). }
      iIntros (CID11 Hq11) "Hcg Hpc".
      assert (Hpp122 : add_vec_int (mword_of_int (SU + 0x120) : mword 64) 2
                       = mword_of_int (SU + 0x122)) by pcw.
      iEval (rewrite Hpp122) in "Hpc".
      assert (Hdeadjj : dir_inum dati jj = bv_0 16).
      { apply bv_eq. rewrite Hz. reflexivity. }
      assert (Hdead' : forall k : nat, (2 <= k)%nat -> (k < S jj)%nat ->
                dir_inum dati k = bv_0 16).
      { intros k Hk2 HkS.
        destruct (decide (k = jj)) as [-> | Hkne]; [exact Hdeadjj |].
        apply Hdead; lia. }
      (* ===== +0x122 c.addiw s3,s3,16 ===== *)
      iApply (wp_caddiw_s_sconf (CID := CID11) (mword_of_int (SU + 0x122)) Rs3
                (mword_of_int 16 : mword 6) N8 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_122 with "Htext"). }
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (N9 := <[Regidx Rs3 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget N8 Rs3)
                          (sign_extend' 64 (sign_extend' 12
                             (mword_of_int 16 : mword 6)))) 31 0))]> N8).
      assert (Hbump : (sign_extend' 64 (subrange_vec_dec
                         (add_vec (rget N8 Rs3)
                            (sign_extend' 64 (sign_extend' 12
                               (mword_of_int 16 : mword 6)))) 31 0) : mword 64)
                      = (mword_of_int (Z.of_nat (16 * S jj)) : mword 64)).
      { assert (Hs3v : (rget N8 Rs3 : mword 64)
                       = (mword_of_int (Z.of_nat (16 * jj)) : mword 64)).
        { rgne. exact (su_regs_s3 _ _ _ _ _ _ HN8regs). }
        rewrite Hs3v.
        rewrite (w32_caddiw_moi (Z.of_nat (16 * jj)) 16
                   (mword_of_int 16 : mword 6) ltac:(pcw)
                   ltac:(assert (E31 : (2 ^ 31 = 2147483648)%Z)
                           by (vm_compute; reflexivity); lia)).
        assert (HE : Z.of_nat (16 * jj) + 16 = Z.of_nat (16 * S jj)) by lia.
        rewrite HE. reflexivity. }
      assert (HN9regs : su_regs m sp0 dpv ipv
                          (mword_of_int (Z.of_nat (16 * S jj))) N9).
      { rewrite /N9.
        apply (su_regs_wr_s3 m sp0 dpv ipv
                 (mword_of_int (Z.of_nat (16 * jj)))
                 (mword_of_int (Z.of_nat (16 * S jj))) N8 _ Hbump HN8regs). }
      assert (Hpp124 : add_vec_int (mword_of_int (SU + 0x122) : mword 64) 2
                       = mword_of_int (SU + 0x124)) by pcw.
      iEval (rewrite Hpp124) in "Hpc".
      (* ===== +0x124 lw a5,76(s2) -- ip->size again ===== *)
      iEval (rewrite /inode_meta) in "Hmeta".
      iDestruct "Hmeta" as "(Hity & Hima & Himi & Hinl & Hisz)".
      iEval (rewrite /i_size) in "Hisz".
      iApply (wp_lw_s_sconf (CID := CID12) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0x124)) Ra5 Rs2
                (mword_of_int 76 : mword 12) N9 (K - 30)%nat
                (di_size dni : mword 32) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc [] [Hisz]").
      { iApply (suli_124 with "Htext"). }
      { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HN9regs) Hipv).
        iExact "Hisz". }
      iIntros (CID13 Hq13) "Hcg Hpc Hisz".
      iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HN9regs) Hipv) in "Hisz".
      iAssert (inode_meta (ientry ki) dni)
        with "[Hity Hima Himi Hinl Hisz]" as "Hmeta".
      { rewrite /inode_meta /i_size. iFrame. }
      set (N10 := <[Regidx Ra5 := regval_into_reg
                     (sign_extend' 64 (di_size dni : mword 32))]> N9).
      assert (HN10a5 : (N10 !!! Regidx Ra5 : mword 64)
                       = (mword_of_int (bv_unsigned (di_size dni)) : mword 64)).
      { etransitivity; [ rewrite /N10; apply upd_eq |].
        exact (su_size_sext (di_size dni : mword 32) Hszlt). }
      assert (HN10regs : su_regs m sp0 dpv ipv
                           (mword_of_int (Z.of_nat (16 * S jj))) N10)
        by (rewrite /N10; apply su_regs_caller; [exact Hcsa5 | exact HN9regs]).
      assert (Hpp128 : add_vec_int (mword_of_int (SU + 0x124) : mword 64) 4
                       = mword_of_int (SU + 0x128)) by pcw.
      iEval (rewrite Hpp128) in "Hpc".
      (* the buffer, put back whole for whichever way the test goes *)
      iEval (rewrite -(su_name_acc dati jj (pa_add (pa_stk sp0 29) 2)))
        in "Hname".
      iEval (rewrite -(su_half_acc dati jj (pa_stk sp0 29) Hal29)) in "Hhalf".
      iAssert ([∗ list] jj0 ∈ seq 0 16,
                 pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] file_byte dati (16 * jj + jj0)%nat)%I
        with "[Hhalf Hname]" as "Hbuf".
      { iEval (rewrite (su_del_split (pa_stk sp0 29)
                          (fun jj0 => file_byte dati (16 * jj + jj0)%nat))).
        iSplitL "Hhalf"; [iExact "Hhalf" | iExact "Hname"]. }
      (* ===== +0x128 bltu s3,a5 : the back edge / the empty exit ===== *)
      destruct (decide (16 * S jj < Z.to_nat (bv_unsigned (di_size dni)))%nat)
        as [Hmore | Hdone].
      + (* ---- the BACK EDGE: re-enter at +0x106 with jj+1 ---- *)
        iApply (wp_bltu_taken_s_sconf (CID := CID13)
                  (mword_of_int (SU + 0x128)) (mword_of_int 8158 : mword 13)
                  Ra5 Rs3 N10 (K - 30)%nat b ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN10a5
                          (su_regs_s3 _ _ _ _ _ _ HN10regs);
                        apply su_loop_back_taken;
                        [lia | exact Hszlt])
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_128 with "Htext"). }
        iIntros (CID14 Hq14). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htg106 : add_vec (mword_of_int (SU + 0x128) : mword 64)
                           (sign_extend' 64 (mword_of_int 8158 : mword 13))
                         = mword_of_int (SU + 0x106)) by pcw.
        iEval (rewrite Htg106) in "Hpc".
        iDestruct (cpu_own_transport CID7 CID14 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (IH CID14 (S jj) N10
                  (fun jj0 => file_byte dati (16 * jj + jj0)%nat)
                  ltac:(lia) Hmore ltac:(lia) Hdead' HN10regs
                  with "Hcg Hown Htext Hkd Hpe Hpc Hbio Hrow Hkenv Hprocs Hdev Hgeo
                        Hdlk Hidev Hmeta Hmap Hblocks Hbuf Hpidq Hbslot
                        HcE HcD HX").
      + (* ---- the EMPTY EXIT: fall to +0x12c, j to +0x8a ---- *)
        iApply (wp_bltu_fall_s_sconf (CID := CID13)
                  (mword_of_int (SU + 0x128)) (mword_of_int 8158 : mword 13)
                  Ra5 Rs3 N10 (K - 30)%nat b ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HN10a5
                          (su_regs_s3 _ _ _ _ _ _ HN10regs);
                        apply su_loop_back_fall;
                        [lia |
                         assert (E31 : (2 ^ 31 = 2147483648)%Z)
                           by (vm_compute; reflexivity); lia])
                  with "Hcg Hpc []").
        { iApply (suli_128 with "Htext"). }
        iIntros (CID14 Hq14) "Hcg Hpc".
        assert (Hpp12c : add_vec_int (mword_of_int (SU + 0x128) : mword 64) 4
                         = mword_of_int (SU + 0x12c)) by pcw.
        iEval (rewrite Hpp12c) in "Hpc".
        (* ===== +0x12c c.j +0x8a ===== *)
        iApply (wp_cj_s_sconf (CID := CID14) (mword_of_int (SU + 0x12c))
                  (sign_extend' 21 (concat_vec (mword_of_int 1967 : mword 11)
                     ('b"0")))
                  N10 (K - 30)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (suli_12c with "Htext"). }
        iIntros (CID15 Hq15). iNext. iIntros "Hcg Hpc".
        assert (Htg8a : add_vec (mword_of_int (SU + 0x12c) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 1967 : mword 11)
                                   ('b"0"))))
                        = mword_of_int (SU + 0x8a)) by pcw.
        iEval (rewrite Htg8a) in "Hpc".
        assert (Hdeadall : forall k : nat, (2 <= k)%nat ->
                  (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
                  dir_inum dati k = bv_0 16).
        { intros k Hk2 Hklt. apply Hdead'; [exact Hk2 |].
          pose proof (su_nrec_le (bv_unsigned (di_size dni)) (S jj) Hsznn
                        ltac:(lia)) as Hn. lia. }
        iDestruct (cpu_own_transport CID7 CID15 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply ("HcD" $! CID15 N10 (mword_of_int (Z.of_nat (16 * S jj)))
                  (fun jj0 => file_byte dati (16 * jj + jj0)%nat)
                  with "[%] [%] [%] Hcg Hown Hpc Hidev Hmeta Hmap Hblocks
                        Hbuf Hpidq Hbslot HX").
        { exact HN10regs. }
        { exact (su_dots_only_scan (bv_unsigned inumi) dni dati Htyz Hnlz
                   Hddix Hdeadall). }
        { exact Hdeadall. }
    - (* -------- record jj is LIVE: taken, ARM E at +0x174 -------- *)
      iApply (wp_cbnez_taken_s_sconf (CID := CID10) (mword_of_int (SU + 0x120))
                (mword_of_int 42 : mword 8) (Cregidx (mword_of_int 7)) Ra5 N8
                (K - 30)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HN8a5;
                      exact (su_neq_of_eq_false _ _ (su_inum_nz _ Hnz)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_120 with "Htext"). }
      iIntros (CID11 Hq11). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg174 : add_vec (mword_of_int (SU + 0x120) : mword 64)
                         (sign_extend' 64
                            (sign_extend' 13
                               (concat_vec (mword_of_int 42 : mword 8)
                                  ('b"0"))))
                       = mword_of_int (SU + 0x174)) by pcw.
      iEval (rewrite Htg174) in "Hpc".
      (* the buffer back together for the tail *)
      iEval (rewrite -(su_name_acc dati jj (pa_add (pa_stk sp0 29) 2)))
        in "Hname".
      iEval (rewrite -(su_half_acc dati jj (pa_stk sp0 29) Hal29)) in "Hhalf".
      iAssert ([∗ list] jj0 ∈ seq 0 16,
                 pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] file_byte dati (16 * jj + jj0)%nat)%I
        with "[Hhalf Hname]" as "Hbuf".
      { iEval (rewrite (su_del_split (pa_stk sp0 29)
                          (fun jj0 => file_byte dati (16 * jj + jj0)%nat))).
        iSplitL "Hhalf"; [iExact "Hhalf" | iExact "Hname"]. }
      iDestruct (cpu_own_transport CID7 CID11 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply ("HcE" $! CID11 N8 (mword_of_int (Z.of_nat (16 * jj)))
                (fun jj0 => file_byte dati (16 * jj + jj0)%nat)
                with "[%] Hcg Hown Hpc Hidev Hmeta Hmap Hblocks Hbuf Hpidq
                      Hbslot HX").
      exact HN8regs.
  Qed.

  (* THE BLOCK: the entry test at +0xf8..+0x104, then the loop. *)
  Lemma su_w4 `{GEN : GenId} `{CID0 : CpuId}
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64) (bn : bio_names)
      (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ki : nat) (inumi : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (be : nat -> bv 8)
      (dpv ipv s3v : mword 64)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Vpr : pprivate) :
    (K_readi <= K - 30)%nat ->
    log_geom_ok cov logstart ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true -> lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    ipv = ientry ki ->
    inode_ok cov logstart dni bmi dati ->
    (* durable-disk 2b-inode-3: the child's record-only facts *)
    inode_rec_local dni ->
    bv_unsigned (di_type dni) = T_DIR_z ->
    bv_unsigned (di_nlink dni) <> 0 ->
    dir_dots_ix (bv_unsigned inumi) dni dati ->
    su_regs m sp0 dpv ipv s3v M ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    panic_env -∗
    pc_is (mword_of_int (SU + 0xf8)) -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    (* the byte view's row, for readi's crossing (durable-disk 1c-flip) *)
    fs_bytes_any gfs -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    i_dev (ientry ki) ↦₄{DfracOwn (1/2)} dev -∗
    inode_meta (ientry ki) dni -∗
    inode_map gfs (ientry ki) bmi -∗
    inode_blocks gfs bmi dati -∗
    ([∗ list] jj0 ∈ seq 0 16, pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] be jj0) -∗
    proc_priv_bare (proc_addr jx) pidv Vpr -∗
    bslot -∗
    su_w4_exitE gfs jx ki dev dni bmi dati pidv dq bn
                m sp0 dpv ipv K eb b lks X Vpr -∗
    su_w4_exitD gfs jx ki dev dni bmi dati pidv dq bn
                m sp0 dpv ipv K eb b lks X Vpr -∗
    X -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal Hipv Hiok Hrl_dati Htyz
           Hnlz Hddix Hregs.
    pose proof Hiok as Hiok0.
    destruct Hiok as (Hbmwf & Hbmcv & Hbmc & Htynz & Hszcap & Hiokrest).
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dni))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dni))).
    assert (Hszlt : bv_unsigned (di_size dni) < 2 ^ 31)
      by (assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity);
          lia).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    iIntros "Hcg Hown #Htext #Hkd #Hpe Hpc #Hbio #Hrow #Hkenv #Hprocs #Hdev #Hgeo
             #Hdlk Hidev Hmeta Hmap Hblocks Hbuf Hpidq Hbslot HcE HcD HX".
    (* ===== +0xf8 lw a4,76(s2) -- ip->size ===== *)
    iEval (rewrite /inode_meta) in "Hmeta".
    iDestruct "Hmeta" as "(Hity & Hima & Himi & Hinl & Hisz)".
    iEval (rewrite /i_size) in "Hisz".
    iApply (wp_lw_s_sconf (CID := CID0) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xf8)) Ra4 Rs2
              (mword_of_int 76 : mword 12) M (K - 30)%nat
              (di_size dni : mword 32) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hisz]").
    { iApply (suli_0f8 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hregs) Hipv).
      iExact "Hisz". }
    iIntros (CID1 Hq1) "Hcg Hpc Hisz".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hregs) Hipv) in "Hisz".
    iAssert (inode_meta (ientry ki) dni)
      with "[Hity Hima Himi Hinl Hisz]" as "Hmeta".
    { rewrite /inode_meta /i_size. iFrame. }
    set (M1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_size dni : mword 32))]> M).
    assert (HM1a4 : (M1 !!! Regidx Ra4 : mword 64)
                    = (mword_of_int (bv_unsigned (di_size dni)) : mword 64)).
    { etransitivity; [ rewrite /M1; apply upd_eq |].
      exact (su_size_sext (di_size dni : mword 32) Hszlt). }
    assert (HM1regs : su_regs m sp0 dpv ipv s3v M1)
      by (rewrite /M1; apply su_regs_caller; [exact Hcsa4 | exact Hregs]).
    assert (Hppfc : add_vec_int (mword_of_int (SU + 0xf8) : mword 64) 4
                    = mword_of_int (SU + 0xfc)) by pcw.
    iEval (rewrite Hppfc) in "Hpc".
    (* ===== +0xfc li a5,32 ===== *)
    iApply (wp_li4_s_sconf (CID := CID1) (mword_of_int (SU + 0xfc)) Ra5
              (mword_of_int 32 : mword 12) (mword_of_int 32 : mword 64) M1
              (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0fc with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (M2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 32 : mword 64)]> M1).
    assert (HM2a5 : (M2 !!! Regidx Ra5 : mword 64) = (mword_of_int 32 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a4 : (M2 !!! Regidx Ra4 : mword 64)
                    = (mword_of_int (bv_unsigned (di_size dni)) : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a4 | nz]).
    assert (HM2regs : su_regs m sp0 dpv ipv s3v M2)
      by (rewrite /M2; apply su_regs_caller; [exact Hcsa5 | exact HM1regs]).
    assert (Hpp100 : add_vec_int (mword_of_int (SU + 0xfc) : mword 64) 4
                     = mword_of_int (SU + 0x100)) by pcw.
    iEval (rewrite Hpp100) in "Hpc".
    (* ===== +0x100 bgeu a5,a4 -> +0x8a (32 >=u size: EMPTY) ===== *)
    destruct (decide (bv_unsigned (di_size dni) <= 32)) as [Hle32 | Hgt32].
    - (* -------- the directory has nothing past its dots -------- *)
      iApply (wp_bgeu_taken_s_sconf (CID := CID2) (mword_of_int (SU + 0x100))
                (mword_of_int 8074 : mword 13) Ra4 Ra5 M2 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM2a5 HM2a4;
                      apply su_loop_entry_taken; lia)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_100 with "Htext"). }
      iIntros (CID3 Hq3). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg8a : add_vec (mword_of_int (SU + 0x100) : mword 64)
                        (sign_extend' 64 (mword_of_int 8074 : mword 13))
                      = mword_of_int (SU + 0x8a)) by pcw.
      iEval (rewrite Htg8a) in "Hpc".
      assert (Hdeadall : forall k : nat, (2 <= k)%nat ->
                (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
                dir_inum dati k = bv_0 16).
      { intros k Hk2 Hklt. exfalso.
        pose proof (su_nrec_le (bv_unsigned (di_size dni)) 2 Hsznn
                      ltac:(lia)) as Hn. lia. }
      iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply ("HcD" $! CID3 M2 s3v be
                with "[%] [%] [%] Hcg Hown Hpc Hidev Hmeta Hmap Hblocks Hbuf
                      Hpidq Hbslot HX").
      { exact HM2regs. }
      { exact (su_dots_only_scan (bv_unsigned inumi) dni dati Htyz Hnlz
                 Hddix Hdeadall). }
      { exact Hdeadall. }
    - (* -------- records to scan: fall through into the loop -------- *)
      iApply (wp_bgeu_fall_s_sconf (CID := CID2) (mword_of_int (SU + 0x100))
                (mword_of_int 8074 : mword 13) Ra4 Ra5 M2 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM2a5 HM2a4;
                      apply su_loop_entry_fall; lia)
                with "Hcg Hpc []").
      { iApply (suli_100 with "Htext"). }
      iIntros (CID3 Hq3) "Hcg Hpc".
      assert (Hpp104 : add_vec_int (mword_of_int (SU + 0x100) : mword 64) 4
                       = mword_of_int (SU + 0x104)) by pcw.
      iEval (rewrite Hpp104) in "Hpc".
      (* ===== +0x104 c.mv s3,a5 -- off = 32 ===== *)
      iApply (wp_cmv_s_sconf (CID := CID3) (mword_of_int (SU + 0x104)) Rs3 Ra5
                M2 (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (suli_104 with "Htext"). }
      iIntros (CID4 Hq4) "Hcg Hpc".
      set (M3 := <[Regidx Rs3 := regval_into_reg
                    (add_vec zero_reg (M2 !!! Regidx Ra5))]> M2).
      assert (HM3regs : su_regs m sp0 dpv ipv
                          (mword_of_int (Z.of_nat (16 * 2)) : mword 64) M3).
      { rewrite /M3.
        apply (su_regs_wr_s3 m sp0 dpv ipv s3v
                 (mword_of_int (Z.of_nat (16 * 2)) : mword 64) M2 _);
          [| exact HM2regs].
        rewrite add_vec_zero_l HM2a5. pcw. }
      assert (Hpp106 : add_vec_int (mword_of_int (SU + 0x104) : mword 64) 2
                       = mword_of_int (SU + 0x106)) by pcw.
      iEval (rewrite Hpp106) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID4 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (su_w4_loop (CID0 := CID4) gs jx gl gu gd gk pd pav pu bn gfs
                ga gf cov logstart dev ki inumi dni bmi dati pidv dq dpv ipv
                m sp0 K eb b lks X Vpr Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal
                Hipv Hiok0 Hrl_dati Htyz Hnlz Hddix
                (Z.to_nat (bv_unsigned (di_size dni))) 2%nat M3 be
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros k Hk2 Hklt; exfalso; lia)
                HM3regs
                with "Hcg Hown Htext Hkd Hpe Hpc Hbio Hrow Hkenv Hprocs Hdev Hgeo
                      Hdlk Hidev Hmeta Hmap Hblocks Hbuf Hpidq Hbslot
                      HcE HcD HX").
  Qed.

  (* ================================================================== *)
  (*  W3: +0x72 .. +0x88 -- [c.sdsp s3], [ilock(ip)], the [blez] panic    *)
  (*  guard and the T_DIR test at +0x86.                                  *)
  (*                                                                     *)
  (*    +0x72 c.sdsp s3,200(sp)       (the THIRD shrink-wrapped save)    *)
  (*    +0x74 jal ilock               (a0 = ip, dirlookup's return)       *)
  (*    +0x78 lh a5,74(s2)            (ip->nlink)                        *)
  (*    +0x7c blez a5 -> +0xec        [panic "unlink: nlink < 1"]        *)
  (*    +0x80 lh a4,68(s2) ; +0x84 c.li a5,1                              *)
  (*    +0x86 beq a4,a5 -> +0xf8      (the T_DIR arm: [su_w4])           *)
  (*                                                                     *)
  (*  THE [blez] FALL-THROUGH IS THE ONLY SOURCE OF [di_nlink ip <> 0],   *)
  (*  and it crosses the +0x8a seam unconditionally: every route to       *)
  (*  +0x8a is below it.                                                 *)
  (*                                                                     *)
  (*  THE T_DIR ARM APPLIES [su_w4], instantiating its opaque [X] with    *)
  (*  dp's bundle, the ledger, the frame and BOTH continuations (the      *)
  (*  +0x8a seam and the caller's exit).  [su_w4_exitE] destructs [X],    *)
  (*  repacks BOTH [ic_loaded]s and closes through [Tails.su_tail_e]      *)
  (*  (its [2 * iput_units <= u] is [su_u1_ge9] against [iput_units]);    *)
  (*  [su_w4_exitD] and the non-dir fall-through both land on the         *)
  (*  isdir-indexed +0x8a seam below, with [ip]'s bundle ∀-bound.         *)
  (*                                                                     *)
  (*  THE EXIT CONTINUATIONS SHIFT THE CALLER'S [wp_next] WITH NO CHAIN   *)
  (*  FACTS IN SCOPE: the exit harts are ∀-bound, so the shift's premise  *)
  (*  is discharged by [proc_addr_nonzero] (the index is the literal      *)
  (*  [true] and the process address is not zero), never by               *)
  (*  [wp_next_chain].                                                   *)
  (* ================================================================== *)
  Lemma su_w3 `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (V : pprivate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf bnm0 bp bd be : nat -> bv 8)
      (w5 w6 w30 : mword 64)
      (m M2 : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    inodestart = icfg_ist ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext (pv_upt V) P1 ->
    (* ---- the +0x72 seam's pure facts, verbatim ---- *)
    su_regs m sp0 (ientry kd) (ientry ks)
            (m !!! Regidx Rs3 : mword 64) M2 ->
    (kd < NINODE)%nat ->
    (ks < NINODE)%nat ->
    bv_unsigned dinum < 16 * Z.of_nat nib ->
    di_type dnd = SpecDirlookup.T_DIR ->
    inode_ok cov logstart dnd bmd datd ->
    (* durable-disk 2b-inode-3: the payload's record-only facts *)
    inode_rec_local dnd ->
    dir_ok icfg_nib dnd datd ->
    dir_dots_ix (bv_unsigned dinum) dnd datd ->
    dir_orphan_clean dnd datd ->
    dir_uniq dnd datd ->
    bname 14 nf <> dot_name ->
    bname 14 nf <> dotdot_name ->
    dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
              (bname 14 nf) = Some kk ->
    (M2 !!! Regidx Ra0 : mword 64) = ientry ks ->
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    sie_cap_gpr KT1 M2 (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    panic_env -∗
    pc_is (mword_of_int (SU + 0x72)) -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
    (* ---- [dp], LOCKED and OPEN (the +0x72 seam's bundle) ---- *)
    is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                     (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
    sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
    ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    dlinks gfs (bv_unsigned dinum) dnd bmd datd -∗
    dinode_at gi dinum dnd -∗
    inode_meta (ientry kd) dnd -∗
    inode_addrs (ientry kd) (bm_cells bmd) -∗
    ind_res gfs bmd -∗
    inode_blocks gfs bmd datd -∗
    (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
    dv_ride (bv_unsigned dinum) (dv_of dnd datd) -∗
    fv_ride (bv_unsigned dinum) (fv_of dnd datd) -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L gfs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
    ity_shot gyd (di_type dnd) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    (* ---- [ip], REFERENCED (dirlookup's iget) ---- *)
    inode_ref ks qs dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    (* ...with the unit that iget minted with it (item 7a-wire) *)
    runit_any
      (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    log_opS g n1 Sb1 -∗
    (* ---- the frame, as the +0x72 seam hands it ---- *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] w5 -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
      (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] be jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    (* ---- THE SEAM at +0x8a, indexed by [isdir], [ip]'s bundle ∀-bound.
       [s3x] and the [be] buffer are existential because the isdirempty
       loop moves both; slot 5 is FILLED (this block's own save).  The
       payload at [true] is T_DIR + [dir_dots_only] + the raw dead-scan
       (verbatim [su_dir_links_orphan]'s third premise); at [false] it is
       the type disequality W5-FILE's [dir_links_not_dir] route reads. ---- *)
    (∀ (CIDs : CpuId) (M3 : regfile) (s3x : mword 64) (bex : nat -> bv 8)
       (isdir : bool) (gili gisli gyi : gname) (si qsi : Qp)
       (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8)),
       ⌜su_regs m sp0 (ientry kd) (ientry ks) s3x M3⌝ -∗
       ⌜bv_unsigned (di_nlink dni) <> 0⌝ -∗
       ⌜inode_ok cov logstart dni bmi dati⌝ -∗
       (* durable-disk 2b-inode-3: the child's record-only facts *)
       ⌜inode_rec_local dni⌝ -∗
       ⌜dir_ok icfg_nib dni dati⌝ -∗
       ⌜dir_dots_ix (bv_unsigned (zero_extend' 32
            (dir_inum datd kk : mword 16) : mword 32)) dni dati⌝ -∗
       ⌜dir_orphan_clean dni dati⌝ -∗
       ⌜dir_uniq dni dati⌝ -∗
       ⌜if isdir
        then bv_unsigned (di_type dni) = T_DIR_z
             /\ dir_dots_only dni dati
             /\ (forall k : nat, (2 <= k)%nat ->
                   (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
                   dir_inum dati k = bv_0 16)
        else bv_unsigned (di_type dni) <> T_DIR_z⌝ -∗
       sie_cap_gpr KT1 M3 (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x8a)) -∗
       fs_crash_seam cov logstart -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
       (* ---- [dp], unchanged ---- *)
       is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                        (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
       ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks gfs (bv_unsigned dinum) dnd bmd datd -∗
       dinode_at gi dinum dnd -∗
       inode_meta (ientry kd) dnd -∗
       inode_addrs (ientry kd) (bm_cells bmd) -∗
       ind_res gfs bmd -∗
       inode_blocks gfs bmd datd -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned dinum) (dv_of dnd datd) -∗
       fv_ride (bv_unsigned dinum) (fv_of dnd datd) -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L gfs) (bv_unsigned dinum)
                (era_node dnd bmd datd) -∗
       ity_shot gyd (di_type dnd) -∗
       (* the payload's freeze token (§3.9, RULING A-prime) *)
       ifreeze_off (bv_unsigned dinum) -∗
       inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
       (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
       runit_any (bv_unsigned dinum) -∗
       (* ---- [ip], LOCKED and OPEN ---- *)
       is_sleeplock_gen gili gisli (i_lock (ientry ks)) "inode"%string
                        (ic_tok cn ks) (slh_tok (icfg_isl ks)) -∗
       sleeplocked_q gisli si (i_lock (ientry ks)) pid -∗
       ic_deposit cn ks (DepShr si dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi) -∗
       i_dev (ientry ks) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry ks) ↦₄{DfracOwn (1/2)}
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       i_valid (ientry ks) ↦₄ valid_word true -∗
       dlinks gfs (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32)) dni bmi dati -∗
       dinode_at gi
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni -∗
       inode_meta (ientry ks) dni -∗
       inode_addrs (ientry ks) (bm_cells bmi) -∗
       ind_res gfs bmi -∗
       inode_blocks gfs bmi dati -∗
       (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
       dv_ride (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32)) (dv_of dni dati) -∗
       fv_ride (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32)) (fv_of dni dati) -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L gfs) (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32))
                (era_node dni bmi dati) -∗
       ity_shot gyi (di_type dni) -∗
       (* the payload's freeze token (§3.9, RULING A-prime) *)
       ifreeze_off (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
       inode_ref_short ks (qsi + si)%Qp qsi dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
       runit_any
         (bv_unsigned
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
       log_opS g n1 Sb1 -∗
       (* ---- the frame, slot 5 FILLED ---- *)
       (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈[KT1] w6 -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
       ([∗ list] jj ∈ seq 0 2,
          pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
       ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
       (pa_stk sp0 27) ↦₄[KT1] lo -∗
       (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
         (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
       (pa_stk sp0 30) ↦₈[KT1] w30 -∗
       (* the caller's own exit, handed BACK *)
       wp_next (CID0 := CIDs) true (proc_addr jx) (fun (CIDx : CpuId) =>
         ∀ (mf : regfile) (P' : uptd),
             ⌜callee_saved m mf⌝ -∗
             ⌜uptd_ext (pv_upt V) P'⌝ -∗
             sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
             cpu_own 0 eb (proc_addr jx) b lks -∗
             trap_csrs_ext KT1 eb -∗
             cpu_claim_ext eb (proc_addr jx) -∗
             pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
             bslots 3 -∗
             sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
             sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
             sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
             iref_slots SpecSysUnlink.sys_unlink_slots -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
             ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
             WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hn1 Hupt1 Hregs Hkd Hks Hdinb
           Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq Hnotdot Hnotdd Hfst
           Hma0 Hal27.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hkd #Hpe Hpc #Hbio #Hlog Hseam Hgen #Hdev #Hgeo
             #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen Hsbb Hsbi Hsbs
             #Hbmres #Hkenv #Hprocs Hpriv #Hslkd Hslkdq Hdepd Hidevd
             Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd
             Hdviewd Hfviewd Htop #Hshotd Hfrz Hkeepd Hrud Hchild Hrui HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hseamk Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hiu2 : (2 * iput_units <= n1)%nat).
    { pose proof (su_u1_ge9 w1) as H9. unfold iput_units. lia. }
    (* dp's region-block facts *)
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    (* ip's inum bound: dirlookup's hit is a LIVE record below [nrec], and
       [dir_ok] at the parent's T_DIR bounds every live inum *)
    assert (Htydz : bv_unsigned (di_type dnd) = T_DIR_z)
      by exact (su_tdir_zof _ Htydir).
    assert (Hinums : dir_inums_ok datd
                       (dir_nrec (bv_unsigned (di_size dnd))) nib)
      by (rewrite Hcnib; exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat nib).
    { rewrite su_zext32_unsigned. exact (Hinums kk Hkklt Hkklive). }
    destruct (Hiregb _ Hinb) as [Hiblki Hiblogi].
    (* the process block, opened for the callees' pid fraction, and THE
       CLOSER, built once (W2's shape) *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    iAssert (proc_priv_bare (proc_addr jx) pid (upd_upt V P1) -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* ip's reference: generation NAMED (the share ilock consumes and the
       one-shot it returns must agree), then shed *)
    iEval (rewrite inode_ref_gen_intro) in "Hchild".
    iDestruct "Hchild" as (gyi) "Hchild".
    iEval (rewrite su_shed_gen) in "Hchild".
    iDestruct "Hchild" as "[Hkeepi Hshri]".
    iDestruct (inode_ref_short_gen_forget with "Hkeepi") as "Hkeepi".
    iDestruct (su_esc_acc cn gfs gi cov logstart kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (su_esc_acc cn gfs gi cov logstart ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (su_slk_acc cn ks Hks with "Hslks") as (gili gisli) "#Hslki".
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* ===== +0x72 c.sdsp s3,200(sp) -- slot 5, saved LATER STILL ===== *)
    assert (Hd5 : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64
                       (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
                  = pa_stk sp0 5)
      by (rewrite (su_regs_sp _ _ _ _ _ _ Hregs); apply su_frm5).
    iEval (rewrite -Hd5) in "Hf5".
    iApply (wp_csdsp_s_sconf (CID := CID0) (mword_of_int (SU + 0x72))
              (mword_of_int 25 : mword 6) Rs3 M2 (K - 30)%nat w5 b
              with "Hcg Hpc [] Hf5").
    { iApply (suli_072 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc Hf5".
    iEval (rgne; rewrite Hd5 (su_regs_s3 _ _ _ _ _ _ Hregs)) in "Hf5".
    assert (Hpp74 : add_vec_int (mword_of_int (SU + 0x72) : mword 64) 2
                    = mword_of_int (SU + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x74 jal ra,ilock ===== *)
    iApply (wp_jal_s_sconf (CID := CID1) (mword_of_int (SU + 0x74)) Rra
              (mword_of_int 2089464 : mword 21) M2 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_074 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x74) : mword 64) 4)]> M2).
    assert (Hjil : add_vec (mword_of_int (SU + 0x74) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089464 : mword 21))
                   = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Hjil) in "Hpc".
    assert (HR0ra : (R0 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x74) : mword 64) 4)
      by (rewrite /R0; apply upd_eq).
    assert (HR0a0 : (R0 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /R0 upd_ne; [exact Hma0 | nz]).
    assert (HR0regs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) R0)
      by (rewrite /R0; apply su_regs_caller; [exact Hcsra | exact Hregs]).
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Ilock.wp_ilock_sconf (CID := CID2) gs jx gl gu gd gk pd pav pu bn
              gfs gi cn gili gisli cov logstart inodestart nib ks (qs/2)%Qp
              gyi PlainK dev
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              pid (DfracOwn (1/4)) dqs R0 (K - 30)%nat eb b lks
              (upd_upt V P1) ltac:(exact Kil) Hks Hgeom Hist0 Hiblki Hinb Hj Hgl HR0a0
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hkd Hpc Hpe Hbio Hitinv Hesci Hireg
                    Hslki Hshri Hrui Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID3 Hq3 mil dni bmi fldi)
      "%Hcsil Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkiq Hdepi
       Hidevi Hiinumi Hivalidi Hloadi #Hshoti Hfrzi %Hfldi Hrui %Hilkpi".
    assert (Hpc78 : ret_pc (R0 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x78)) by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc78) in "Hpc".
    assert (Hilregs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) mil)
      by exact (su_regs_cs m sp0 _ _ _ R0 mil Hcsil HR0regs).
    (* [ip]'s loaded bundle, opened: the +0x8a seam wants it in pieces and
       the [lh]s below read two of its meta cells *)
    iDestruct (ic_loaded_open with "Hloadi") as (dati)"(%Hioki & %Hrl_dati & %Hdoki & %Hddixi & %Hdoci & %Hduqi & Hdlnki & Hdiati & Hmetai & Haddrsi & Hindi & Hblocksi & Hdviewi & Hfviewi & Htopi)".
    (* ===== +0x78 lh a5,74(s2) -- ip->nlink ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_nlink) in "Hinli".
    iApply (wp_lh_s_sconf (CID := CID3) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0x78)) Ra5 Rs2
              (mword_of_int 74 : mword 12) mil (K - 30)%nat
              (di_nlink dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinli]").
    { iApply (suli_078 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hilregs)).
      iExact "Hinli". }
    iIntros (CID4 Hq4) "Hcg Hpc Hinli".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hilregs)) in "Hinli".
    iAssert (inode_meta (ientry ks) dni)
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /i_nlink. iFrame. }
    set (M3 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_nlink dni : mword 16))]> mil).
    assert (HM3a5 : (M3 !!! Regidx Ra5 : mword 64)
                    = (sign_extend' 64 (di_nlink dni : mword 16) : mword 64))
      by (rewrite /M3; apply upd_eq).
    assert (HM3regs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) M3)
      by (rewrite /M3; apply su_regs_caller; [exact Hcsa5 | exact Hilregs]).
    assert (Hpp7c : add_vec_int (mword_of_int (SU + 0x78) : mword 64) 4
                    = mword_of_int (SU + 0x7c)) by pcw.
    iEval (rewrite Hpp7c) in "Hpc".
    (* ===== +0x7c blez a5 -> +0xec -- the panic guard ===== *)
    destruct (Z.le_gt_cases (bv_signed (di_nlink dni)) 0) as [Hnpos | Hpos].
    { (* TAKEN: "unlink: nlink < 1", and panic never returns *)
      iApply (wp_bge_x0_taken_s_sconf (CID := CID4) (mword_of_int (SU + 0x7c))
                (mword_of_int 112 : mword 13) Ra5 M3 (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite HM3a5; exact (su_nlink_pos_taken _ Hnpos))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_07c with "Htext"). }
      iNext. iIntros (CID5 Hq5) "Hcg Hpc".
      assert (Htgec : add_vec (mword_of_int (SU + 0x7c) : mword 64)
                        (sign_extend' 64 (mword_of_int 112 : mword 13))
                      = mword_of_int (SU + 0xec)) by pcw.
      iEval (rewrite Htgec) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_nlink (CID0 := CID5) M3 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hkd Hpe Hpc"). }
    (* FALL-THROUGH: the count is signed-positive, so it is NONZERO -- the
       one fact every route below +0x7c carries *)
    iApply (wp_bge_x0_fall_s_sconf (CID := CID4) (mword_of_int (SU + 0x7c))
              (mword_of_int 112 : mword 13) Ra5 M3 (K - 30)%nat b
              ltac:(nz)
              ltac:(rgne; rewrite HM3a5; exact (su_nlink_pos_fall _ Hpos))
              with "Hcg Hpc []").
    { iApply (suli_07c with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    assert (Hnlzi : bv_unsigned (di_nlink dni) <> 0)
      by exact (su_signed_pos_nz _ Hpos).
    assert (Hpp80 : add_vec_int (mword_of_int (SU + 0x7c) : mword 64) 4
                    = mword_of_int (SU + 0x80)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ===== +0x80 lh a4,68(s2) -- ip->type ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_type) in "Hityi".
    iApply (wp_lh_s_sconf (CID := CID5) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0x80)) Ra4 Rs2
              (mword_of_int 68 : mword 12) M3 (K - 30)%nat
              (di_type dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hityi]").
    { iApply (suli_080 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HM3regs)).
      iExact "Hityi". }
    iIntros (CID6 Hq6) "Hcg Hpc Hityi".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HM3regs)) in "Hityi".
    iAssert (inode_meta (ientry ks) dni)
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /i_type. iFrame. }
    set (M4 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dni : mword 16))]> M3).
    assert (HM4a4 : (M4 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4regs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) M4)
      by (rewrite /M4; apply su_regs_caller; [exact Hcsa4 | exact HM3regs]).
    assert (Hpp84 : add_vec_int (mword_of_int (SU + 0x80) : mword 64) 4
                    = mword_of_int (SU + 0x84)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    (* ===== +0x84 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := CID6) (mword_of_int (SU + 0x84)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              M4 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_084 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M5 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> M4).
    assert (HM5a4 : (M5 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a4 | nz]).
    assert (HM5a5 : (M5 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /M5; apply upd_eq).
    assert (HM5regs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) M5)
      by (rewrite /M5; apply su_regs_caller; [exact Hcsa5 | exact HM4regs]).
    assert (Hpp86 : add_vec_int (mword_of_int (SU + 0x84) : mword 64) 2
                    = mword_of_int (SU + 0x86)) by pcw.
    iEval (rewrite Hpp86) in "Hpc".
    (* ===== +0x86 beq a4,a5 -> +0xf8 -- the T_DIR test ===== *)
    assert (Htgf8 : add_vec (mword_of_int (SU + 0x86) : mword 64)
                      (sign_extend' 64 (mword_of_int 114 : mword 13))
                    = mword_of_int (SU + 0xf8)) by pcw.
    destruct (decide (bv_unsigned (di_type dni) = T_DIR_z))
      as [Htyzi | Htynzi].
    - (* ---------------- T_DIR: the inlined isdirempty ---------------- *)
      iApply (wp_beq_taken_s_sconf (CID := CID7) (mword_of_int (SU + 0x86))
                (mword_of_int 114 : mword 13) Ra5 Ra4 M5 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM5a4 HM5a5;
                      exact (su_tdir_eq _ (su_tdir_z _ Htyzi)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_086 with "Htext"). }
      iIntros (CID8 Hq8). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgf8) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      (* the loop's opaque [X]: dp's bundle, the ledger, the frame and BOTH
         continuations, combined so [su_w4]'s exits can hand them back *)
      iCombine "Hseam Hgen Hbs2 Hsbb Hsbi Hsbs Hpre Hslkdq
                Hdepd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad Haddrsd
                Hindd Hblocksd Hdviewd Hfviewd Htop Hfrz Hkeepd Hrud Hslkiq Hdepi Hiinumi
                Hivalidi
                Hdlnki Hdiati Hdviewi Hfviewi Htopi Hfrzi Hkeepi Hrui HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14
                Hnm2 HbP H27lo H27hi H30 Hseamk Hcont" as "HX".
      (* the byte view's row (durable-disk 1c-flip step 3) *)
      iPoseProof (ireg_inv_bytes with "Hireg") as "#Hrow".
      iApply (su_w4 (CID0 := CID8) gs jx gl gu gd gk pd pav pu bn gfs ga gf
                cov logstart dev ks
                (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                dni bmi dati pid (DfracOwn (1/4)) be
                (ientry kd) (ientry ks) (m !!! Regidx Rs3 : mword 64)
                m M5 sp0 K eb b lks _
                (upd_upt V P1) Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal eq_refl
                Hioki Hrl_dati Htyzi
                Hnlzi Hddixi HM5regs
                with "Hcg Hown Htext Hkd Hpe Hpc Hbio Hrow Hkenv Hprocs Hdev Hgeo
                      Hdlk Hidevi Hmetai [Haddrsi Hindi] Hblocksi HbE Hpidq
                      Hbs1 [] [] HX").
      { rewrite /inode_map. iFrame "Haddrsi Hindi". }
      { (* ---- ARM E: a live non-dot record -- [Tails.su_tail_e] ---- *)
        iIntros (CIDx Mx s3x bex) "%Hxregs Hcg Hown Hpc Hidevi Hmetai Hmapi
                                    Hblocksi Hbuf Hpidq Hbslot HX".
        iDestruct "HX" as "(Hseam & Hgen & Hbs2 & Hsbb & Hsbi & Hsbs
                            & Hpre & Hslkdq & Hdepd & Hidevd &
                            Hiinumd & Hivalidd & Hdlnkd & Hdiatd & Hmetad &
                            Haddrsd & Hindd & Hblocksd & Hdviewd & Hfviewd & Htop & Hfrz & Hkeepd & Hrud &
                            Hslkiq &
                             Hdepi & Hiinumi & Hivalidi & Hdlnki &
                            Hdiati & Hdviewi & Hfviewi & Htopi & Hfrzi & Hkeepi & Hrui & HopS & Hf1 & Hf2 & Hf3 & Hf4 &
                            Hf5 & Hf6 & HbD & Hnm14 & Hnm2 & HbP & H27lo &
                            H27hi & H30 & Hseamk & Hcont)".
        iDestruct "Hmapi" as "[Haddrsi Hindi]".
        (* both bundles repacked: neither release below opens them *)
        iAssert (ic_loaded gfs gi cov logstart kd dinum dnd bmd)
          with "[Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd
                 Htop]" as "Hloadd".
        { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists datd.
          iFrame "Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd
                  Htop".
          iPureIntro. split_and!;[exact Hiok | exact Hrl_datd | exact Hdok | exact Hddix | exact Hdoc | exact Hduq]. }
        iAssert (ic_loaded gfs gi cov logstart ks
                   (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                   dni bmi)
          with "[Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi
                 Htopi]" as "Hloadi".
        { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists dati.
          iFrame "Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi
                  Htopi".
          iPureIntro. split_and!;[exact Hioki | exact Hrl_dati | exact Hdoki | exact Hddixi | exact Hdoci
            | exact Hduqi]. }
        (* the buffers and slot 27, put back for the tail *)
        iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
          as "HbNj".
        iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
        iDestruct (su_off_join sp0 lo
                     (mword_of_int (Z.of_nat (16 * kk)) : mword 32) Hal27
                     with "H27lo H27hi") as "H27".
        assert (HMxsp : su_sp sp0 Mx) by exact (su_regs_sp _ _ _ _ _ _ Hxregs).
        assert (HMxthr : su_thr m Mx)
          by exact (su_regs_thr _ _ _ _ _ _ Hxregs).
        assert (HMxs1 : (Mx !!! Regidx Rs1 : mword 64) = ientry kd)
          by exact (su_regs_s1 _ _ _ _ _ _ Hxregs).
        assert (HMxs2 : (Mx !!! Regidx Rs2 : mword 64) = ientry ks)
          by exact (su_regs_s2 _ _ _ _ _ _ Hxregs).
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDx)
                     ltac:(intros [Hf | Hz];
                           [ discriminate
                           | exfalso; exact (proc_addr_nonzero jx Hj Hz) ])
                     with "Hcont") as "Hcont".
        iApply (Tails.su_tail_e (CID0 := CIDx) gs jx gl gu gd gk pd pav pu bn
                  g gfs gi cn gtl gild gisld gili gisli cov logstart bmapstart
                  inodestart nib size dev kd qdi sd gyd dinum dnd bmd
                  ks (qs/2)%Qp (qs/2)%Qp gyi
                  (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                  dni bmi n1 pid (DfracOwn (1/4)) dqb dqs m Mx sp0 K eb b lks
                  w6
                  (word_of_words lo (mword_of_int (Z.of_nat (16 * kk))
                                     : mword 32))
                  w30 bd bnf bp bex
                  (upd_upt V P1) Kiup Keo K30 Kpop Hkd Hks Hgeom Hsize Hbm0 Hbmcov Hbmlog
                  Hist0 Hdiblk Hdiblog Hdinb Hiblki Hiblogi Hinb Hcovb Hiu2
                  Hj Hgl Hlkempty Hsp0 HMxsp HMxthr HMxs1 HMxs2 Hal
                  with "Hcg Hown [] [] Htext Hkd Hpc Hpe Hbio Hlog Hseam Hgen
                        Hitab Hitinv Hescd Hesci Hireg Hropen Hslkd Hslkdq
                        Hdepd Hidevd Hiinumd Hivalidd Hloadd Hshotd Hfrz
                        Hkeepd Hrud
                        Hslki Hslkiq Hdepi Hidevi Hiinumi Hivalidi
                        Hloadi Hshoti Hfrzi Hkeepi Hrui Hsbb Hsbi Hbmres Hpidq Hprocs
                        Hdev Hgeo Hdlk [Hbslot Hbs2] [HopS] Hf1 Hf2 Hf3 Hf4
                        Hf5 Hf6 HbD HbNj HbP H27 Hbuf H30
                        [Hcont Hpre Hsbs]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply su_bs3. iFrame "Hbslot Hbs2". }
        { rewrite /log_op. iExists Sb1. iExact "HopS". }
        iEval (rewrite /wp_next).
        iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce
                                        Hcce Hpc Hpidq Hsbb Hsbi Hbsl
                                        Hislots".
        iDestruct ("Hpre" with "Hpidq") as "Hpriv".
        iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hbsl Hsbb Hsbi Hsbs [Hislots] Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt1. }
        { rewrite su_slots2. iExact "Hislots". }
        { left. rewrite Ha0f. reflexivity. } }
      { (* ---- the EMPTY exit: the +0x8a seam at [isdir = true] ---- *)
        iIntros (CIDx Mx s3x bex) "%Hxregs %Hdots %Hdead Hcg Hown Hpc Hidevi
                                    Hmetai Hmapi Hblocksi Hbuf Hpidq Hbslot
                                    HX".
        iDestruct "HX" as "(Hseam & Hgen & Hbs2 & Hsbb & Hsbi & Hsbs
                            & Hpre & Hslkdq & Hdepd & Hidevd &
                            Hiinumd & Hivalidd & Hdlnkd & Hdiatd & Hmetad &
                            Haddrsd & Hindd & Hblocksd & Hdviewd & Hfviewd & Htop & Hfrz & Hkeepd & Hrud &
                            Hslkiq &
                             Hdepi & Hiinumi & Hivalidi & Hdlnki &
                            Hdiati & Hdviewi & Hfviewi & Htopi & Hfrzi & Hkeepi & Hrui & HopS & Hf1 & Hf2 & Hf3 & Hf4 &
                            Hf5 & Hf6 & HbD & Hnm14 & Hnm2 & HbP & H27lo &
                            H27hi & H30 & Hseamk & Hcont)".
        iDestruct "Hmapi" as "[Haddrsi Hindi]".
        iDestruct ("Hpre" with "Hpidq") as "Hpriv".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDx)
                     ltac:(intros [Hf | Hz];
                           [ discriminate
                           | exfalso; exact (proc_addr_nonzero jx Hj Hz) ])
                     with "Hcont") as "Hcont".
        iApply ("Hseamk" $! CIDx Mx s3x bex true gili gisli gyi (qs/2)%Qp
                  (qs/2)%Qp dni bmi dati
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hown Hpc Hseam Hgen
                        [Hbslot Hbs2] Hsbb Hsbi Hsbs Hpriv Hslkd
                        Hslkdq Hdepd Hidevd Hiinumd Hivalidd Hdlnkd
                        Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd Hfrz Hkeepd Hrud
                        Hslki Hslkiq Hdepi Hidevi Hiinumi Hivalidi
                        Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi Htopi Hshoti
                        Hfrzi Hkeepi Hrui HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2
                        HbP H27lo H27hi Hbuf H30 [Hcont]").
        { exact Hxregs. }
        { exact Hnlzi. }
        { exact Hioki. }
        { exact Hrl_dati. }
        { exact Hdoki. }
        { exact Hddixi. }
        { exact Hdoci. }
        { exact Hduqi. }
        { split_and!; [exact Htyzi | exact Hdots | exact Hdead]. }
        { iApply su_bs3. iFrame "Hbslot Hbs2". }
        { iExact "Hcont". } }
    - (* ---------------- NOT a directory: fall to +0x8a ---------------- *)
      iApply (wp_beq_fall_s_sconf (CID := CID7) (mword_of_int (SU + 0x86))
                (mword_of_int 114 : mword 13) Ra5 Ra4 M5 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM5a4 HM5a5;
                      exact (su_tdir_ne _ (su_tdir_z_ne _ Htynzi)))
                with "Hcg Hpc []").
      { iApply (suli_086 with "Htext"). }
      iIntros (CID8 Hq8) "Hcg Hpc".
      assert (Hpp8a : add_vec_int (mword_of_int (SU + 0x86) : mword 64) 4
                      = mword_of_int (SU + 0x8a)) by pcw.
      iEval (rewrite Hpp8a) in "Hpc".
      iDestruct ("Hpre" with "Hpidq") as "Hpriv".
      iDestruct (cpu_own_transport CID3 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                   ltac:(intros [Hf | Hz];
                         [ discriminate
                         | exfalso; exact (proc_addr_nonzero jx Hj Hz) ])
                   with "Hcont") as "Hcont".
      iApply ("Hseamk" $! CID8 M5 (m !!! Regidx Rs3 : mword 64) be false
                gili gisli gyi (qs/2)%Qp (qs/2)%Qp dni bmi dati
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hown Hpc Hseam Hgen
                      [Hbs1 Hbs2] Hsbb Hsbi Hsbs Hpriv Hslkd Hslkdq
                      Hdepd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd
                      Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd Hfrz Hkeepd Hrud Hslki
                      Hslkiq Hdepi Hidevi Hiinumi Hivalidi Hdlnki
                      Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi Htopi Hshoti Hfrzi Hkeepi Hrui HopS
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 [Hcont]").
      { exact HM5regs. }
      { exact Hnlzi. }
      { exact Hioki. }
      { exact Hrl_dati. }
      { exact Hdoki. }
      { exact Hddixi. }
      { exact Hdoci. }
      { exact Hduqi. }
      { exact Htynzi. }
      { iApply su_bs3. iFrame "Hbs1 Hbs2". }
      { iExact "Hcont". }
  Qed.

  (* ================================================================== *)
  (*  W5-FILE: +0x8a .. +0xe0 at the +0x8a seam's [isdir = false].       *)
  (*                                                                     *)
  (*    memset(&de,0,16) ; writei(dp,0,&de,off,16)  -- the zeroing.      *)
  (*    VERDICT #3 (home-live) and VERDICT #1 ([dir_links_unlink] +      *)
  (*    [dinode_at_excl] + the [b = true] refutation through             *)
  (*    [IregDirBit.ireg_dirbit_ty]) both fire at the writei.            *)
  (*    Then the +0xb4 T_DIR test FALLS (this arm's payload),            *)
  (*    iunlockput(dp) CREDITED off [wi16_post]'s membership trio,       *)
  (*    ip->nlink-- / iupdate(ip) at the LEFT receipt (a FILE's          *)
  (*    decrement can land at zero), iunlockput(ip) credited off         *)
  (*    iupdate's own [∪ {IBLOCK ip}], end_op, a0 = 0, the three         *)
  (*    reloads, and the shared epilogue.                                *)

  (* ================================================================== *)
  Lemma su_w5_file `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (V : pprivate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf bnm0 bp bd bex : nat -> bv 8)
      (w6 w30 : mword 64)
      (gili gisli gyi : gname) (si qsi : Qp)
      (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8))
      (m M3 : regfile) (sp0 s3x : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    g = icfg_log ->
    printk_gen_contract (kt := KT1) gpr gu gd ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    inodestart = icfg_ist ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext (pv_upt V) P1 ->
    (kd < NINODE)%nat ->
    (ks < NINODE)%nat ->
    bv_unsigned dinum < 16 * Z.of_nat nib ->
    di_type dnd = SpecDirlookup.T_DIR ->
    inode_ok cov logstart dnd bmd datd ->
    (* durable-disk 2b-inode-3: the payload's record-only facts *)
    inode_rec_local dnd ->
    dir_ok icfg_nib dnd datd ->
    dir_dots_ix (bv_unsigned dinum) dnd datd ->
    dir_orphan_clean dnd datd ->
    dir_uniq dnd datd ->
    bname 14 nf <> dot_name ->
    bname 14 nf <> dotdot_name ->
    dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
              (bname 14 nf) = Some kk ->
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    (* ---- the +0x8a seam's pure facts, at the FILE payload ---- *)
    su_regs m sp0 (ientry kd) (ientry ks) s3x M3 ->
    bv_unsigned (di_nlink dni) <> 0 ->
    inode_ok cov logstart dni bmi dati ->
    (* durable-disk 2b-inode-3: the child's record-only facts *)
    inode_rec_local dni ->
    dir_ok icfg_nib dni dati ->
    dir_dots_ix (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni dati ->
    dir_orphan_clean dni dati ->
    dir_uniq dni dati ->
    bv_unsigned (di_type dni) <> T_DIR_z ->
    sie_cap_gpr KT1 M3 (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    printk_env gpr gu gd -∗
    pc_is (mword_of_int (SU + 0x8a)) -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
    (* ---- [dp], LOCKED and OPEN ---- *)
    is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                     (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
    sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
    ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    dlinks gfs (bv_unsigned dinum) dnd bmd datd -∗
    dinode_at gi dinum dnd -∗
    inode_meta (ientry kd) dnd -∗
    inode_addrs (ientry kd) (bm_cells bmd) -∗
    ind_res gfs bmd -∗
    inode_blocks gfs bmd datd -∗
    (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
    dv_ride (bv_unsigned dinum) (dv_of dnd datd) -∗
    fv_ride (bv_unsigned dinum) (fv_of dnd datd) -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L gfs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
    ity_shot gyd (di_type dnd) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    (* ---- [ip], LOCKED and OPEN ---- *)
    is_sleeplock_gen gili gisli (i_lock (ientry ks)) "inode"%string
                     (ic_tok cn ks) (slh_tok (icfg_isl ks)) -∗
    sleeplocked_q gisli si (i_lock (ientry ks)) pid -∗
    ic_deposit cn ks (DepShr si dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi) -∗
    i_dev (ientry ks) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry ks) ↦₄{DfracOwn (1/2)}
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    i_valid (ientry ks) ↦₄ valid_word true -∗
    dlinks gfs (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni bmi dati -∗
    dinode_at gi
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni -∗
    inode_meta (ientry ks) dni -∗
    inode_addrs (ientry ks) (bm_cells bmi) -∗
    ind_res gfs bmi -∗
    inode_blocks gfs bmi dati -∗
    (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
    dv_ride (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (dv_of dni dati) -∗
    fv_ride (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (fv_of dni dati) -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L gfs) (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (era_node dni bmi dati) -∗
    ity_shot gyi (di_type dni) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    inode_ref_short ks (qsi + si)%Qp qsi dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any
      (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    log_opS g n1 Sb1 -∗
    (* ---- the frame, slot 5 FILLED ---- *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
      (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hglog Hprk Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hn1 Hupt1 Hkd Hks
           Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq Hnotdot Hnotdd
           Hfst Hal27
           Hregs Hnlzi Hioki Hrl_dati Hdoki Hddixi Hdoci Hduqi Htynzi.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hdata #Hprenv Hpc #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hpriv
             #Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop #Hshotd Hfrz Hkeepd Hrud
             #Hslki Hslkiq Hdepi Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi Htopi #Hshoti Hfrzi Hkeepi Hrui HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpanenv".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbeq. cbn in Hbeq.
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa3 : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    (* ---- the pure groundwork ---- *)
    assert (Htydz : bv_unsigned (di_type dnd) = T_DIR_z)
      by exact (su_tdir_zof _ Htydir).
    assert (Hinums : dir_inums_ok datd
                       (dir_nrec (bv_unsigned (di_size dnd))) nib)
      by (rewrite Hcnib; exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hkkname : bname 14 (dir_name datd kk) = bname 14 nf)
      by exact (dir_first_name _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat nib).
    { rewrite su_zext32_unsigned. exact (Hinums kk Hkklt Hkklive). }
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    destruct (Hiregb _ Hinb) as [Hiblki Hiblogi].
    (* VERDICT #3 -- the home-live derivation: the matched record's name is
       neither dot, so [dp] cannot be orphaned. *)
    assert (Hdplive : bv_unsigned (di_nlink dnd) <> 0).
    { intro Hz.
      destruct (Hdoc Htydz Hz kk Hkklt Hkklive) as [Hd | Hd];
        rewrite Hkkname in Hd; [exact (Hnotdot Hd) | exact (Hnotdd Hd)]. }
    (* ...and the matched record is neither dot SLOT *)
    destruct (Hddix Htydz Hdplive) as
      (Hnrec2 & Hlv0 & Hself0 & Hname0 & Hlv1 & Hname1).
    assert (Hkk0 : kk <> 0%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname0.
      exact (Hnotdot Hname0). }
    assert (Hkk1 : kk <> 1%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname1.
      exact (Hnotdd Hname1). }
    assert (Hkk0' : (0%nat <> kk)) by (intro He; apply Hkk0; symmetry; exact He).
    assert (Hkk1' : (1%nat <> kk)) by (intro He; apply Hkk1; symmetry; exact He).
    (* the byte bound of the zeroed slot *)
    assert (Hszcap : bv_unsigned (di_size dnd)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { destruct Hiok as (_ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dnd))
      by (pose proof (bv_unsigned_in_range _ (di_size dnd)) as Hr; lia).
    assert (Hkk16 : (16 * kk + 16 <= Z.to_nat (bv_unsigned (di_size dnd)))%nat).
    { pose proof (su_nrec16 (bv_unsigned (di_size dnd)) Hsznn) as Hle. lia. }
    assert (HkkZ : Z.of_nat (16 * kk + 16)%nat <= bv_unsigned (di_size dnd)).
    { rewrite <- (Z2Nat.id (bv_unsigned (di_size dnd)) Hsznn).
      apply Nat2Z.inj_le. exact Hkk16. }
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (Hkk31 : Z.of_nat (16 * kk)%nat < 2 ^ 31).
    { rewrite Nat2Z.inj_add in HkkZ. lia. }
    (* the record does not name [dp] ITSELF -- VERDICT #1's exclusivity
       half: two full [dinode_at]s at one inum collide. *)
    destruct (decide (bv_unsigned (dir_inum datd kk) = bv_unsigned dinum))
      as [Heqi | Hnotself].
    { assert (Hweq : (zero_extend' 32 (dir_inum datd kk : mword 16)
                      : mword 32) = dinum)
        by (apply bv_eq; rewrite su_zext32_unsigned; exact Heqi).
      iEval (rewrite Hweq) in "Hdiati".
      iExFalso. iApply (dinode_at_excl with "Hdiatd Hdiati"). }
    (* the process block, opened for the callees' pid fraction, and THE
       CLOSER, built once (W2/W3's shape) *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    iAssert (proc_priv_bare (proc_addr jx) pid (upd_upt V P1) -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* ===== +0x8a addi s3,s0,-64 -- writei's [&de] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID0) (mword_of_int (SU + 0x8a)) Rs3 Rs0
              (mword_of_int 4032 : mword 12) M3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_08a with "Htext"). }
    iIntros (D1 Hd1) "Hcg Hpc".
    set (A1 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12)))]> M3).
    assert (HA1v : add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12))
                   = pa_stk sp0 8).
    { rewrite (su_regs_s0 _ _ _ _ _ _ Hregs). apply su_bufde. }
    assert (HA1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A1).
    { rewrite /A1.
      exact (su_regs_wr_s3 m sp0 (ientry kd) (ientry ks) s3x (pa_stk sp0 8)
               M3 _ HA1v Hregs). }
    assert (Hpp8e : add_vec_int (mword_of_int (SU + 0x8a) : mword 64) 4
                    = mword_of_int (SU + 0x8e)) by pcw.
    iEval (rewrite Hpp8e) in "Hpc".
    (* ===== +0x8e c.li a2,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D1) (mword_of_int (SU + 0x8e)) Ra2
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              A1 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_08e with "Htext"). }
    iIntros (D2 Hd2) "Hcg Hpc".
    set (A2 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> A1).
    assert (HA2a2 : (A2 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A2; apply upd_eq).
    assert (HA2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A2)
      by (rewrite /A2; apply su_regs_caller; [exact Hcsa2 | exact HA1regs]).
    assert (Hpp90 : add_vec_int (mword_of_int (SU + 0x8e) : mword 64) 2
                    = mword_of_int (SU + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x90 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D2) (mword_of_int (SU + 0x90)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              A2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_090 with "Htext"). }
    iIntros (D3 Hd3) "Hcg Hpc".
    set (A3 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> A2).
    assert (HA3a1 : (A3 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A3; apply upd_eq).
    assert (HA3a2 : (A3 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a2 | nz]).
    assert (HA3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A3)
      by (rewrite /A3; apply su_regs_caller; [exact Hcsa1 | exact HA2regs]).
    assert (Hpp92 : add_vec_int (mword_of_int (SU + 0x90) : mword 64) 2
                    = mword_of_int (SU + 0x92)) by pcw.
    iEval (rewrite Hpp92) in "Hpc".
    (* ===== +0x92 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D3) (mword_of_int (SU + 0x92)) Ra0 Rs3 A3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_092 with "Htext"). }
    iIntros (D4 Hd4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (A3 !!! Regidx Rs3))]> A3).
    assert (HA4a0 : (A4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /A4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HA3regs). }
    assert (HA4a1 : (A4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a1 | nz]).
    assert (HA4a2 : (A4 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a2 | nz]).
    assert (HA4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A4)
      by (rewrite /A4; apply su_regs_caller; [exact Hcsa0 | exact HA3regs]).
    assert (Hpp94 : add_vec_int (mword_of_int (SU + 0x92) : mword 64) 2
                    = mword_of_int (SU + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 jal ra,memset ===== *)
    iApply (wp_jal_s_sconf (CID := D4) (mword_of_int (SU + 0x94)) Rra
              (mword_of_int 2079820 : mword 21) A4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_094 with "Htext"). }
    iIntros (D5 Hd5) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)]> A4).
    assert (Hjms : add_vec (mword_of_int (SU + 0x94) : mword 64)
                     (sign_extend' 64 (mword_of_int 2079820 : mword 21))
                   = mword_of_int KernelSyms.memset) by pcw.
    iEval (rewrite Hjms) in "Hpc".
    assert (HA5ra : (A5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5a0 : (A5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8)
      by (rewrite /A5 upd_ne; [exact HA4a0 | nz]).
    assert (HA5a1 : (A5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a1 | nz]).
    assert (HA5a2 : (A5 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a2 | nz]).
    assert (HA5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A5)
      by (rewrite /A5; apply su_regs_caller; [exact Hcsra | exact HA4regs]).
    iApply (Memset.wp_memset_sconf KT1 KT1 (CID := D5) A5 (K - 30)%nat 16
              (mword_of_int 0 : mword 64) bd b (proc_addr jx)
              K2 ltac:(vm_compute; reflexivity) HA5a1
              ltac:(rewrite HA5a2; pcw)
              with "Hcg Htext Hpc [HbD]").
    { iEval (rewrite HA5a0). iExact "HbD". }
    iIntros (D6 Hd6 mms) "Hcg Hpc HbD %Hcsms".
    iEval (rewrite HA5a0) in "HbD".
    assert (Hpc98 : ret_pc (A5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x98)) by (rewrite HA5ra; pcw).
    iEval (rewrite Hpc98) in "Hpc".
    assert (Hmsregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mms)
      by exact (su_regs_cs m sp0 _ _ _ A5 mms Hcsms HA5regs).
    (* the memset byte is NUL *)
    assert (Hcb : nth_byte (autocast (T := mword)
                    (subrange_vec_dec (mword_of_int 0 : mword 64)
                       (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0%nat = NUL)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb) in "HbD".
    (* ===== +0x98 c.li a4,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D6) (mword_of_int (SU + 0x98)) Ra4
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mms (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_098 with "Htext"). }
    iIntros (D7 Hd7) "Hcg Hpc".
    set (B1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mms).
    assert (HB1a4 : (B1 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B1; apply upd_eq).
    assert (HB1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B1)
      by (rewrite /B1; apply su_regs_caller; [exact Hcsa4 | exact Hmsregs]).
    assert (Hpp9a : add_vec_int (mword_of_int (SU + 0x98) : mword 64) 2
                    = mword_of_int (SU + 0x9a)) by pcw.
    iEval (rewrite Hpp9a) in "Hpc".
    (* ===== +0x9a lw a3,-212(s0) -- [uint off], slot 27's UPPER word ===== *)
    iApply (wp_lw_s_sconf (CID := D7) (mword_of_int (SU + 0x9a)) Ra3 Rs0
              (mword_of_int 3884 : mword 12) B1 (K - 30)%nat
              (mword_of_int (Z.of_nat (16 * kk)) : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H27hi]").
    { iApply (suli_09a with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell).
      iExact "H27hi". }
    iIntros (D8 Hd8) "Hcg Hpc H27hi".
    iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell)
      in "H27hi".
    set (B2 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64
                     (mword_of_int (Z.of_nat (16 * kk)) : mword 32))]> B1).
    assert (Ha3lit : (sign_extend' 64
                        (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                      : mword 64)
                     = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { assert (Hus : bv_unsigned (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                    = Z.of_nat (16 * kk)%nat)
        by (apply moi32_small; lia).
      rewrite su_size_sext; rewrite Hus; [reflexivity | lia]. }
    assert (HB2a3 : (B2 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { etransitivity; [rewrite /B2; apply upd_eq |]. exact Ha3lit. }
    assert (HB2a4 : (B2 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1a4 | nz]).
    assert (HB2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B2)
      by (rewrite /B2; apply su_regs_caller; [exact Hcsa3 | exact HB1regs]).
    assert (Hpp9e : add_vec_int (mword_of_int (SU + 0x9a) : mword 64) 4
                    = mword_of_int (SU + 0x9e)) by pcw.
    iEval (rewrite Hpp9e) in "Hpc".
    (* ===== +0x9e c.mv a2,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D8) (mword_of_int (SU + 0x9e)) Ra2 Rs3 B2
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_09e with "Htext"). }
    iIntros (D9 Hd9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B2 !!! Regidx Rs3))]> B2).
    assert (HB3a2 : (B3 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /B3; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HB2regs). }
    assert (HB3a3 : (B3 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a3 | nz]).
    assert (HB3a4 : (B3 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a4 | nz]).
    assert (HB3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B3)
      by (rewrite /B3; apply su_regs_caller; [exact Hcsa2 | exact HB2regs]).
    assert (Hppa0 : add_vec_int (mword_of_int (SU + 0x9e) : mword 64) 2
                    = mword_of_int (SU + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa0 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D9) (mword_of_int (SU + 0xa0)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              B3 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a0 with "Htext"). }
    iIntros (D10 Hd10) "Hcg Hpc".
    set (B4 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> B3).
    assert (HB4a1 : (B4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B4; apply upd_eq).
    assert (HB4a2 : (B4 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B4 upd_ne; [exact HB3a2 | nz]).
    assert (HB4a3 : (B4 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a3 | nz]).
    assert (HB4a4 : (B4 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a4 | nz]).
    assert (HB4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B4)
      by (rewrite /B4; apply su_regs_caller; [exact Hcsa1 | exact HB3regs]).
    assert (Hppa2 : add_vec_int (mword_of_int (SU + 0xa0) : mword 64) 2
                    = mword_of_int (SU + 0xa2)) by pcw.
    iEval (rewrite Hppa2) in "Hpc".
    (* ===== +0xa2 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D10) (mword_of_int (SU + 0xa2)) Ra0 Rs1 B4
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0a2 with "Htext"). }
    iIntros (D11 Hd11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B4 !!! Regidx Rs1))]> B4).
    assert (HB5a0 : (B5 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /B5; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HB4regs). }
    assert (HB5a1 : (B5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a1 | nz]).
    assert (HB5a2 : (B5 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B5 upd_ne; [exact HB4a2 | nz]).
    assert (HB5a3 : (B5 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a3 | nz]).
    assert (HB5a4 : (B5 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a4 | nz]).
    assert (HB5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B5)
      by (rewrite /B5; apply su_regs_caller; [exact Hcsa0 | exact HB4regs]).
    assert (Hppa4 : add_vec_int (mword_of_int (SU + 0xa2) : mword 64) 2
                    = mword_of_int (SU + 0xa4)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ===== +0xa4 jal ra,writei -- THE ZEROING ===== *)
    iApply (wp_jal_s_sconf (CID := D11) (mword_of_int (SU + 0xa4)) Rra
              (mword_of_int 2090644 : mword 21) B5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0a4 with "Htext"). }
    iIntros (D12 Hd12) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)]> B5).
    assert (Hjwi : add_vec (mword_of_int (SU + 0xa4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090644 : mword 21))
                   = mword_of_int KernelSyms.writei) by pcw.
    iEval (rewrite Hjwi) in "Hpc".
    assert (HB6ra : (B6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)
      by (rewrite /B6; apply upd_eq).
    assert (HB6a0 : (B6 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /B6 upd_ne; [exact HB5a0 | nz]).
    assert (HB6a1 : (B6 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a1 | nz]).
    assert (HB6a2 : (B6 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B6 upd_ne; [exact HB5a2 | nz]).
    assert (HB6a3 : (B6 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a3 | nz]).
    assert (HB6a4 : (B6 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a4 | nz]).
    assert (HB6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B6)
      by (rewrite /B6; apply su_regs_caller; [exact Hcsra | exact HB5regs]).
    (* [inode_ok dp]'s conjuncts, read once *)
    assert (Hiok0 : inode_ok cov logstart dnd bmd datd) by exact Hiok.
    destruct Hiok0 as (Hwfd & Hcovd & Haddrd & Htynzd & _ & Hhzd & Hszdd).
    assert (Hoffn31 : Z.of_nat (16 * kk)%nat + Z.of_nat 16%nat < 2 ^ 31)
      by lia.
    assert (Hszd31 : bv_unsigned (di_size dnd) < 2 ^ 31) by lia.
    pose proof (su_u1_ge9 w1) as Hge9.
    assert (Hcost : (wi_cost_bmonly (16 * kk) 16 <= n1)%nat)
      by (rewrite (su_wi_cost kk); lia).
    assert (Htynzz : bv_unsigned (di_type dnd) <> 0)
      by (rewrite Htydz; unfold T_DIR_z; lia).
    assert (Hnls : di_nlink_stable dnd dnd)
      by (apply di_nlink_stable_refl; exact Htynzz).
    assert (Hbmgeom : bitmap_geom_ok cov logstart bmapstart size)
      by (unfold bitmap_geom_ok;
          exact (conj Hsize (conj Hbm0 (conj Hbmcov Hbmlog)))).
    assert (Ha1t : eq_vec (B6 !!! Regidx Ra1 : mword 64) (zero_reg : mword 64)
                   = negb false)
      by (rewrite HB6a1; vm_compute; reflexivity).
    assert (Ha3t : (B6 !!! Regidx Ra3 : mword 64)
                   = (mword_of_int (Z.of_nat (16 * kk)%nat) : mword 64))
      by (rewrite HB6a3; reflexivity).
    assert (Ha4t : (B6 !!! Regidx Ra4 : mword 64)
                   = (mword_of_int (Z.of_nat 16%nat) : mword 64))
      by (rewrite HB6a4; pcw).
    iDestruct (cpu_own_transport CID0 D12 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Writei.wp_writei_gen KT1 (CID := D12) gs jx gl gu gd gk pd pav pu bn
              g gfs gi ga gf cov logstart inodestart nib bmapstart size dev
              gpr (ientry kd) dinum bmd datd dnd dnd false
              (16 * kk)%nat 16%nat (fun _ => NUL) (upd_upt V P1) n1 Sb1 pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs dqb dqbs
              B6 (K - 30)%nat eb b lks
              ltac:(exact Kwr) Hcost
              Hgeom Hist0 Hdiblk Hdiblog Hdinb Haddrd
              Htynzz
              (di_type_stable_refl dnd)
              Hnls
              Hwfd Hhzd Hcovd Hoffn31 Hszd31
              Hbmgeom
              Hprk Hj Hgl HB6a0
              Ha1t Ha3t Ha4t
              (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hdata Hprenv Hbio Hlog
                    Hkenv Hidevd Hiinumd Hmetad [Haddrsd Hindd] Hblocksd
                    Hsbi Hsbs Hsbb Hbmres Hireg Hdiatd [HbD Hpidq] Hprocs
                    Hdev Hgeo Hdlk Hbsl HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /inode_map. iFrame "Haddrsd Hindd". }
    { iSplitL "HbD"; [| iExact "Hpidq"].
      iEval (rewrite HB6a2). iExact "HbD". }
    iIntros (D13 Hd13 mfw tot bm' data' dnW dn0W nw wrote dist dstb Pw
             Sbw)
      "%Hcsw %Hwf' %Hhz' %Haddr' %Hszlt' %Hcov' %Hcapp %Hszp %Hdistle
       %Hdisttot %Hdist0f %Hrng %Hwr %Harm %Hspend %Hsbsub %Hpost16 %Hspendany
       %Hatomic %Hupw Hcg Hown _ _ Hpc Hidevd Hiinumd Hmetad Hmapd Hblocksd
       Hsbi Hsbs Hsbb Hdiatd [HbD Hpidq] Hbsl HopS".
    iEval (rewrite HB6a2) in "HbD".
    assert (Hpca8 : ret_pc (B6 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xa8)) by (rewrite HB6ra; pcw).
    iEval (rewrite Hpca8) in "Hpc".
    assert (Hwregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mfw)
      by exact (su_regs_cs m sp0 _ _ _ B6 mfw Hcsw HB6regs).
    (* ===== +0xa8 c.li a5,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D13) (mword_of_int (SU + 0xa8)) Ra5
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mfw (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a8 with "Htext"). }
    iIntros (D14 Hd14) "Hcg Hpc".
    set (C1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mfw).
    assert (HC1a5 : (C1 !!! Regidx Ra5 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (HC1a0 : (C1 !!! Regidx Ra0 : mword 64)
                    = (mfw !!! Regidx Ra0 : mword 64))
      by (rewrite /C1 upd_ne; [reflexivity | nz]).
    assert (HC1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C1)
      by (rewrite /C1; apply su_regs_caller; [exact Hcsa5 | exact Hwregs]).
    assert (Hppaa : add_vec_int (mword_of_int (SU + 0xa8) : mword 64) 2
                    = mword_of_int (SU + 0xaa)) by pcw.
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa bne a0,a5 -> [panic "unlink: writei"] ===== *)
    destruct Harm as [(Ha0m & _ & Htot0 & _) | (Ha0w & Htotle & HdnW & Hdn0W)].
    { (* the -1 arm: writei refused; the test is TAKEN and panic never
         returns *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0m HC1a5;
                      apply su_neq_of_eq_false; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    destruct (decide (tot = 16%nat)) as [-> | Hne16].
    2:{ (* the SHORT WRITE: taken, panic *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                      exact (su_neq_of_eq_false _ _
                               (su_tot16_ne tot Htotle Hne16)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    (* ===== the write is FULL: sixteen bytes, the record is DEAD ===== *)
    iApply (wp_bne_fall_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
              (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                    apply su_neq_of_eq_true;
                    apply (proj2 (eq_vec_true_iff _ _)); reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0aa with "Htext"). }
    iIntros (D15 Hd15) "Hcg Hpc".
    assert (Hppae : add_vec_int (mword_of_int (SU + 0xaa) : mword 64) 4
                    = mword_of_int (SU + 0xae)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    assert (Hdist0 : dist = 0%nat) by (exact (Hdist0f eq_refl)).
    (* the flushed record: type/nlink/addrs by definition, size by the
       in-range decide *)
    assert (Hty'v : di_type dnW = di_type dnd) by (rewrite HdnW; reflexivity).
    assert (Hnl'v : di_nlink dnW = di_nlink dnd) by (rewrite HdnW; reflexivity).
    assert (Hsz'v : di_size dnW = di_size dnd).
    { rewrite HdnW. unfold wi_dinode. cbn [di_size].
      rewrite decide_False; [reflexivity | lia]. }
    assert (Haddr'v : di_addrs dnW = bm_cells bm')
      by (rewrite HdnW; reflexivity).
    (* the membership trio -- what pays the whole tail *)
    destruct (Hpost16 ltac:(lia) (su_wi_blocks kk))
      as (Hsp16 & Htgt16 & Hibd16 & Halc16).
    (* the ledger figures *)
    assert (Hnw5 : (5 <= nw)%nat).
    { destruct Hspend as [Hs1 _]. rewrite (su_wi_cost kk) in Hs1. lia. }
    (* the range clause, specialised to the record's sixteen bytes *)
    assert (Hrng16 : forall x : nat,
              file_byte data' x
              = if decide ((16 * kk <= x)%nat /\ (x < 16 * kk + 16)%nat)
                then dirent_bytes dirent_zero !!! (x - 16 * kk)%nat
                else file_byte datd x).
    { intro x. rewrite (Hrng x). rewrite Hdist0.
      destruct (Nat.lt_ge_cases x (16 * kk)%nat) as [Hlo | Hge].
      - rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
        rewrite decide_False; [reflexivity | lia].
      - destruct (Nat.lt_ge_cases x (16 * kk + 16)%nat) as [Hin | Hhi].
        + rewrite decide_True; [| lia]. rewrite decide_True; [| lia].
          rewrite (Hwr eq_refl (x - 16 * kk)%nat ltac:(lia)).
          rewrite (su_dz_byte (x - 16 * kk)%nat ltac:(lia)). reflexivity.
        + rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
          rewrite decide_False; [reflexivity | lia]. }
    (* the three data' facts *)
    assert (Hz' : dir_inum data' kk = bv_0 16).
    { rewrite (dir_inum_of_two data' kk dirent_zero); [exact su_dz_inum |].
      intros jq Hjq. rewrite (Hrng16 (16 * kk + jq)%nat).
      rewrite decide_True; [| lia].
      replace (16 * kk + jq - 16 * kk)%nat with jq by lia. reflexivity. }
    assert (Hagree : forall q : nat, q <> kk ->
              dir_inum data' q = dir_inum datd q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng16 (16 * q)%nat) (Hrng16 (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    assert (Hnm' : forall q : nat, q <> kk ->
              bname 14 (dir_name data' q) = bname 14 (dir_name datd q)).
    { intros q Hq. unfold bname. f_equal.
      apply bview_ext. intros jq Hjq. unfold dir_name.
      rewrite (Hrng16 (16 * q + 2 + jq)%nat).
      rewrite decide_False; [reflexivity | lia]. }
    (* [dp]'s pure re-park facts at the flushed record *)
    assert (Hiok' : inode_ok cov logstart dnW bm' data').
    { unfold inode_ok. split_and!.
      - exact Hwf'.
      - exact Hcov'.
      - exact Haddr'v.
      - rewrite Hty'v Htydz. unfold T_DIR_z. lia.
      - exact (Hcapp Hszcap).
      - exact Hhz'.
      - exact (Hszp Hszdd). }
    assert (Hdok' : dir_ok icfg_nib dnW data').
    { intros _ k Hk Hlvk. rewrite Hsz'v in Hk.
      destruct (decide (k = kk)) as [-> | Hne].
      - exfalso. apply Hlvk. exact Hz'.
      - rewrite (Hagree k Hne). rewrite <- Hcnib.
        apply (Hinums k Hk). unfold dir_live.
        rewrite <- (Hagree k Hne). exact Hlvk. }
    assert (Hddix' : dir_dots_ix (bv_unsigned dinum) dnW data').
    { intros _ _. rewrite Hsz'v. split_and!.
      - exact Hnrec2.
      - unfold dir_live. rewrite (Hagree 0%nat Hkk0'). exact Hlv0.
      - rewrite (Hagree 0%nat Hkk0'). exact Hself0.
      - rewrite (Hnm' 0%nat Hkk0'). exact Hname0.
      - unfold dir_live. rewrite (Hagree 1%nat Hkk1'). exact Hlv1.
      - rewrite (Hnm' 1%nat Hkk1'). exact Hname1. }
    (* the RECORD-ONLY facts at the zeroed record (durable-disk
       2b-inode-3): [wi_dinode] moved neither the type, the count nor the
       size, so all three ride. *)
    assert (Hrl_data' : inode_rec_local dnW).
    { apply (inode_rec_local_same_type dnd dnW Hrl_datd Hty'v).
      - rewrite Hnl'v. exact (proj1 (proj2 Hrl_datd)).
      - intros Hd. rewrite Hsz'v. apply (proj2 (proj2 Hrl_datd)).
        rewrite -Hty'v. exact Hd. }
    assert (Hnlz' : bv_unsigned (di_nlink dnW) <> 0)
      by (rewrite Hnl'v; exact Hdplive).
    assert (Hdoc' : dir_orphan_clean dnW data')
      by exact (dir_orphan_clean_live dnW data' Hnlz').
    (* UNIQUENESS across the zeroing: it only REMOVES a live name, and the
       size does not move ([Hsz'v]). *)
    assert (Hduq' : dir_uniq dnW data')
      by exact (dir_uniq_zero dnd dnW datd data' kk Hty'v
                  ltac:(rewrite Hsz'v; lia)
                  (conj Hz' (conj Hagree Hnm')) Hduq).
    (* ===== VERDICT #1: [dir_links_unlink] fires CALLER-side ===== *)
    assert (Hkknotdot : dir_bname datd kk <> DOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdot.
      rewrite Hc DOT_dot_name. reflexivity. }
    (* ...and the counting RA's half of the same move (durable-disk
       2b-inode-5): the entry that is being zeroed gives up its token, and
       that token is exactly what pays for [ip->nlink--] below. *)
    iDestruct (dlinks_open with "Hdlnkd") as "[Hdlnkd Hetkd]".
    iDestruct (ent_toks_unlink (fs_gamma_L gfs) (bv_unsigned dinum)
                 dnd dnW bmd bm' datd data' kk
                 Hkklt Hkklive Hnotself Hkknotdot (Hduq Htydz)
                 (conj Hz' (conj Hagree Hnm')) Htydz Hdplive Hnlz'
                 Hty'v Hsz'v Hhzd Hhz' Hszcap
                 with "Hetkd") as "[Htoken Hetkd]".
    iDestruct (dir_links_unlink (bv_unsigned dinum) dnd dnW datd data'
                 dirent_zero (dir_nrec (bv_unsigned (di_size dnd))) kk 16
                 Htydz eq_refl Hkklt ltac:(lia) ltac:(lia) su_dz_inum
                 Hdplive Hkklive Hnotself Hkk0 Hkk1 Hty'v Hsz'v Hrng16
                 with "Hdlnkd") as (bfl) "[Hticket Hrepark]".
    destruct bfl.
    { (* [b = true]: the ticket is d-flavoured, so the REGION says the
         removed record names a DIRECTORY -- refuted by this arm's payload.
         V2's file-arm adaptation; since V5' the record is at index >= 2 and
         its unit is the TAGGED one, so the reader is
         [IregDirBit.ireg_dirbit_ty_dp] -- (T1) is stated at [wdu + wdt] and
         does not care which of the two the caller holds. *)
      iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Hticket".
      iApply fupd_wp.
      iMod (ireg_dirbit_ty_dp ⊤ gi gfs inodestart nib
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
              (bv_unsigned dinum)
              ltac:(solve_ndisj) Hinb with "Hireg Hdiati Hticket")
        as "(%Htydi & _ & _)".
      destruct (Htynzi Htydi). }
    (* [b = false]: a plain [ilink], and the re-park owes nothing *)
    iAssert (ilink (bv_unsigned (dir_inum datd kk))) with "[Hticket]"
      as "Hticket"; [iExact "Hticket" |].
    iDestruct ("Hrepark" with "[%]") as "Hdlnkd".
    { cbn. rewrite Hnl'v. lia. }
    iDestruct (dlinks_intro with "Hdlnkd Hetkd") as "Hdlnkd".
    (* [dp]'s bundle, repacked at the flushed record *)
    iDestruct "Hmapd" as "[Haddrsd Hindd]".
    (* THE MOVER (namei-pinned-lookup.md §9 W3, sys_unlink's row): the
       memset+writei zeroed this directory's record, so the hold moves with
       the bytes.  The fragment is WHOLE, so this is one free own-update --
       [dir_view_zero] states the DELTA and is the client's business
       (N-3/N-4), not the carrier's. *)
    iApply fupd_wp.
    iMod (dvw_set_rt ⊤ gi gfs inodestart nib
            (bv_unsigned dinum) (dv_of dnd datd) (dv_of dnW data')
            (fv_of dnd datd) (fv_of dnW data')
            ltac:(solve_ndisj)
           with "Hireg Hdviewd Hfviewd") as "[Hdviewd Hfviewd]".
    (* ...and the ERA's abstract value with them (durable-disk 2b-inode-3):
       [ireg_top_retag] opens [ftopN] alone. *)
    iMod (ireg_top_retag ⊤ gfs (bv_unsigned dinum)
            (era_node dnd bmd datd) (era_node dnW bm' data')
            ltac:(solve_ndisj) with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded gfs gi cov logstart kd dinum dnW bm')
      with "[Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop]"
      as "Hloadd".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists data'.
      rewrite Hdn0W.
      iFrame "Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd
              Htop".
      iPureIntro. split_and!;[exact Hiok' | exact Hrl_data' | exact Hdok' | exact Hddix' | exact Hdoc'
        | exact Hduq']. }
    iAssert (ity_shot gyd (di_type dnW)) as "#Hshotd2".
    { rewrite Hty'v. iExact "Hshotd". }
    iClear "Hshotd".
    (* ===== +0xae lh a4,68(s2) -- ip->type ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_type) in "Hityi".
    iApply (wp_lh_s_sconf (CID := D15) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xae)) Ra4 Rs2
              (mword_of_int 68 : mword 12) C1 (K - 30)%nat
              (di_type dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hityi]").
    { iApply (suli_0ae with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)).
      iExact "Hityi". }
    iIntros (D16 Hd16) "Hcg Hpc Hityi".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)) in "Hityi".
    iAssert (inode_meta (ientry ks) dni)
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /i_type. iFrame. }
    set (C2 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dni : mword 16))]> C1).
    assert (HC2a4 : (C2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C2; apply upd_eq).
    assert (HC2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C2)
      by (rewrite /C2; apply su_regs_caller; [exact Hcsa4 | exact HC1regs]).
    assert (Hppb2 : add_vec_int (mword_of_int (SU + 0xae) : mword 64) 4
                    = mword_of_int (SU + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb2 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := D16) (mword_of_int (SU + 0xb2)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              C2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0b2 with "Htext"). }
    iIntros (D17 Hd17) "Hcg Hpc".
    set (C3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> C2).
    assert (HC3a4 : (C3 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C3 upd_ne; [exact HC2a4 | nz]).
    assert (HC3a5 : (C3 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /C3; apply upd_eq).
    assert (HC3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C3)
      by (rewrite /C3; apply su_regs_caller; [exact Hcsa5 | exact HC2regs]).
    assert (Hppb4 : add_vec_int (mword_of_int (SU + 0xb2) : mword 64) 2
                    = mword_of_int (SU + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 beq a4,a5 -- the second T_DIR test FALLS (this arm) ===== *)
    iApply (wp_beq_fall_s_sconf (CID := D17) (mword_of_int (SU + 0xb4))
              (mword_of_int 146 : mword 13) Ra5 Ra4 C3 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC3a4 HC3a5;
                    exact (su_tdir_ne _ (su_tdir_z_ne _ Htynzi)))
              with "Hcg Hpc []").
    { iApply (suli_0b4 with "Htext"). }
    iIntros (D18 Hd18) "Hcg Hpc".
    assert (Hppb8 : add_vec_int (mword_of_int (SU + 0xb4) : mword 64) 4
                    = mword_of_int (SU + 0xb8)) by pcw.
    iEval (rewrite Hppb8) in "Hpc".
    (* ===== +0xb8 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D18) (mword_of_int (SU + 0xb8)) Ra0 Rs1 C3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0b8 with "Htext"). }
    iIntros (D19 Hd19) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (C3 !!! Regidx Rs1))]> C3).
    assert (HC4a0 : (C4 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /C4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HC3regs). }
    assert (HC4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C4)
      by (rewrite /C4; apply su_regs_caller; [exact Hcsa0 | exact HC3regs]).
    assert (Hppba : add_vec_int (mword_of_int (SU + 0xb8) : mword 64) 2
                    = mword_of_int (SU + 0xba)) by pcw.
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba jal ra,iunlockput(dp) -- CREDITED off the trio ===== *)
    iApply (wp_jal_s_sconf (CID := D19) (mword_of_int (SU + 0xba)) Rra
              (mword_of_int 2089990 : mword 21) C4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ba with "Htext"). }
    iIntros (D20 Hd20) "Hcg Hpc".
    set (C5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)]> C4).
    assert (Hjup : add_vec (mword_of_int (SU + 0xba) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089990 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HC5ra : (C5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)
      by (rewrite /C5; apply upd_eq).
    assert (HC5a0 : (C5 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /C5 upd_ne; [exact HC4a0 | nz]).
    assert (HC5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C5)
      by (rewrite /C5; apply su_regs_caller; [exact Hcsra | exact HC4regs]).
    iDestruct (cpu_own_transport D13 D20 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc cn gfs gi cov logstart kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (log_opS_named with "HopS") as (e0) "HopS".
    iApply (Iunlockput.wp_iunlockput_gen (CID := D20) gs jx gl gu gd gk pd pav
              pu bn g gfs gi cn gtl gild gisld cov logstart bmapstart
              inodestart nib size dev kd qdi sd gyd dinum dnW bm'
              nw Sbw false true false e0 pid (DfracOwn (1/4)) dqb dqs
              C5 (K - 30)%nat eb b lks
              (upd_upt V P1) ltac:(exact Kiup) Hkd ltac:(discriminate)
              ltac:(intros _; exact Hibd16)
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hdiblk Hdiblog Hdinb Hcovb
              ltac:(unfold iput_units; lia) Hj Hgl HC5a0 (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd Hslkdq Hdepd Hidevd Hiinumd
                    Hivalidd Hloadd Hshotd2 Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk Hbsl [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D21 Hd21 mup n2 Sb2 wg)
      "%Hcsup Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi Hbsl %Hsb2 %Hwg
       %Hwgc %Hn2 HopS Hisl".
    assert (Hpcbe : ret_pc (C5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xbe)) by (rewrite HC5ra; pcw).
    iEval (rewrite Hpcbe) in "Hpc".
    assert (Hupregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mup)
      by exact (su_regs_cs m sp0 _ _ _ C5 mup Hcsup HC5regs).
    assert (Hn24 : (4 <= n2)%nat).
    { destruct Hn2 as [Hn2a Hn2b].
      exact (su_iunlockput_from5 wg nw n2 Hnw5 Hn2a). }
    (* ===== +0xbe lhu a5,74(s2) -- ip->nlink ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_nlink) in "Hinli".
    iApply (wp_lhu_s_sconf (CID := D21) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xbe)) Ra5 Rs2
              (mword_of_int 74 : mword 12) mup (K - 30)%nat
              (di_nlink dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0be with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)).
      iExact "Hinli". }
    iIntros (D22 Hd22) "Hcg Hpc Hinli".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)) in "Hinli".
    set (C6 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_nlink dni : mword 16))]> mup).
    assert (HC6a5 : (C6 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (di_nlink dni : mword 16) : mword 64))
      by (rewrite /C6; apply upd_eq).
    assert (HC6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C6)
      by (rewrite /C6; apply su_regs_caller; [exact Hcsa5 | exact Hupregs]).
    assert (Hppc2 : add_vec_int (mword_of_int (SU + 0xbe) : mword 64) 4
                    = mword_of_int (SU + 0xc2)) by pcw.
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (CID := D22) (mword_of_int (SU + 0xc2)) Ra5
              (mword_of_int 63 : mword 6) C6 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c2 with "Htext"). }
    iIntros (D23 Hd23) "Hcg Hpc".
    set (C7 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget C6 Ra5)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 63 : mword 6))))
                     31 0))]> C6).
    assert (HC7a5 : (C7 !!! Regidx Ra5 : mword 64)
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec
                           (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 63 : mword 6))
                            : mword 64)) 31 0)).
    { rewrite /C7 upd_eq. rgne. rewrite HC6a5. reflexivity. }
    assert (HC7regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C7)
      by (rewrite /C7; apply su_regs_caller; [exact Hcsa5 | exact HC6regs]).
    assert (Hppc4 : add_vec_int (mword_of_int (SU + 0xc2) : mword 64) 2
                    = mword_of_int (SU + 0xc4)) by pcw.
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 sh a5,74(s2) -- the decrement lands ===== *)
    iApply (wp_sh_s_sconf (CID := D23) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xc4))
              Ra5 Rs2 (mword_of_int 74 : mword 12) C7 (K - 30)%nat
              (di_nlink dni : mword 16) b with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0c4 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs)).
      iExact "Hinli". }
    iIntros (D24 Hd24) "Hcg Hpc Hinli".
    iEval (rgne; rgne;
           rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs) HC7a5) in "Hinli".
    (* the stored halfword, named; the record it makes is [su_setnl] *)
    iAssert (inode_meta (ientry ks)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /su_setnl /= /i_nlink. iFrame. }
    assert (Hdecr : bv_unsigned (di_nlink dni)
                    = bv_unsigned (di_nlink (su_setnl dni
                        (trunc16 (sign_extend' 64 (subrange_vec_dec
                           (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                                     : mword 64)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 63 : mword 6))
                               : mword 64)) 31 0))))) + 1).
    { rewrite su_setnl_nlink. exact (su_nlink_decr (di_nlink dni) Hnlzi). }
    assert (Hppc8 : add_vec_int (mword_of_int (SU + 0xc4) : mword 64) 4
                    = mword_of_int (SU + 0xc8)) by pcw.
    iEval (rewrite Hppc8) in "Hpc".
    (* ===== +0xc8 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D24) (mword_of_int (SU + 0xc8)) Ra0 Rs2 C7
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c8 with "Htext"). }
    iIntros (D25 Hd25) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (C7 !!! Regidx Rs2))]> C7).
    assert (HC8a0 : (C8 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /C8; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ HC7regs). }
    assert (HC8regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C8)
      by (rewrite /C8; apply su_regs_caller; [exact Hcsa0 | exact HC7regs]).
    assert (Hppca : add_vec_int (mword_of_int (SU + 0xc8) : mword 64) 2
                    = mword_of_int (SU + 0xca)) by pcw.
    iEval (rewrite Hppca) in "Hpc".
    (* ===== +0xca jal ra,iupdate(ip) -- the LEFT receipt ===== *)
    iApply (wp_jal_s_sconf (CID := D25) (mword_of_int (SU + 0xca)) Rra
              (mword_of_int 2089198 : mword 21) C8 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ca with "Htext"). }
    iIntros (D26 Hd26) "Hcg Hpc".
    set (C9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)]> C8).
    assert (Hjiu : add_vec (mword_of_int (SU + 0xca) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089198 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Hjiu) in "Hpc".
    assert (HC9ra : (C9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)
      by (rewrite /C9; apply upd_eq).
    assert (HC9a0 : (C9 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /C9 upd_ne; [exact HC8a0 | nz]).
    assert (HC9regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C9)
      by (rewrite /C9; apply su_regs_caller; [exact Hcsra | exact HC8regs]).
    assert (Htynzi0 : bv_unsigned (di_type dni) <> 0).
    { destruct Hioki as (_ & _ & _ & Hc & _). exact Hc. }
    assert (Haddri : di_addrs dni = bm_cells bmi).
    { destruct Hioki as (_ & _ & Hc & _). exact Hc. }
    assert (Hdirleni : length (bm_dir bmi) = NDIRECT).
    { destruct Hioki as (Hc & _). exact (blkmap_wf_dir_len cov logstart bmi Hc). }
    destruct n2 as [| c2]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D21 D26 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* the spent ticket, at the region's own index spelling *)
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Hticket".
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    iApply (Iupdate.wp_iupdate_unlink (CID := D26) gs jx gl gu gd gk pd pav pu
              bn g gfs gi cov logstart inodestart nib dev (ientry ks)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                 (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                           : mword 64)
                    (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))
                     : mword 64)) 31 0))))
              dni bmi c2 (Sb2 : gset Z) false None pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              C9 (K - 30)%nat eb b lks
              (upd_upt V P1) ltac:(exact Kiupd) ltac:(discriminate) Hgeom Hist0 Hiblki
              Hiblogi Hinb (su_setnl_type_stable dni _)
              ltac:(rewrite su_setnl_type; exact Htynzi0)
              ltac:(exact Hdecr)
              ltac:(rewrite su_setnl_addrs; exact Haddri)
              Hdirleni Hj Hgl HC9a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevi Hiinumi Hmetai
                    [Haddrsi Hindi] Hsbi Hireg Hdiati [Hticket] Htoken [] Hpidq
                    Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsi Hindi". }
    { iEval (cbn [ilink_fl]). iExact "Hticket". }
    { iLeft. iSplit; iPureIntro; [exact Hglog | exact Hcist]. }
    iIntros (D27 Hd27 miu)
      "%Hcsiu Hcg Hown Hpc Hpidq Hidevi Hiinumi Hmetai Hmapi Hsbi Hdiati
       Hbs2 HopS".
    assert (Hpcce : ret_pc (C9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xce)) by (rewrite HC9ra; pcw).
    iEval (rewrite Hpcce) in "Hpc".
    assert (Hiuregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) miu)
      by exact (su_regs_cs m sp0 _ _ _ C9 miu Hcsiu HC9regs).
    (* hm: the bslot unit peeled for iupdate must come back *)
    (* ===== +0xce c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D27) (mword_of_int (SU + 0xce)) Ra0 Rs2 miu
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0ce with "Htext"). }
    iIntros (D28 Hd28) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (E1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (miu !!! Regidx Rs2))]> miu).
    assert (HE1a0 : (E1 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /E1; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ Hiuregs). }
    assert (HE1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E1)
      by (rewrite /E1; apply su_regs_caller; [exact Hcsa0 | exact Hiuregs]).
    assert (Hppd0 : add_vec_int (mword_of_int (SU + 0xce) : mword 64) 2
                    = mword_of_int (SU + 0xd0)) by pcw.
    iEval (rewrite Hppd0) in "Hpc".
    (* ===== +0xd0 jal ra,iunlockput(ip) -- credited off iupdate's own
       [∪ {IBLOCK ip}] ===== *)
    iApply (wp_jal_s_sconf (CID := D28) (mword_of_int (SU + 0xd0)) Rra
              (mword_of_int 2089968 : mword 21) E1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d0 with "Htext"). }
    iIntros (D29 Hd29) "Hcg Hpc".
    set (E2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)]> E1).
    assert (Hjup2 : add_vec (mword_of_int (SU + 0xd0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2089968 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup2) in "Hpc".
    assert (HE2ra : (E2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)
      by (rewrite /E2; apply upd_eq).
    assert (HE2a0 : (E2 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /E2 upd_ne; [exact HE1a0 | nz]).
    assert (HE2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E2)
      by (rewrite /E2; apply su_regs_caller; [exact Hcsra | exact HE1regs]).
    (* [ip]'s bundle, repacked at the decremented record *)
    iDestruct "Hmapi" as "[Haddrsi Hindi]".
    iAssert (dlinks gfs (bv_unsigned (zero_extend' 32
                 (dir_inum datd kk : mword 16) : mword 32))
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
      as "Hdlnki2".
    { iApply dlinks_not_dir. rewrite su_setnl_type. exact Htynzi. }
    (* ...and the ERA's abstract value follows the count (2b-inode-3). *)
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ gfs
            (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                          : mword 32))
            (era_node dni bmi dati)
            (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
            ltac:(solve_ndisj) with "[] Htopi") as "Htopi";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded gfs gi cov logstart ks
               (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi)
      with "[Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi
             Htopi]" as "Hloadi".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists dati.
      iSplit; [iPureIntro; exact (su_setnl_inode_ok cov logstart dni bmi dati _ Hioki) |].
      (* [su_setnl] moves the COUNT alone, so the type and the size ride;
         the new count is one BELOW one the region already bounded, and the
         directory clause is vacuous here (durable-disk 2b-inode-3). *)
      iSplit; [iPureIntro;
               apply (inode_rec_local_same_type dni _ Hrl_dati
                        (su_setnl_type dni _));
               [ exact (su_dec_short _ _ Hdecr (proj1 (proj2 Hrl_dati)))
               | exact (proj2 (proj2 Hrl_dati)) ] |].
      iSplit; [iPureIntro; exact (su_setnl_dir_ok icfg_nib dni dati _ Hdoki) |].
      iSplit; [iPureIntro; apply dir_dots_ix_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplit; [iPureIntro; apply dir_orphan_clean_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplit; [iPureIntro; apply dir_uniq_not_dir;
               rewrite su_setnl_type; exact Htynzi |].
      iSplitL "Hdlnki2"; [iExact "Hdlnki2" |].
      iSplitL "Hdiati"; [iExact "Hdiati" |].
      iSplitL "Hmetai"; [iExact "Hmetai" |].
      iSplitL "Haddrsi"; [iExact "Haddrsi" |].
      iSplitL "Hindi"; [iExact "Hindi" |].
      iSplitL "Hblocksi"; [iExact "Hblocksi" |].
      (* [su_setnl] moves [di_nlink] only and [dv_of] reads [di_size], so the
         contents value is unmoved (§9 W3). *)
      iSplitL "Hdviewi";
        [iApply (dv_ride_size _ dni _ dati (eq_sym (su_setnl_size dni _))
                  with "Hdviewi") |].
      iSplitL "Hfviewi";
        [iApply (fv_ride_size _ dni _ dati (eq_sym (su_setnl_size dni _))
                  with "Hfviewi")
        | iExact "Htopi"]. }
    iAssert (ity_shot gyi (di_type (su_setnl dni (trunc16 (sign_extend' 64
               (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))) as "#Hshoti2".
    { rewrite su_setnl_type. iExact "Hshoti". }
    iDestruct (cpu_own_transport D27 D29 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc cn gfs gi cov logstart ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (log_opS_named with "HopS") as (e1) "HopS".
    pose (dni2 := su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dni : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrb2 : false = true ->
              bmapstart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) inodestart]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcru2 : true = true ->
              IBLOCK (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                inodestart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                  (dir_inum datd kk : mword 16) : mword 32) inodestart]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnu2 : (iput_units <= c2)%nat).
    { unfold iput_units. lia. }
    iApply (Iunlockput.wp_iunlockput_gen (CID := D29) gs jx gl gu gd gk pd pav
              pu bn g gfs gi cn gtl gili gisli cov logstart bmapstart
              inodestart nib size dev ks qsi si gyi
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              dni2
              bmi c2 (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) inodestart]})
              false true false e1 pid (DfracOwn (1/4)) dqb dqs
              E2 (K - 30)%nat eb b lks
              (upd_upt V P1) Kiup Hks Hcrb2 Hcru2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblki Hiblogi Hinb Hcovb
              Hnu2 Hj Hgl HE2a0 (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hesci Hireg Hropen Hslki Hslkiq Hdepi Hidevi Hiinumi
                    Hivalidi Hloadi Hshoti2 Hfrzi [$Hkeepi $Hrui] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D30 Hd30 mip n3 Sb3 wh)
      "%Hcsip Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi Hbsl %Hsb3
       %Hwh %Hwhc %Hn3 HopS Hisl2".
    clear Hcrb2 Hcru2 Hnu2 dni2.
    assert (Hpcd4 : ret_pc (E2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd4)) by (rewrite HE2ra; pcw).
    iEval (rewrite Hpcd4) in "Hpc".
    assert (Hipregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mip)
      by exact (su_regs_cs m sp0 _ _ _ E2 mip Hcsip HE2regs).
    (* ===== +0xd4 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := D30) (mword_of_int (SU + 0xd4)) Rra
              (mword_of_int 2092174 : mword 21) mip (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d4 with "Htext"). }
    iIntros (D31 Hd31) "Hcg Hpc".
    set (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)]> mip).
    assert (Hjeo : add_vec (mword_of_int (SU + 0xd4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092174 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HE3ra : (E3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)
      by (rewrite /E3; apply upd_eq).
    assert (HE3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E3)
      by (rewrite /E3; apply su_regs_caller; [exact Hcsra | exact Hipregs]).
    iDestruct (cpu_own_transport D30 D31 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D30 D31 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D30 D31 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := D31) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n3 pid (DfracOwn (1/4)) E3 (K - 30)%nat
              eb b lks (upd_upt V P1) Keo Hgeom Hj Hgl
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpanenv Hbio Hlog Hseam Hgen
                    Hpidq Hprocs Hdev Hgeo Hdlk [HopS]").
    { rewrite /log_op. iExists Sb3. iExact "HopS". }
    iIntros (D32 Hd32 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpidq".
    assert (Hpcd8 : ret_pc (E3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd8)) by (rewrite HE3ra; pcw).
    iEval (rewrite Hpcd8) in "Hpc".
    assert (Heoregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) meo)
      by exact (su_regs_cs m sp0 _ _ _ E3 meo Hcseo HE3regs).
    (* ===== +0xd8 c.li a0,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D32) (mword_of_int (SU + 0xd8)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              meo (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0d8 with "Htext"). }
    iIntros (D33 Hd33) "Hcg Hpc".
    set (F1 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> meo).
    assert (HF1a0 : (F1 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) F1)
      by (rewrite /F1; apply su_regs_caller; [exact Hcsa0 | exact Heoregs]).
    assert (Hppda : add_vec_int (mword_of_int (SU + 0xd8) : mword 64) 2
                    = mword_of_int (SU + 0xda)) by pcw.
    iEval (rewrite Hppda) in "Hpc".
    (* ===== +0xda c.ldsp s1,216(sp) ===== *)
    assert (Hd3a : add_vec (F1 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                   = pa_stk sp0 3)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF1regs); apply su_frm3).
    iApply (wp_cldsp_s_sconf (CID := D33) (mword_of_int (SU + 0xda))
              (mword_of_int 27 : mword 6) Rs1 F1 (K - 30)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (suli_0da with "Htext"). }
    { iEval (rewrite Hd3a). iExact "Hf3". }
    iIntros (D34 Hd34) "Hcg Hpc Hf3".
    iEval (rewrite Hd3a) in "Hf3".
    set (F2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> F1).
    assert (HF2a0 : (F2 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F2 upd_ne; [exact HF1a0 | nz]).
    assert (HF2regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
                        (pa_stk sp0 8) F2).
    { rewrite /F2.
      exact (su_regs_wr_s1 m sp0 (ientry kd) (m !!! Regidx Rs1 : mword 64)
               (ientry ks) (pa_stk sp0 8) F1 _ eq_refl HF1regs). }
    assert (Hppdc : add_vec_int (mword_of_int (SU + 0xda) : mword 64) 2
                    = mword_of_int (SU + 0xdc)) by pcw.
    iEval (rewrite Hppdc) in "Hpc".
    (* ===== +0xdc c.ldsp s2,208(sp) ===== *)
    assert (Hd4a : add_vec (F2 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                   = pa_stk sp0 4)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF2regs); apply su_frm4).
    iApply (wp_cldsp_s_sconf (CID := D34) (mword_of_int (SU + 0xdc))
              (mword_of_int 26 : mword 6) Rs2 F2 (K - 30)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (suli_0dc with "Htext"). }
    { iEval (rewrite Hd4a). iExact "Hf4". }
    iIntros (D35 Hd35) "Hcg Hpc Hf4".
    iEval (rewrite Hd4a) in "Hf4".
    set (F3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> F2).
    assert (HF3a0 : (F3 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
    assert (HF3regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F3).
    { rewrite /F3.
      exact (su_regs_wr_s2 m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F2 _ eq_refl
               HF2regs). }
    assert (Hppde : add_vec_int (mword_of_int (SU + 0xdc) : mword 64) 2
                    = mword_of_int (SU + 0xde)) by pcw.
    iEval (rewrite Hppde) in "Hpc".
    (* ===== +0xde c.ldsp s3,200(sp) ===== *)
    assert (Hd5a : add_vec (F3 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
                   = pa_stk sp0 5)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF3regs); apply su_frm5).
    iApply (wp_cldsp_s_sconf (CID := D35) (mword_of_int (SU + 0xde))
              (mword_of_int 25 : mword 6) Rs3 F3 (K - 30)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf5]").
    { iApply (suli_0de with "Htext"). }
    { iEval (rewrite Hd5a). iExact "Hf5". }
    iIntros (D36 Hd36) "Hcg Hpc Hf5".
    iEval (rewrite Hd5a) in "Hf5".
    set (F4 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> F3).
    assert (HF4a0 : (F4 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3a0 | nz]).
    assert (HF4regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) F4).
    { rewrite /F4.
      exact (su_regs_wr_s3 m sp0 (m !!! Regidx Rs1 : mword 64)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8)
               (m !!! Regidx Rs3 : mword 64) F3 _ eq_refl HF3regs). }
    assert (Hppe0 : add_vec_int (mword_of_int (SU + 0xde) : mword 64) 2
                    = mword_of_int (SU + 0xe0)) by pcw.
    iEval (rewrite Hppe0) in "Hpc".
    (* ===== +0xe0 c.j +0x168 -- into the shared epilogue ===== *)
    iApply (wp_cj_s_sconf (CID := D36) (mword_of_int (SU + 0xe0))
              (sign_extend' 21 (concat_vec (mword_of_int 68 : mword 11) ('b"0")))
              F4 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0e0 with "Htext"). }
    iIntros (D37 Hd37). iNext. iIntros "Hcg Hpc".
    assert (Htg168 : add_vec (mword_of_int (SU + 0xe0) : mword 64)
                       (sign_extend' 64
                          (sign_extend' 21
                             (concat_vec (mword_of_int 68 : mword 11) ('b"0"))))
                     = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Htg168) in "Hpc".
    (* the buffers and slot 27, put back for the epilogue *)
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
      as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iDestruct (su_off_join sp0 lo
                 (mword_of_int (Z.of_nat (16 * kk)) : mword 32) Hal27
                 with "H27lo H27hi") as "H27".
    assert (HF4sp : su_sp sp0 F4) by exact (su_regs_sp _ _ _ _ _ _ HF4regs).
    assert (HF4thr : su_thr m F4) by exact (su_regs_thr _ _ _ _ _ _ HF4regs).
    assert (HF4s1 : (F4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by exact (su_regs_s1 _ _ _ _ _ _ HF4regs).
    assert (HF4s2 : (F4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by exact (su_regs_s2 _ _ _ _ _ _ HF4regs).
    assert (HF4s3 : (F4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (su_regs_s3 _ _ _ _ _ _ HF4regs).
    iDestruct (cpu_own_transport D32 D37 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D32 D37 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D32 D37 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := D37)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := D37) m F4 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              (m !!! Regidx Rs3 : mword 64) w6
              (word_of_words lo (mword_of_int (Z.of_nat (16 * kk)) : mword 32))
              w30 (fun _ => NUL) bnf bp bex
              K30 Kpop Hsp0 HF4sp HF4thr HF4s1 HF4s2 HF4s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                    HbE H30
                    [Hown Htce Hcce Hpidq Hsbb Hsbi Hsbs Hbsl Hisl
                     Hisl2 Hpre Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport D37 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D37 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D37 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct ("Hpre" with "Hpidq") as "Hpriv".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hbsl Hsbb Hsbi Hsbs [Hisl Hisl2] Hpriv [%]").
    { exact Hcsf. }
    { exact Hupt1. }
    { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
      rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
    { right. rewrite Ha0f HF4a0. pcw. }
  Qed.

  (* ================================================================== *)
  (*  W5-DIR: the same span at the seam's [isdir = true] -- the shared    *)
  (*  zeroing, the +0xb4 test TAKEN into the +0x146 tail (dp->nlink--,   *)
  (*  iupdate(dp) CREDITED, spending the child's [".."] ticket out of     *)
  (*  [dir_links_dotdot_out]), the rejoin at +0xb8, and [ip]'s orphan     *)
  (*  re-park ([ireg_link_grey] + [su_dir_links_orphan] fed by            *)
  (*  [dir_links_empty_nlink] + the blez).  TAKES TWO NAMED PREMISES the  *)
  (*  model cannot yet supply -- see the statement's banner and           *)
  (*  fs-sysfile.md S7-unlink W5.  The seal is STOPPED on them.           *)
  (* ================================================================== *)
  Lemma su_w5_dir `{GEN : GenId} `{CID0 : CpuId}
      (gf ga : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (V : pprivate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf bnm0 bp bd bex : nat -> bv 8)
      (w6 w30 : mword 64)
      (gili gisli gyi : gname) (si qsi : Qp)
      (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8))
      (m M3 : regfile) (sp0 s3x : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    g = icfg_log ->
    printk_gen_contract (kt := KT1) gpr gu gd ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    inodestart = icfg_ist ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext (pv_upt V) P1 ->
    (kd < NINODE)%nat ->
    (ks < NINODE)%nat ->
    bv_unsigned dinum < 16 * Z.of_nat nib ->
    di_type dnd = SpecDirlookup.T_DIR ->
    inode_ok cov logstart dnd bmd datd ->
    (* durable-disk 2b-inode-3: the payload's record-only facts *)
    inode_rec_local dnd ->
    dir_ok icfg_nib dnd datd ->
    dir_dots_ix (bv_unsigned dinum) dnd datd ->
    dir_orphan_clean dnd datd ->
    dir_uniq dnd datd ->
    bname 14 nf <> dot_name ->
    bname 14 nf <> dotdot_name ->
    dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
              (bname 14 nf) = Some kk ->
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    (* ---- the +0x8a seam's pure facts, at the T_DIR payload ---- *)
    su_regs m sp0 (ientry kd) (ientry ks) s3x M3 ->
    bv_unsigned (di_nlink dni) <> 0 ->
    inode_ok cov logstart dni bmi dati ->
    (* durable-disk 2b-inode-3: the child's record-only facts *)
    inode_rec_local dni ->
    dir_ok icfg_nib dni dati ->
    dir_dots_ix (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni dati ->
    dir_orphan_clean dni dati ->
    dir_uniq dni dati ->
    bv_unsigned (di_type dni) = T_DIR_z ->
    dir_dots_only dni dati ->
    (forall k : nat, (2 <= k)%nat ->
       (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
       dir_inum dati k = bv_0 16) ->
    (* ==== THE TWO DESIGN FACTS ARE NOW DERIVED INSIDE, AND THE PREMISES
       ARE GONE (V5' increment W).  For the record, since this lemma's
       statement is where they stood for three increments:
         (D1) [bv_unsigned (dir_inum dati 1) = bv_unsigned dinum] -- the
              child's [".."] names the parent.  Derived at the zeroing:
              the released ticket is the TAGGED parent-record unit
              [ilinkdp ip dp] (the tag is dp's own inum, off the payload's
              [self] parameter), the child's payload hands out the other
              half of the same register through
              [DirLinks.dir_links_dotdot_out]'s tie, and
              [IcacheRef.iparent_agree] collapses the two values -- no
              region open, no tree fragment.  The root exclusion the tie's
              guard wants comes from [IregLinkNz.ireg_tok_root_min2]
              against FINDING 3's [nlink ip = 1].
         (D2) [2 <= bv_unsigned (di_nlink dnd)] -- a directory holding a
              live subdirectory entry has at least two links.  Derived
              before the zeroing by [IregDirBit.dir_links_subdir_nlink2],
              which is (T1')'s plain-flavour refutation plus
              [DirView.dlc_lower] at the counted record.
       ==== *)
    sie_cap_gpr KT1 M3 (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    printk_env gpr gu gd -∗
    pc_is (mword_of_int (SU + 0x8a)) -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
    (* ---- [dp], LOCKED and OPEN ---- *)
    is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                     (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
    sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
    ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    dlinks gfs (bv_unsigned dinum) dnd bmd datd -∗
    dinode_at gi dinum dnd -∗
    inode_meta (ientry kd) dnd -∗
    inode_addrs (ientry kd) (bm_cells bmd) -∗
    ind_res gfs bmd -∗
    inode_blocks gfs bmd datd -∗
    (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
    dv_ride (bv_unsigned dinum) (dv_of dnd datd) -∗
    fv_ride (bv_unsigned dinum) (fv_of dnd datd) -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L gfs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
    ity_shot gyd (di_type dnd) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    (* ---- [ip], LOCKED and OPEN ---- *)
    is_sleeplock_gen gili gisli (i_lock (ientry ks)) "inode"%string
                     (ic_tok cn ks) (slh_tok (icfg_isl ks)) -∗
    sleeplocked_q gisli si (i_lock (ientry ks)) pid -∗
    ic_deposit cn ks (DepShr si dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi) -∗
    i_dev (ientry ks) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry ks) ↦₄{DfracOwn (1/2)}
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    i_valid (ientry ks) ↦₄ valid_word true -∗
    dlinks gfs (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) dni bmi dati -∗
    dinode_at gi
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni -∗
    inode_meta (ientry ks) dni -∗
    inode_addrs (ientry ks) (bm_cells bmi) -∗
    ind_res gfs bmi -∗
    inode_blocks gfs bmi dati -∗
    (* the payload's contents hold (namei-pinned-lookup.md §9 W2) *)
    dv_ride (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (dv_of dni dati) -∗
    fv_ride (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (fv_of dni dati) -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L gfs) (bv_unsigned (zero_extend' 32
        (dir_inum datd kk : mword 16) : mword 32)) (era_node dni bmi dati) -∗
    ity_shot gyi (di_type dni) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    inode_ref_short ks (qsi + si)%Qp qsi dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any
      (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    log_opS g n1 Sb1 -∗
    (* ---- the frame, slot 5 FILLED ---- *)
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
    (pa_stk sp0 6) ↦₈[KT1] w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ[KT1] bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ[KT1] nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ[KT1] bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ[KT1] bp jj) -∗
    (pa_stk sp0 27) ↦₄[KT1] lo -∗
    (pa_add (pa_stk sp0 27) 4) ↦₄[KT1]
      (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
    (pa_stk sp0 30) ↦₈[KT1] w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr KT1 mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hglog Hprk Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hn1 Hupt1 Hkd Hks
           Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq Hnotdot Hnotdd
           Hfst Hal27
           Hregs Hnlzi Hioki Hrl_dati Hdoki Hddixi Hdoci Hduqi Htyzi Hdots
           Hdead.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hdata #Hprenv Hpc #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hpriv
             #Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop #Hshotd Hfrz Hkeepd Hrud
             #Hslki Hslkiq Hdepi Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi Htopi #Hshoti Hfrzi Hkeepi Hrui HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpanenv".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbeq. cbn in Hbeq.
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa3 : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    (* ---- the pure groundwork ---- *)
    assert (Htydz : bv_unsigned (di_type dnd) = T_DIR_z)
      by exact (su_tdir_zof _ Htydir).
    assert (Hinums : dir_inums_ok datd
                       (dir_nrec (bv_unsigned (di_size dnd))) nib)
      by (rewrite Hcnib; exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hkkname : bname 14 (dir_name datd kk) = bname 14 nf)
      by exact (dir_first_name _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat nib).
    { rewrite su_zext32_unsigned. exact (Hinums kk Hkklt Hkklive). }
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    destruct (Hiregb _ Hinb) as [Hiblki Hiblogi].
    (* VERDICT #3 -- the home-live derivation: the matched record's name is
       neither dot, so [dp] cannot be orphaned. *)
    assert (Hdplive : bv_unsigned (di_nlink dnd) <> 0).
    { intro Hz.
      destruct (Hdoc Htydz Hz kk Hkklt Hkklive) as [Hd | Hd];
        rewrite Hkkname in Hd; [exact (Hnotdot Hd) | exact (Hnotdd Hd)]. }
    (* ...and the matched record is neither dot SLOT *)
    destruct (Hddix Htydz Hdplive) as
      (Hnrec2 & Hlv0 & Hself0 & Hname0 & Hlv1 & Hname1).
    assert (Hkk0 : kk <> 0%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname0.
      exact (Hnotdot Hname0). }
    assert (Hkk1 : kk <> 1%nat).
    { intro He. rewrite He in Hkkname. rewrite Hkkname in Hname1.
      exact (Hnotdd Hname1). }
    assert (Hkk0' : (0%nat <> kk)) by (intro He; apply Hkk0; symmetry; exact He).
    assert (Hkk1' : (1%nat <> kk)) by (intro He; apply Hkk1; symmetry; exact He).
    (* the byte bound of the zeroed slot *)
    assert (Hszcap : bv_unsigned (di_size dnd)
                     <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { destruct Hiok as (_ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dnd))
      by (pose proof (bv_unsigned_in_range _ (di_size dnd)) as Hr; lia).
    assert (Hkk16 : (16 * kk + 16 <= Z.to_nat (bv_unsigned (di_size dnd)))%nat).
    { pose proof (su_nrec16 (bv_unsigned (di_size dnd)) Hsznn) as Hle. lia. }
    assert (HkkZ : Z.of_nat (16 * kk + 16)%nat <= bv_unsigned (di_size dnd)).
    { rewrite <- (Z2Nat.id (bv_unsigned (di_size dnd)) Hsznn).
      apply Nat2Z.inj_le. exact Hkk16. }
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (Hkk31 : Z.of_nat (16 * kk)%nat < 2 ^ 31).
    { rewrite Nat2Z.inj_add in HkkZ. lia. }
    (* the record does not name [dp] ITSELF -- VERDICT #1's exclusivity
       half: two full [dinode_at]s at one inum collide. *)
    destruct (decide (bv_unsigned (dir_inum datd kk) = bv_unsigned dinum))
      as [Heqi | Hnotself].
    { assert (Hweq : (zero_extend' 32 (dir_inum datd kk : mword 16)
                      : mword 32) = dinum)
        by (apply bv_eq; rewrite su_zext32_unsigned; exact Heqi).
      iEval (rewrite Hweq) in "Hdiati".
      iExFalso. iApply (dinode_at_excl with "Hdiatd Hdiati"). }
    (* the process block, opened for the callees' pid fraction, and THE
       CLOSER, built once (W2/W3's shape) *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    iAssert (proc_priv_bare (proc_addr jx) pid (upd_upt V P1) -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* ===== +0x8a addi s3,s0,-64 -- writei's [&de] ===== *)
    iApply (wp_addi4_s_sconf (CID := CID0) (mword_of_int (SU + 0x8a)) Rs3 Rs0
              (mword_of_int 4032 : mword 12) M3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_08a with "Htext"). }
    iIntros (D1 Hd1) "Hcg Hpc".
    set (A1 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12)))]> M3).
    assert (HA1v : add_vec (M3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 4032 : mword 12))
                   = pa_stk sp0 8).
    { rewrite (su_regs_s0 _ _ _ _ _ _ Hregs). apply su_bufde. }
    assert (HA1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A1).
    { rewrite /A1.
      exact (su_regs_wr_s3 m sp0 (ientry kd) (ientry ks) s3x (pa_stk sp0 8)
               M3 _ HA1v Hregs). }
    assert (Hpp8e : add_vec_int (mword_of_int (SU + 0x8a) : mword 64) 4
                    = mword_of_int (SU + 0x8e)) by pcw.
    iEval (rewrite Hpp8e) in "Hpc".
    (* ===== +0x8e c.li a2,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D1) (mword_of_int (SU + 0x8e)) Ra2
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              A1 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_08e with "Htext"). }
    iIntros (D2 Hd2) "Hcg Hpc".
    set (A2 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> A1).
    assert (HA2a2 : (A2 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A2; apply upd_eq).
    assert (HA2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A2)
      by (rewrite /A2; apply su_regs_caller; [exact Hcsa2 | exact HA1regs]).
    assert (Hpp90 : add_vec_int (mword_of_int (SU + 0x8e) : mword 64) 2
                    = mword_of_int (SU + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x90 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D2) (mword_of_int (SU + 0x90)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              A2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_090 with "Htext"). }
    iIntros (D3 Hd3) "Hcg Hpc".
    set (A3 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> A2).
    assert (HA3a1 : (A3 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A3; apply upd_eq).
    assert (HA3a2 : (A3 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a2 | nz]).
    assert (HA3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A3)
      by (rewrite /A3; apply su_regs_caller; [exact Hcsa1 | exact HA2regs]).
    assert (Hpp92 : add_vec_int (mword_of_int (SU + 0x90) : mword 64) 2
                    = mword_of_int (SU + 0x92)) by pcw.
    iEval (rewrite Hpp92) in "Hpc".
    (* ===== +0x92 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D3) (mword_of_int (SU + 0x92)) Ra0 Rs3 A3
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_092 with "Htext"). }
    iIntros (D4 Hd4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (A3 !!! Regidx Rs3))]> A3).
    assert (HA4a0 : (A4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /A4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HA3regs). }
    assert (HA4a1 : (A4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a1 | nz]).
    assert (HA4a2 : (A4 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3a2 | nz]).
    assert (HA4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A4)
      by (rewrite /A4; apply su_regs_caller; [exact Hcsa0 | exact HA3regs]).
    assert (Hpp94 : add_vec_int (mword_of_int (SU + 0x92) : mword 64) 2
                    = mword_of_int (SU + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 jal ra,memset ===== *)
    iApply (wp_jal_s_sconf (CID := D4) (mword_of_int (SU + 0x94)) Rra
              (mword_of_int 2079820 : mword 21) A4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_094 with "Htext"). }
    iIntros (D5 Hd5) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)]> A4).
    assert (Hjms : add_vec (mword_of_int (SU + 0x94) : mword 64)
                     (sign_extend' 64 (mword_of_int 2079820 : mword 21))
                   = mword_of_int KernelSyms.memset) by pcw.
    iEval (rewrite Hjms) in "Hpc".
    assert (HA5ra : (A5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x94) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5a0 : (A5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 8)
      by (rewrite /A5 upd_ne; [exact HA4a0 | nz]).
    assert (HA5a1 : (A5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a1 | nz]).
    assert (HA5a2 : (A5 !!! Regidx Ra2 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a2 | nz]).
    assert (HA5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) A5)
      by (rewrite /A5; apply su_regs_caller; [exact Hcsra | exact HA4regs]).
    iApply (Memset.wp_memset_sconf KT1 KT1 (CID := D5) A5 (K - 30)%nat 16
              (mword_of_int 0 : mword 64) bd b (proc_addr jx)
              K2 ltac:(vm_compute; reflexivity) HA5a1
              ltac:(rewrite HA5a2; pcw)
              with "Hcg Htext Hpc [HbD]").
    { iEval (rewrite HA5a0). iExact "HbD". }
    iIntros (D6 Hd6 mms) "Hcg Hpc HbD %Hcsms".
    iEval (rewrite HA5a0) in "HbD".
    assert (Hpc98 : ret_pc (A5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x98)) by (rewrite HA5ra; pcw).
    iEval (rewrite Hpc98) in "Hpc".
    assert (Hmsregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mms)
      by exact (su_regs_cs m sp0 _ _ _ A5 mms Hcsms HA5regs).
    (* the memset byte is NUL *)
    assert (Hcb : nth_byte (autocast (T := mword)
                    (subrange_vec_dec (mword_of_int 0 : mword 64)
                       (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0%nat = NUL)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb) in "HbD".
    (* ===== +0x98 c.li a4,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D6) (mword_of_int (SU + 0x98)) Ra4
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mms (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_098 with "Htext"). }
    iIntros (D7 Hd7) "Hcg Hpc".
    set (B1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mms).
    assert (HB1a4 : (B1 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B1; apply upd_eq).
    assert (HB1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B1)
      by (rewrite /B1; apply su_regs_caller; [exact Hcsa4 | exact Hmsregs]).
    assert (Hpp9a : add_vec_int (mword_of_int (SU + 0x98) : mword 64) 2
                    = mword_of_int (SU + 0x9a)) by pcw.
    iEval (rewrite Hpp9a) in "Hpc".
    (* ===== +0x9a lw a3,-212(s0) -- [uint off], slot 27's UPPER word ===== *)
    iApply (wp_lw_s_sconf (CID := D7) (mword_of_int (SU + 0x9a)) Ra3 Rs0
              (mword_of_int 3884 : mword 12) B1 (K - 30)%nat
              (mword_of_int (Z.of_nat (16 * kk)) : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H27hi]").
    { iApply (suli_09a with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell).
      iExact "H27hi". }
    iIntros (D8 Hd8) "Hcg Hpc H27hi".
    iEval (rgne; rewrite (su_regs_s0 _ _ _ _ _ _ HB1regs) su_offcell)
      in "H27hi".
    set (B2 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64
                     (mword_of_int (Z.of_nat (16 * kk)) : mword 32))]> B1).
    assert (Ha3lit : (sign_extend' 64
                        (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                      : mword 64)
                     = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { assert (Hus : bv_unsigned (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
                    = Z.of_nat (16 * kk)%nat)
        by (apply moi32_small; lia).
      rewrite su_size_sext; rewrite Hus; [reflexivity | lia]. }
    assert (HB2a3 : (B2 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64)).
    { etransitivity; [rewrite /B2; apply upd_eq |]. exact Ha3lit. }
    assert (HB2a4 : (B2 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1a4 | nz]).
    assert (HB2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B2)
      by (rewrite /B2; apply su_regs_caller; [exact Hcsa3 | exact HB1regs]).
    assert (Hpp9e : add_vec_int (mword_of_int (SU + 0x9a) : mword 64) 4
                    = mword_of_int (SU + 0x9e)) by pcw.
    iEval (rewrite Hpp9e) in "Hpc".
    (* ===== +0x9e c.mv a2,s3 ===== *)
    iApply (wp_cmv_s_sconf (CID := D8) (mword_of_int (SU + 0x9e)) Ra2 Rs3 B2
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_09e with "Htext"). }
    iIntros (D9 Hd9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B2 !!! Regidx Rs3))]> B2).
    assert (HB3a2 : (B3 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8).
    { etransitivity; [rewrite /B3; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s3 _ _ _ _ _ _ HB2regs). }
    assert (HB3a3 : (B3 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a3 | nz]).
    assert (HB3a4 : (B3 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a4 | nz]).
    assert (HB3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B3)
      by (rewrite /B3; apply su_regs_caller; [exact Hcsa2 | exact HB2regs]).
    assert (Hppa0 : add_vec_int (mword_of_int (SU + 0x9e) : mword 64) 2
                    = mword_of_int (SU + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa0 c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D9) (mword_of_int (SU + 0xa0)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              B3 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a0 with "Htext"). }
    iIntros (D10 Hd10) "Hcg Hpc".
    set (B4 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> B3).
    assert (HB4a1 : (B4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B4; apply upd_eq).
    assert (HB4a2 : (B4 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B4 upd_ne; [exact HB3a2 | nz]).
    assert (HB4a3 : (B4 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a3 | nz]).
    assert (HB4a4 : (B4 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a4 | nz]).
    assert (HB4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B4)
      by (rewrite /B4; apply su_regs_caller; [exact Hcsa1 | exact HB3regs]).
    assert (Hppa2 : add_vec_int (mword_of_int (SU + 0xa0) : mword 64) 2
                    = mword_of_int (SU + 0xa2)) by pcw.
    iEval (rewrite Hppa2) in "Hpc".
    (* ===== +0xa2 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D10) (mword_of_int (SU + 0xa2)) Ra0 Rs1 B4
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0a2 with "Htext"). }
    iIntros (D11 Hd11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B4 !!! Regidx Rs1))]> B4).
    assert (HB5a0 : (B5 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /B5; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HB4regs). }
    assert (HB5a1 : (B5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a1 | nz]).
    assert (HB5a2 : (B5 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B5 upd_ne; [exact HB4a2 | nz]).
    assert (HB5a3 : (B5 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a3 | nz]).
    assert (HB5a4 : (B5 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a4 | nz]).
    assert (HB5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B5)
      by (rewrite /B5; apply su_regs_caller; [exact Hcsa0 | exact HB4regs]).
    assert (Hppa4 : add_vec_int (mword_of_int (SU + 0xa2) : mword 64) 2
                    = mword_of_int (SU + 0xa4)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ===== +0xa4 jal ra,writei -- THE ZEROING ===== *)
    iApply (wp_jal_s_sconf (CID := D11) (mword_of_int (SU + 0xa4)) Rra
              (mword_of_int 2090644 : mword 21) B5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0a4 with "Htext"). }
    iIntros (D12 Hd12) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)]> B5).
    assert (Hjwi : add_vec (mword_of_int (SU + 0xa4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090644 : mword 21))
                   = mword_of_int KernelSyms.writei) by pcw.
    iEval (rewrite Hjwi) in "Hpc".
    assert (HB6ra : (B6 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xa4) : mword 64) 4)
      by (rewrite /B6; apply upd_eq).
    assert (HB6a0 : (B6 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /B6 upd_ne; [exact HB5a0 | nz]).
    assert (HB6a1 : (B6 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a1 | nz]).
    assert (HB6a2 : (B6 !!! Regidx Ra2 : mword 64) = pa_stk sp0 8)
      by (rewrite /B6 upd_ne; [exact HB5a2 | nz]).
    assert (HB6a3 : (B6 !!! Regidx Ra3 : mword 64)
                    = (mword_of_int (Z.of_nat (16 * kk)) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a3 | nz]).
    assert (HB6a4 : (B6 !!! Regidx Ra4 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a4 | nz]).
    assert (HB6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) B6)
      by (rewrite /B6; apply su_regs_caller; [exact Hcsra | exact HB5regs]).
    (* [inode_ok dp]'s conjuncts, read once *)
    assert (Hiok0 : inode_ok cov logstart dnd bmd datd) by exact Hiok.
    destruct Hiok0 as (Hwfd & Hcovd & Haddrd & Htynzd & _ & Hhzd & Hszdd).
    assert (Hoffn31 : Z.of_nat (16 * kk)%nat + Z.of_nat 16%nat < 2 ^ 31)
      by lia.
    assert (Hszd31 : bv_unsigned (di_size dnd) < 2 ^ 31) by lia.
    pose proof (su_u1_ge9 w1) as Hge9.
    assert (Hcost : (wi_cost_bmonly (16 * kk) 16 <= n1)%nat)
      by (rewrite (su_wi_cost kk); lia).
    assert (Htynzz : bv_unsigned (di_type dnd) <> 0)
      by (rewrite Htydz; unfold T_DIR_z; lia).
    assert (Hnls : di_nlink_stable dnd dnd)
      by (apply di_nlink_stable_refl; exact Htynzz).
    assert (Hbmgeom : bitmap_geom_ok cov logstart bmapstart size)
      by (unfold bitmap_geom_ok;
          exact (conj Hsize (conj Hbm0 (conj Hbmcov Hbmlog)))).
    assert (Ha1t : eq_vec (B6 !!! Regidx Ra1 : mword 64) (zero_reg : mword 64)
                   = negb false)
      by (rewrite HB6a1; vm_compute; reflexivity).
    assert (Ha3t : (B6 !!! Regidx Ra3 : mword 64)
                   = (mword_of_int (Z.of_nat (16 * kk)%nat) : mword 64))
      by (rewrite HB6a3; reflexivity).
    assert (Ha4t : (B6 !!! Regidx Ra4 : mword 64)
                   = (mword_of_int (Z.of_nat 16%nat) : mword 64))
      by (rewrite HB6a4; pcw).
    iDestruct (cpu_own_transport CID0 D12 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Writei.wp_writei_gen KT1 (CID := D12) gs jx gl gu gd gk pd pav pu bn
              g gfs gi ga gf cov logstart inodestart nib bmapstart size dev
              gpr (ientry kd) dinum bmd datd dnd dnd false
              (16 * kk)%nat 16%nat (fun _ => NUL) (upd_upt V P1) n1 Sb1 pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs dqb dqbs
              B6 (K - 30)%nat eb b lks
              ltac:(exact Kwr) Hcost
              Hgeom Hist0 Hdiblk Hdiblog Hdinb Haddrd
              Htynzz
              (di_type_stable_refl dnd)
              Hnls
              Hwfd Hhzd Hcovd Hoffn31 Hszd31
              Hbmgeom
              Hprk Hj Hgl HB6a0
              Ha1t Ha3t Ha4t
              (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hdata Hprenv Hbio Hlog
                    Hkenv Hidevd Hiinumd Hmetad [Haddrsd Hindd] Hblocksd
                    Hsbi Hsbs Hsbb Hbmres Hireg Hdiatd [HbD Hpidq] Hprocs
                    Hdev Hgeo Hdlk Hbsl HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /inode_map. iFrame "Haddrsd Hindd". }
    { iSplitL "HbD"; [| iExact "Hpidq"].
      iEval (rewrite HB6a2). iExact "HbD". }
    iIntros (D13 Hd13 mfw tot bm' data' dnW dn0W nw wrote dist dstb Pw
             Sbw)
      "%Hcsw %Hwf' %Hhz' %Haddr' %Hszlt' %Hcov' %Hcapp %Hszp %Hdistle
       %Hdisttot %Hdist0f %Hrng %Hwr %Harm %Hspend %Hsbsub %Hpost16 %Hspendany
       %Hatomic %Hupw Hcg Hown _ _ Hpc Hidevd Hiinumd Hmetad Hmapd Hblocksd
       Hsbi Hsbs Hsbb Hdiatd [HbD Hpidq] Hbsl HopS".
    iEval (rewrite HB6a2) in "HbD".
    assert (Hpca8 : ret_pc (B6 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xa8)) by (rewrite HB6ra; pcw).
    iEval (rewrite Hpca8) in "Hpc".
    assert (Hwregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mfw)
      by exact (su_regs_cs m sp0 _ _ _ B6 mfw Hcsw HB6regs).
    (* ===== +0xa8 c.li a5,16 ===== *)
    iApply (wp_cli_s_sconf (CID := D13) (mword_of_int (SU + 0xa8)) Ra5
              (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64)
              mfw (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0a8 with "Htext"). }
    iIntros (D14 Hd14) "Hcg Hpc".
    set (C1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int 16 : mword 64)]> mfw).
    assert (HC1a5 : (C1 !!! Regidx Ra5 : mword 64) = (mword_of_int 16 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (HC1a0 : (C1 !!! Regidx Ra0 : mword 64)
                    = (mfw !!! Regidx Ra0 : mword 64))
      by (rewrite /C1 upd_ne; [reflexivity | nz]).
    assert (HC1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C1)
      by (rewrite /C1; apply su_regs_caller; [exact Hcsa5 | exact Hwregs]).
    assert (Hppaa : add_vec_int (mword_of_int (SU + 0xa8) : mword 64) 2
                    = mword_of_int (SU + 0xaa)) by pcw.
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa bne a0,a5 -> [panic "unlink: writei"] ===== *)
    destruct Harm as [(Ha0m & _ & Htot0 & _) | (Ha0w & Htotle & HdnW & Hdn0W)].
    { (* the -1 arm: writei refused; the test is TAKEN and panic never
         returns *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0m HC1a5;
                      apply su_neq_of_eq_false; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    destruct (decide (tot = 16%nat)) as [-> | Hne16].
    2:{ (* the SHORT WRITE: taken, panic *)
      iApply (wp_bne_taken_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
                (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                      exact (su_neq_of_eq_false _ _
                               (su_tot16_ne tot Htotle Hne16)))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (suli_0aa with "Htext"). }
      iIntros (D15 Hd15). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg13a : add_vec (mword_of_int (SU + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 144 : mword 13))
                       = mword_of_int (SU + 0x13a)) by pcw.
      iEval (rewrite Htg13a) in "Hpc".
      iPoseProof (printk_env_panic with "Hprenv") as "#Hpe5".
      iDestruct (cpu_own_transport D13 D15 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Tails.su_panic_writei (CID0 := D15) C1 (K - 30)%nat 0%nat eb b
                (proc_addr jx) lks (su_pn_K K HK) su_pn_noff (Hlb "pr"%string)
                with "Hcg Hown Htext Hdata Hpe5 Hpc"). }
    (* ===== the write is FULL: sixteen bytes, the record is DEAD ===== *)
    iApply (wp_bne_fall_s_sconf (CID := D14) (mword_of_int (SU + 0xaa))
              (mword_of_int 144 : mword 13) Ra5 Ra0 C1 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC1a0 Ha0w HC1a5;
                    apply su_neq_of_eq_true;
                    apply (proj2 (eq_vec_true_iff _ _)); reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0aa with "Htext"). }
    iIntros (D15 Hd15) "Hcg Hpc".
    assert (Hppae : add_vec_int (mword_of_int (SU + 0xaa) : mword 64) 4
                    = mword_of_int (SU + 0xae)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    assert (Hdist0 : dist = 0%nat) by (exact (Hdist0f eq_refl)).
    subst dn0W.
    (* the flushed record: type/nlink/addrs by definition, size by the
       in-range decide *)
    assert (Hty'v : di_type dnW = di_type dnd) by (rewrite HdnW; reflexivity).
    assert (Hnl'v : di_nlink dnW = di_nlink dnd) by (rewrite HdnW; reflexivity).
    assert (Hsz'v : di_size dnW = di_size dnd).
    { rewrite HdnW. unfold wi_dinode. cbn [di_size].
      rewrite decide_False; [reflexivity | lia]. }
    assert (Haddr'v : di_addrs dnW = bm_cells bm')
      by (rewrite HdnW; reflexivity).
    (* the membership trio -- what pays the whole tail *)
    destruct (Hpost16 ltac:(lia) (su_wi_blocks kk))
      as (Hsp16 & Htgt16 & Hibd16 & Halc16).
    (* the ledger figures *)
    assert (Hnw5 : (5 <= nw)%nat).
    { destruct Hspend as [Hs1 _]. rewrite (su_wi_cost kk) in Hs1. lia. }
    (* the range clause, specialised to the record's sixteen bytes *)
    assert (Hrng16 : forall x : nat,
              file_byte data' x
              = if decide ((16 * kk <= x)%nat /\ (x < 16 * kk + 16)%nat)
                then dirent_bytes dirent_zero !!! (x - 16 * kk)%nat
                else file_byte datd x).
    { intro x. rewrite (Hrng x). rewrite Hdist0.
      destruct (Nat.lt_ge_cases x (16 * kk)%nat) as [Hlo | Hge].
      - rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
        rewrite decide_False; [reflexivity | lia].
      - destruct (Nat.lt_ge_cases x (16 * kk + 16)%nat) as [Hin | Hhi].
        + rewrite decide_True; [| lia]. rewrite decide_True; [| lia].
          rewrite (Hwr eq_refl (x - 16 * kk)%nat ltac:(lia)).
          rewrite (su_dz_byte (x - 16 * kk)%nat ltac:(lia)). reflexivity.
        + rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
          rewrite decide_False; [reflexivity | lia]. }
    (* the three data' facts *)
    assert (Hz' : dir_inum data' kk = bv_0 16).
    { rewrite (dir_inum_of_two data' kk dirent_zero); [exact su_dz_inum |].
      intros jq Hjq. rewrite (Hrng16 (16 * kk + jq)%nat).
      rewrite decide_True; [| lia].
      replace (16 * kk + jq - 16 * kk)%nat with jq by lia. reflexivity. }
    assert (Hagree : forall q : nat, q <> kk ->
              dir_inum data' q = dir_inum datd q).
    { intros q Hq. unfold dir_inum.
      rewrite (Hrng16 (16 * q)%nat) (Hrng16 (16 * q + 1)%nat).
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      reflexivity. }
    assert (Hnm' : forall q : nat, q <> kk ->
              bname 14 (dir_name data' q) = bname 14 (dir_name datd q)).
    { intros q Hq. unfold bname. f_equal.
      apply bview_ext. intros jq Hjq. unfold dir_name.
      rewrite (Hrng16 (16 * q + 2 + jq)%nat).
      rewrite decide_False; [reflexivity | lia]. }
    (* [dp]'s pure re-park facts at the flushed record *)
    assert (Hiok' : inode_ok cov logstart dnW bm' data').
    { unfold inode_ok. split_and!.
      - exact Hwf'.
      - exact Hcov'.
      - exact Haddr'v.
      - rewrite Hty'v Htydz. unfold T_DIR_z. lia.
      - exact (Hcapp Hszcap).
      - exact Hhz'.
      - exact (Hszp Hszdd). }
    assert (Hdok' : dir_ok icfg_nib dnW data').
    { intros _ k Hk Hlvk. rewrite Hsz'v in Hk.
      destruct (decide (k = kk)) as [-> | Hne].
      - exfalso. apply Hlvk. exact Hz'.
      - rewrite (Hagree k Hne). rewrite <- Hcnib.
        apply (Hinums k Hk). unfold dir_live.
        rewrite <- (Hagree k Hne). exact Hlvk. }
    assert (Hddix' : dir_dots_ix (bv_unsigned dinum) dnW data').
    { intros _ _. rewrite Hsz'v. split_and!.
      - exact Hnrec2.
      - unfold dir_live. rewrite (Hagree 0%nat Hkk0'). exact Hlv0.
      - rewrite (Hagree 0%nat Hkk0'). exact Hself0.
      - rewrite (Hnm' 0%nat Hkk0'). exact Hname0.
      - unfold dir_live. rewrite (Hagree 1%nat Hkk1'). exact Hlv1.
      - rewrite (Hnm' 1%nat Hkk1'). exact Hname1. }
    (* the RECORD-ONLY facts at the zeroed record (durable-disk
       2b-inode-3): [wi_dinode] moved neither the type, the count nor the
       size, so all three ride. *)
    assert (Hrl_data' : inode_rec_local dnW).
    { apply (inode_rec_local_same_type dnd dnW Hrl_datd Hty'v).
      - rewrite Hnl'v. exact (proj1 (proj2 Hrl_datd)).
      - intros Hd. rewrite Hsz'v. apply (proj2 (proj2 Hrl_datd)).
        rewrite -Hty'v. exact Hd. }
    assert (Hnlz' : bv_unsigned (di_nlink dnW) <> 0)
      by (rewrite Hnl'v; exact Hdplive).
    assert (Hdoc' : dir_orphan_clean dnW data')
      by exact (dir_orphan_clean_live dnW data' Hnlz').
    (* UNIQUENESS across the zeroing: it only REMOVES a live name, and the
       size does not move ([Hsz'v]). *)
    assert (Hduq' : dir_uniq dnW data')
      by exact (dir_uniq_zero dnd dnW datd data' kk Hty'v
                  ltac:(rewrite Hsz'v; lia)
                  (conj Hz' (conj Hagree Hnm')) Hduq).
    (* the child's payload projections, read while the guard holds *)
    destruct (Hddixi Htyzi Hnlzi) as
      (Hnrec2i & Hlv0i & Hself0i & Hname0i & Hlv1i & Hname1i).
    (* the payload's links conjunct opens into the LEDGER half, which the
       three readings below and the orphan re-park move, and the counting
       RA's TOKENS, whose [".."] unit is what pays for [dp->nlink--]
       (durable-disk 2b-inode-5). *)
    iDestruct (dlinks_open with "Hdlnki") as "[Hdlnki Hetki]".
    iDestruct (dir_links_empty_nlink
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32)) dni dati Hdead
                 with "Hdlnki") as %Hle1.
    assert (Hnl1 : bv_unsigned (di_nlink dni) = 1).
    { exact (su_le1_nz_eq1 _
               (proj1 (bv_unsigned_in_range _ (di_nlink dni)))
               (Hle1 Htyzi) Hnlzi). }
    (* the parent's decremented halfword, and its arithmetic *)
    assert (HnlzW : bv_unsigned (di_nlink dnW) <> 0)
      by (rewrite Hnl'v; exact Hdplive).
    assert (HdWnd : bv_unsigned (di_nlink dnW)
                    = bv_unsigned (di_nlink dnd))
      by (rewrite Hnl'v; reflexivity).
    assert (HdecrW : bv_unsigned (di_nlink dnW)
                     = bv_unsigned (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))) + 1)
      by (exact (su_nlink_decr (di_nlink dnW) HnlzW)).
    assert (HtyF2 : di_type (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) = di_type dnd)
      by (rewrite su_setnl_type; exact Hty'v).
    assert (HszF2 : di_size (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) = di_size dnd)
      by (rewrite su_setnl_size; exact Hsz'v).
    (* ===================================================================
       (D2) FALLS HERE, and the premise is gone (V5' increment W).  A
       directory holding a LIVE record for a directory has at least two
       links: the record's ticket is d-flavoured (a PLAIN one dies against
       (T1') at the child the walk names), so [DirView.dlc_lower] counts it
       and reads [1 + 1 <= nlink] off [dp]'s own payload.  All of that is
       [IregDirBit.dir_links_subdir_nlink2], one mask-preserving step, and
       every one of its premises is a holding of the +0x8a seam.  It runs
       BEFORE the zeroing because it reads [dp]'s payload at the record the
       zeroing is about to kill.
       =================================================================== *)
    iDestruct (dlinks_open with "Hdlnkd") as "[Hdlnkd Hetkd]".
    iApply fupd_wp.
    iMod (dir_links_subdir_nlink2 ⊤ gi gfs inodestart nib
            (bv_unsigned dinum) dnd datd kk
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
            ltac:(solve_ndisj) Hinb Htydz Hdplive ltac:(lia) Hkklt Hkklive
            Hnotself (su_zext32_unsigned (dir_inum datd kk)) Htyzi
            with "Hireg Hdiati Hdlnkd") as "(%Hdp2 & Hdiati & Hdlnkd)".
    iModIntro.
    (* ===== VERDICT #1 (dir arm): [dir_links_unlink] at the record the
       [+0x146] tail is ABOUT to flush -- the [b = true] flavour needs no
       refutation, because the [dp->nlink--] pays the unit ===== *)
    assert (HnlzF2a : bv_unsigned (di_nlink (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))) <> 0).
    { rewrite su_setnl_nlink.
      exact (su_decr_pos _ _ _ HdecrW HdWnd Hdp2). }
    assert (Hkknotdot : dir_bname datd kk <> DOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdot.
      rewrite Hc DOT_dot_name. reflexivity. }
    (* ...and the counting RA's half of the same move (durable-disk
       2b-inode-5): the zeroed entry gives up its token, which is what
       pays for the CHILD's own [ip->nlink--] below. *)
    iDestruct (ent_toks_unlink (fs_gamma_L gfs) (bv_unsigned dinum)
                 dnd (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmd bm' datd data' kk
                 Hkklt Hkklive Hnotself Hkknotdot (Hduq Htydz)
                 (conj Hz' (conj Hagree Hnm')) Htydz Hdplive HnlzF2a
                 HtyF2 HszF2 Hhzd Hhz' Hszcap
                 with "Hetkd") as "[Htoken Hetkd]".
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    iDestruct (dir_links_unlink (bv_unsigned dinum) dnd (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))
                 datd data'
                 dirent_zero (dir_nrec (bv_unsigned (di_size dnd))) kk 16
                 Htydz eq_refl Hkklt ltac:(lia) ltac:(lia) su_dz_inum
                 Hdplive Hkklive Hnotself Hkk0 Hkk1 HtyF2 HszF2 Hrng16
                 with "Hdlnkd") as (bfl) "[Hticket Hrepark]".
    (* ===== V4's PAYOFF: the [b = false] flavour is REFUTED, the exact
       MIRROR of the file arm's [b = true] refutation.  The record being
       zeroed names [ip], the walk holds [ip]'s own [dinode_at] and its
       T_DIR test, and a PLAIN ticket against a directory dies on (T1')
       ([IregDirBit.ireg_link_not_dir]).  The wand's equality then prices
       the [b = true] arm alone -- the decrement pays exactly one. ===== *)
    destruct bfl; last first.
    { iAssert (ilink (bv_unsigned (dir_inum datd kk))) with "[Hticket]"
        as "Hticket"; [iExact "Hticket" |].
      iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Hticket".
      iApply fupd_wp.
      iMod (ireg_link_not_dir ⊤ gi gfs inodestart nib
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
              ltac:(solve_ndisj) Hinb with "Hireg Hdiati Hticket")
        as "(%Hndi & _ & _)".
      destruct (Hndi Htyzi). }
    iDestruct ("Hrepark" with "[%]") as "Hdlnkd2".
    { cbn. rewrite <- HdWnd. exact (eq_sym HdecrW). }
    iDestruct (dlinks_intro with "Hdlnkd2 Hetkd") as "Hdlnkd2".
    (* ===================================================================
       (D1) FALLS HERE, IN THREE STEPS, and the premise is gone (V5'
       increment W).  This is the fact the whole parent-register carrier
       exists for, and none of the three steps opens the region twice or
       reads a tree fragment:

         1. THE RELEASED TICKET IS TAGGED.  The record just zeroed is at
            index >= 2 -- a NAME record -- and since V5' a name record
            naming a directory carries [IcacheRef.ilinkdp ip self], whose
            tag is the payload's OWN [self] parameter, i.e. [dp]'s inum
            verbatim.  The [b = false] arm was refuted one step above by
            (T1'), so what the walk holds is [ilinkdp ip dp].
         2. THE CHILD HANDS OUT THE OTHER HALF.  [ip]'s payload carries
            [DirLinks.dir_par_tie] -- [∃ pv, iparent ip pv ∗
            ⌜dir_inum dati 1 = pv⌝] -- under a guard whose two live
            conjuncts the seam already supplies and whose third is the root
            exclusion, and THAT is [IregLinkNz.ireg_tok_root_min2] against
            FINDING 3's [nlink ip = 1]: the region's unspendable keep-alive
            token plus the one the zeroing just released put root's count at
            two.
         3. THE AGREEMENT.  Half plus half is at most the whole register,
            so [IcacheRef.iparent_agree] collapses [dp] and [pv] --
            fragment against fragment, no region open at all.  With
            [⌜dir_inum dati 1 = pv⌝] that IS (D1).

       The lock is what makes it an episode rather than a coincidence: the
       walk has held [ip]'s reference and sleeplock continuously since
       [ilock], both fragments are HELD resources, and the only authority
       reads are at create's mint and at the spend below.
       =================================================================== *)
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Hticket".
    iApply fupd_wp.
    iMod (ireg_tok_root_min2 ⊤ gi gfs inodestart nib
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
            ltac:(solve_ndisj) Hinb
            with "Hireg Hdiati Htoken") as "(%Hrmin & Hdiati & Htoken)".
    iModIntro.
    assert (Hipnroot : bv_unsigned (zero_extend' 32
                         (dir_inum datd kk : mword 16) : mword 32)
                       <> dl_root).
    { rewrite dl_root_ireg_root. intro Hc.
      pose proof (Hrmin Hc) as Hge2. rewrite Hnl1 in Hge2. lia. }
    iDestruct (dir_links_dotdot_out
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32)) dni dati
                 Htyzi Hnlzi Hddixi Hipnroot with "Hdlnki")
      as (pvv) "(Hipar & %Hpv & Hdotacc)".
    iDestruct (iparent_agree
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32))
                 (bv_unsigned dinum) pvv with "Hticket Hipar") as %Hagr.
    assert (Hpar : bv_unsigned (dir_inum dati 1) = bv_unsigned dinum)
      by (rewrite Hpv; exact (eq_sym Hagr)).
    (* the half comes out at the payload's own reading of the register;
       the agreement is what lets the SPEND below name it [dp]'s *)
    iEval (rewrite -Hagr) in "Hipar".
    (* [dp]'s pure re-park facts, moved DOWN to the decremented record *)
    assert (HiokF2 : inode_ok cov logstart (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
      by (exact (su_setnl_inode_ok cov logstart dnW bm' data' _ Hiok')).
    assert (HdokF2 : dir_ok icfg_nib (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) data')
      by (exact (su_setnl_dir_ok icfg_nib dnW data' _ Hdok')).
    assert (HddixF2 : dir_dots_ix (bv_unsigned dinum)
                        (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) data').
    { intros _ _. rewrite su_setnl_size Hsz'v. split_and!.
      - exact Hnrec2.
      - unfold dir_live. rewrite (Hagree 0%nat Hkk0'). exact Hlv0.
      - rewrite (Hagree 0%nat Hkk0'). exact Hself0.
      - rewrite (Hnm' 0%nat Hkk0'). exact Hname0.
      - unfold dir_live. rewrite (Hagree 1%nat Hkk1'). exact Hlv1.
      - rewrite (Hnm' 1%nat Hkk1'). exact Hname1. }
    assert (HnlzF2 : bv_unsigned (di_nlink (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))) <> 0).
    { rewrite su_setnl_nlink.
      exact (su_decr_pos _ _ _ HdecrW HdWnd Hdp2). }
    assert (HdocF2 : dir_orphan_clean (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) data')
      by (exact (dir_orphan_clean_live _ _ HnlzF2)).
    (* the [--] moved the COUNT, and [dir_uniq] reads only type and size *)
    assert (HduqF2 : dir_uniq (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) data')
      by (exact (dir_uniq_cong dnW _ data' (su_setnl_type _ _)
                   (su_setnl_size _ _) Hduq')).
    iDestruct "Hmapd" as "[Haddrsd Hindd]".
    (* ===== +0xae lh a4,68(s2) -- ip->type ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_type) in "Hityi".
    iApply (wp_lh_s_sconf (CID := D15) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xae)) Ra4 Rs2
              (mword_of_int 68 : mword 12) C1 (K - 30)%nat
              (di_type dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hityi]").
    { iApply (suli_0ae with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)).
      iExact "Hityi". }
    iIntros (D16 Hd16) "Hcg Hpc Hityi".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC1regs)) in "Hityi".
    iAssert (inode_meta (ientry ks) dni)
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /i_type. iFrame. }
    set (C2 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dni : mword 16))]> C1).
    assert (HC2a4 : (C2 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C2; apply upd_eq).
    assert (HC2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C2)
      by (rewrite /C2; apply su_regs_caller; [exact Hcsa4 | exact HC1regs]).
    assert (Hppb2 : add_vec_int (mword_of_int (SU + 0xae) : mword 64) 4
                    = mword_of_int (SU + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb2 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (CID := D16) (mword_of_int (SU + 0xb2)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              C2 (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0b2 with "Htext"). }
    iIntros (D17 Hd17) "Hcg Hpc".
    set (C3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> C2).
    assert (HC3a4 : (C3 !!! Regidx Ra4 : mword 64)
                    = (sign_extend' 64 (di_type dni : mword 16) : mword 64))
      by (rewrite /C3 upd_ne; [exact HC2a4 | nz]).
    assert (HC3a5 : (C3 !!! Regidx Ra5 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /C3; apply upd_eq).
    assert (HC3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C3)
      by (rewrite /C3; apply su_regs_caller; [exact Hcsa5 | exact HC2regs]).
    assert (Hppb4 : add_vec_int (mword_of_int (SU + 0xb2) : mword 64) 2
                    = mword_of_int (SU + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 beq a4,a5 -- the second T_DIR test is TAKEN ===== *)
    assert (Htg146 : add_vec (mword_of_int (SU + 0xb4) : mword 64)
                       (sign_extend' 64 (mword_of_int 146 : mword 13))
                     = mword_of_int (SU + 0x146)) by pcw.
    iApply (wp_beq_taken_s_sconf (CID := D17) (mword_of_int (SU + 0xb4))
              (mword_of_int 146 : mword 13) Ra5 Ra4 C3 (K - 30)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HC3a4 HC3a5;
                    exact (su_tdir_eq _ (su_tdir_z _ Htyzi)))
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0b4 with "Htext"). }
    iIntros (T1 Ht1). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htg146) in "Hpc".
    (* ===== +0x146 lhu a5,74(s1) -- dp->nlink ===== *)
    iEval (rewrite /inode_meta) in "Hmetad".
    iDestruct "Hmetad" as "(Hityd & Himad & Himid & Hinld & Hiszd)".
    iEval (rewrite /i_nlink) in "Hinld".
    iApply (wp_lhu_s_sconf (CID := T1) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0x146)) Ra5 Rs1
              (mword_of_int 74 : mword 12) C3 (K - 30)%nat
              (di_nlink dnW : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinld]").
    { iApply (suli_146 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s1 _ _ _ _ _ _ HC3regs)).
      iExact "Hinld". }
    iIntros (T2 Ht2) "Hcg Hpc Hinld".
    iEval (rgne; rewrite (su_regs_s1 _ _ _ _ _ _ HC3regs)) in "Hinld".
    set (G1 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_nlink dnW : mword 16))]> C3).
    assert (HG1a5 : (G1 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (di_nlink dnW : mword 16) : mword 64))
      by (rewrite /G1; apply upd_eq).
    assert (HG1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) G1)
      by (rewrite /G1; apply su_regs_caller; [exact Hcsa5 | exact HC3regs]).
    assert (Hpp14a : add_vec_int (mword_of_int (SU + 0x146) : mword 64) 4
                     = mword_of_int (SU + 0x14a)) by pcw.
    iEval (rewrite Hpp14a) in "Hpc".
    (* ===== +0x14a c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (CID := T2) (mword_of_int (SU + 0x14a)) Ra5
              (mword_of_int 63 : mword 6) G1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_14a with "Htext"). }
    iIntros (T3 Ht3) "Hcg Hpc".
    set (G2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget G1 Ra5)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 63 : mword 6))))
                     31 0))]> G1).
    assert (HG2a5 : (G2 !!! Regidx Ra5 : mword 64)
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec
                           (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 63 : mword 6))
                            : mword 64)) 31 0)).
    { rewrite /G2 upd_eq. rgne. rewrite HG1a5. reflexivity. }
    assert (HG2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) G2)
      by (rewrite /G2; apply su_regs_caller; [exact Hcsa5 | exact HG1regs]).
    assert (Hpp14c : add_vec_int (mword_of_int (SU + 0x14a) : mword 64) 2
                     = mword_of_int (SU + 0x14c)) by pcw.
    iEval (rewrite Hpp14c) in "Hpc".
    (* ===== +0x14c sh a5,74(s1) -- the parent's decrement lands ===== *)
    iApply (wp_sh_s_sconf (CID := T3) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0x14c))
              Ra5 Rs1 (mword_of_int 74 : mword 12) G2 (K - 30)%nat
              (di_nlink dnW : mword 16) b with "Hcg Hpc [] [Hinld]").
    { iApply (suli_14c with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s1 _ _ _ _ _ _ HG2regs)).
      iExact "Hinld". }
    iIntros (T4 Ht4) "Hcg Hpc Hinld".
    iEval (rgne; rgne;
           rewrite (su_regs_s1 _ _ _ _ _ _ HG2regs) HG2a5) in "Hinld".
    iAssert (inode_meta (ientry kd) (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))
      with "[Hityd Himad Himid Hinld Hiszd]" as "Hmetad".
    { rewrite /inode_meta /su_setnl /= /i_nlink. iFrame. }
    assert (Hpp150 : add_vec_int (mword_of_int (SU + 0x14c) : mword 64) 4
                     = mword_of_int (SU + 0x150)) by pcw.
    iEval (rewrite Hpp150) in "Hpc".
    (* ===== +0x150 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := T4) (mword_of_int (SU + 0x150)) Ra0 Rs1 G2
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_150 with "Htext"). }
    iIntros (T5 Ht5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (G2 !!! Regidx Rs1))]> G2).
    assert (HG3a0 : (G3 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /G3; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ HG2regs). }
    assert (HG3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) G3)
      by (rewrite /G3; apply su_regs_caller; [exact Hcsa0 | exact HG2regs]).
    assert (Hpp152 : add_vec_int (mword_of_int (SU + 0x150) : mword 64) 2
                     = mword_of_int (SU + 0x152)) by pcw.
    iEval (rewrite Hpp152) in "Hpc".
    (* ===== +0x152 jal ra,iupdate(dp) -- CREDITED off the trio, spending
       the child's [".."] ticket (VERDICT #2's site) ===== *)
    iApply (wp_jal_s_sconf (CID := T5) (mword_of_int (SU + 0x152)) Rra
              (mword_of_int 2089062 : mword 21) G3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_152 with "Htext"). }
    iIntros (T6 Ht6) "Hcg Hpc".
    set (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x152) : mword 64) 4)]> G3).
    assert (Hjiud : add_vec (mword_of_int (SU + 0x152) : mword 64)
                      (sign_extend' 64 (mword_of_int 2089062 : mword 21))
                    = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Hjiud) in "Hpc".
    assert (HG4ra : (G4 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0x152) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4a0 : (G4 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) G4)
      by (rewrite /G4; apply su_regs_caller; [exact Hcsra | exact HG3regs]).
    (* the [".."]-extraction: the accessor's second leg, opened with the
       disequality (D1) has just made available -- record 1 names [dp], and
       [dp] is not [ip] ([InodeRegion.dinode_at_excl], two records held at
       once).  The ticket comes out at index 1's inum, which [Hpar] then
       rewrites to [dp]'s: that index identity is exactly what
       [wp_iupdate_unlink]'s fragment premise is fixed at, and it is
       irreducibly (D1). *)
    assert (Hz1ne : bv_unsigned (dir_inum dati 1)
                    <> bv_unsigned (zero_extend' 32
                         (dir_inum datd kk : mword 16) : mword 32)).
    { rewrite su_zext32_unsigned Hpar. intro Hc. apply Hnotself.
      symmetry. exact Hc. }
    iDestruct ("Hdotacc" with "[%]") as (b2) "[Hticket2 _]";
      [exact Hz1ne |].
    iEval (rewrite Hpar) in "Hticket2".
    (* ...AND THE COUNTING RA's SAME MOVE (durable-disk 2b-inode-5): the
       child's count is about to reach zero, so its [".."] becomes
       TOKENLESS and the token it carried goes back to the parent -- which
       is exactly what pays for [dp->nlink--] here.  [t <> i] is (D1)'s own
       [Hz1ne], the self-parent exclusion. *)
    assert (Hhzi : blk_holes_zero bmi dati).
    { destruct Hioki as (_ & _ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hszcapi : bv_unsigned (di_size dni)
                      <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { destruct Hioki as (_ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hnl2za : bv_unsigned (di_nlink (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))) = 0).
    { rewrite su_setnl_nlink.
      exact (su_decr_zero _ _ (su_nlink_decr (di_nlink dni) Hnlzi) Hnl1). }
    iDestruct (ent_toks_era_orphan (fs_gamma_L gfs)
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32))
                 dni (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati (bv_unsigned dinum)
                 (su_setnl_type _ _) (su_setnl_size _ _) Hnlzi Hnl2za
                 Htyzi Hhzi Hszcapi (Hduqi Htyzi) Hnrec2i Hlv1i Hname1i Hpar
                 ltac:(intro Hc; exact (Hz1ne (eq_trans Hpar Hc)))
                 with "Hetki") as "[Htokend Hetki]".
    assert (Hmoidin : (mword_of_int (bv_unsigned dinum) : mword 32) = dinum)
      by (exact (su_moi32_id dinum)).
    destruct nw as [| c1]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D13 T6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iupdate.wp_iupdate_unlink (CID := T6) gs jx gl gu gd gk pd pav pu
              bn g gfs gi cov logstart inodestart nib dev (ientry kd) dinum
              (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))
              dnW bm' c1 (Sbw : gset Z) true (dlc_fl b2) pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G4 (K - 30)%nat eb b lks
              (upd_upt V P1) ltac:(exact Kiupd) ltac:(intros _; exact Hibd16) Hgeom Hist0
              Hdiblk Hdiblog Hdinb (su_setnl_type_stable dnW _)
              ltac:(rewrite su_setnl_type Hty'v Htydz; unfold T_DIR_z; lia)
              ltac:(rewrite su_setnl_nlink; exact HdecrW)
              ltac:(rewrite su_setnl_addrs; exact Haddr'v)
              ltac:(exact (blkmap_wf_dir_len cov logstart bm' Hwf'))
              Hj Hgl HG4a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevd Hiinumd Hmetad
                    [Haddrsd Hindd] Hsbi Hireg [Hdiatd] [Hticket2] Htokend []
                    Hpidq Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsd Hindd". }
    { iExact "Hdiatd". }
    { iExact "Hticket2". }
    { iLeft. iSplit; iPureIntro; [exact Hglog | exact Hcist]. }
    iIntros (T7 Ht7 mtu)
      "%Hcstu Hcg Hown Hpc Hpidq Hidevd Hiinumd Hmetad Hmapd Hsbi Hdiatd
       Hbs2 HopS".
    assert (Hpc156 : ret_pc (G4 !!! Regidx Rra : mword 64)
                     = mword_of_int (SU + 0x156)) by (rewrite HG4ra; pcw).
    iEval (rewrite Hpc156) in "Hpc".
    assert (Hturegs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mtu)
      by exact (su_regs_cs m sp0 _ _ _ G4 mtu Hcstu HG4regs).
    (* ===== +0x156 c.j +0xb8 -- rejoin the file spine below the test ===== *)
    iApply (wp_cj_s_sconf (CID := T7) (mword_of_int (SU + 0x156))
              (sign_extend' 21 (concat_vec (mword_of_int 1969 : mword 11) ('b"0")))
              mtu (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_156 with "Htext"). }
    iIntros (D18 Hd18). iNext. iIntros "Hcg Hpc".
    assert (Htgb8 : add_vec (mword_of_int (SU + 0x156) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21
                            (concat_vec (mword_of_int 1969 : mword 11) ('b"0"))))
                    = mword_of_int (SU + 0xb8)) by pcw.
    iEval (rewrite Htgb8) in "Hpc".
    (* [dp]'s bundle, repacked at the decremented record *)
    iDestruct "Hmapd" as "[Haddrsd Hindd]".
    (* THE MOVER (namei-pinned-lookup.md §9 W3, sys_unlink's row): the
       memset+writei zeroed this directory's record.  One free own-update;
       the [su_setnl] that follows moves [di_nlink] only. *)
    iApply fupd_wp.
    iMod (dvw_set_rt ⊤ gi gfs inodestart nib
            (bv_unsigned dinum) (dv_of dnd datd) (dv_of dnW data')
            (fv_of dnd datd) (fv_of dnW data')
            ltac:(solve_ndisj)
           with "Hireg Hdviewd Hfviewd") as "[Hdviewd Hfviewd]".
    (* ...and the ERA's abstract value with them (durable-disk 2b-inode-3):
       [ireg_top_retag] opens [ftopN] alone. *)
    iMod (ireg_top_retag ⊤ gfs (bv_unsigned dinum)
            (era_node dnd bmd datd) (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
            ltac:(solve_ndisj) with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded gfs gi cov logstart kd dinum (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm')
      with "[Hdlnkd2 Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd
             Htop]" as "Hloadd".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists data'.
      iSplitR; [iPureIntro; exact HiokF2 |].
      (* [su_setnl] moves the COUNT alone (durable-disk 2b-inode-3) *)
      iSplitR; [iPureIntro;
                exact (inode_rec_local_same_type dnW _ Hrl_data'
                         (su_setnl_type dnW _)
                         (su_dec_short _ _ HdecrW (proj1 (proj2 Hrl_data')))
                         (proj2 (proj2 Hrl_data'))) |].
      iSplitR; [iPureIntro; exact HdokF2 |].
      iSplitR; [iPureIntro; exact HddixF2 |].
      iSplitR; [iPureIntro; exact HdocF2 |].
      iSplitR; [iPureIntro; exact HduqF2 |].
      iFrame "Hdlnkd2 Hdiatd Hmetad Haddrsd Hindd Hblocksd".
      (* [su_setnl] moves [di_nlink] only and [dv_of] reads [di_size], so the
         contents value is unmoved (§9 W3). *)
      iSplitL "Hdviewd";
        [iApply (dv_ride_size _ dnW _ data' (eq_sym (su_setnl_size dnW _))
                  with "Hdviewd") |].
      iSplitL "Hfviewd";
        [iApply (fv_ride_size _ dnW _ data' (eq_sym (su_setnl_size dnW _))
                  with "Hfviewd")
        | iExact "Htop"]. }
    iAssert (ity_shot gyd (di_type (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))) as "#Hshotd2".
    { rewrite su_setnl_type Hty'v. iExact "Hshotd". }
    iClear "Hshotd".
    (* ===== +0xb8 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (CID := D18) (mword_of_int (SU + 0xb8)) Ra0 Rs1 mtu
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0b8 with "Htext"). }
    iIntros (D19 Hd19) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mtu !!! Regidx Rs1))]> mtu).
    assert (HC4a0 : (C4 !!! Regidx Ra0 : mword 64) = ientry kd).
    { etransitivity; [rewrite /C4; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s1 _ _ _ _ _ _ Hturegs). }
    assert (HC4regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C4)
      by (rewrite /C4; apply su_regs_caller; [exact Hcsa0 | exact Hturegs]).
    assert (Hppba : add_vec_int (mword_of_int (SU + 0xb8) : mword 64) 2
                    = mword_of_int (SU + 0xba)) by pcw.
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba jal ra,iunlockput(dp) -- CREDITED off the trio ===== *)
    iApply (wp_jal_s_sconf (CID := D19) (mword_of_int (SU + 0xba)) Rra
              (mword_of_int 2089990 : mword 21) C4 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ba with "Htext"). }
    iIntros (D20 Hd20) "Hcg Hpc".
    set (C5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)]> C4).
    assert (Hjup : add_vec (mword_of_int (SU + 0xba) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089990 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup) in "Hpc".
    assert (HC5ra : (C5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xba) : mword 64) 4)
      by (rewrite /C5; apply upd_eq).
    assert (HC5a0 : (C5 !!! Regidx Ra0 : mword 64) = ientry kd)
      by (rewrite /C5 upd_ne; [exact HC4a0 | nz]).
    assert (HC5regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C5)
      by (rewrite /C5; apply su_regs_caller; [exact Hcsra | exact HC4regs]).
    iDestruct (cpu_own_transport T7 D20 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc cn gfs gi cov logstart kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (log_opS_named with "HopS") as (e0) "HopS".
    pose (dnW2 := su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dnW : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrbd2 : false = true ->
              bmapstart ∈ (Sbw ∪ {[IBLOCK dinum inodestart]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcrud2 : true = true ->
              IBLOCK dinum inodestart ∈ (Sbw ∪ {[IBLOCK dinum inodestart]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnud2 : (iput_units <= S c1)%nat).
    { unfold iput_units. lia. }
    iApply (Iunlockput.wp_iunlockput_gen (CID := D20) gs jx gl gu gd gk pd pav
              pu bn g gfs gi cn gtl gild gisld cov logstart bmapstart
              inodestart nib size dev kd qdi sd gyd dinum dnW2 bm'
              (S c1) (Sbw ∪ {[IBLOCK dinum inodestart]}) false true false e0 pid (DfracOwn (1/4)) dqb dqs
              C5 (K - 30)%nat eb b lks
              (upd_upt V P1) Kiup Hkd Hcrbd2 Hcrud2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hdiblk Hdiblog Hdinb Hcovb
              Hnud2 Hj Hgl HC5a0 (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd Hslkdq Hdepd Hidevd Hiinumd
                    Hivalidd Hloadd Hshotd2 Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D21 Hd21 mup n2 Sb2 wg)
      "%Hcsup Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi Hbsl %Hsb2 %Hwg
       %Hwgc %Hn2 HopS Hisl".
    clear Hcrbd2 Hcrud2 Hnud2 dnW2.
    assert (Hpcbe : ret_pc (C5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xbe)) by (rewrite HC5ra; pcw).
    iEval (rewrite Hpcbe) in "Hpc".
    assert (Hupregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mup)
      by exact (su_regs_cs m sp0 _ _ _ C5 mup Hcsup HC5regs).
    assert (Hn24 : (4 <= n2)%nat).
    { destruct Hn2 as [Hn2a Hn2b].
      exact (su_iunlockput_from5 wg (S c1) n2 Hnw5 Hn2a). }
    (* ===== +0xbe lhu a5,74(s2) -- ip->nlink ===== *)
    iEval (rewrite /inode_meta) in "Hmetai".
    iDestruct "Hmetai" as "(Hityi & Himai & Himii & Hinli & Hiszi)".
    iEval (rewrite /i_nlink) in "Hinli".
    iApply (wp_lhu_s_sconf (CID := D21) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xbe)) Ra5 Rs2
              (mword_of_int 74 : mword 12) mup (K - 30)%nat
              (di_nlink dni : mword 16) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0be with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)).
      iExact "Hinli". }
    iIntros (D22 Hd22) "Hcg Hpc Hinli".
    iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ Hupregs)) in "Hinli".
    set (C6 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (di_nlink dni : mword 16))]> mup).
    assert (HC6a5 : (C6 !!! Regidx Ra5 : mword 64)
                    = (zero_extend' 64 (di_nlink dni : mword 16) : mword 64))
      by (rewrite /C6; apply upd_eq).
    assert (HC6regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C6)
      by (rewrite /C6; apply su_regs_caller; [exact Hcsa5 | exact Hupregs]).
    assert (Hppc2 : add_vec_int (mword_of_int (SU + 0xbe) : mword 64) 4
                    = mword_of_int (SU + 0xc2)) by pcw.
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (CID := D22) (mword_of_int (SU + 0xc2)) Ra5
              (mword_of_int 63 : mword 6) C6 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c2 with "Htext"). }
    iIntros (D23 Hd23) "Hcg Hpc".
    set (C7 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget C6 Ra5)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 63 : mword 6))))
                     31 0))]> C6).
    assert (HC7a5 : (C7 !!! Regidx Ra5 : mword 64)
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec
                           (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 63 : mword 6))
                            : mword 64)) 31 0)).
    { rewrite /C7 upd_eq. rgne. rewrite HC6a5. reflexivity. }
    assert (HC7regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C7)
      by (rewrite /C7; apply su_regs_caller; [exact Hcsa5 | exact HC6regs]).
    assert (Hppc4 : add_vec_int (mword_of_int (SU + 0xc2) : mword 64) 2
                    = mword_of_int (SU + 0xc4)) by pcw.
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 sh a5,74(s2) -- the decrement lands ===== *)
    iApply (wp_sh_s_sconf (CID := D23) (kt := KT1) (ktd := KT0) (mword_of_int (SU + 0xc4))
              Ra5 Rs2 (mword_of_int 74 : mword 12) C7 (K - 30)%nat
              (di_nlink dni : mword 16) b with "Hcg Hpc [] [Hinli]").
    { iApply (suli_0c4 with "Htext"). }
    { iEval (rgne; rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs)).
      iExact "Hinli". }
    iIntros (D24 Hd24) "Hcg Hpc Hinli".
    iEval (rgne; rgne;
           rewrite (su_regs_s2 _ _ _ _ _ _ HC7regs) HC7a5) in "Hinli".
    (* the stored halfword, named; the record it makes is [su_setnl] *)
    iAssert (inode_meta (ientry ks)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))
      with "[Hityi Himai Himii Hinli Hiszi]" as "Hmetai".
    { rewrite /inode_meta /su_setnl /= /i_nlink. iFrame. }
    assert (Hdecr : bv_unsigned (di_nlink dni)
                    = bv_unsigned (di_nlink (su_setnl dni
                        (trunc16 (sign_extend' 64 (subrange_vec_dec
                           (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                                     : mword 64)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 63 : mword 6))
                               : mword 64)) 31 0))))) + 1).
    { rewrite su_setnl_nlink. exact (su_nlink_decr (di_nlink dni) Hnlzi). }
    assert (Hppc8 : add_vec_int (mword_of_int (SU + 0xc4) : mword 64) 4
                    = mword_of_int (SU + 0xc8)) by pcw.
    iEval (rewrite Hppc8) in "Hpc".
    (* ===== +0xc8 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D24) (mword_of_int (SU + 0xc8)) Ra0 Rs2 C7
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0c8 with "Htext"). }
    iIntros (D25 Hd25) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (C7 !!! Regidx Rs2))]> C7).
    assert (HC8a0 : (C8 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /C8; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ HC7regs). }
    assert (HC8regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C8)
      by (rewrite /C8; apply su_regs_caller; [exact Hcsa0 | exact HC7regs]).
    assert (Hppca : add_vec_int (mword_of_int (SU + 0xc8) : mword 64) 2
                    = mword_of_int (SU + 0xca)) by pcw.
    iEval (rewrite Hppca) in "Hpc".
    (* ===== +0xca jal ra,iupdate(ip) -- the LEFT receipt ===== *)
    iApply (wp_jal_s_sconf (CID := D25) (mword_of_int (SU + 0xca)) Rra
              (mword_of_int 2089198 : mword 21) C8 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0ca with "Htext"). }
    iIntros (D26 Hd26) "Hcg Hpc".
    set (C9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)]> C8).
    assert (Hjiu : add_vec (mword_of_int (SU + 0xca) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089198 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Hjiu) in "Hpc".
    assert (HC9ra : (C9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xca) : mword 64) 4)
      by (rewrite /C9; apply upd_eq).
    assert (HC9a0 : (C9 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /C9 upd_ne; [exact HC8a0 | nz]).
    assert (HC9regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) C9)
      by (rewrite /C9; apply su_regs_caller; [exact Hcsra | exact HC8regs]).
    assert (Htynzi0 : bv_unsigned (di_type dni) <> 0).
    { destruct Hioki as (_ & _ & _ & Hc & _). exact Hc. }
    assert (Haddri : di_addrs dni = bm_cells bmi).
    { destruct Hioki as (_ & _ & Hc & _). exact Hc. }
    assert (Hdirleni : length (bm_dir bmi) = NDIRECT).
    { destruct Hioki as (Hc & _). exact (blkmap_wf_dir_len cov logstart bmi Hc). }
    destruct n2 as [| c2]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D21 D26 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* THE TAGGED SPEND (V5' increment W).  Both halves of [ip]'s parent
       register come in here -- the [ilinkdp] the parent's name record
       released at the zeroing and the [iparent] the child's own tie handed
       out -- so the flush's local update is [Some (1, ag dp) -> None]:
       [wdt] falls 1 -> 0 and **the register is RESET**.  That is
       §20.9(b)'s escape clause paying off: nothing survives into the free,
       so the next mkdir that reuses this inum under a different parent
       mints against a clean [p = None].  The ticket is already at the
       region's own index spelling (rewritten at (D1) above). *)
    iApply (Iupdate.wp_iupdate_unlink (CID := D26) gs jx gl gu gd gk pd pav pu
              bn g gfs gi cov logstart inodestart nib dev (ientry ks)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                 (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                           : mword 64)
                    (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))
                     : mword 64)) 31 0))))
              dni bmi c2 (Sb2 : gset Z) false
              (Some (Some (bv_unsigned dinum))) pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              C9 (K - 30)%nat eb b lks
              (upd_upt V P1) ltac:(exact Kiupd) ltac:(discriminate) Hgeom Hist0 Hiblki
              Hiblogi Hinb (su_setnl_type_stable dni _)
              ltac:(rewrite su_setnl_type; exact Htynzi0)
              ltac:(exact Hdecr)
              ltac:(rewrite su_setnl_addrs; exact Haddri)
              Hdirleni Hj Hgl HC9a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevi Hiinumi Hmetai
                    [Haddrsi Hindi] Hsbi Hireg Hdiati [Hticket Hipar] Htoken []
                    Hpidq Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsi Hindi". }
    { cbn [ilink_fl]. iSplitL "Hticket"; [iExact "Hticket" | iExact "Hipar"]. }
    { iLeft. iSplit; iPureIntro; [exact Hglog | exact Hcist]. }
    iIntros (D27 Hd27 miu)
      "%Hcsiu Hcg Hown Hpc Hpidq Hidevi Hiinumi Hmetai Hmapi Hsbi Hdiati
       Hbs2 HopS".
    assert (Hpcce : ret_pc (C9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xce)) by (rewrite HC9ra; pcw).
    iEval (rewrite Hpcce) in "Hpc".
    assert (Hiuregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) miu)
      by exact (su_regs_cs m sp0 _ _ _ C9 miu Hcsiu HC9regs).
    (* hm: the bslot unit peeled for iupdate must come back *)
    (* ===== +0xce c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (CID := D27) (mword_of_int (SU + 0xce)) Ra0 Rs2 miu
              (K - 30)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (suli_0ce with "Htext"). }
    iIntros (D28 Hd28) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (E1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (miu !!! Regidx Rs2))]> miu).
    assert (HE1a0 : (E1 !!! Regidx Ra0 : mword 64) = ientry ks).
    { etransitivity; [rewrite /E1; apply upd_eq |].
      rewrite add_vec_zero_l. exact (su_regs_s2 _ _ _ _ _ _ Hiuregs). }
    assert (HE1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E1)
      by (rewrite /E1; apply su_regs_caller; [exact Hcsa0 | exact Hiuregs]).
    assert (Hppd0 : add_vec_int (mword_of_int (SU + 0xce) : mword 64) 2
                    = mword_of_int (SU + 0xd0)) by pcw.
    iEval (rewrite Hppd0) in "Hpc".
    (* ===== +0xd0 jal ra,iunlockput(ip) -- credited off iupdate's own
       [∪ {IBLOCK ip}] ===== *)
    iApply (wp_jal_s_sconf (CID := D28) (mword_of_int (SU + 0xd0)) Rra
              (mword_of_int 2089968 : mword 21) E1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d0 with "Htext"). }
    iIntros (D29 Hd29) "Hcg Hpc".
    set (E2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)]> E1).
    assert (Hjup2 : add_vec (mword_of_int (SU + 0xd0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2089968 : mword 21))
                    = mword_of_int KernelSyms.iunlockput) by pcw.
    iEval (rewrite Hjup2) in "Hpc".
    assert (HE2ra : (E2 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd0) : mword 64) 4)
      by (rewrite /E2; apply upd_eq).
    assert (HE2a0 : (E2 !!! Regidx Ra0 : mword 64) = ientry ks)
      by (rewrite /E2 upd_ne; [exact HE1a0 | nz]).
    assert (HE2regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E2)
      by (rewrite /E2; apply su_regs_caller; [exact Hcsra | exact HE1regs]).
    (* [ip]'s bundle, RE-MINTED AS THE ORPHAN: the count reached ZERO,
       records 2.. are dead (the isdirempty loop's own conclusion), record
       0 is the self record, and record 1 goes back GREY -- FINDING 3's
       re-park, [su_dir_links_orphan] fed by [dir_links_empty_nlink] (V2)
       + the [blez]'s [1 <=] *)
    iDestruct "Hmapi" as "[Haddrsi Hindi]".
    assert (Hnl2z : bv_unsigned (di_nlink (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))) = 0).
    { rewrite su_setnl_nlink.
      exact (su_decr_zero _ _ (su_nlink_decr (di_nlink dni) Hnlzi) Hnl1). }
    assert (Hdead2 : forall k : nat, (2 <= k)%nat ->
              (k < dir_nrec (bv_unsigned
                     (di_size (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))))%nat ->
              dir_inum dati k = bv_0 16).
    { intros k Hk1 Hk2. apply (Hdead k Hk1).
      revert Hk2. rewrite su_setnl_size. exact (fun H => H). }
    assert (HddixZ : dir_dots_ix (bv_unsigned (zero_extend' 32
                       (dir_inum datd kk : mword 16) : mword 32))
                       (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) dati).
    { intros _ Hc. exfalso. apply Hc. exact Hnl2z. }
    assert (HdocZ : dir_orphan_clean (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) dati).
    { apply dir_orphan_clean_of_only.
      apply (dir_dots_only_of dni (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) dati).
      - rewrite su_setnl_size. reflexivity.
      - exact Hdots. }
    assert (HduqZ : dir_uniq (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) dati)
      by (exact (dir_uniq_cong dni _ dati (su_setnl_type _ _)
                   (su_setnl_size _ _) Hduqi)).
    iApply fupd_wp.
    iMod (ireg_link_grey ⊤ gi gfs inodestart nib
            (zero_extend' 32 (dir_inum dati 1 : mword 16) : mword 32)
            ltac:(solve_ndisj)
            ltac:(rewrite su_zext32_unsigned Hpar; exact Hdinb)
            with "Hireg") as "Hgrey".
    iModIntro.
    iEval (rewrite su_zext32_unsigned) in "Hgrey".
    iAssert (dir_links (bv_unsigned (zero_extend' 32
                 (dir_inum datd kk : mword 16) : mword 32))
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) dati)%I
      with "[Hgrey]" as "Hdlnki2".
    { iApply (su_dir_links_orphan _ _ dati Hnl2z Hself0i Hdead2).
      iExact "Hgrey". }
    iDestruct (dlinks_intro with "Hdlnki2 Hetki") as "Hdlnki2".
    (* ...and the ERA's abstract value follows the count (2b-inode-3). *)
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ gfs
            (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                          : mword 32))
            (era_node dni bmi dati)
            (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
            ltac:(solve_ndisj) with "[] Htopi") as "Htopi";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded gfs gi cov logstart ks
               (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi)
      with "[Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi
             Htopi]" as "Hloadi".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists dati.
      iFrame "Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi
              Htopi".
      iPureIntro. split_and!.
      - exact (su_setnl_inode_ok cov logstart dni bmi dati _ Hioki).
      - apply (inode_rec_local_same_type dni _ Hrl_dati (su_setnl_type dni _));
          [ exact (su_dec_short _ _ Hdecr (proj1 (proj2 Hrl_dati)))
          | exact (proj2 (proj2 Hrl_dati)) ].
      - exact (su_setnl_dir_ok icfg_nib dni dati _ Hdoki).
      - exact HddixZ.
      - exact HdocZ.
      - exact HduqZ. }
    iAssert (ity_shot gyi (di_type (su_setnl dni (trunc16 (sign_extend' 64
               (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))) as "#Hshoti2".
    { rewrite su_setnl_type. iExact "Hshoti". }
    iDestruct (cpu_own_transport D27 D29 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (su_esc_acc cn gfs gi cov logstart ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (log_opS_named with "HopS") as (e1) "HopS".
    pose (dni2 := su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dni : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrb2 : false = true ->
              bmapstart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) inodestart]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcru2 : true = true ->
              IBLOCK (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                inodestart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                  (dir_inum datd kk : mword 16) : mword 32) inodestart]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnu2 : (iput_units <= c2)%nat).
    { unfold iput_units. lia. }
    iApply (Iunlockput.wp_iunlockput_gen (CID := D29) gs jx gl gu gd gk pd pav
              pu bn g gfs gi cn gtl gili gisli cov logstart bmapstart
              inodestart nib size dev ks qsi si gyi
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              dni2
              bmi c2 (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) inodestart]})
              false true false e1 pid (DfracOwn (1/4)) dqb dqs
              E2 (K - 30)%nat eb b lks
              (upd_upt V P1) Kiup Hks Hcrb2 Hcru2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblki Hiblogi Hinb Hcovb
              Hnu2 Hj Hgl HE2a0 (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hesci Hireg Hropen Hslki Hslkiq Hdepi Hidevi Hiinumi
                    Hivalidi Hloadi Hshoti2 Hfrzi [$Hkeepi $Hrui] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D30 Hd30 mip n3 Sb3 wh)
      "%Hcsip Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi Hbsl %Hsb3
       %Hwh %Hwhc %Hn3 HopS Hisl2".
    clear Hcrb2 Hcru2 Hnu2 dni2.
    assert (Hpcd4 : ret_pc (E2 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd4)) by (rewrite HE2ra; pcw).
    iEval (rewrite Hpcd4) in "Hpc".
    assert (Hipregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) mip)
      by exact (su_regs_cs m sp0 _ _ _ E2 mip Hcsip HE2regs).
    (* ===== +0xd4 jal ra,end_op ===== *)
    iApply (wp_jal_s_sconf (CID := D30) (mword_of_int (SU + 0xd4)) Rra
              (mword_of_int 2092174 : mword 21) mip (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0d4 with "Htext"). }
    iIntros (D31 Hd31) "Hcg Hpc".
    set (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)]> mip).
    assert (Hjeo : add_vec (mword_of_int (SU + 0xd4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092174 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Hjeo) in "Hpc".
    assert (HE3ra : (E3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SU + 0xd4) : mword 64) 4)
      by (rewrite /E3; apply upd_eq).
    assert (HE3regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) E3)
      by (rewrite /E3; apply su_regs_caller; [exact Hcsra | exact Hipregs]).
    iDestruct (cpu_own_transport D30 D31 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D30 D31 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D30 D31 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iApply (EndOp.wp_end_op_sconf (CID := D31) gs jx gl gu gd gk pd pav pu bn
              g gfs cov logstart dev n3 pid (DfracOwn (1/4)) E3 (K - 30)%nat
              eb b lks (upd_upt V P1) Keo Hgeom Hj Hgl
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpanenv Hbio Hlog Hseam Hgen
                    Hpidq Hprocs Hdev Hgeo Hdlk [HopS]").
    { rewrite /log_op. iExists Sb3. iExact "HopS". }
    iIntros (D32 Hd32 meo) "%Hcseo Hcg Hown Htce Hcce Hpc Hpidq".
    assert (Hpcd8 : ret_pc (E3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0xd8)) by (rewrite HE3ra; pcw).
    iEval (rewrite Hpcd8) in "Hpc".
    assert (Heoregs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) meo)
      by exact (su_regs_cs m sp0 _ _ _ E3 meo Hcseo HE3regs).
    (* ===== +0xd8 c.li a0,0 ===== *)
    iApply (wp_cli_s_sconf (CID := D32) (mword_of_int (SU + 0xd8)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              meo (K - 30)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (suli_0d8 with "Htext"). }
    iIntros (D33 Hd33) "Hcg Hpc".
    set (F1 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int 0 : mword 64)]> meo).
    assert (HF1a0 : (F1 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1regs : su_regs m sp0 (ientry kd) (ientry ks) (pa_stk sp0 8) F1)
      by (rewrite /F1; apply su_regs_caller; [exact Hcsa0 | exact Heoregs]).
    assert (Hppda : add_vec_int (mword_of_int (SU + 0xd8) : mword 64) 2
                    = mword_of_int (SU + 0xda)) by pcw.
    iEval (rewrite Hppda) in "Hpc".
    (* ===== +0xda c.ldsp s1,216(sp) ===== *)
    assert (Hd3a : add_vec (F1 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 27 : mword 6) ('b"000")))
                   = pa_stk sp0 3)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF1regs); apply su_frm3).
    iApply (wp_cldsp_s_sconf (CID := D33) (mword_of_int (SU + 0xda))
              (mword_of_int 27 : mword 6) Rs1 F1 (K - 30)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (suli_0da with "Htext"). }
    { iEval (rewrite Hd3a). iExact "Hf3". }
    iIntros (D34 Hd34) "Hcg Hpc Hf3".
    iEval (rewrite Hd3a) in "Hf3".
    set (F2 := <[Regidx Rs1 := regval_into_reg
                  (m !!! Regidx Rs1 : mword 64)]> F1).
    assert (HF2a0 : (F2 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F2 upd_ne; [exact HF1a0 | nz]).
    assert (HF2regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
                        (pa_stk sp0 8) F2).
    { rewrite /F2.
      exact (su_regs_wr_s1 m sp0 (ientry kd) (m !!! Regidx Rs1 : mword 64)
               (ientry ks) (pa_stk sp0 8) F1 _ eq_refl HF1regs). }
    assert (Hppdc : add_vec_int (mword_of_int (SU + 0xda) : mword 64) 2
                    = mword_of_int (SU + 0xdc)) by pcw.
    iEval (rewrite Hppdc) in "Hpc".
    (* ===== +0xdc c.ldsp s2,208(sp) ===== *)
    assert (Hd4a : add_vec (F2 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                   = pa_stk sp0 4)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF2regs); apply su_frm4).
    iApply (wp_cldsp_s_sconf (CID := D34) (mword_of_int (SU + 0xdc))
              (mword_of_int 26 : mword 6) Rs2 F2 (K - 30)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (suli_0dc with "Htext"). }
    { iEval (rewrite Hd4a). iExact "Hf4". }
    iIntros (D35 Hd35) "Hcg Hpc Hf4".
    iEval (rewrite Hd4a) in "Hf4".
    set (F3 := <[Regidx Rs2 := regval_into_reg
                  (m !!! Regidx Rs2 : mword 64)]> F2).
    assert (HF3a0 : (F3 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2a0 | nz]).
    assert (HF3regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F3).
    { rewrite /F3.
      exact (su_regs_wr_s2 m sp0 (m !!! Regidx Rs1 : mword 64) (ientry ks)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8) F2 _ eq_refl
               HF2regs). }
    assert (Hppde : add_vec_int (mword_of_int (SU + 0xdc) : mword 64) 2
                    = mword_of_int (SU + 0xde)) by pcw.
    iEval (rewrite Hppde) in "Hpc".
    (* ===== +0xde c.ldsp s3,200(sp) ===== *)
    assert (Hd5a : add_vec (F3 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64
                        (concat_vec (mword_of_int 25 : mword 6) ('b"000")))
                   = pa_stk sp0 5)
      by (rewrite (su_regs_sp _ _ _ _ _ _ HF3regs); apply su_frm5).
    iApply (wp_cldsp_s_sconf (CID := D35) (mword_of_int (SU + 0xde))
              (mword_of_int 25 : mword 6) Rs3 F3 (K - 30)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf5]").
    { iApply (suli_0de with "Htext"). }
    { iEval (rewrite Hd5a). iExact "Hf5". }
    iIntros (D36 Hd36) "Hcg Hpc Hf5".
    iEval (rewrite Hd5a) in "Hf5".
    set (F4 := <[Regidx Rs3 := regval_into_reg
                  (m !!! Regidx Rs3 : mword 64)]> F3).
    assert (HF4a0 : (F4 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3a0 | nz]).
    assert (HF4regs : su_regs m sp0 (m !!! Regidx Rs1 : mword 64)
                        (m !!! Regidx Rs2 : mword 64)
                        (m !!! Regidx Rs3 : mword 64) F4).
    { rewrite /F4.
      exact (su_regs_wr_s3 m sp0 (m !!! Regidx Rs1 : mword 64)
               (m !!! Regidx Rs2 : mword 64) (pa_stk sp0 8)
               (m !!! Regidx Rs3 : mword 64) F3 _ eq_refl HF3regs). }
    assert (Hppe0 : add_vec_int (mword_of_int (SU + 0xde) : mword 64) 2
                    = mword_of_int (SU + 0xe0)) by pcw.
    iEval (rewrite Hppe0) in "Hpc".
    (* ===== +0xe0 c.j +0x168 -- into the shared epilogue ===== *)
    iApply (wp_cj_s_sconf (CID := D36) (mword_of_int (SU + 0xe0))
              (sign_extend' 21 (concat_vec (mword_of_int 68 : mword 11) ('b"0")))
              F4 (K - 30)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (suli_0e0 with "Htext"). }
    iIntros (D37 Hd37). iNext. iIntros "Hcg Hpc".
    assert (Htg168 : add_vec (mword_of_int (SU + 0xe0) : mword 64)
                       (sign_extend' 64
                          (sign_extend' 21
                             (concat_vec (mword_of_int 68 : mword 11) ('b"0"))))
                     = mword_of_int (SU + 0x168)) by pcw.
    iEval (rewrite Htg168) in "Hpc".
    (* the buffers and slot 27, put back for the epilogue *)
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
      as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iDestruct (su_off_join sp0 lo
                 (mword_of_int (Z.of_nat (16 * kk)) : mword 32) Hal27
                 with "H27lo H27hi") as "H27".
    assert (HF4sp : su_sp sp0 F4) by exact (su_regs_sp _ _ _ _ _ _ HF4regs).
    assert (HF4thr : su_thr m F4) by exact (su_regs_thr _ _ _ _ _ _ HF4regs).
    assert (HF4s1 : (F4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by exact (su_regs_s1 _ _ _ _ _ _ HF4regs).
    assert (HF4s2 : (F4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by exact (su_regs_s2 _ _ _ _ _ _ HF4regs).
    assert (HF4s3 : (F4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by exact (su_regs_s3 _ _ _ _ _ _ HF4regs).
    iDestruct (cpu_own_transport D32 D37 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D32 D37 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D32 D37 eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := D37)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (su_epilogue (CID0 := D37) m F4 sp0 K b (proc_addr jx)
              (m !!! Regidx Rs1 : mword 64) (m !!! Regidx Rs2 : mword 64)
              (m !!! Regidx Rs3 : mword 64) w6
              (word_of_words lo (mword_of_int (Z.of_nat (16 * kk)) : mword 32))
              w30 (fun _ => NUL) bnf bp bex
              K30 Kpop Hsp0 HF4sp HF4thr HF4s1 HF4s2 HF4s3 Hal
              with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                    HbE H30
                    [Hown Htce Hcce Hpidq Hsbb Hsbi Hsbs Hbsl Hisl
                     Hisl2 Hpre Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
    iDestruct (cpu_own_transport D37 CIDy 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D37 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D37 CIDy eb (proc_addr jx)
                 ltac:(rewrite Hbeq; wp_next_chain) with "Hcce") as "Hcce".
    iDestruct ("Hpre" with "Hpidq") as "Hpriv".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hbsl Hsbb Hsbi Hsbs [Hisl Hisl2] Hpriv [%]").
    { exact Hcsf. }
    { exact Hupt1. }
    { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
      rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
    { right. rewrite Ha0f HF4a0. pcw. }
  Qed.


  (* ==================================================================== *)
  (*  **THE SEAL.**  W1 ∘ W2 ∘ W3 ∘ {W5-FILE, W5-DIR}, and nothing else.  *)
  (*                                                                      *)
  (*  Every block is a landed lemma and every seam is the next block's     *)
  (*  premise list verbatim, so this composes rather than proves: the only *)
  (*  work is naming the seam's ∀-bound bundle and handing the caller's    *)
  (*  exit BACK at each stage (durable-notes, "chaining two halves").      *)
  (*  [trap_csrs_ext eb] and [cpu_claim_ext eb] are DROPPED at entry --    *)
  (*  both are [emp] at [eb = true], which this contract's own premise     *)
  (*  forces -- and the exit continuation the walk hands on is the         *)
  (*  caller's own, which still demands them, so nothing is lost.          *)
  (*                                                                      *)
  (*  The T_DIR arm takes NO design-fact premise any more: (D1) and (D2)   *)
  (*  are derived inside [su_w5_dir] (V5' increment W).                    *)
  (* ==================================================================== *)
  Lemma wp_sys_unlink_sconf `{GEN : GenId} `{CID0 : CpuId}
      (gf ga gpr : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (dqb dqs dqbs : dfrac) (v0 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    SpecSysUnlink.wp_sys_unlink_sconf_body gf ga gpr gs jx gl gu gd gk pd pav
      pu bn g gfs gi cn gtl cov logstart bmapstart inodestart nib size dev
      dqb dqs dqbs v0 pid V m K eb b lks.
  Proof.
    cbv beta zeta delta [SpecSysUnlink.wp_sys_unlink_sconf_body].
    intros HK Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hnib16 Hprk Hj Hgl Heb Harg0.
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hprenv #Hbio #Hlog
             Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows
             #Hslks #Hireg #Hropen Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv
             Hcont".
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpenv".
    (* ---- W1, +0x00..+0x2e: the prologue, argstr, begin_op, nameiparent ---- *)
    iApply (su_w1 gf ga gs jx gl gu gd gk pd pav pu bn g gfs gi cn gtl cov
              logstart bmapstart inodestart nib size dev dqb dqs dqbs
              v0 pid V m K eb b lks HK Hcdev Hcnib Hclog Hcist HdevR Hnib0
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb
              Harg0
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv [] Hcont").
    iIntros (CIDa Ms P1 n1 Sb1 w1 dpv nf bp bnm0 bd be w4 w5 w6 w27 w30).
    iIntros "%Hal %Hregs1 %Hma01 %Hupt1 %Hn1 %Hw1 %Hdpvnz
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv Hir
             Hheld HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE
             H30 Hcont".
    (* ---- W2, +0x30..+0x6e: ilock(dp), the two namecmp refusals,
       dirlookup ---- *)
    iApply (su_w2 gf ga gs jx gl gu gd gk pd pav pu bn g gfs gi cn gtl cov
              logstart bmapstart inodestart nib size dev dqb dqs dqbs
              pid V P1 n1 Sb1 w1 dpv nf bnm0 bp bd be w4 w5 w6 w27 w30
              m Ms (m !!! Regidx csp_rs1 : mword 64) K eb b lks
              HK Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hregs1 Hma01 Hn1
              Hupt1
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv Hheld HopS
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE H30
                    [] Hcont").
    iIntros (CIDb M2 kd ks kk gild gisld gyd qdi sd qs dinum dnd bmd datd lo).
    iIntros "%Hregs2 %Hkd %Hks %Hdinb %Htydir %Hiok %Hrl_datd %Hdok %Hddix
             %Hdoc %Hduq
             %Hnotdot %Hnotdd %Hfst %Hma02 %Hal27
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W3, +0x72..+0x88: ilock(ip), the nlink panic, the T_DIR test
       (and, on the taken arm, the whole isdirempty loop through W4) ---- *)
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpetop".
    iApply (su_w3 gf ga gs jx gl gu gd gk pd pav pu bn g gfs gi cn gtl cov
              logstart bmapstart inodestart nib size dev dqb dqs dqbs
              pid V P1 n1 Sb1 w1 kd ks kk gild gisld gyd qdi sd qs
              dinum dnd bmd datd lo nf bnm0 bp bd be w5 w6 w30
              m M2 (m !!! Regidx csp_rs1 : mword 64) K eb b lks
              HK Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1 Hupt1 Hregs2
              Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
              Hnotdot Hnotdd
              Hfst Hma02 Hal27
              with "Hcg Hown Htext Hdata Hpetop Hpc Hbio Hlog Hseam Hgen Hdev Hgeo
                    Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen Hsbb Hsbi
                    Hsbs Hbmres Hkenv Hprocs Hpriv Hslkd Hslkdq
                    Hdepd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad
                    Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                    HbE H30 [] Hcont").
    iIntros (CIDc M3 s3x bex isdir gili gisli gyi si qsi dni bmi dati).
    iIntros "%Hregs3 %Hnlzi %Hioki %Hrl_dati %Hdoki %Hddixi %Hdoci %Hduqi
             %Hisd
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd Hfrz Hkeepd Hrud
             Hslki Hslkiq Hdepi Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Hdviewi Hfviewi Htopi Hshoti Hfrzi Hkeepi Hrui HopS
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W5, +0x8a..: the zeroing and the two tails, split on the seam's
       own index.  The FILE arm is [su_w5_file]; the T_DIR arm is
       [su_w5_dir], which since V5' increment W derives (D1) and (D2)
       internally and takes neither as a premise. ---- *)
    destruct isdir.
    - destruct Hisd as (Htyzi & Hdots & Hdead).
      iApply (su_w5_dir gf ga gs jx gl gu gd gk pd pav pu bn g gfs gi cn gtl
                gpr cov logstart bmapstart inodestart nib size dev
                dqb dqs dqbs pid V P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks
                HK Hclog Hprk Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Htyzi Hdots Hdead
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq Hdepi Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Hdviewi Hfviewi Htopi Hshoti Hfrzi Hkeepi Hrui HopS
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
    - iApply (su_w5_file gf ga gs jx gl gu gd gk pd pav pu bn g gfs gi cn gtl
                gpr cov logstart bmapstart inodestart nib size dev
                dqb dqs dqbs pid V P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks
                HK Hclog Hprk Hcdev Hcnib Hcist Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Hisd
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq Hdepd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Hdviewd Hfviewd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq Hdepi Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Hdviewi Hfviewi Htopi Hshoti Hfrzi Hkeepi Hrui HopS
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
  Qed.

End ProofSysUnlinkBody.

End SysUnlinkProof.
