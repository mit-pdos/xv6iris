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
   innermost [CpuId] and the guard degrades to a tautology.

   ==== THE TWO CONTINUATIONS ARE NAMED ================================

   This file's cost was never a hot sentence -- it was |Delta|, RULE ONE in
   claude-notes/optimization.md.  A mid-walk dump found 87 hypotheses / 11.7
   kB, of which TWO entries, both continuations spelled inline, were 55 %:
   the block's own fall-through seam ([su_wN_seam] beside each block lemma)
   and the RETURN continuation ([SpecSysUnlink.sys_unlink_closer], which was
   written out ten times -- the contract and nine statements here).  Naming
   both, all TRANSPARENT, changed no proof script and took the file

     153.7 s -> 133.1 s (-13.4 %), .vo 8.94 MB -> 7.62 MB (-14.8 %)

   isolated, min of three interleaved runs.  The optimization note's
   ProofSysUnlink case study has the full ranking and the two negative
   results (do NOT fold the open-inode bundles or the frame; they are
   consumed row by row). *)
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
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
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
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import IregLinkNz.   (* the nonzero-count reading at a held token
                                ([ireg_tok_nz]) and the agreement of two
                                fragments of one register
                                ([ireg_toks_agree]), which is (D1) *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import SpecReadi.
Require Import SpecWritei.
Require Import SpecNamex.
Require Import CodeSysUnlink.
Require Import SysUnlinkBudget.
Require Import SpecSysUnlink.
Require Import ProofSysUnlinkParts.
Require Import ProofSysUnlinkTails.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows] / [off_rows_dep] / [off_rows_to_dep] -- the inode's off rows (items 35/36) *)

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

Lemma su_upd_upt_idem `{XI : CurCtx} (V : pprivate) (P1 P2 : uptd) :
  upd_upt (upd_upt V P1) P2 = upd_upt V P2.
Proof. reflexivity. Qed.

Lemma su_cwd_upt `{XI : CurCtx} (V : pprivate) (P : uptd) : pv_cwd (upd_upt V P) = pv_cwd V.
Proof. reflexivity. Qed.

Lemma su_upd_cwd_upt `{XI : CurCtx} (V : pprivate) (P : uptd) :
  upd_cwd (upd_upt V P) (pv_cwd V) = upd_upt V P.
Proof. destruct V; reflexivity. Qed.

(* [SysUnlinkBudget] and [SpecSysUnlink] both define [sys_unlink_slots];
   this file imports both, so every mention of the allowance is spelled at
   the CONTRACT's copy and this is the bridge to the literal the callees
   want. *)
Lemma su_slots2 `{XI : CurCtx} : SpecSysUnlink.sys_unlink_slots = 2%nat.
Proof. reflexivity. Qed.

(* argstr's [noff] premise at the walk's own depth, which is zero. *)
Lemma su_noff0 `{XI : CurCtx} : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia.
Qed.

(* nameiparent's counter report, read into the ledger's own name.  [ok]
   fixes the second summand at zero, which is the only difference between
   this and [su_u1f]. *)
Lemma su_cnt_ok `{XI : CurCtx} (w1 : bool) (n1 : nat) :
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
Lemma su_dot_name `{XI : CurCtx} : bname 14 su_dot_f = dot_name.
Proof. vm_compute. reflexivity. Qed.

Lemma su_dotdot_name `{XI : CurCtx} : bname 14 su_dotdot_f = dotdot_name.
Proof. vm_compute. reflexivity. Qed.

(* the two [auipc]/[addi] pairs, computed.  CLOSED terms -- no free
   address -- so [vm_compute] is safe here (contrast [su_offcell]). *)
Lemma su_dotaddr `{XI : CurCtx} :
  add_vec (add_vec (mword_of_int (SU + 0x34) : mword 64)
                   (auipc_off (mword_of_int 2 : mword 20)))
          (sign_extend' 64 (mword_of_int 1554 : mword 12))
  = (mword_of_int su_dot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_dotdotaddr `{XI : CurCtx} :
  add_vec (add_vec (mword_of_int (SU + 0x48) : mword 64)
                   (auipc_off (mword_of_int 2 : mword 20)))
          (sign_extend' 64 (mword_of_int 1542 : mword 12))
  = (mword_of_int su_dotdot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [di_type dn = T_DIR] at the sixteen-bit width, read as the Z-level
   equality [DirView] states its type tests at.  The
   [ity_shot] agreement gives the left form and every payload clause wants
   the right one. *)
Lemma su_tdir_zof `{XI : CurCtx} (t : mword 16) :
  t = SpecDirlookup.T_DIR -> bv_unsigned t = T_DIR_z.
Proof. intros ->. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  W4's PURE LAYER -- the isdirempty loop's index arithmetic and the      *)
(*  dots-only harvest at its empty exit.                                  *)
(* ===================================================================== *)

(* 8-alignment weakens to the [lhu]'s 2 (ProofDirlookupParts' shape,
   restated: a whole-function proof's parts file is not a dependency this
   one may take). *)
Lemma su_rem8_2 `{XI : CurCtx} (x : Z) : 0 <= x -> Z.rem x 8 = 0 -> Z.rem x 2 = 0.
Proof.
  intros H0 H8.
  rewrite Z.rem_mod_nonneg in H8; [| exact H0 | lia].
  rewrite Z.rem_mod_nonneg; [| exact H0 | lia].
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in H8; [| lia].
  destruct H8 as [c Hc]. exists (4 * c). lia.
Qed.

Lemma su_align_8_2 `{XI : CurCtx} (a : Arch.pa) :
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
Lemma su_dots_only_scan `{XI : CurCtx} (self : Z) (dn : dinode) (data : nat -> list (bv 8)) :
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
Lemma su_moi32_id `{XI : CurCtx} (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  apply Z_to_bv_bv_unsigned.
Qed.

(* the [lw] of ip->size, read at the literal the loop's compares want *)
Lemma su_size_sext `{XI : CurCtx} (w : mword 32) :
  bv_unsigned w < 2 ^ 31 ->
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_unsigned w).
Proof.
  intro Hw. rewrite -{1}(su_moi32_id w). apply w32_sext_moi.
  pose proof (proj1 (bv_unsigned_in_range _ w)). lia.
Qed.

(* [rd_clamp] at n = 16: never more; and 16 exactly means the whole record
   sits inside the file *)
Lemma su_clamp_le16 `{XI : CurCtx} (szw : bv 32) (off : nat) :
  (rd_clamp szw off 16 <= 16)%nat.
Proof. unfold rd_clamp. case_decide; lia. Qed.

Lemma su_clamp16_in `{XI : CurCtx} (szw : bv 32) (off : nat) :
  rd_clamp szw off 16 = 16%nat ->
  (off + 16 <= Z.to_nat (bv_unsigned szw))%nat.
Proof. unfold rd_clamp. case_decide; lia. Qed.

(* [dir_nrec] against the byte bound, both directions *)
Lemma su_nrec_le `{XI : CurCtx} (sz : Z) (j : nat) :
  0 <= sz -> sz <= 16 * Z.of_nat j -> (dir_nrec sz <= j)%nat.
Proof.
  intros H0 Hj. unfold dir_nrec.
  assert (Hd : sz `div` 16 <= Z.of_nat j) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma su_nrec16 `{XI : CurCtx} (sz : Z) :
  0 <= sz -> (16 * dir_nrec sz <= Z.to_nat sz)%nat.
Proof.
  intro H0. unfold dir_nrec.
  pose proof (Z.mul_div_le sz 16 ltac:(lia)) as Hle.
  pose proof (Z.div_pos sz 16 H0 ltac:(lia)) as Hp. lia.
Qed.

(* [neq_vec] off the [eq_vec] facts the parts file states *)
Lemma su_neq_of_eq_true `{XI : CurCtx} (x y : mword 64) :
  eq_vec x y = true -> neq_vec x y = false.
Proof. intro H. unfold neq_vec. rewrite H. reflexivity. Qed.

Lemma su_neq_of_eq_false `{XI : CurCtx} (x y : mword 64) :
  eq_vec x y = false -> neq_vec x y = true.
Proof. intro H. unfold neq_vec. rewrite H. reflexivity. Qed.

(* the two inum bytes of a record, and its fourteen name bytes
   ([ProofDirlookupParts]' shapes, restated) *)
Lemma su_half_bytes_eq `{XI : CurCtx} (data : nat -> list (bv 8)) (i j : nat) :
  (j < 2)%nat -> nth_byte (dir_inum data i) j = file_byte data (16 * i + j)%nat.
Proof.
  intro Hj. destruct j as [| [| j]]; [| | exfalso; lia].
  - rewrite dir_inum_byte0. f_equal; lia.
  - rewrite dir_inum_byte1. f_equal; lia.
Qed.

Lemma su_name_shift `{XI : CurCtx} (data : nat -> list (bv 8)) (i j : nat) :
  file_byte data (16 * i + (2 + j))%nat = dir_name data i j.
Proof. unfold dir_name. f_equal; lia. Qed.

(* the [zero_extend' 32] dirlookup's iget wraps the halfword inum in is
   unsigned-transparent -- W3 reads the region bound through it *)
Lemma su_zext32_unsigned `{XI : CurCtx} (w : mword 16) :
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
          [] [] 1%positive (mword_of_int 0) [] 0.

(* readi's delivered byte at [tot = 16] is the file's byte *)
Lemma su_rdd_eq `{XI : CurCtx} (data : nat -> list (bv 8)) (olds : nat -> bv 8)
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
Lemma su_wi_blocks `{XI : CurCtx} (k : nat) : wi_blocks (16 * k) 16 = 1%nat.
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

Lemma su_wi_cost `{XI : CurCtx} (k : nat) : wi_cost_bmonly (16 * k) 16 = 4%nat.
Proof. unfold wi_cost_bmonly. rewrite (su_wi_blocks k). reflexivity. Qed.

(* [iunlockput] can report at most one bitmap unit spent on this credited
   call.  Keep that arithmetic out of the whole-function Iris context. *)
Lemma su_iunlockput_from5 `{XI : CurCtx} (w : bool) (n n' : nat) :
  (5 <= n)%nat ->
  ((n - ip_spend_w w true false)%nat <= n')%nat ->
  (4 <= n')%nat.
Proof. unfold ip_spend_w, ip_bm. destruct w; cbn; lia. Qed.

(* the zero record: its inum field and each of its sixteen bytes *)
Lemma su_dz_inum `{XI : CurCtx} : de_inum dirent_zero = bv_0 16.
Proof. reflexivity. Qed.

Lemma su_dz_byte `{XI : CurCtx} (j : nat) :
  (j < 16)%nat -> dirent_bytes dirent_zero !!! j = NUL.
Proof.
  intro Hj. rewrite dirent_bytes_zero.
  do 16 (destruct j as [| j]; [reflexivity |]). exfalso. lia.
Qed.

(* the decrement arithmetic, mword-free *)
Lemma su_decr_pay `{XI : CurCtx} (x y : Z) (bb : bool) :
  y = x + 1 -> x + (if bb then 1 else 0) <= y.
Proof. intro H. destruct bb; lia. Qed.

(* the decrement stays short, over plain [Z] (durable-disk 2b-inode-3):
   [lia]'s zify hook does not come back with [bv_unsigned] in the goal. *)
Lemma su_dec_short `{XI : CurCtx} (a c : Z) : c = a + 1 -> c <= 32767 -> a <= 32767.
Proof. lia. Qed.

Lemma su_decr_pos `{XI : CurCtx} (x y z : Z) : y = x + 1 -> y = z -> 2 <= z -> x <> 0.
Proof. intros. lia. Qed.

Lemma su_le1_nz_eq1 `{XI : CurCtx} (x : Z) : 0 <= x -> x <= 1 -> x <> 0 -> x = 1.
Proof. intros. lia. Qed.

Lemma su_decr_zero `{XI : CurCtx} (x y : Z) : y = x + 1 -> y = 1 -> x = 0.
Proof. intros. lia. Qed.

(* panic's side conditions as CLOSED lemmas over plain nat/gset -- never an
   inline [ltac:] in the application (see claude-notes/projects/panic.md). *)
Lemma su_pn_K `{XI : CurCtx} (K : nat) : (K_sys_unlink <= K)%nat -> (panic_stack <= K - 30)%nat.
Proof. lia. Qed.

Lemma su_pn_K_readi `{XI : CurCtx} (K : nat) :
  (K_readi <= K - 30)%nat -> (panic_stack <= K - 30)%nat.
Proof. lia. Qed.

Lemma su_pn_noff `{XI : CurCtx} : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma su_pn_below `{XI : CurCtx} (lks : gset string) :
  locks_below lks "log" -> locks_below lks "pr".
Proof. intros H. apply (locks_below_mono lks "log" "pr" H). vm_compute; lia. Qed.
(* ==================================================================== *)
(*  ProofSysUnlinkW3.v -- sys_unlink's W3 block. *)
(*                                                                      *)
(*  Split out of ProofSysUnlink.v FOR THE BUILD DAG: the five block      *)
(*  lemmas are mutually independent (each seam is the NEXT block's        *)
(*  premise list, so the seal composes them and nothing else does), and   *)
(*  [Tails.] is named only inside proofs, never in a statement -- so each *)
(*  file makes its own [Tails] and the vocabulary they share             *)
(*  (ProofSysUnlinkShared.v) needs no functor argument at all.            *)
(* ==================================================================== *)

Require Import ProofSysUnlinkShared.

Module SysUnlinkW3 (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) (PN : PANIC) (Ilock : ILOCK) (Readi : READI).

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkW3.
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
  Definition su_w4_exitE `{XI : CurCtx} `{GEN : GenId}
      (jx ki : nat)
 (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (sp0 dpv ipv : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Upr : ustate) : iProp Σ :=
    (∀ (CIDx : CpuId) (Mx : regfile) (s3x : mword 64) (bex : nat -> bv 8),
       ⌜su_regs m sp0 dpv ipv s3x Mx⌝ -∗
       sie_cap_gpr KT1 Mx (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x174)) -∗
       i_dev (ientry ki) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       inode_meta (ientry ki) dni -∗
       inode_map fsc_fs (ientry ki) bmi -∗
       inode_blocks fsc_fs bmi dati -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
       proc_priv_bare (proc_addr jx) pidv Upr -∗
       bslot -∗
       X -∗
       WP (Loop : expr riscv_lang))%I.

  (* the EMPTY exit: every record past the dots is dead, and the payload
     clause is [dir_dots_only] -- exactly what W5-DIR's re-park
     ([su_dir_links_orphan]) reads, stated at the loop's own [dati]. *)
  Definition su_w4_exitD `{XI : CurCtx} `{GEN : GenId}
      (jx ki : nat)
 (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (sp0 dpv ipv : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Upr : ustate) : iProp Σ :=
    (∀ (CIDx : CpuId) (Mx : regfile) (s3x : mword 64) (bex : nat -> bv 8),
       ⌜su_regs m sp0 dpv ipv s3x Mx⌝ -∗
       ⌜dir_dots_only dni dati⌝ -∗
       ⌜forall k : nat, (2 <= k)%nat ->
          (k < dir_nrec (bv_unsigned (di_size dni)))%nat ->
          dir_inum dati k = bv_0 16⌝ -∗
       sie_cap_gpr KT1 Mx (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x8a)) -∗
       i_dev (ientry ki) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       inode_meta (ientry ki) dni -∗
       inode_map fsc_fs (ientry ki) bmi -∗
       inode_blocks fsc_fs bmi dati -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ[KT1] bex jj) -∗
       proc_priv_bare (proc_addr jx) pidv Upr -∗
       bslot -∗
       X -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE ITERATION, by fuel over the remaining bytes.  Entry at +0x106
     with s3 = 16*jj, records 2..jj-1 known dead. *)
  Local Lemma su_w4_loop `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (ki : nat) (inumi : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (dpv ipv : mword 64)
      (m : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Upr : ustate) :
    (K_readi <= K - 30)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true -> lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    ipv = ientry ki ->
    inode_ok fsc_cov fsc_logst dni bmi dati ->
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
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    (* the byte view's row, for readi's crossing (durable-disk 1c-flip) *)
    fs_bytes_any fsc_fs -∗
    kalloc_env fsc_kalloc None -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    i_dev (ientry ki) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    inode_meta (ientry ki) dni -∗
    inode_map fsc_fs (ientry ki) bmi -∗
    inode_blocks fsc_fs bmi dati -∗
    ([∗ list] jj0 ∈ seq 0 16, pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] bcur jj0) -∗
    proc_priv_bare (proc_addr jx) pidv Upr -∗
    bslot -∗
    su_w4_exitE jx ki dni bmi dati pidv dq
                m sp0 dpv ipv K eb b lks X Upr -∗
    su_w4_exitD jx ki dni bmi dati pidv dq
                m sp0 dpv ipv K eb b lks X Upr -∗
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
    iDestruct (inode_map_q_1_to _ _ _ _ eq_refl with "Hmap") as "Hmap".
    iDestruct (inode_blocks_q_1_to _ _ _ _ eq_refl with "Hblocks") as "Hblocks".
    iApply (Readi.wp_readi_sconf KT1 (CID := CID6) gs jx gl pd pav pu
 gf (ientry ki) bmi dati dni false
              (16 * jj)%nat 16%nat bcur (upd_usM Upr _) pidv (DfracOwn 1) (DfracOwn (1/2))
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
    iDestruct (inode_map_q_1_of _ _ _ _ eq_refl with "Hmap") as "Hmap".
    iDestruct (inode_blocks_q_1_of _ _ _ _ eq_refl with "Hblocks") as "Hblocks".
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
        iIntros (CID15 Hq15). iApply bi.later_intro. iIntros "Hcg Hpc".
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
  Lemma su_w4 `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (ki : nat) (inumi : mword 32) (dni : dinode) (bmi : blkmap)
      (dati : nat -> list (bv 8))
      (pidv : mword 32) (dq : dfrac)
      (be : nat -> bv 8)
      (dpv ipv s3v : mword 64)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (X : iProp Σ) (Upr : ustate) :
    (K_readi <= K - 30)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    (jx < NPROC)%nat -> gs !! jx = Some gl ->
    eb = true -> lks = ∅ ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    ipv = ientry ki ->
    inode_ok fsc_cov fsc_logst dni bmi dati ->
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
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    (* the byte view's row, for readi's crossing (durable-disk 1c-flip) *)
    fs_bytes_any fsc_fs -∗
    kalloc_env fsc_kalloc None -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    i_dev (ientry ki) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    inode_meta (ientry ki) dni -∗
    inode_map fsc_fs (ientry ki) bmi -∗
    inode_blocks fsc_fs bmi dati -∗
    ([∗ list] jj0 ∈ seq 0 16, pa_add (pa_stk sp0 29) jj0 ↦ₘ[KT1] be jj0) -∗
    proc_priv_bare (proc_addr jx) pidv Upr -∗
    bslot -∗
    su_w4_exitE jx ki dni bmi dati pidv dq
                m sp0 dpv ipv K eb b lks X Upr -∗
    su_w4_exitD jx ki dni bmi dati pidv dq
                m sp0 dpv ipv K eb b lks X Upr -∗
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
      iApply (su_w4_loop (CID0 := CID4) gs jx gl pd pav pu
 gf ki inumi dni bmi dati pidv dq dpv ipv
                m sp0 K eb b lks X Upr Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal
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
  (* W3'S SEAM, NAMED.  claude-notes/optimization.md, "Fold block
     continuations into named definitions" and the ProofSysUnlink case study
     beside it.  Spelled inline this was 121 lines, and a mid-walk dump of
     [Delta] here measured it as the single largest entry in the context by
     an order of magnitude: 5626 of 11722 printed characters, 48 %.  It is
     inert for the whole walk and applied only at the block's exits, which is
     exactly the row a fold should take -- the rows AROUND it (the two
     open-inode bundles, the frame) are consumed one at a time and must stay
     spelled out.

     TRANSPARENT on purpose: the [iApply ("Hseamk" $! ...)] sites and the
     [iIntros] that discharges this goal in [wp_sys_unlink_sconf] unify
     straight through a transparent constant, so NOT ONE LINE of proof script
     changed.  [CIDs] is an explicit binder because the body writes
     [wp_next (CID0 := CIDs)], and its other rows resolve their [CpuId]
     instance to the innermost one. *)
  Definition su_w3_seam `{GEN : GenId} `{CIDs : CpuId} `{XI : CurCtx}
      (gf : gname) (jx : nat)
 (dqb : dfrac) (dqs : dfrac) (dqbs : dfrac)
      (pid : mword 32) (U : ustate) (P1 : uptd) (n1 : nat) (Sb1 : gset Z)
      (kd : nat) (ks : nat) (kk : nat) (gild : gname) (gisld : gname)
      (gyd : gname) (loyd tlyd : nat) (qdi : Qp) (sd : Qp) (dinum : mword 32) (dnd : dinode)
      (bmd : blkmap) (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf : nat -> bv 8) (bnm0 : nat -> bv 8) (bp : nat -> bv 8)
      (bd : nat -> bv 8) (w6 : mword 64) (w30 : mword 64) (m : regfile)
      (sp0 : mword 64) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (t : nat) (M3 : regfile) (s3x : mword 64) (bex : nat -> bv 8)
      (isdir : bool) (gili : gname) (gisli : gname) (gyi : gname) (si : Qp)
      (qsi : Qp) (loyi tlyi : nat) (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8)) : iProp Σ :=
    (⌜su_regs m sp0 (ientry kd) (ientry ks) s3x M3⌝ -∗
       ⌜bv_unsigned (di_nlink dni) <> 0⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dni bmi dati⌝ -∗
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
       fs_crash_seam fsc_cov fsc_logst -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
       (* ---- [dp], unchanged ---- *)
       is_sleeplock_genl gild gisld (i_lock (ientry kd)) "inode"%string
                        (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
       ⌜(loyd <= tlyd)%nat⌝ -∗
       IcacheRef.cred_floor loyd tlyd -∗
       IcacheInv.iref_claims -∗
       ic_handle fsc_ic kd (DepTx sd icfg_dev dinum gyd loyd t (1/4)) -∗
       off_rows off_cfg kd cur_ctx -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned dinum) dnd bmd datd -∗
       dinode_at fsc_ireg dinum dnd -∗
       inode_meta (ientry kd) dnd -∗
       inode_addrs (ientry kd) (bm_cells bmd) -∗
       ind_res fsc_fs bmd -∗
       inode_blocks fsc_fs bmd datd -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dinum)
                (era_node dnd bmd datd) -∗
       ity_shot gyd (di_type dnd) -∗
       (* the payload's freeze token (§3.9, RULING A-prime) *)
       ifreeze_off (bv_unsigned dinum) -∗
       inode_ref_short kd (qdi + sd)%Qp qdi icfg_dev dinum -∗
       (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
       runit_any (bv_unsigned dinum) -∗
       (* ---- [ip], LOCKED and OPEN ---- *)
       is_sleeplock_genl gili gisli (i_lock (ientry ks)) "inode"%string
                        (ic_slp fsc_ic ks) (slh_tok (icfg_isl ks)) -∗
       sleeplocked_q gisli si (i_lock (ientry ks)) pid -∗
       ⌜(loyi <= tlyi)%nat⌝ -∗
       IcacheRef.cred_floor loyi tlyi -∗
       IcacheInv.iref_claims -∗
       ic_handle fsc_ic ks (DepTx si icfg_dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi loyi
         t (1/4)) -∗
       off_rows off_cfg ks cur_ctx -∗
       i_dev (ientry ks) ↦₄{DfracOwn (1/2)} icfg_dev -∗
       i_inum (ientry ks) ↦₄{DfracOwn (1/2)}
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       i_valid (ientry ks) ↦₄ valid_word true -∗
       dlinks fsc_fs (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32)) dni bmi dati -∗
       dinode_at fsc_ireg
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni -∗
       inode_meta (ientry ks) dni -∗
       inode_addrs (ientry ks) (bm_cells bmi) -∗
       ind_res fsc_fs bmi -∗
       inode_blocks fsc_fs bmi dati -∗
       (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned (zero_extend' 32
           (dir_inum datd kk : mword 16) : mword 32))
                (era_node dni bmi dati) -∗
       ity_shot gyi (di_type dni) -∗
       (* the payload's freeze token (§3.9, RULING A-prime) *)
       ifreeze_off (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
       inode_ref_short ks (qsi + si)%Qp qsi icfg_dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
       runit_any
         (bv_unsigned
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
       log_opS icfg_log n1 Sb1 -∗
       (* the transaction token rides beside the budget: this walk ends the
          operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
       t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
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
         SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
           (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
           dqb dqs dqbs) -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma su_w3 `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (U : ustate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (kd ks kk : nat) (gild gisld gyd : gname) (qdi sd qs : Qp)
      (loyd tlyd : nat)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32)
      (nf bnm0 bp bd be : nat -> bv 8)
      (w5 w6 w30 : mword 64)
      (m M2 : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (t : nat) :
    (K_sys_unlink <= K)%nat ->
    (0 < icfg_nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    (jx < NPROC)%nat ->
    gs !! jx = Some gl ->
    eb = true ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    su_al sp0 ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P1 ->
    (* ---- the +0x72 seam's pure facts, verbatim ---- *)
    su_regs m sp0 (ientry kd) (ientry ks)
            (m !!! Regidx Rs3 : mword 64) M2 ->
    (kd < NINODE)%nat ->
    (ks < NINODE)%nat ->
    bv_unsigned dinum < 16 * Z.of_nat icfg_nib ->
    di_type dnd = SpecDirlookup.T_DIR ->
    inode_ok fsc_cov fsc_logst dnd bmd datd ->
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
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    bslots 3 -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    kalloc_env fsc_kalloc None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
    (* ---- [dp], LOCKED and OPEN (the +0x72 seam's bundle) ---- *)
    is_sleeplock_genl gild gisld (i_lock (ientry kd)) "inode"%string
                     (ic_slp fsc_ic kd) (slh_tok (icfg_isl kd)) -∗
    sleeplocked_q gisld sd (i_lock (ientry kd)) pid -∗
    ⌜(loyd <= tlyd)%nat⌝ -∗
    IcacheRef.cred_floor loyd tlyd -∗
    IcacheInv.iref_claims -∗
    ic_handle fsc_ic kd (DepTx sd icfg_dev dinum gyd loyd t (1/2)) -∗
    off_rows off_cfg kd cur_ctx -∗
    i_dev (ientry kd) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
    i_valid (ientry kd) ↦₄ valid_word true -∗
    dlinks fsc_fs (bv_unsigned dinum) dnd bmd datd -∗
    dinode_at fsc_ireg dinum dnd -∗
    inode_meta (ientry kd) dnd -∗
    inode_addrs (ientry kd) (bm_cells bmd) -∗
    ind_res fsc_fs bmd -∗
    inode_blocks fsc_fs bmd datd -∗
    (* ...and the era's abstract value (durable-disk 2b-inode-3) *)
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
    ity_shot gyd (di_type dnd) -∗
    (* the payload's freeze token (§3.9, RULING A-prime) *)
    ifreeze_off (bv_unsigned dinum) -∗
    inode_ref_short kd (qdi + sd)%Qp qdi icfg_dev dinum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned dinum) -∗
    (* ---- [ip], REFERENCED (dirlookup's iget) ---- *)
    inode_ref ks qs icfg_dev
      (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
    (* ...with the unit that iget minted with it (item 7a-wire) *)
    runit_any
      (bv_unsigned
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)) -∗
    log_opS icfg_log n1 Sb1 -∗
    (* the transaction token rides beside the budget: this walk ends the
       operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
    t ↪[ln_tx icfg_log]{#(1/2)} tt -∗
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
       payload at [true] is T_DIR + [dir_dots_only] + the raw dead-scan;
       at [false] it is the type disequality W5-FILE's [dlinks_not_dir]
       route reads. ---- *)
    (∀ (CIDs : CpuId) (M3 : regfile) (s3x : mword 64) (bex : nat -> bv 8)
       (isdir : bool) (gili gisli gyi : gname) (si qsi : Qp) (loyi tlyi : nat)
       (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8)),
       su_w3_seam (CIDs := CIDs)
          gf jx dqb dqs
          dqbs pid U P1 n1 Sb1 kd ks kk gild gisld gyd loyd tlyd qdi sd dinum dnd bmd
          datd lo nf bnm0 bp bd w6 w30 m sp0 K eb b lks t M3 s3x bex isdir
          gili gisli gyi si qsi loyi tlyi dni bmi dati) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hn1 Hupt1 Hregs Hkd Hks Hdinb
           Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq Hnotdot Hnotdd Hfst
           Hma0 Hal27.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hkd #Hpe Hpc #Hbio #Hlog Hseam Hgen #Hdev #Hgeo
             #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen Hsbb Hsbi Hsbs
             #Hbmres #Hkenv #Hprocs Hpriv #Hslkd Hslkdq %Hleyd #Hflyd #Hclaimsyd Hdepd Hoffrd Hidevd
             Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd
             Htop #Hshotd Hfrz Hkeepd Hrud Hchild Hrui HopS Htx
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
                       (dir_nrec (bv_unsigned (di_size dnd))) icfg_nib)
      by (exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat icfg_nib).
    { rewrite su_zext32_unsigned. exact (Hinums kk Hkklt Hkklive). }
    destruct (Hiregb _ Hinb) as [Hiblki Hiblogi].
    (* the process block, opened for the callees' pid fraction, and THE
       CLOSER, built once (W2's shape) *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    iAssert (proc_priv_bare (proc_addr jx) pid (us_upt U P1) -∗
             proc_priv gf (proc_addr jx) pid (us_upt U P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)).
      rewrite proc_priv_nocwd_bare.
      iSplitR "Href"; [| iExact "Href"].
      iSplitL "Hpidq"; [iExact "Hpidq" | iExact "Hofiles"]. }
    (* ip's reference: generation NAMED (the share ilock consumes and the
       one-shot it returns must agree), then shed *)
    iEval (rewrite inode_ref_gen_intro) in "Hchild".
    iDestruct "Hchild" as (gyi loyi tlyi) "(%Hleyi & #Hflyi & Hchild)".
    iEval (rewrite IcacheRef.inode_ref_genlo_shed) in "Hchild".
    iDestruct "Hchild" as "[Hkeepi Hshri]".
    iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hleyi
                 with "Hflyi Hkeepi") as "Hkeepi".
    iDestruct (su_esc_acc kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (su_esc_acc ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (su_slk_acc ks Hks with "Hslks") as (gili gisli) "#Hslki".
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
    (* BOTH INODES ARE WRITE-LOCKED NOW (durable-disk B''-tx2), and the
       child's arm is taken AT ITS CHECKOUT (B''-tx3): the parent's arm
       SHRINKS to a quarter first and what comes back is what [ilock] parks,
       so the residue the walk keeps is a half and no bundleless arm ever
       stands. *)
    iApply fupd_wp.
    iMod (ic_shrink_tx ⊤ fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kd sd icfg_dev dinum gyd loyd true
            t (1/2) (1/4) (1/4) (eq_sym Qp.quarter_quarter)
            ltac:(solve_ndisj) with "Hescd Hivalidd Hdepd")
      as "(Hivalidd & Hdepd & Htp)".
    iModIntro.
    iPoseProof (TsoGhost.llb_0 loglen_name) as "#Hllb0b".   (* r25 lane (ii): nothing to present at this ilock *)
    iApply (Ilock.wp_ilock_dep_sconf (CID := CID2) gs jx gl pd pav pu
              gili gisli ks (qs/2)%Qp
              gyi loyi tlyi (DepTx (qs/2)%Qp icfg_dev
                     (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                     gyi loyi t (1/4)) PlainK
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              pid (DfracOwn (1/4)) dqs R0 (K - 30)%nat eb b lks
              (us_upt U P1) ltac:(exact Kil) eq_refl ltac:(discriminate)
              Hks Hgeom Hist0 Hiblki Hinb Hj Hgl HR0a0
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hkd Hpc Hpe Hbio Hitinv Hesci Hireg
                    Hslki [//] Hflyi Hclaimsyd Hshri [Htp] Hrui Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1 Hllb0b").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /ic_dep_side. iExact "Htp". }
    iIntros (CID3 Hq3 mil dni bmi fldi)
      "%Hcsil _ Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkiq Hdepi Hoffri
       Hidevi Hiinumi Hivalidi Hloadi #Hshoti Hfrzi %Hfldi Hrui %Hilkpi".
    iEval (rewrite /ic_dep_held /=) in "Hloadi".
    assert (Hpc78 : ret_pc (R0 !!! Regidx Rra : mword 64)
                    = mword_of_int (SU + 0x78)) by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc78) in "Hpc".
    assert (Hilregs : su_regs m sp0 (ientry kd) (ientry ks)
                        (m !!! Regidx Rs3 : mword 64) mil)
      by exact (su_regs_cs m sp0 _ _ _ R0 mil Hcsil HR0regs).
    (* [ip]'s loaded bundle, opened: the +0x8a seam wants it in pieces and
       the [lh]s below read two of its meta cells *)
    iDestruct (ic_loaded_open with "Hloadi") as (dati)"(%Hioki & %Hrl_dati & %Hdoki & %Hddixi & %Hdoci & %Hduqi & Hdlnki & Hdiati & Hmetai & Haddrsi & Hindi & Hblocksi & Htopi)".
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
      iApply bi.later_intro. iIntros (CID5 Hq5) "Hcg Hpc".
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
      iIntros (CID8 Hq8). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgf8) in "Hpc".
      iDestruct (cpu_own_transport CID3 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      (* the loop's opaque [X]: dp's bundle, the ledger, the frame and BOTH
         continuations, combined so [su_w4]'s exits can hand them back *)
      iCombine "Hseam Hgen Hbs2 Hsbb Hsbi Hsbs Hpre Hslkdq
                Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad Haddrsd
                Hindd Hblocksd Htop Hfrz Hkeepd Hrud Hslkiq Hdepi Hoffri Hiinumi
                Hivalidi
                Hdlnki Hdiati Htopi Hfrzi Hkeepi Hrui HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14
                Hnm2 HbP H27lo H27hi H30 Hseamk Hcont" as "HX".
      (* the byte view's row (durable-disk 1c-flip step 3) *)
      iPoseProof (ireg_inv_bytes with "Hireg") as "#Hrow".
      iApply (su_w4 (CID0 := CID8) gs jx gl pd pav pu gf
 ks
                (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                dni bmi dati pid (DfracOwn (1/4)) be
                (ientry kd) (ientry ks) (m !!! Regidx Rs3 : mword 64)
                m M5 sp0 K eb b lks _
                (us_upt U P1) Kre Hgeom Hj Hgl Heb Hlkempty Hsp0 Hal eq_refl
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
                            & Hpre & Hslkdq & Hdepd & Hoffrd & Hidevd &
                            Hiinumd & Hivalidd & Hdlnkd & Hdiatd & Hmetad &
                            Haddrsd & Hindd & Hblocksd & Htop & Hfrz & Hkeepd & Hrud &
                            Hslkiq &
                             Hdepi & Hoffri & Hiinumi & Hivalidi & Hdlnki &
                            Hdiati & Htopi & Hfrzi & Hkeepi & Hrui & HopS & Htx & Hf1 & Hf2 & Hf3 & Hf4 &
                            Hf5 & Hf6 & HbD & Hnm14 & Hnm2 & HbP & H27lo &
                            H27hi & H30 & Hseamk & Hcont)".
        iDestruct "Hmapi" as "[Haddrsi Hindi]".
        (* both bundles repacked: neither release below opens them *)
        iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum dnd bmd)
          with "[Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop]" as "Hloadd".
        { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists datd.
          iFrame "Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop".
          iPureIntro. split_and!;[exact Hiok | exact Hrl_datd | exact Hdok | exact Hddix | exact Hdoc | exact Hduq]. }
        iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst ks
                   (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                   dni bmi)
          with "[Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi]" as "Hloadi".
        { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
          iExists dati.
          iFrame "Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi".
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
        iDestruct (log_tx_split icfg_log t (1/2) (1/4) (1/4)
                     (eq_sym Qp.quarter_quarter) with "Htx") as "[Htxd Htxi]".
        iAssert (ic_tx_dep_at fsc_ic kd sd icfg_dev dinum gyd loyd t (1/4))
          with "[Hdepd Htxd]" as "Hdepd";
          [rewrite /ic_tx_dep_at; iFrame "Hdepd Htxd" |].
        iAssert (ic_tx_dep_at fsc_ic ks (qs/2)%Qp icfg_dev
                   (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                   gyi loyi t (1/4))
          with "[Hdepi Htxi]" as "Hdepi";
          [rewrite /ic_tx_dep_at; iFrame "Hdepi Htxi" |].
        iApply (Tails.su_tail_e (CID0 := CIDx) gs jx gl pd pav pu
 gild gisld gili gisli
 kd qdi sd gyd loyd tlyd dinum dnd bmd
                  ks (qs/2)%Qp (qs/2)%Qp gyi loyi tlyi
                  (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                  dni bmi n1 pid (DfracOwn (1/4)) dqb dqs m Mx sp0 K eb b lks
                  w6
                  (word_of_words lo (mword_of_int (Z.of_nat (16 * kk))
                                     : mword 32))
                  w30 bd bnf bp bex
                  (us_upt U P1) t Kiup Keo K30 Kpop Hkd Hks Hgeom Hsize Hbm0 Hbmcov Hbmlog
                  Hist0 Hdiblk Hdiblog Hdinb Hiblki Hiblogi Hinb Hcovb Hiu2
                  Hj Hgl Hlkempty Hsp0 HMxsp HMxthr HMxs1 HMxs2 Hal
                  with "Hcg Hown [] [] Htext Hkd Hpc Hpe Hbio Hlog Hseam Hgen
                        Hitab Hitinv Hescd Hesci Hireg Hropen Hslkd Hslkdq
                        [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hloadd Hshotd Hfrz
                        Hkeepd Hrud
                        Hslki Hslkiq [//] Hflyi Hclaimsyd Hdepi Hoffri Hidevi Hiinumi Hivalidi
                        Hloadi Hshoti Hfrzi Hkeepi Hrui Hsbb Hsbi Hbmres Hpidq Hprocs
                        Hdev Hgeo Hdlk [Hbslot Hbs2] [HopS] Hf1 Hf2 Hf3 Hf4
                        Hf5 Hf6 HbD HbNj HbP H27 Hbuf H30
                        [Hcont Hpre Hsbs]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply su_bs3. iFrame "Hbslot Hbs2". }
        { iApply (log_opS_opb with "HopS"). }
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
                            & Hpre & Hslkdq & Hdepd & Hoffrd & Hidevd &
                            Hiinumd & Hivalidd & Hdlnkd & Hdiatd & Hmetad &
                            Haddrsd & Hindd & Hblocksd & Htop & Hfrz & Hkeepd & Hrud &
                            Hslkiq &
                             Hdepi & Hoffri & Hiinumi & Hivalidi & Hdlnki &
                            Hdiati & Htopi & Hfrzi & Hkeepi & Hrui & HopS & Htx & Hf1 & Hf2 & Hf3 & Hf4 &
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
                  (qs/2)%Qp loyi tlyi dni bmi dati
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hown Hpc Hseam Hgen
                        [Hbslot Hbs2] Hsbb Hsbi Hsbs Hpriv Hslkd
                        Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
                        Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud
                        Hslki Hslkiq [//] Hflyi Hclaimsyd Hdepi Hoffri Hidevi Hiinumi Hivalidi
                        Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi Hshoti
                        Hfrzi Hkeepi Hrui HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2
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
                gili gisli gyi (qs/2)%Qp (qs/2)%Qp loyi tlyi dni bmi dati
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hown Hpc Hseam Hgen
                      [Hbs1 Hbs2] Hsbb Hsbi Hsbs Hpriv Hslkd Hslkdq [//] Hflyd Hclaimsyd
                      Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd
                      Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud Hslki
                      Hslkiq [//] Hflyi Hclaimsyd Hdepi Hoffri Hidevi Hiinumi Hivalidi Hdlnki
                      Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
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

End ProofSysUnlinkW3.

End SysUnlinkW3.
