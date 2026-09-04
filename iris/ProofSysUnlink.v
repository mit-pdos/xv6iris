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
Require Import SpecPrintk.
Require Import WpUart.
Require Import ByteBuf.
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
          [] [] 1%positive (mword_of_int 0) [].

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
(*  ProofSysUnlink.v -- the seal. *)
(*                                                                      *)
(*  Split out of ProofSysUnlink.v FOR THE BUILD DAG: the five block      *)
(*  lemmas are mutually independent (each seam is the NEXT block's        *)
(*  premise list, so the seal composes them and nothing else does), and   *)
(*  [Tails.] is named only inside proofs, never in a statement -- so each *)
(*  file makes its own [Tails] and the vocabulary they share             *)
(*  (ProofSysUnlinkShared.v) needs no functor argument at all.            *)
(* ==================================================================== *)

Require Import ProofSysUnlinkShared.
Require Import ProofSysUnlinkW1 ProofSysUnlinkW2 ProofSysUnlinkW3.
Require Import ProofSysUnlinkW5File ProofSysUnlinkW5Dir.

Module SysUnlinkProof (Argstr : ARGSTR) (BeginOp : BEGIN_OP)
                      (Nameiparent : NAMEIPARENT) (Ilock : ILOCK)
                      (Namecmp : NAMECMP) (Dirlookup : DIRLOOKUP)
                      (Memset : MEMSET) (Readi : READI) (Writei : WRITEI)
                      (Iupdate : IUPDATE) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP) (PN : PANIC) : SYSUNLINK.

  Module MW1 := SysUnlinkW1 Iunlockput EndOp PN Argstr BeginOp Nameiparent.
  Module MW2 := SysUnlinkW2 Iunlockput EndOp PN Ilock Namecmp Dirlookup.
  Module MW3 := SysUnlinkW3 Iunlockput EndOp PN Ilock Readi.
  Module MWF := SysUnlinkW5File Iunlockput EndOp PN Memset Writei Iupdate.
  Module MWD := SysUnlinkW5Dir Iunlockput EndOp PN Memset Writei Iupdate.
  Import MW1. Import MW2. Import MW3. Import MWF. Import MWD.

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
  Lemma wp_sys_unlink_sconf `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac) (v0 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    SpecSysUnlink.wp_sys_unlink_sconf_body gf gs jx gl pd pav
      pu
      dqb dqs dqbs v0 pid U m K eb b lks.
  Proof.
    cbv beta zeta delta [SpecSysUnlink.wp_sys_unlink_sconf_body].
    intros HK HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hnib16 Hprk Hj Hgl Heb Harg0.
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hprenv #Hbio #Hlog
             Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows
             #Hslks #Hireg #Hropen Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv
             Hcont".
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpenv".
    (* ---- W1, +0x00..+0x2e: the prologue, argstr, begin_op, nameiparent ---- *)
    iApply (su_w1 gf gs jx gl pd pav pu
 dqb dqs dqbs
              v0 pid U m K eb b lks HK HdevR Hnib0
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb
              Harg0
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv [] Hcont").
    iIntros (CIDa Ms P1 n1 Sb1 w1 dpv nf bp bnm0 bd be w4 w5 w6 w27 w30).
    iIntros "%Hal %Hregs1 %Hma01 %Hupt1 %Hn1 %Hw1 %Hdpvnz
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv Hir
             Hheld HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE
             H30 Hcont".
    (* ---- W2, +0x30..+0x6e: ilock(dp), the two namecmp refusals,
       dirlookup ---- *)
    iApply (su_w2 gf gs jx gl pd pav pu
 dqb dqs dqbs
              pid U P1 n1 Sb1 w1 dpv nf bnm0 bp bd be w4 w5 w6 w27 w30
              m Ms (m !!! Regidx csp_rs1 : mword 64) K eb b lks
              HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hregs1 Hma01 Hn1
              Hupt1
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv Hheld HopS Htx
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE H30
                    [] Hcont").
    iIntros (CIDb M2 kd ks kk gild gisld gyd loyd tlyd qdi sd qs dinum dnd bmd datd lo t).
    iIntros "%Hregs2 %Hkd %Hks %Hdinb %Htydir %Hiok %Hrl_datd %Hdok %Hddix
             %Hdoc %Hduq
             %Hnotdot %Hnotdd %Hfst %Hma02 %Hal27
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             Hslkd Hslkdq %Hleyd #Hflyd #Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS Htx
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W3, +0x72..+0x88: ilock(ip), the nlink panic, the T_DIR test
       (and, on the taken arm, the whole isdirempty loop through W4) ---- *)
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpetop".
    iApply (su_w3 gf gs jx gl pd pav pu
 dqb dqs dqbs
              pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd qdi sd qs loyd tlyd
              dinum dnd bmd datd lo nf bnm0 bp bd be w5 w6 w30
              m M2 (m !!! Regidx csp_rs1 : mword 64) K eb b lks t
              HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1 Hupt1 Hregs2
              Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
              Hnotdot Hnotdd
              Hfst Hma02 Hal27
              with "Hcg Hown Htext Hdata Hpetop Hpc Hbio Hlog Hseam Hgen Hdev Hgeo
                    Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen Hsbb Hsbi
                    Hsbs Hbmres Hkenv Hprocs Hpriv Hslkd Hslkdq
                    [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad
                    Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS Htx
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                    HbE H30 [] Hcont").
    iIntros (CIDc M3 s3x bex isdir gili gisli gyi si qsi loyi tlyi dni bmi dati).
    iIntros "%Hregs3 %Hnlzi %Hioki %Hrl_dati %Hdoki %Hddixi %Hdoci %Hduqi
             %Hisd
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             Hslkd Hslkdq %Hleyd5 #Hflyd5 #Hclaimsyd5 Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud
             Hslki Hslkiq %Hleyi #Hflyi #Hclaimsyi Hdepi Hoffri Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W5, +0x8a..: the zeroing and the two tails, split on the seam's
       own index.  The FILE arm is [su_w5_file]; the T_DIR arm is
       [su_w5_dir], which since V5' increment W derives (D1) and (D2)
       internally and takes neither as a premise. ---- *)
    destruct isdir.
    - destruct Hisd as (Htyzi & Hdots & Hdead).
      iApply (su_w5_dir gf gs jx gl pd pav pu

                dqb dqs dqbs pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs loyd tlyd dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi loyi tlyi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks t
                HK Hprk Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Htyzi Hdots Hdead
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffri Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
    - iApply (su_w5_file gf gs jx gl pd pav pu

                dqb dqs dqbs pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs loyd tlyd dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi loyi tlyi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks t
                HK Hprk Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Hisd
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffri Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
  Qed.

End ProofSysUnlinkBody.

End SysUnlinkProof.
