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
(*  ProofSysUnlinkW2.v -- sys_unlink's W2 block. *)
(*                                                                      *)
(*  Split out of ProofSysUnlink.v FOR THE BUILD DAG: the five block      *)
(*  lemmas are mutually independent (each seam is the NEXT block's        *)
(*  premise list, so the seal composes them and nothing else does), and   *)
(*  [Tails.] is named only inside proofs, never in a statement -- so each *)
(*  file makes its own [Tails] and the vocabulary they share             *)
(*  (ProofSysUnlinkShared.v) needs no functor argument at all.            *)
(* ==================================================================== *)

Require Import ProofSysUnlinkShared.

Module SysUnlinkW2 (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) (PN : PANIC) (Ilock : ILOCK) (Namecmp : NAMECMP) (Dirlookup : DIRLOOKUP).

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkW2.
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
  Lemma su_w2_bad `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gil gisl : gname)
      (kk : nat) (qi s : Qp) (gy : gname) (loy tly : nat) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (u : nat) (pidv : mword 32) (dqb dqs dqbs : dfrac)
      (U : ustate) (P1 : uptd)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string)
      (w4 w5 w6 w27 w30 : mword 64) (bd nfx bnm0 bp be : nat -> bv 8) :
    (K_iunlockput <= K - 30)%nat -> (K_end_op <= K - 30)%nat ->
    (30 <= K)%nat -> ((K - 30) + 30 = K)%nat ->
    (kk < NINODE)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    IBLOCK inum icfg_ist ∈ fsc_cov ->
    ~ (IBLOCK inum icfg_ist ∈ log_region_set fsc_logst) ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    cov_below fsc_cov fsc_size ->
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
    uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P1 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (SU + 0x15a)) -∗
    panic_env -∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
    fs_crash_seam fsc_cov fsc_logst -∗
    gen_cert -∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
    itable_inv -∗
    ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst kk -∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    is_sleeplock_genl gil gisl (i_lock (ientry kk)) "inode"%string
                     (ic_slp fsc_ic kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s (i_lock (ientry kk)) pidv -∗
    ⌜(loy <= tly)%nat⌝ -∗
    IcacheRef.cred_floor loy tly -∗
    IcacheInv.iref_claims -∗
    ic_tx_dep fsc_ic kk s icfg_dev inum gy loy -∗
    off_rows off_cfg kk cur_ctx -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    (* the payload's freeze token (§3.9, RULING A-prime), relayed to
       [su_tail_bad]'s iunlockput *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short kk (qi + s)%Qp qi icfg_dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    proc_priv_bare (proc_addr jx) pidv (us_upt U P1) -∗
    (proc_priv_bare (proc_addr jx) pidv (us_upt U P1) -∗
       proc_priv gf (proc_addr jx) pidv (us_upt U P1)) -∗
    procs_inv gs -∗
    dev_inv fsc_uart fsc_disk -∗
    disk_geom fsc_disk pd pav pu -∗
    is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
    bslots 3 -∗
    iref_slots 1 -∗
    log_opb icfg_log u -∗
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
      SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pidv U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 HMs2
           HMs3 Hal Heb Hupt1.
    iIntros "Hcg Hown #Htext #Hkd Hpc #Hpenv #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
             #Hesck #Hireg #Hropen #Hslkk Hslkd %Hley #Hfly #Hclaimsy Hdep Hoffr Hidev Hiinum Hivalid Hload
             #Hshot Hfrz Hkeep Hru Hsbb Hsbi Hsbs #Hbmres Hpidq Hpre #Hprocs #Hdev
             #Hgeo
             #Hdlk Hbsl Hir Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27
             HbE H30 Hcont".
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nfx with "Hnm14 Hnm2") as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iApply (Tails.su_tail_bad (CID0 := CID0) gs jx gl pd pav pu
              gil gisl
 kk qi s gy loy tly inum dn bm u pidv (DfracOwn (1/4)) dqb dqs
              m M sp0 K eb b lks w4 w5 w6 w27 w30 bd bnf bp be
              (us_upt U P1) HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs2 HMs3 Hal
              with "Hcg Hown [] [] Htext Hkd Hpc Hpenv Hbio Hlog Hseam Hgen Hitab
                    Hitinv Hesck Hireg Hropen Hslkk Hslkd [//] Hfly Hclaimsy Hdep Hoffr Hidev Hiinum
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
  (* W2'S SEAM, NAMED -- the same fold as [su_w3_seam] below, whose header
     carries the measurement (W3's seam was 48 % of [Delta] at a mid-walk
     dump).  Spelled inline this one was 96 lines.

     TRANSPARENT on purpose: the [iApply ("Hseamk" $! ...)] sites and the
     [iIntros] that discharges this goal in [wp_sys_unlink_sconf] unify
     straight through a transparent constant, so NOT ONE LINE of proof script
     changed.  [CIDs] is an explicit binder because the body writes
     [wp_next (CID0 := CIDs)], and its other rows resolve their [CpuId]
     instance to the innermost one. *)
  Definition su_w2_seam `{GEN : GenId} `{CIDs : CpuId} `{XI : CurCtx}
      (gf : gname) (jx : nat)
 (dqb : dfrac) (dqs : dfrac)
      (dqbs : dfrac) (pid : mword 32) (U : ustate) (P1 : uptd) (n1 : nat)
      (Sb1 : gset Z) (nf : nat -> bv 8) (bnm0 : nat -> bv 8)
      (bp : nat -> bv 8) (bd : nat -> bv 8) (be : nat -> bv 8)
      (w5 : mword 64) (w6 : mword 64) (w30 : mword 64) (m : regfile)
      (sp0 : mword 64) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (M2 : regfile) (kd : nat) (ks : nat) (kk : nat) (gild : gname)
      (gisld : gname) (gyd : gname) (loyd tlyd : nat) (qdi : Qp) (sd : Qp) (qs : Qp)
      (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
      (datd : nat -> list (bv 8)) (lo : bv 32) (t : nat) : iProp Σ :=
    (⌜su_regs m sp0 (ientry kd) (ientry ks)
                (m !!! Regidx Rs3 : mword 64) M2⌝ -∗
       ⌜(kd < NINODE)%nat⌝ -∗
       ⌜(ks < NINODE)%nat⌝ -∗
       ⌜bv_unsigned dinum < 16 * Z.of_nat icfg_nib⌝ -∗
       ⌜di_type dnd = SpecDirlookup.T_DIR⌝ -∗
       ⌜inode_ok fsc_cov fsc_logst dnd bmd datd⌝ -∗
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
       fs_crash_seam fsc_cov fsc_logst -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
       (* ---- [dp], LOCKED and OPEN ---- *)
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
       top_frag (fs_gamma_L fsc_fs) (bv_unsigned dinum)
                (era_node dnd bmd datd) -∗
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
         SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
           (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
           dqb dqs dqbs) -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma su_w2 `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (pid : mword 32) (U : ustate) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (dpv : mword 64)
      (nf bnm0 bp bd be : nat -> bv 8)
      (w4 w5 w6 w27 w30 : mword 64)
      (m M : regfile) (sp0 : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) :
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
    su_regs m sp0 dpv (m !!! Regidx Rs2 : mword 64)
            (m !!! Regidx Rs3 : mword 64) M ->
    (M !!! Regidx Ra0 : mword 64) = dpv ->
    (su_u1 w1 <= n1)%nat ->
    uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P1 ->
    sie_cap_gpr KT1 M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (SU + 0x30)) -∗
    panic_env -∗
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
    iref_slots 1 -∗
    proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
    inode_held_ty dpv T_DIR -∗
    log_opS icfg_log n1 Sb1 -∗
    (* the transaction token rides beside the budget: this walk ends the
       operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
    log_tx icfg_log -∗
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
       (kd ks kk : nat) (gild gisld gyd : gname) (loyd tlyd : nat) (qdi sd qs : Qp)
       (dinum : mword 32) (dnd : dinode) (bmd : blkmap)
       (datd : nat -> list (bv 8)) (lo : bv 32) (t : nat),
       su_w2_seam (CIDs := CIDs)
          gf jx dqb
          dqs dqbs pid U P1 n1 Sb1 nf bnm0 bp bd be w5 w6 w30 m sp0 K eb b
          lks M2 kd ks kk gild gisld gyd loyd tlyd qdi sd qs dinum dnd bmd datd lo t) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
           Hcovb Hiregb Hj Hgl Heb Hsp0 Hal Hregs Hma0 Hn1 Hupt1.
    destruct (su_kb K HK) as (Knp & Kdl & Kre & Kwr & Kar & Kbo & Keo & Kil
                              & Kiupd & Kiup & Knc & K2 & K10 & K30 & Kpop).
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpenv2 #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg #Hropen
             Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv Hheld HopS Htx
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
    iDestruct "Hheld" as (kd qd dinum gyd lod tld)
      "(%Hdpe & %Hkd & %Hdinumc & %Hled & #Hfld &
        Hrefdp & #Hshotd & Hrud)".
    assert (Hdinb : bv_unsigned dinum < 16 * Z.of_nat icfg_nib)
      by (exact Hdinumc).
    destruct (Hiregb dinum Hdinb) as [Hdiblk Hdiblog].
    iEval (rewrite IcacheRef.inode_ref_genlo_shed) in "Hrefdp".
    iDestruct "Hrefdp" as "[Hkeepd Hshrd]".
    iDestruct (inode_ref_short_gen_forget _ _ _ _ _ _ _ _ Hled
                 with "Hfld Hkeepd") as "Hkeepd".
    iDestruct (su_esc_acc kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (su_slk_acc kd Hkd with "Hslks") as (gild gisld) "#Hslkd0".
    iDestruct (is_itable2_claims with "Hitab") as "#Hclaimssu".
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    (* the process block, opened for the callees' pid fraction *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)
                 with "Hpriv") as "[Hpnc Href]".
    iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
    iDestruct "Hpnc" as "[Hpidq Hofiles]".
    (* THE CLOSER, built once: every arm below hands the BLOCK back and wants
       [proc_priv] whole, and nothing between here and the seam touches the
       fd table or the cwd reference. *)
    iAssert (proc_priv_bare (proc_addr jx) pid (us_upt U P1) -∗
             proc_priv gf (proc_addr jx) pid (us_upt U P1))%I
      with "[Hofiles Href]" as "Hpre".
    { iIntros "Hpidq".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)).
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
    (* THE PARENT'S CHECKOUT IS ARMED (durable-disk B''-tx2), AT THE CHECKOUT
       ITSELF (B''-tx3): the half is handed to [ilock] as the descriptor's own
       parked share, so the escrow's OUT arm is a [DepTx] from the instant the
       entry leaves.  The transaction id is named from here on: sys_unlink's
       second lock has to park at the SAME transaction. *)

    iDestruct (log_tx_open with "Htx") as (t) "Htw".
    iDestruct (log_tx_split icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htw") as "[Htp Htx]".
    iPoseProof (TsoGhost.llb_0 loglen_name) as "#Hllb0".   (* r25 lane (ii): nothing to present at this ilock *)
    iApply (Ilock.wp_ilock_dep_sconf (CID := CID1) gs jx gl pd pav pu
              gild gisld kd (qd/2)%Qp
              gyd lod tld (DepTx (qd/2)%Qp icfg_dev dinum gyd lod t (1/2)) PlainK dinum
              pid (DfracOwn (1/4)) dqs R0 (K - 30)%nat eb b
              lks
              (us_upt U P1) ltac:(exact Kil) eq_refl ltac:(discriminate)
              Hkd Hgeom Hist0 Hdiblk Hdinb Hj Hgl HR0a0
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hitinv Hescd Hireg
                    Hslkd0 [//] Hfld Hclaimssu Hshrd [Htp] Hrud Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1 Hllb0").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { rewrite /ic_dep_side. iExact "Htp". }
    iIntros (CID2 Hq2 mil dnd bmd fld)
      "%Hcsil _ Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkdd Hdep Hoffr
       Hidev Hiinum Hivalid Hload #Hshotl Hfrz %Hfld Hrud %Hilkpd".
    iEval (rewrite /ic_dep_held /=) in "Hload".
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
      iDestruct (ic_tx_dep_intro with "Hdep Htx") as "Hdep".
      iApply (su_w2_bad (CID0 := CID8) gf gs jx gl pd pav pu
                gild gisld
 kd (qd/2)%Qp (qd/2)%Qp gyd lod tld dinum dnd bmd n1 pid
                dqb dqs dqbs U P1 m mn1 sp0 K eb b lks w4 w5 w6 w27 w30
                bd nf bnm0 bp be
                Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                (su_regs_sp _ _ _ _ _ _ Hn1regs) (su_regs_thr _ _ _ _ _ _ Hn1regs)
                ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn1regs); exact Hdpe)
                (su_regs_s2 _ _ _ _ _ _ Hn1regs)
                (su_regs_s3 _ _ _ _ _ _ Hn1regs) Hal Heb Hupt1
                with "Hcg Hown Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen Hitab
                      Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd [//] Hfld Hclaimssu Hdep Hoffr Hidev
                      Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb Hsbi Hsbs
                      Hbmres Hpidq Hpre Hprocs Hdev Hgeo Hdlk
                      [Hbs1 Hbs2] Hir [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD
                      Hnm14 Hnm2 HbP H27 HbE H30 Hcont").
      { iApply su_bs3. iFrame "Hbs1 Hbs2". }
      { iApply (log_opS_opb with "HopS"). }
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
        iDestruct (ic_tx_dep_intro with "Hdep Htx") as "Hdep".
        iApply (su_w2_bad (CID0 := CID14) gf gs jx gl pd pav pu
                  gild gisld
 kd (qd/2)%Qp (qd/2)%Qp gyd lod tld dinum dnd bmd
                  n1 pid dqb dqs dqbs U P1 m mn2 sp0 K eb b lks
                  w4 w5 w6 w27 w30 bd nf bnm0 bp be
                  Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                  Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                  (su_regs_sp _ _ _ _ _ _ Hn2regs)
                  (su_regs_thr _ _ _ _ _ _ Hn2regs)
                  ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn2regs); exact Hdpe)
                  (su_regs_s2 _ _ _ _ _ _ Hn2regs)
                  (su_regs_s3 _ _ _ _ _ _ Hn2regs) Hal Heb Hupt1
                  with "Hcg Hown Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen Hitab
                        Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd [//] Hfld Hclaimssu Hdep Hoffr Hidev
                        Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb Hsbi Hsbs
                        Hbmres Hpidq Hpre Hprocs Hdev Hgeo Hdlk
                        [Hbs1 Hbs2] Hir [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD
                        Hnm14 Hnm2 HbP H27 HbE H30 Hcont").
        { iApply su_bs3. iFrame "Hbs1 Hbs2". }
        { iApply (log_opS_opb with "HopS"). }
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
        iDestruct (ctx_word_pointsto_aligned_p with "H27") as %Hal27.
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
        iDestruct (ic_loaded_open with "Hload") as (datd)"(%Hiok & %Hrl_datd & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind & Hblocks & Htop)".
        pose proof Hiok as Hiok0.
        destruct Hiok as (Hbmwf & Hbmcv & Hbmc & Htynz & Hszcap & Hiokrest).
        assert (Hinums : dir_inums_ok datd
                           (dir_nrec (bv_unsigned (di_size dnd))) icfg_nib)
          by (exact (Hdok Htydz)).
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
        iApply (Dirlookup.wp_dirlookup_sconf (CID := CID19) gs jx gl
                  pd pav pu gf
                  (ientry kd) dinum bmd datd dnd dnd nf true (word_hi w27) pid
                  (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  R12 (K - 30)%nat eb b lks
                  (us_upt U P1) ltac:(exact Kdl) Htydir Hgeom Hbmwf Hbmcv Hszcap Hholesd Hinums
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

          iApply ("Hseamk" $! CID22 R13 kd kslot kk gild gisld gyd lod tld (qd/2)%Qp
                    (qd/2)%Qp qs dinum dnd bmd datd (word_lo w27) t
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    [%] [%]
                    Hcg Hown Hpc Hseam Hgen [Hbs1 Hbs2] Hsbb Hsbi Hsbs
                    Hpriv Hslkd0 Hslkdd [//] Hfld Hclaimssu Hdep Hoffr Hidev Hiinum Hivalid
                    Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Htop Hshotl Hfrz Hkeepd Hrud
                    Hchild Hruc HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP
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
          iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum dnd bmd)
            with "[Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Htop]"
            as "Hload".
          { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body.
            iExists datd. iFrame "Hdlnk Hdiat Hmeta
              Haddrs Hind Hblocks Htop". iPureIntro. split_and!;
              [ exact Hiok0 | exact Hrl_datd | exact Hdok | exact Hddix
              | exact Hdoc | exact Hduq ]. }
          iDestruct (cpu_own_transport CID20 CID22 0 eb (proc_addr jx) b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iDestruct (ic_tx_dep_intro with "Hdep Htx") as "Hdep".
          iApply (Tails.su_tail_d (CID0 := CID22) gs jx gl pd pav pu
 gild gisld
 kd (qd/2)%Qp (qd/2)%Qp gyd lod tld
                    dinum dnd bmd n1 pid (DfracOwn (1/4)) dqb dqs
                    m R13 sp0 K eb b lks w5 w6 (word_of_words (word_lo w27)
                    (word_hi w27)) w30 bd bnf bp be
                    (us_upt U P1) Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog
                    Hist0 Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty
                    Hsp0 HR13sp HR13thr HR13s1 HR13s3 Hal
                    with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen
                          Hitab Hitinv Hescd Hireg Hropen Hslkd0 Hslkdd [//] Hfld Hclaimssu Hdep Hoffr
                          Hidev Hiinum Hivalid Hload Hshotl Hfrz Hkeepd Hrud Hsbb
                          Hsbi
                          Hbmres Hpidq Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2]
                          [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                          HbE H30
                          [Hcont Hpre Hsbs Hislot]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iApply su_bs3. iFrame "Hbs1 Hbs2". }
          { iApply (log_opS_opb with "HopS"). }
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

End ProofSysUnlinkW2.

End SysUnlinkW2.
