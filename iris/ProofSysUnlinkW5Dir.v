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
(*  ProofSysUnlinkW5Dir.v -- sys_unlink's W5Dir block. *)
(*                                                                      *)
(*  Split out of ProofSysUnlink.v FOR THE BUILD DAG: the five block      *)
(*  lemmas are mutually independent (each seam is the NEXT block's        *)
(*  premise list, so the seal composes them and nothing else does), and   *)
(*  [Tails.] is named only inside proofs, never in a statement -- so each *)
(*  file makes its own [Tails] and the vocabulary they share             *)
(*  (ProofSysUnlinkShared.v) needs no functor argument at all.            *)
(* ==================================================================== *)

Require Import ProofSysUnlinkShared.

Module SysUnlinkW5Dir (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) (PN : PANIC) (Memset : MEMSET) (Writei : WRITEI) (Iupdate : IUPDATE).

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkW5Dir.
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
  (*  W5-DIR: the same span at the seam's [isdir = true] -- the shared    *)
  (*  zeroing, the +0xb4 test TAKEN into the +0x146 tail (dp->nlink--,   *)
  (*  iupdate(dp) CREDITED, spending the child's [".."] fragment out of   *)
  (*  its own [ent_toks]), the rejoin at +0xb8, and [ip]'s orphan re-park *)
  (*  ([FsStateEra.ent_toks_era_orphan] + the blez).  TAKES TWO NAMED     *)
  (*  PREMISES the                                                       *)
  (*  model cannot yet supply -- see the statement's banner and           *)
  (*  fs-sysfile.md S7-unlink W5.  The seal is STOPPED on them.           *)
  (* ================================================================== *)
  Lemma su_w5_dir `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
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
      (nf bnm0 bp bd bex : nat -> bv 8)
      (w6 w30 : mword 64)
      (gili gisli gyi : gname) (si qsi : Qp) (loyi tlyi : nat)
      (dni : dinode) (bmi : blkmap) (dati : nat -> list (bv 8))
      (m M3 : regfile) (sp0 s3x : mword 64) (K : nat) (eb b : bool)
      (lks : gset string) (t : nat) :
    (K_sys_unlink <= K)%nat ->
    printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
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
    is_aligned_paddr (Physaddr (pa_stk sp0 27)) 8 = true ->
    (* ---- the +0x8a seam's pure facts, at the T_DIR payload ---- *)
    su_regs m sp0 (ientry kd) (ientry ks) s3x M3 ->
    bv_unsigned (di_nlink dni) <> 0 ->
    inode_ok fsc_cov fsc_logst dni bmi dati ->
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
              child's [".."] names the parent.  Derived at the zeroing off
              the TYPE REGISTER: the parent's name record for the child
              carries [TDir dp] and the child's own ["."] fragment carries
              [TDir p], and [IregLinkNz.ireg_toks_agree] against the
              child's authority collapses the two, so [p = dp] and the
              child's [".."] is a fragment of [dp]'s register.  One region
              open, no tree fragment.
         (D2) [2 <= bv_unsigned (di_nlink dnd)] -- a directory holding a
              live subdirectory entry has at least two links.  Read off the
              PARENT's own per-directory exactness
              ([FsStateInode.node_exact]) once (D1) has shown the removed
              name is MARKED, i.e. in the parent's marker set: the count is
              the marker set's size plus one.  That is why the two readings
              run in this order, and both are before the zeroing.
       ==== *)
    sie_cap_gpr KT1 M3 (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗
    kernel_data -∗
    printk_env fsc_printk fsc_uart fsc_disk -∗
    pc_is (mword_of_int (SU + 0x8a)) -∗
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
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
    ireg_open -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    kalloc_env fsc_kalloc None -∗
    procs_inv gs -∗
    proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
    (* ---- [dp], LOCKED and OPEN ---- *)
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
    top_frag (fs_gamma_L fsc_fs) (bv_unsigned dinum) (era_node dnd bmd datd) -∗
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
    ic_handle fsc_ic ks (DepTx si icfg_dev (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) gyi loyi t (1/4)) -∗
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
        (dir_inum datd kk : mword 16) : mword 32)) (era_node dni bmi dati) -∗
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
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hprk Hnib0 Hgeom Hsize Hbm0 Hbmcov
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
             #Hslkd Hslkdq %Hleyd #Hflyd #Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop #Hshotd Hfrz Hkeepd Hrud
             #Hslki Hslkiq %Hleyi #Hflyi #Hclaimsyi Hdepi Hoffri Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi #Hshoti Hfrzi Hkeepi Hrui HopS Htx
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
                       (dir_nrec (bv_unsigned (di_size dnd))) icfg_nib)
      by (exact (Hdok Htydz)).
    assert (Hkklt : (kk < dir_nrec (bv_unsigned (di_size dnd)))%nat)
      by exact (dir_first_lt _ _ _ _ Hfst).
    assert (Hkklive : dir_live datd kk)
      by exact (dir_first_live _ _ _ _ Hfst).
    assert (Hkkname : bname 14 (dir_name datd kk) = bname 14 nf)
      by exact (dir_first_name _ _ _ _ Hfst).
    assert (Hinb : bv_unsigned (zero_extend' 32
                     (dir_inum datd kk : mword 16) : mword 32)
                   < 16 * Z.of_nat icfg_nib).
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
    (* A6.68: memset's contract is context-indexed AND so is the buffer
       ([↦ₘ] is the ctx tower), so the two shim crossings that used to
       bracket this call were IDENTITIES and are simply gone. *)
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
    assert (Hiok0 : inode_ok fsc_cov fsc_logst dnd bmd datd) by exact Hiok.
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
    assert (Hbmgeom : bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size)
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
    iApply (Writei.wp_writei_gen KT1 (CID := D12) gs jx gl pd pav pu
 gf
 (ientry kd) dinum bmd datd dnd dnd false
              (16 * kk)%nat 16%nat (fun _ => NUL) (upd_usM (us_upt U P1) _) n1 Sb1 pid
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
       %Hdisttot %Hdist0f %Hrng %Hwr %Hwru %Harm %Hspend %Hsbsub %Hpost16 %Hspendany
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
    destruct Harm as [(Ha0m & _ & Htot0 & _) | (Ha0w & _ & Htotle & HdnW & Hdn0W)].
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
    (* [wi16_post]'s guard is [0 < tot], and this arm has already
       substituted [tot := 16], so the goal is [0 < 16].  HOISTED OUT OF
       ARGUMENT POSITION and closed by a term: spliced as [ltac:(lia)] it
       reifies this proof's whole context -- the tree's largest -- to
       decide it, and measured 3.4 s at each of the two sites. *)
    assert (Htot16 : (0 < 16)%nat) by (apply Nat.lt_0_succ).
    destruct (Hpost16 Htot16 (su_wi_blocks kk))
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
    assert (Hiok' : inode_ok fsc_cov fsc_logst dnW bm' data').
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
      - rewrite (Hagree k Hne).
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
    (* the payload's links conjunct opens into the TYPE REGISTER's entry
       units, whose [".."] one is what pays for [dp->nlink--]
       (durable-disk 2b-inode-5). *)
    iDestruct (dlinks_open with "Hdlnki")
      as "(%Di & [%Hdoki0 %Hxacti] & Hetki)".
    (* FINDING 3, READ AT THE CHILD (durable-disk G5/G6).  [isdirempty] has
       just reported that its live records are its two dots, so nothing in
       it can be MARKED ([ent_dset_ok] admits neither dot name) and its
       EXACT count stands at ONE. *)
    assert (Hnl1 : bv_unsigned (di_nlink dni) = 1).
    { assert (HDi0 : Di = ∅)
        by exact (FsStateEra.ent_dset_ok_dots_only dni bmi dati Di
                    ltac:(destruct Hioki as (_ & _ & _ & _ & _ & Hc & _);
                          exact Hc)
                    ltac:(destruct Hioki as (_ & _ & _ & _ & Hc & _); exact Hc)
                    Hdots Hdoki0).
      pose proof (Hxacti ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                               apply bool_decide_eq_true; exact Htyzi)) as Hex.
      rewrite /fn_nlink era_node_rec
        (fn_orphan_era_nz dni bmi dati Hnlzi) HDi0 size_empty in Hex.
      pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dni))) as Hnn.
      clear -Hex Hnn Hnlzi. lia. }
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
       (D1) AND (D2) FALL HERE, IN THAT ORDER.  (D2) reads the parent's
       exactness at the MARKED name, and it is (D1) that shows the name is
       marked -- so (D1) comes first.

       Both readings are BEFORE the zeroing's ghost move, and each borrows
       its unit out of an [ent_toks] and hands it straight back.
       =================================================================== *)
    iDestruct (dlinks_open with "Hdlnkd")
      as "(%Dd & [%Hdokd %Hxactd] & Hetkd)".
    assert (Hkknotdot : dir_bname datd kk <> DOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdot.
      rewrite Hc DOT_dot_name. reflexivity. }
    assert (Hkknotdd : dir_bname datd kk <> DOTDOT).
    { rewrite /dir_bname Hkkname. intro Hc. apply Hnotdd.
      rewrite Hc DOTDOT_dotdot. reflexivity. }
    (* ===================================================================
       (D1) AND (D2) BOTH FALL OFF THE TYPE REGISTER (durable-disk G5).
       Two fragments at the child's inum are in hand, borrowed out of the
       two [ent_toks] this walk already holds and handed straight back:

         - [dp]'s own NAME record for [ip], whose value is [TDir dp] EXACTLY
           WHEN the name is MARKED in [dp]'s marker set, and [TFile]
           otherwise ([FsStateEra.ent_toks_era_borrow_at]);
         - [ip]'s own ["."] record, whose value PINS [ip]'s [".."] target
           ([FsStateInode.ent_ty_ok]'s dot arm).

       The region says the first fragment's value matches [ip]'s RECORD --
       and this arm's guard has [ip] a directory -- so the name IS marked.
       That is (D2) straight away: [dp]'s bundle carries the EXACT count
       [nlink dp = |D| + 1], and a nonempty [D] puts it at two.  And the
       RA's own agreement collapses the two fragments to one value, so the
       ["."] record's pin reads [dp] -- which is (D1).  Neither step opens
       the region twice, and neither reads a tree fragment. *)
    (* [dp]'s record for [ip] *)
    iDestruct (ent_toks_era_borrow_at (fs_gamma_L fsc_fs) (bv_unsigned dinum)
                 dnd bmd datd kk Dd Hdplive Htydz Hhzd Hszcap (Hduq Htydz)
                 Hkklt Hkklive Hkknotdot Hkknotdd Hnotself
                 with "Hetkd") as "[(%vkk & Htokb & %Hvkk) Hetkdback]".
    (* [ip]'s own ["."] record *)
    assert (Hhzi0 : blk_holes_zero bmi dati).
    { destruct Hioki as (_ & _ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hszcapi0 : bv_unsigned (di_size dni)
                       <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
    { destruct Hioki as (_ & _ & _ & _ & Hc & _). exact Hc. }
    assert (Hentsi : dir_entries (era_node dni bmi dati)
                     = dir_view dati
                         (dir_nrec (bv_unsigned (di_size dni)))).
    { rewrite (dir_entries_era_node dni bmi dati Hhzi0 Hszcapi0)
        (bool_decide_eq_true_2 _ Htyzi) //. }
    assert (Hdoti : dir_entries (era_node dni bmi dati) !! DOT
                    = Some (bv_unsigned (zero_extend' 32
                        (dir_inum datd kk : mword 16) : mword 32))).
    { rewrite Hentsi -Hself0i DOT_dot_name -Hname0i.
      exact (dir_view_live dati _ 0%nat (Hduqi Htyzi)
               ltac:(lia) Hlv0i). }
    assert (Hddi : FsStateInode.fn_dd (era_node dni bmi dati)
                   = Some (bv_unsigned (dir_inum dati 1%nat))).
    { rewrite /FsStateInode.fn_dd Hentsi DOTDOT_dotdot -Hname1i.
      exact (dir_view_live dati _ 1%nat (Hduqi Htyzi) Hnrec2i Hlv1i). }
    iDestruct (ent_toks_era_borrow_dot (fs_gamma_L fsc_fs)
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32))
                 dni bmi dati Di Hnlzi Hdoti
                 with "Hetki") as "[(%vdot & Hdott & %Hvdot) Hetkiback]".
    (* the region's reading: the two agree, and the value is [ip]'s kind *)
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htokb".
    iApply fupd_wp.
    iMod (IregLinkNz.ireg_toks_agree ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
            vkk vdot ltac:(solve_ndisj) Hinb
            with "Hireg Hdiati Htokb Hdott")
      as "([%Hvag %Hvok] & Hdiati & Htokb & Hdott)".
    iModIntro.
    (* THE NAME IS MARKED: a [TFile] fragment cannot stand at a directory *)
    assert (HmarkD : dir_bname datd kk ∈ Dd).
    { destruct (decide (dir_bname datd kk ∈ Dd)) as [Hin | Hin];
        [exact Hin | exfalso].
      rewrite (bool_decide_eq_false_2 _ Hin) in Hvkk.
      rewrite Hvkk /InodeRegion.ireg_reg_ok in Hvok.
      apply Hvok. rewrite /InodeRegion.ireg_dir_ty. exact Htyzi. }
    assert (Hvkkd : vkk = TDir (bv_unsigned dinum))
      by (rewrite (bool_decide_eq_true_2 _ HmarkD) in Hvkk; exact Hvkk).
    (* ===== (D1) ===== *)
    assert (Hpar : bv_unsigned (dir_inum dati 1%nat) = bv_unsigned dinum)
      by exact (Hvdot (bv_unsigned dinum) (bv_unsigned (dir_inum dati 1%nat))
                  ltac:(rewrite -Hvag; exact Hvkkd) Hddi).
    (* ===== (D2), off [dp]'s own EXACT count ===== *)
    assert (Hdp2 : 2 <= bv_unsigned (di_nlink dnd)).
    { pose proof (Hxactd ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                               apply bool_decide_eq_true; exact Htydz)) as Hex.
      rewrite /fn_nlink era_node_rec (fn_orphan_era_nz dnd bmd datd Hdplive)
        in Hex.
      pose proof (subseteq_size {[dir_bname datd kk]} Dd
                    ltac:(apply singleton_subseteq_l; exact HmarkD)) as Hsz1.
      rewrite size_singleton in Hsz1.
      pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dnd))) as Hnn.
      clear -Hex Hsz1 Hnn. lia. }
    (* the two fragments go home *)
    iEval (rewrite (su_zext32_unsigned (dir_inum datd kk))) in "Htokb".
    iDestruct ("Hetkdback" with "[Htokb]") as "Hetkd".
    { iExists vkk. iFrame "Htokb". iPureIntro. exact Hvkk. }
    iDestruct ("Hetkiback" with "[Hdott]") as "Hetki".
    { iExists vdot. iFrame "Hdott". iPureIntro. exact Hvdot. }
    (* ...and the counting RA's half of the zeroing move (durable-disk
       2b-inode-5): the zeroed entry gives up its token, which is what
       pays for the CHILD's own [ip->nlink--] below. *)
    assert (HnlzF2a : bv_unsigned (di_nlink (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))) <> 0).
    { rewrite su_setnl_nlink.
      exact (su_decr_pos _ _ _ HdecrW HdWnd Hdp2). }
    iDestruct (ent_toks_unlink (fs_gamma_L fsc_fs) (bv_unsigned dinum)
                 dnd (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmd bm' datd data' kk Dd
                 Hkklt Hkklive Hnotself Hkknotdot Hkknotdd Hnotself (Hduq Htydz)
                 (conj Hz' (conj Hagree Hnm')) Htydz Hdplive HnlzF2a
                 HtyF2 HszF2 Hhzd Hhz' Hszcap
                 with "Hetkd") as "[(%uty & Htoken & %Hutyd) Hetkd]".
    (* the value is the child's own -- the name was MARKED, so the record's
       fragment says [TDir dp] (durable-disk G5). *)
    assert (Hutyd' : uty = TDir (bv_unsigned dinum))
      by (rewrite (bool_decide_eq_true_2 _ HmarkD) in Hutyd; exact Hutyd).
    iEval (rewrite -(su_zext32_unsigned (dir_inum datd kk))) in "Htoken".
    (* THE MARKER SET LOSES EXACTLY THE ZEROED NAME, and [dp]'s count drops
       with it -- which is what keeps the per-directory count EXACT across
       an rmdir (durable-disk G5's (D2), the write half). *)
    assert (HentsD : dir_entries (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
                     = delete (dir_bname datd kk)
                         (dir_entries (era_node dnd bmd datd)))
      by exact (dir_entries_unlink_eq dnd (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmd bm' datd data' kk
                  Hkklt Hkklive (Hduq Htydz)
                  (conj Hz' (conj Hagree Hnm')) Htydz HtyF2 HszF2
                  Hhzd Hhz' Hszcap).
    assert (HdokF2E : FsStateInode.ent_dset_ok (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
                       (Dd ∖ {[dir_bname datd kk]}))
      by exact (FsStateInode.ent_dset_ok_delete _ _ (dir_bname datd kk) _
                  HentsD
                  ltac:(apply not_elem_of_difference; right;
                        apply elem_of_singleton; reflexivity)
                  ltac:(intros tz Htz; apply Hdokd;
                        exact (proj1 (proj1 (elem_of_difference _ _ _) Htz)))). 
    assert (HxactF2E : FsStateInode.node_exact (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
                       (Dd ∖ {[dir_bname datd kk]})).
    { intros _.
      pose proof (Hxactd ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                               apply bool_decide_eq_true; exact Htydz)) as Hex.
      rewrite /fn_nlink era_node_rec (fn_orphan_era_nz dnd bmd datd Hdplive)
        in Hex.
      pose proof (subseteq_size {[dir_bname datd kk]} Dd
                    ltac:(apply singleton_subseteq_l; exact HmarkD)) as Hsz1.
      rewrite size_singleton in Hsz1.
      pose proof (size_difference Dd {[dir_bname datd kk]}
                    ltac:(apply singleton_subseteq_l; exact HmarkD)) as Hszd.
      rewrite size_singleton in Hszd.
      rewrite /fn_nlink era_node_rec.
      rewrite (fn_orphan_era_nz (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data' HnlzF2a).
      rewrite Hszd.
      pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dnW))) as Hnn.
      pose proof (proj1 (bv_unsigned_in_range _ (di_nlink (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))))) as Hnn2.
      rewrite su_setnl_nlink in Hnn2 |- *.
      (* the count itself, in small steps: [lia] does not see through
         [Z.to_nat] of a decremented halfword in one go. *)
      match goal with
      | |- Z.to_nat ?X = _ =>
          assert (HXd : X = bv_unsigned (di_nlink dnd) - 1)
            by (rewrite -HdWnd HdecrW Z.add_simpl_r; reflexivity);
          rewrite HXd
      end.
      rewrite Z2Nat.inj_sub; [| clear; lia].
      rewrite Hex. clear -Hsz1. change (Z.to_nat 1) with 1%nat. lia. }
    iDestruct (dlinks_intro _ _ _ _ _ (Dd ∖ {[dir_bname datd kk]})
                 HdokF2E HxactF2E with "Hetkd") as "Hdlnkd2".
    (* [dp]'s pure re-park facts, moved DOWN to the decremented record *)
    assert (HiokF2 : inode_ok fsc_cov fsc_logst (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
      by (exact (su_setnl_inode_ok fsc_cov fsc_logst dnW bm' data' _ Hiok')).
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
    assert (Hz1ne : bv_unsigned (dir_inum dati 1)
                    <> bv_unsigned (zero_extend' 32
                         (dir_inum datd kk : mword 16) : mword 32)).
    { rewrite su_zext32_unsigned Hpar. intro Hc. apply Hnotself.
      symmetry. exact Hc. }
    (* THE [".."] UNIT GOES BACK (durable-disk 2b-inode-5): the
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
    iDestruct (ent_toks_era_orphan (fs_gamma_L fsc_fs)
                 (bv_unsigned (zero_extend' 32
                    (dir_inum datd kk : mword 16) : mword 32))
                 dni (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati (bv_unsigned dinum) Di
                 (su_setnl_type _ _) (su_setnl_size _ _) Hnlzi Hnl2za
                 Htyzi Hhzi Hszcapi (Hduqi Htyzi) Hnrec2i Hlv1i
                 ltac:(rewrite DOTDOT_dotdot; exact Hname1i) Hpar
                 Hlv0i ltac:(rewrite DOT_dot_name; exact Hname0i)
                 Hself0i
                 ltac:(intro Hc; exact (Hz1ne (eq_trans Hpar Hc)))
                 with "Hetki")
      as "[(%tyup & Htokend) [(%tydot & Hdotf & %Hdotok) Hetki]]".
    (* the ["."] fragment and the freed NAME record are fragments at the
       SAME inum, so the RA's own agreement values them alike (G5). *)
    iApply fupd_wp.
    iMod (IregLinkNz.ireg_toks_agree ⊤ fsc_ireg fsc_fs icfg_ist icfg_nib
            (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) dni
            uty tydot ltac:(solve_ndisj) Hinb
            with "Hireg Hdiati Htoken Hdotf")
      as "([%Hagd _] & Hdiati & Htoken & Hdotf)".
    iModIntro.
    (* FINDING 3: [ip]'s own count is EXACT and stands at one, so its
       marker set is EMPTY -- which is what re-seals its bundle at the
       orphaned record. *)
    assert (HDiempty : Di = ∅).
    { apply leibniz_equiv, size_empty_inv.
      pose proof (Hxacti ltac:(rewrite /fn_is_dir /fn_type era_node_rec;
                               apply bool_decide_eq_true; exact Htyzi)) as Hex.
      rewrite /fn_nlink era_node_rec Hnl1
        (fn_orphan_era_nz dni bmi dati Hnlzi) in Hex.
      change (Z.to_nat 1) with 1%nat in Hex. clear -Hex. lia. }
    assert (HdokiZ : FsStateInode.ent_dset_ok (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati) Di)
      by (rewrite HDiempty; intros tz Htz;
          exfalso; exact (not_elem_of_empty tz Htz)).
    assert (HxactiZ : FsStateInode.node_exact (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati) Di).
    { intros _. rewrite /fn_orphan /fn_nlink era_node_rec Hnl2za HDiempty
        size_empty. reflexivity. }
    assert (Hmoidin : (mword_of_int (bv_unsigned dinum) : mword 32) = dinum)
      by (exact (su_moi32_id dinum)).
    destruct nw as [| c1]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D13 T6 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Iupdate.wp_iupdate_unlink (CID := T6) gs jx gl pd pav pu
 (ientry kd) dinum
              (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))
              dnW bm' c1 (Sbw : gset Z) true tyup pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              G4 (K - 30)%nat eb b lks
              (us_upt U P1) ltac:(exact Kiupd) ltac:(intros _; exact Hibd16) Hgeom Hist0
              Hdiblk Hdiblog Hdinb (su_setnl_type_stable dnW _)
              ltac:(rewrite su_setnl_type Hty'v Htydz; unfold T_DIR_z; lia)
              ltac:(rewrite su_setnl_nlink; exact HdecrW)
              ltac:(rewrite su_setnl_addrs; exact Haddr'v)
              ltac:(exact (blkmap_wf_dir_len fsc_cov fsc_logst bm' Hwf'))
              Hj Hgl HG4a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevd Hiinumd Hmetad
                    [Haddrsd Hindd] Hsbi Hireg [Hdiatd] [Htokend]
                    Hpidq Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsd Hindd". }
    { iExact "Hdiatd". }
    { (* [dp] stays live, so its multiplicity drops by exactly one *)
      rewrite (InodeRegion.ireg_dot_delta_live _ _ HnlzF2a)
        FsStateLink.link_reps_1. iExact "Htokend". }
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
    iIntros (D18 Hd18). iApply bi.later_intro. iIntros "Hcg Hpc".
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
    (* ...and the ERA's abstract value with them (durable-disk 2b-inode-3):
       [ireg_top_retag] opens [ftopN] alone. *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): rmdir lowers the
       parent's own count, and the re-pack below proves the same four facts
       -- the entry's removal left the directory well-formed and the count
       move touches nothing else. *)
    assert (HlocW : inode_local (bv_unsigned dinum)
              (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                              : mword 64)
                       (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 63 : mword 6))
                        : mword 64)) 31 0)))) bm' data')).
    { apply (inode_local_of_ok_rec (bv_unsigned dinum) fsc_cov fsc_logst _ bm' data').
      - exact HiokF2.
      - exact (inode_rec_local_same_type dnW _ Hrl_data'
                 (su_setnl_type dnW _)
                 (su_dec_short _ _ HdecrW (proj1 (proj2 Hrl_data')))
                 (proj2 (proj2 Hrl_data'))).
      - exact HduqF2.
      - exact HddixF2. }
    iMod (ireg_top_retag ⊤ fsc_fs (bv_unsigned dinum)
            (era_node dnd bmd datd) (era_node (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm' data')
            ltac:(solve_ndisj) HlocW with "[] Htop") as "Htop";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst kd dinum (su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dnW : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bm')
      with "[Hdlnkd2 Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop]" as "Hloadd".
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
      iExact "Htop". }
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
    iDestruct (su_esc_acc kd Hkd with "Hescrows")
      as "#Hescd".
    iDestruct (log_opS_named with "HopS") as (e0) "HopS".
    pose (dnW2 := su_setnl dnW (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dnW : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrbd2 : false = true ->
              fsc_bmapstart ∈ (Sbw ∪ {[IBLOCK dinum icfg_ist]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcrud2 : true = true ->
              IBLOCK dinum icfg_ist ∈ (Sbw ∪ {[IBLOCK dinum icfg_ist]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnud2 : (iput_units <= S c1)%nat).
    { unfold iput_units. lia. }
    (* [dp]'s arm comes off at its own release (durable-disk B''-tx2) *)
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the quarter it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffrd") as "Hoffdd".
    iApply (Iunlockput.wp_iunlockput_dep_gen (CID := D20) gs jx gl pd pav
              pu gild gisld
 kd qdi sd gyd loyd tlyd
              (DepTx sd icfg_dev dinum gyd loyd t (1/4)%Qp) dinum dnW2 bm'
              (S c1) (Sbw ∪ {[IBLOCK dinum icfg_ist]}) false true false e0 _ _ pid (DfracOwn (1/4)) dqb dqs
              C5 (K - 30)%nat eb b lks
              (us_upt U P1) Kiup eq_refl Hkd Hcrbd2 Hcrud2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hdiblk Hdiblog Hdinb Hcovb
              Hnud2 Hj Hgl HC5a0 (Hlb "log"%string) eq_refl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hescd Hireg Hropen Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffdd Hidevd Hiinumd
                    Hivalidd Hloadd Hshotd2 Hfrz [$Hkeepd $Hrud] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D21 Hd21 mup n2 Sb2 wg)
      "%Hcsup Hcg Hown _ _ Hpc Hpidq Hsbb Hsbi Hbsl %Hsb2 %Hwg
       %Hwgc %Hn2 HopS Hisl Htq1".
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
    { destruct Hioki as (Hc & _). exact (blkmap_wf_dir_len fsc_cov fsc_logst bmi Hc). }
    destruct n2 as [| c2]; [exfalso; lia |].
    iDestruct (su_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport D21 D26 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    (* THE ORPHANING SPEND (lane G5): the child's multiplicity crosses
       [1 + 1 -> 0] -- its NAME record in [dp], freed by the zeroing, and
       its own ["."], freed by the orphan move. *)
    iApply (Iupdate.wp_iupdate_unlink (CID := D26) gs jx gl pd pav pu
 (ientry ks)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                 (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                           : mword 64)
                    (sign_extend' 64
                       (sign_extend' 12 (mword_of_int 63 : mword 6))
                     : mword 64)) 31 0))))
              dni bmi c2 (Sb2 : gset Z) false
              (TDir (bv_unsigned dinum)) pid
              (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn (1/2)) dqs
              C9 (K - 30)%nat eb b lks
              (us_upt U P1) ltac:(exact Kiupd) ltac:(discriminate) Hgeom Hist0 Hiblki
              Hiblogi Hinb (su_setnl_type_stable dni _)
              ltac:(rewrite su_setnl_type; exact Htynzi0)
              ltac:(exact Hdecr)
              ltac:(rewrite su_setnl_addrs; exact Haddri)
              Hdirleni Hj Hgl HC9a0 Heb (Hlb "log"%string)
              with "Hcg Hown Htext Hdata Hpc Hpanenv Hbio Hlog Hidevi Hiinumi Hmetai
                    [Haddrsi Hindi] Hsbi Hireg Hdiati
                    [Htoken Hdotf]
                    Hpidq Hprocs Hdev Hgeo Hdlk Hbs2 HopS").
    { rewrite /inode_map. iFrame "Haddrsi Hindi". }
    { (* THE DELTA IS TWO (lane G5): the child's multiplicity crosses
         [1 + 1 -> 0], and the two fragments are its NAME in [dp] (freed by
         the zeroing) and its own ["."] (freed by the orphan move). *)
      assert (Hdd2 : InodeRegion.ireg_dot_delta
                      (bv_unsigned (di_type (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0))))))
                      (bv_unsigned (di_nlink (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))))) = 2%nat).
      { rewrite /InodeRegion.ireg_dot_delta
          (bool_decide_eq_true_2 _ Hnl2za) su_setnl_type
          (bool_decide_eq_true_2
             (bv_unsigned (di_type dni) = InodeRegion.ireg_dir_ty)
             ltac:(rewrite /InodeRegion.ireg_dir_ty; exact Htyzi)) //. }
      rewrite Hdd2 FsStateLink.link_toks_reps_S FsStateLink.link_reps_1.
      iSplitL "Htoken".
      - rewrite -Hutyd'. iExact "Htoken".
      - rewrite -Hutyd' Hagd. iExact "Hdotf". }
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
       0 is the self record, and record 1 goes back TOKENLESS -- an
       orphan's dots owe nothing ([FsStateEra.ent_toks_era_orphan]), fed by
       FINDING 3 and the [blez]'s [1 <=] *)
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
    iDestruct (dlinks_intro _ _ _ _ _ Di HdokiZ HxactiZ
                 with "Hetki") as "Hdlnki2".
    (* ...and the ERA's abstract value follows the count (2b-inode-3). *)
    (* THE RETAG OWES THE ROW (durable-disk lane A): a lowered link count
       leaves the inode well-formed, and these are the re-pack's own four
       facts.  This is the RMDIR arm, so the child IS a directory and the
       two dot clauses ride [HddixZ]/[HduqZ], proved just above. *)
    assert (Hlocdec : inode_local
              (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                            : mword 32))
              (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                    (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                              : mword 64)
                       (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 63 : mword 6))
                        : mword 64)) 31 0)))) bmi dati)).
    { apply (inode_local_of_ok_rec _ fsc_cov fsc_logst _ bmi dati).
      - exact (su_setnl_inode_ok fsc_cov fsc_logst dni bmi dati _ Hioki).
      - apply (inode_rec_local_same_type dni _ Hrl_dati
                 (su_setnl_type dni _));
          [ exact (su_dec_short _ _ Hdecr (proj1 (proj2 Hrl_dati)))
          | exact (proj2 (proj2 Hrl_dati)) ].
      - exact HduqZ.
      - exact HddixZ. }
    iApply fupd_wp.
    iMod (ireg_top_retag ⊤ fsc_fs
            (bv_unsigned (zero_extend' 32 (dir_inum datd kk : mword 16)
                          : mword 32))
            (era_node dni bmi dati)
            (era_node (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi dati)
            ltac:(solve_ndisj) Hlocdec with "[] Htopi") as "Htopi";
      [iApply (ireg_inv_ftop with "Hireg") |].
    iModIntro.
    iAssert (ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst ks
               (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
               (su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
                  (add_vec (zero_extend' 64 (di_nlink dni : mword 16)
                            : mword 64)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 63 : mword 6))
                      : mword 64)) 31 0)))) bmi)
      with "[Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi]" as "Hloadi".
    { iApply ic_loaded_flat; rewrite /ic_loaded_flat_body. iExists dati.
      iFrame "Hdlnki2 Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi".
      iPureIntro. split_and!.
      - exact (su_setnl_inode_ok fsc_cov fsc_logst dni bmi dati _ Hioki).
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
    iDestruct (su_esc_acc ks Hks with "Hescrows")
      as "#Hesci".
    iDestruct (log_opS_named with "HopS") as (e1) "HopS".
    pose (dni2 := su_setnl dni (trunc16 (sign_extend' 64 (subrange_vec_dec
              (add_vec (zero_extend' 64 (di_nlink dni : mword 16) : mword 64)
                 (sign_extend' 64
                    (sign_extend' 12 (mword_of_int 63 : mword 6))))
              31 0)))).
    assert (Hcrb2 : false = true ->
              fsc_bmapstart ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})).
    { intros Hfalse. discriminate Hfalse. }
    assert (Hcru2 : true = true ->
              IBLOCK (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                icfg_ist ∈ (Sb2 ∪ {[IBLOCK (zero_extend' 32
                  (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})).
    { intros _. apply elem_of_union_r, elem_of_singleton. reflexivity. }
    assert (Hnu2 : (iput_units <= c2)%nat).
    { unfold iput_units. lia. }
    (* ...and [ip]'s at its own *)
    (* THE ARM RETIRES AT THE PARK (durable-disk B''-tx4): the descriptor
       goes in and the quarter it parked comes back in the post, so no
       bundleless out-state stands across the call. *)
    iDestruct (off_rows_to_dep with "Hoffri") as "Hoffdi".
    iApply (Iunlockput.wp_iunlockput_dep_gen (CID := D29) gs jx gl pd pav
              pu gili gisli
 ks qsi si gyi loyi tlyi
              (DepTx si icfg_dev
                 (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
                 gyi loyi t (1/4)%Qp)
              (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32)
              dni2
              bmi c2 (Sb2 ∪ {[IBLOCK (zero_extend' 32
                (dir_inum datd kk : mword 16) : mword 32) icfg_ist]})
              false true false e1 _ _ pid (DfracOwn (1/4)) dqb dqs
              E2 (K - 30)%nat eb b lks
              (us_upt U P1) Kiup eq_refl Hks Hcrb2 Hcru2
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblki Hiblogi Hinb Hcovb
              Hnu2 Hj Hgl HE2a0 (Hlb "log"%string) eq_refl
              with "Hcg Hown [] [] Htext Hdata Hpc Hpanenv Hbio Hlog Hitab Hitinv
                    Hesci Hireg Hropen Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffdi Hidevi Hiinumi
                    Hivalidi Hloadi Hshoti2 Hfrzi [$Hkeepi $Hrui] Hsbb Hsbi Hbmres Hpidq
                    Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2] [] HopS").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    { iApply su_bs3. iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"]. }
    { iEval (cbn beta iota). iEmpIntro. }
    iIntros (D30 Hd30 mip n3 Sb3 wh)
      "%Hcsip Hcg Hown Htce Hcce Hpc Hpidq Hsbb Hsbi Hbsl %Hsb3
       %Hwh %Hwhc %Hn3 HopS Hisl2 Htq2".
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
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr2 : b = false \/ proc_addr jx = zero_reg
                     -> (D31 : CPU) = (D30 : CPU)) by wp_next_chain.
    assert (Htre2 : eb = false \/ proc_addr jx = zero_reg
                      -> (D31 : CPU) = (D30 : CPU)) by (rewrite Hbeq; exact Htr2).
    iDestruct (cpu_own_transport D30 D31 0 eb (proc_addr jx) b
                 Htr2 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D30 D31 eb (proc_addr jx)
                 Htre2 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D30 D31 eb (proc_addr jx)
                 Htre2 with "Hcce") as "Hcce".
    (* both arms are home, so the element is whole again for the [end_op] *)
    iDestruct (log_tx_add icfg_log t (1/2) (1/4) (1/4)
                 (eq_sym Qp.quarter_quarter) with "Htq1 Htq2") as "Htp".
    iDestruct (log_tx_add icfg_log t 1 (1/2) (1/2)
                 (eq_sym Qp.half_half) with "Htp Htx") as "Htw".
    iDestruct (log_tx_full with "Htw") as "Htx".

    iApply (EndOp.wp_end_op_sconf (CID := D31) gs jx gl fsc_uart fsc_disk fsc_dlock pd pav pu fsc_bio
              icfg_log fsc_fs fsc_cov fsc_logst icfg_dev n3 pid (DfracOwn (1/4)) E3 (K - 30)%nat
              eb b lks (us_upt U P1) Keo Hgeom Hj Hgl
              ltac:(rewrite Hlkempty; apply locks_below_empty)
              with "Hcg Hown Htce Hcce Htext Hdata Hpc Hpanenv Hbio Hlog Hseam Hgen
                    Hpidq Hprocs Hdev Hgeo Hdlk [HopS Htx]").
    { iApply (log_opS_op with "HopS Htx"). }
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
    iIntros (D37 Hd37). iApply bi.later_intro. iIntros "Hcg Hpc".
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
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr4 : b = false \/ proc_addr jx = zero_reg
                     -> (D37 : CPU) = (D32 : CPU)) by wp_next_chain.
    assert (Htre4 : eb = false \/ proc_addr jx = zero_reg
                      -> (D37 : CPU) = (D32 : CPU)) by (rewrite Hbeq; exact Htr4).
    iDestruct (cpu_own_transport D32 D37 0 eb (proc_addr jx) b
                 Htr4 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D32 D37 eb (proc_addr jx)
                 Htre4 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D32 D37 eb (proc_addr jx)
                 Htre4 with "Hcce") as "Hcce".
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
    (* ONE hoisted premise for the whole triple, not three inline [ltac:]s.
       [wp_next_chain] is a [repeat match goal], i.e. a whole-context scan, and
       optimization.md's rule is that such a tactic spliced into ARGUMENT
       position is priced by the depth of its call site rather than by its goal
       -- the splice's goal is an evar carrying every variable in scope.  The
       three transports here share one CID pair, so one [assert] serves all
       three and the [eb] form is one rewrite off the [b] form. *)
    assert (Htr6 : b = false \/ proc_addr jx = zero_reg
                     -> (CIDy : CPU) = (D37 : CPU)) by wp_next_chain.
    assert (Htre6 : eb = false \/ proc_addr jx = zero_reg
                      -> (CIDy : CPU) = (D37 : CPU)) by (rewrite Hbeq; exact Htr6).
    iDestruct (cpu_own_transport D37 CIDy 0 eb (proc_addr jx) b
                 Htr6 with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport D37 CIDy eb (proc_addr jx)
                 Htre6 with "Htce") as "Htce".
    iDestruct (cpu_claim_ext_transport D37 CIDy eb (proc_addr jx)
                 Htre6 with "Hcce") as "Hcce".
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

End ProofSysUnlinkW5Dir.

End SysUnlinkW5Dir.
