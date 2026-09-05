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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import W32Arith.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
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
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheHeld.
Require Import IcacheInv.
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
Require Import SpecIput.
Require Import SpecIunlockput.
Require Import SpecDirlookup.
Require Import SpecDirlink.
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
(*  ProofSysUnlinkW1.v -- sys_unlink's W1 block. *)
(*                                                                      *)
(*  Split out of ProofSysUnlink.v FOR THE BUILD DAG: the five block      *)
(*  lemmas are mutually independent (each seam is the NEXT block's        *)
(*  premise list, so the seal composes them and nothing else does), and   *)
(*  [Tails.] is named only inside proofs, never in a statement -- so each *)
(*  file makes its own [Tails] and the vocabulary they share             *)
(*  (ProofSysUnlinkShared.v) needs no functor argument at all.            *)
(* ==================================================================== *)

Require Import ProofSysUnlinkShared.

Module SysUnlinkW1 (Iunlockput : IUNLOCKPUT) (EndOp : END_OP) (PN : PANIC) (Argstr : ARGSTR) (BeginOp : BEGIN_OP) (Nameiparent : NAMEIPARENT).

Module Tails := SysUnlinkTails Iunlockput EndOp PN.

Section ProofSysUnlinkW1.
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
  (* W1'S SEAM, NAMED -- the same fold as [su_w3_seam] below, whose header
     carries the measurement (W3's seam was 48 % of [Delta] at a mid-walk
     dump).  Spelled inline this one was 58 lines.

     TRANSPARENT on purpose: the [iApply ("Hseamk" $! ...)] sites and the
     [iIntros] that discharges this goal in [wp_sys_unlink_sconf] unify
     straight through a transparent constant, so NOT ONE LINE of proof script
     changed.  [CIDs] is an explicit binder because the body writes
     [wp_next (CID0 := CIDs)], and its other rows resolve their [CpuId]
     instance to the innermost one. *)
  Definition su_w1_seam `{GEN : GenId} `{CIDs : CpuId} `{XI : CurCtx}
      (gf : gname) (jx : nat)
 (dqb : dfrac)
      (dqs : dfrac) (dqbs : dfrac) (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (Ms : regfile) (P1 : uptd)
      (n1 : nat) (Sb1 : gset Z) (w1 : bool)
      (dpv : mword 64) (nf : nat -> bv 8) (bp1 : nat -> bv 8)
      (bnm0 : nat -> bv 8) (bd0 : nat -> bv 8) (be0 : nat -> bv 8)
      (w4 : mword 64) (w5 : mword 64) (w6 : mword 64) (w27 : mword 64)
      (w30 : mword 64) : iProp Σ :=
    (⌜su_al (m !!! Regidx csp_rs1 : mword 64)⌝ -∗
       ⌜su_regs m (m !!! Regidx csp_rs1 : mword 64) dpv
                (m !!! Regidx Rs2 : mword 64) (m !!! Regidx Rs3 : mword 64) Ms⌝ -∗
       (* [a0] STILL HOLDS [dp] AT THE SEAM, and it has to be said: [su_regs]
          pins the five CALLEE-SAVED registers and [a0] is not one of them,
          so the [c.mv s1,a0] at +0x2c leaves the fact true and unexported.
          W2's [ilock(dp)] reads [a0], so this is its first premise.  (Found
          by the seal, which is the first consumer to compose W1 with W2.) *)
       ⌜(Ms !!! Regidx Ra0 : mword 64) = dpv⌝ -∗
       ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P1⌝ -∗
       ⌜(su_u1 w1 <= n1)%nat⌝ -∗
       ⌜w1 = true -> fsc_bmapstart ∈ Sb1⌝ -∗
       ⌜dpv <> (zero_reg : mword 64)⌝ -∗
       sie_cap_gpr KT1 Ms (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x30)) -∗
       fs_crash_seam fsc_cov fsc_logst -∗
       gen_cert -∗
       bslots 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
       proc_priv gf (proc_addr jx) pid (us_upt U P1) -∗
       iref_slots 1 -∗
       inode_held_ty dpv T_DIR -∗
       log_opS icfg_log n1 Sb1 -∗
       (* the transaction token rides beside the budget: this walk ends the
          operation, and end_op takes the whole [log_op] (durable-disk lane A) *)
       log_tx icfg_log -∗
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
         SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
           (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
           dqb dqs dqbs) -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma su_w1 `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64) (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string) :
    (K_sys_unlink <= K)%nat ->
    icfg_dev = ROOTDEV ->
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
    pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
    sie_cap_gpr KT1 m K b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int KernelSyms.sys_unlink) -∗
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
    iref_slots SpecSysUnlink.sys_unlink_slots -∗
    proc_priv gf (proc_addr jx) pid U -∗
    (* ---- THE SEAM: the fall-through, at +0x30 with [dp] resolved ---- *)
    (∀ (CIDs : CpuId) (Ms : regfile) (P1 : uptd)
       (n1 : nat) (Sb1 : gset Z) (w1 : bool) (dpv : mword 64)
       (nf bp1 bnm0 bd0 be0 : nat -> bv 8)
       (w4 w5 w6 w27 w30 : mword 64),
       su_w1_seam (CIDs := CIDs)
          gf jx dqb dqs dqbs pid U
          m K eb b lks Ms P1 n1 Sb1 w1 dpv nf bp1 bnm0 bd0 be0 w4 w5 w6 w27
          w30) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      SpecSysUnlink.sys_unlink_closer (CID := CIDx) gf (proc_addr jx) pid U m
        (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
        dqb dqs dqbs) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
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
    iDestruct (cpu_own_transport CID0 CID8 0 eb (proc_addr jx) b
                 ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID8) fsc_kalloc gf M6 (K - 30)%nat 0%nat eb
              (proc_addr jx) 0%nat v0 pid U 128%nat bp0 b lks
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
      iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1) with "Hpriv")
        as "[Hpnc [Href Hftok]]".
      iEval (rewrite proc_priv_nocwd_bare) in "Hpnc".
      iDestruct "Hpnc" as "[Hpidq Hofiles]".
      iDestruct (cwd_ref_at_held_at with "Href") as "Hcwdref".
      iEval (cbn [upd_upt pv_cwd pv_fdg]) in "Hcwdref".
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
      iApply (BeginOp.wp_begin_op_sconf (CID := CID12) gs jx gl fsc_bio icfg_log fsc_fs fsc_cov
                fsc_logst icfg_dev pid (DfracOwn (1/4)) N0 (K - 30)%nat eb b lks
                (us_upt U P1) ltac:(exact Kbo) Hj Hgl (Hlb "log"%string)
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
      iDestruct (log_op_openS with "Hop") as (Sb0) "[HopS Htx]".
      iEval (rewrite su_slots2) in "Hir".
      iDestruct (cpu_own_transport CID13 CID16 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iApply (Nameiparent.wp_nameiparent_gen (CID := CID16) gs jx gl
                pd pav pu gf
 pk1 bp1 bnm0
                MAXOPBLOCKS Sb0 pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                N3 (K - 30)%nat eb b lks
                (us_upt U P1) ltac:(exact Knp) HdevR Hnib0 Hgeom
                Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hpcstr1
                (proj2 (su_len_range pk1 Hpk1))
                ltac:(exact (su_walk_need_closes _)) Hj Hgl
                with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hkenv Hitab Hitinv
                      Hescrows Hslks Hireg Hropen Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                      Hbmres Hpidq Hcwdref [Hbufp] [Hnm14] Hbsl Hir
                      [$HopS $Htx]").
      (* nameiparent is eb-generic now; sys_unlink is at [eb = true]. *)
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { iEval (rewrite HN3a0). iExact "Hbufp". }
      { iEval (rewrite HN3a1). iExact "Hnm14". }
      iIntros (CID17 Hq17 mnp n1 Sb1 ok1 nf dpv w1)
        "%Hcsnp Hcg Hown _ _ Hpc Hsbb Hsbi Hpidq Hcwdref
         Hbufp Hnm14 Hbsl %HSb1 %Hw1 %Hn1 [HopS Htx] Hres1".
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
        iDestruct "Hhelddp" as (kd qd dinum gyd lod tld)
          "(%Hdpe & %Hkd & %Hdinumc & %Hled & #Hfld &
            Hrefdp & #Hshotd & Hrud)".
        assert (Hdpnz : dpv <> (zero_reg : mword 64))
          by (rewrite Hdpe; apply ientry_ne_zero; lia).
        iAssert (inode_held_ty dpv T_DIR) with "[Hrefdp Hrud]" as "Hhelddp".
        { iExists kd, qd, dinum, gyd, lod, tld.
          iSplitR; [done |]. iSplitR; [done |].
          iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iExact "Hfld" |].
          iFrame "Hrefdp Hrud". iExact "Hshotd". }
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
        iDestruct (cwd_ref_at_of_held_at with "Hcwdref") as "Href".
        iCombine "Hpidq Hofiles" as "Hpnc".
        iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)
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
                  Hir1 Hhelddp HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2
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
        iApply (Tails.su_tail_b (CID0 := CID19) gs jx gl pd pav pu
 n1 pid (DfracOwn (1/4))
                  m N4 sp0 K eb b lks u4 u5 u6 u27 u30 bd0 bnf bpf be0
                  (us_upt U P1) ltac:(exact Keo) K30 Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) HN4sp HN4thr HN4s2 HN4s3 Hal
                  with "Hcg Hown [] [] Htext Hdata Hpc Hpenv2 Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk [HopS Htx] Hf1 Hf2 Hf3 Hf4
                        Hf5 Hf6 HbD HbNj HbPj H27 HbE H30
                        [Hcont Hbsl Hsbb Hsbi Hsbs Hir2 Hofiles
                         Hcwdref Hftok]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { iApply (log_opS_op with "HopS Htx"). }
        iEval (rewrite /wp_next).
        iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                             Hpc Hpidq".
        iDestruct (cwd_ref_at_of_held_at with "Hcwdref") as "Href".
        iCombine "Hpidq Hofiles" as "Hpnc".
        iEval (rewrite -proc_priv_nocwd_bare) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (us_upt U P1)
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
      iApply bi.later_intro. iIntros (CID10 Hq10) "Hcg Hpc".
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

End ProofSysUnlinkW1.

End SysUnlinkW1.
