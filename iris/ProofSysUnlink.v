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

   NO SEAL YET.  [LinkSysUnlink.v] still supplies [SYSUNLINK] with an
   [Axiom]: the T_DIR half of W5 cannot be closed until the design ruling
   FINDING 3 asks for lands (an empty directory's link count is 1, which
   the model states nowhere), so the walk is built to STOP one pure premise
   short of the seal.  See projects/fs-sysfile.md, S7-unlink, FINDING 3.

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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelRvcDecode.
Require Import BvShift.
Require Import StackOwn StackBytes.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import PanicStub.
Require Import SpecPrintk.
Require Import WpUart.
Require Import ByteBuf.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import DirLinks.
Require Import FsLookup.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
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
Require Import SpecFetchstr.
Require Import CodeSysUnlink.
Require Import SysUnlinkBudget.
Require Import SpecSysUnlink.
Require Import ProofSysUnlinkParts.
Require Import ProofSysUnlinkTails.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
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
          (sign_extend' 64 (mword_of_int 1656 : mword 12))
  = (mword_of_int su_dot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma su_dotdotaddr :
  add_vec (add_vec (mword_of_int (SU + 0x48) : mword 64)
                   (auipc_off (mword_of_int 2 : mword 20)))
          (sign_extend' 64 (mword_of_int 1644 : mword 12))
  = (mword_of_int su_dotdot_addr : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [di_type dn = T_DIR] at the sixteen-bit width, read as the Z-level
   equality [DirView] / [DirLinks] state their type tests at.  The
   [ity_shot] agreement gives the left form and every payload clause wants
   the right one. *)
Lemma su_tdir_zof (t : mword 16) :
  t = SpecDirlookup.T_DIR -> bv_unsigned t = T_DIR_z.
Proof. intros ->. vm_compute. reflexivity. Qed.

Module SysUnlinkProof (Argstr : ARGSTR) (BeginOp : BEGIN_OP)
                      (Nameiparent : NAMEIPARENT) (Ilock : ILOCK)
                      (Namecmp : NAMECMP) (Dirlookup : DIRLOOKUP)
                      (Memset : MEMSET) (Readi : READI) (Writei : WRITEI)
                      (Iupdate : IUPDATE) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP).

Module Tails := SysUnlinkTails Iunlockput EndOp.

Section ProofSysUnlinkBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).

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
    (SpecDirlink.ic_sleeplocks cn -∗
     ∃ gil gisl : gname,
       is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string
                        (ic_tok cn k) (slh_tok (icfg_isl k))
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /SpecDirlink.ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma su_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
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

  (* [KernelDataInv.kernel_data_window] extracts the bytes of a machine
     WORD; a name literal is a byte STRING that is not NUL-terminated
     within its window, so neither that lemma nor [kernel_data_string]
     applies.  The same proof at a byte function. *)
  Lemma su_kd_bytes `{GEN : GenId} (A : Z) (W : nat) (f : nat -> bv 8) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    (forall j, (j < W)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some (f j)) ->
    kernel_data -∗
    ([∗ list] j ∈ seq 0 W, (pa_add a j) ↦ₘ□ f j).
  Proof.
    iIntros (-> HA Hbytes) "#Hd". iApply big_sepL_intro. iIntros "!>" (i j Hi).
    apply lookup_seq in Hi. destruct Hi as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat i)%Z (f i) with "Hd").
    apply map_lookup_filter_Some_2; [apply Hbytes; exact Hlt | cbn; lia].
  Qed.

  Lemma su_dot_window `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dot_f j).
  Proof.
    intros ->. iApply (su_kd_bytes su_dot_addr 14 su_dot_f _ eq_refl
                         ltac:(unfold text_end, su_dot_addr; lia)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  Lemma su_dotdot_window `{GEN : GenId} (a : mword 64) :
    a = mword_of_int su_dotdot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ su_dotdot_f j).
  Proof.
    intros ->. iApply (su_kd_bytes su_dotdot_addr 14 su_dotdot_f _ eq_refl
                         ltac:(unfold text_end, su_dotdot_addr; lia)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
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
      (size : Z) (dev : mword 32) (used : gset Z)
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
    sie_cap_gpr m K b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int KernelSyms.sys_unlink) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    iref_slots SpecSysUnlink.sys_unlink_slots -∗
    proc_priv gf (proc_addr jx) pid V -∗
    (* ---- THE SEAM: the fall-through, at +0x30 with [dp] resolved ---- *)
    (∀ (CIDs : CpuId) (Ms : regfile) (P1 : uptd)
       (n1 : nat) (Sb1 used1 : gset Z) (w1 : bool) (dpv : mword 64)
       (nf bp1 bnm0 bd0 be0 : nat -> bv 8)
       (w4 w5 w6 w27 w30 : mword 64),
       ⌜su_al (m !!! Regidx csp_rs1 : mword 64)⌝ -∗
       ⌜su_regs m (m !!! Regidx csp_rs1 : mword 64) dpv
                (m !!! Regidx Rs2 : mword 64) (m !!! Regidx Rs3 : mword 64) Ms⌝ -∗
       ⌜uptd_ext (pv_upt V) P1⌝ -∗
       ⌜used1 ⊆ used⌝ -∗
       ⌜(su_u1 w1 <= n1)%nat⌝ -∗
       ⌜w1 = true -> bmapstart ∈ Sb1⌝ -∗
       ⌜dpv <> (zero_reg : mword 64)⌝ -∗
       sie_cap_gpr Ms (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x30)) -∗
       fs_crash_seam cov logstart -∗
       gen_cert -∗
       bslots bn 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       bitmap_res gfs bmapstart cov logstart size used1 -∗
       proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
       iref_slots 1 -∗
       inode_held_ty dpv T_DIR -∗
       log_opS g n1 Sb1 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 4) ↦₈ w4 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 5) ↦₈ w5 -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 6) ↦₈ w6 -∗
       ([∗ list] jj ∈ seq 0 16,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 8) jj ↦ₘ bd0 jj) -∗
       ([∗ list] jj ∈ seq 0 14,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10) jj ↦ₘ nf jj) -∗
       ([∗ list] jj ∈ seq 0 2,
          pa_add (pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 10) 14) jj
            ↦ₘ bnm0 (14 + jj)%nat) -∗
       ([∗ list] jj ∈ seq 0 128,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 26) jj ↦ₘ bp1 jj) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 27) ↦₈ w27 -∗
       ([∗ list] jj ∈ seq 0 16,
          pa_add (pa_stk (m !!! Regidx csp_rs1 : mword 64) 29) jj ↦ₘ be0 jj) -∗
       (pa_stk (m !!! Regidx csp_rs1 : mword 64) 30) ↦₈ w30 -∗
       (* the caller's own exit, handed BACK *)
       wp_next (CID0 := CIDs) true (proc_addr jx) (fun (CIDx : CpuId) =>
         ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
             ⌜callee_saved m mf⌝ -∗
             ⌜uptd_ext (pv_upt V) P'⌝ -∗
             sie_cap_gpr mf K b (proc_addr jx) -∗
             cpu_own 0 eb (proc_addr jx) b lks -∗
             trap_csrs_ext eb -∗
             cpu_claim_ext eb (proc_addr jx) -∗
             pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
             bslots bn 3 -∗
             sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
             sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
             sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
             bitmap_res gfs bmapstart cov logstart size used' -∗
             iref_slots SpecSysUnlink.sys_unlink_slots -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
             ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
             WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots bn 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
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
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpanic #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg
             Hsbb Hsbi Hsbs Hbmres #Hkenv #Hprocs Hir Hpriv Hseamk Hcont".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    iPoseProof (suli_000 with "Htext") as "Hi00".
    iPoseProof (suli_002 with "Htext") as "Hi02".
    iPoseProof (suli_004 with "Htext") as "Hi04".
    iPoseProof (suli_006 with "Htext") as "Hi06".
    iPoseProof (suli_008 with "Htext") as "Hi08".
    iPoseProof (suli_00c with "Htext") as "Hi0c".
    iPoseProof (suli_010 with "Htext") as "Hi10".
    iPoseProof (suli_012 with "Htext") as "Hi12".
    iPoseProof (suli_016 with "Htext") as "Hi16".
    iPoseProof (suli_01a with "Htext") as "Hi1a".
    iPoseProof (suli_01c with "Htext") as "Hi1c".
    iPoseProof (suli_020 with "Htext") as "Hi20".
    iPoseProof (suli_024 with "Htext") as "Hi24".
    iPoseProof (suli_028 with "Htext") as "Hi28".
    iPoseProof (suli_02c with "Htext") as "Hi2c".
    iPoseProof (suli_02e with "Htext") as "Hi2e".
    (* ===== +0x00 c.addi16sp sp,-240 ===== *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.sys_unlink)
              (mword_of_int 49 : mword 6) m K 30 b ltac:(exact K30)
              (su_push sp0) with "Hcg Hpc Hi00").
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
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SU + 0x2) : mword 64) 2
                    = mword_of_int (SU + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,224(sp) ===== *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SU + 0x4))
              (mword_of_int 28 : mword 6) Rs0 M1 (K - 30)%nat u2 b
              with "Hcg Hpc Hi04 Hf2").
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
              with "Hcg Hpc Hi06").
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
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi08").
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
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
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi10").
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
              (mword_of_int 2087182 : mword 21) M5 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x12) : mword 64) 4)]> M5).
    assert (Hjas : add_vec (mword_of_int (SU + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087182 : mword 21))
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
                with "Hcg Hpc Hi16").
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
                with "Hcg Hpc Hi1a Hf3").
      iIntros (CID11 Hq11) "Hcg Hpc Hf3".
      iEval (rgne; rewrite Hd3 Hass1) in "Hf3".
      assert (Hpp1c : add_vec_int (mword_of_int (SU + 0x1a) : mword 64) 2
                      = mword_of_int (SU + 0x1c)) by pcw.
      iEval (rewrite Hpp1c) in "Hpc".
      (* THE PROCESS BLOCK, OPENED for the walk. *)
      iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1) with "Hpriv")
        as "[Hpnc Href]".
      iDestruct (proc_priv_nocwd_cwd_pid gf (proc_addr jx) pid (upd_upt V P1) with "Hpnc")
        as "(Hcwd & Hpidq & Hpback)".
      iDestruct (cwd_ref_held with "Href") as "Hcwdref".
      iEval (cbn [upd_upt pv_cwd]) in "Hcwd".
      iEval (cbn [upd_upt pv_cwd]) in "Hcwdref".
      (* ===== +0x1c jal ra,begin_op ===== *)
      iApply (wp_jal_s_sconf (CID := CID11) (mword_of_int (SU + 0x1c)) Rra
                (mword_of_int 2092232 : mword 21) mas (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (N0 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x1c) : mword 64) 4)]> mas).
      assert (Hjbo : add_vec (mword_of_int (SU + 0x1c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092232 : mword 21))
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
                ltac:(exact Kbo) Hj Hgl (Hlb "log"%string)
                with "Hcg Hown [] [] Htext Hpc Hpanic Hlog Hpidq Hprocs").
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
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
                (mword_of_int 2091768 : mword 21) N2 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28").
      iIntros (CID16 Hq16) "Hcg Hpc".
      set (N3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x28) : mword 64) 4)]> N2).
      assert (Hjnp : add_vec (mword_of_int (SU + 0x28) : mword 64)
                       (sign_extend' 64 (mword_of_int 2091768 : mword 21))
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
                inodestart nib size dev used (pv_cwd V) pk1 bp1 bnm0
                MAXOPBLOCKS Sb0 pid (DfracOwn (1/4)) dqb dqs (DfracOwn 1)
                N3 (K - 30)%nat eb b lks
                ltac:(exact Knp) Hcdev Hcnib Hclog Hcist HdevR Hnib0 Hgeom
                Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hpcstr1
                (proj2 (su_len_range pk1 Hpk1))
                ltac:(exact (su_walk_need_closes _)) Hj Hgl Heb
                with "Hcg Hown Htext Hpc Hpanic Hbio Hlog Hkenv Hitab Hitinv
                      Hescrows Hslks Hireg Hprocs Hdev Hgeo Hdlk Hsbb Hsbi
                      Hbmres Hpidq Hcwd Hcwdref [Hbufp] [Hnm14] Hbsl Hir
                      HopS").
      { iEval (rewrite HN3a0). iExact "Hbufp". }
      { iEval (rewrite HN3a1). iExact "Hnm14". }
      iIntros (CID17 Hq17 mnp n1 used1 Sb1 ok1 nf dpv w1)
        "%Hcsnp Hcg Hown Hpc Hsbb Hsbi %Hused1 Hbmres Hpidq Hcwd Hcwdref
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
                with "Hcg Hpc Hi2c").
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
          "(%Hdpe & %Hkd & %Hdinumc & Hrefdp & #Hshotd)".
        assert (Hdpnz : dpv <> (zero_reg : mword 64))
          by (rewrite Hdpe; apply ientry_ne_zero; lia).
        iAssert (inode_held_ty dpv T_DIR) with "[Hrefdp]" as "Hhelddp".
        { iExists kd, qd, dinum, gyd. iSplitR; [done |]. iSplitR; [done |].
          iSplitR; [done |]. iFrame "Hrefdp". iExact "Hshotd". }
        iApply (wp_cbeqz_fall_s_sconf (CID := CID18)
                  (mword_of_int (SU + 0x2e)) (mword_of_int 90 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 N4 (K - 30)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HN4a0 (proj1 Hnp);
                        apply (proj2 (eq_vec_false_iff _ _)); exact Hdpnz)
                  with "Hcg Hpc Hi2e").
        iIntros (CID19 Hq19) "Hcg Hpc".
        assert (Hpp30 : add_vec_int (mword_of_int (SU + 0x2e) : mword 64) 2
                        = mword_of_int (SU + 0x30)) by pcw.
        iEval (rewrite Hpp30) in "Hpc".
        (* the process block, rebuilt whole for the seam *)
        iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
        iDestruct ("Hpback" $! (pv_cwd V) with "Hcwd Hpidq") as "Hpnc".
        iEval (rewrite su_upd_cwd_upt) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                     with "[Hpnc Href]") as "Hpriv";
          [iSplitL "Hpnc"; [iExact "Hpnc" | iExact "Href"] |].
        (* the path buffer, rejoined and renamed *)
        iDestruct (su_buf_join (pa_stk sp0 26) bp1 pk1 Hpk1
                     with "Hbufp Hbufpr") as "HbPj".
        iDestruct (su_bytes_name (pa_stk sp0 26) 128 with "HbPj") as (bpf) "HbPj".
        iDestruct (su_bytes_name (pa_stk sp0 8) 16 with "HbD") as (bd0) "HbD".
        iDestruct (su_bytes_name (pa_stk sp0 29) 16 with "HbE") as (be0) "HbE".
        iDestruct (cpu_own_transport CID17 CID19 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        rewrite (proj1 Hnp) in HN4regs.
        iApply ("Hseamk" $! CID19 N4 P1 n1 Sb1 used1 w1 dpv nf bpf bnm0 bd0 be0
                  u4 u5 u6 u27 u30 with "[%] [%] [%] [%] [%] [%] [%]
                  Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hbmres Hpriv
                  Hir1 Hhelddp HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2
                  HbPj H27 HbE H30 [Hcont]").
        { exact Hal. }
        { exact HN4regs. }
        { exact Hupt1. }
        { exact Hused1. }
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
                  with "Hcg Hpc Hi2e").
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
                  ltac:(exact Keo) K30 Kpop Hgeom Hj Hgl Hlkempty
                  ltac:(reflexivity) HN4sp HN4thr HN4s2 HN4s3 Hal
                  with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                        Hpidq Hprocs Hdev Hgeo Hdlk [HopS] Hf1 Hf2 Hf3 Hf4
                        Hf5 Hf6 HbD HbNj HbPj H27 HbE H30
                        [Hcont Hbsl Hsbb Hsbi Hsbs Hbmres Hir2 Hcwd Hpback
                         Hcwdref]").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        { rewrite /log_op. iExists Sb1. iExact "HopS". }
        iEval (rewrite /wp_next).
        iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                             Hpc Hpidq".
        iDestruct (cwd_ref_of_held with "Hcwdref") as "Href".
        iDestruct ("Hpback" $! (pv_cwd V) with "Hcwd Hpidq") as "Hpnc".
        iEval (rewrite su_upd_cwd_upt) in "Hpnc".
        iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                     with "[Hpnc Href]") as "Hpriv";
          [iSplitL "Hpnc"; [iExact "Hpnc" | iExact "Href"] |].
        iEval (rewrite -su_slots2) in "Hir2".
        iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf used1 P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                  Hbsl Hsbb Hsbi Hsbs Hbmres Hir2 Hpriv [%]").
        { exact Hcsf. }
        { exact Hupt1. }
        { left. rewrite Ha0f. reflexivity. }
    - (* ---------------- ARM A: argstr returned -1 ---------------- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID9) (mword_of_int (SU + 0x16))
                (mword_of_int 346 : mword 13) Ra0 mas (K - 30)%nat b
                ltac:(nz)
                ltac:(rgne; rewrite Hpr1; exact su_m1_neg)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16").
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
                      [Hcont Hown Hbsl Hsbb Hsbi Hsbs Hbmres Hir Hpriv]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CID9 CIDy 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used P1 with "[%] [%] Hcg Hown [] [] Hpc
                Hbsl Hsbb Hsbi Hsbs Hbmres Hir Hpriv [%]").
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
    sie_cap_gpr M k b pp -∗
    ⌜(8 <= uint (M !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds _ (trap_res b + k)%nat with "Hstk").
    destruct b; unfold trap_res, kv_frame_slots; lia.
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
      (size : Z) (dev : mword 32) (used : gset Z)
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
    sie_cap_gpr M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ pc_is (mword_of_int (SU + 0x15a)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart kk -∗
    ireg_inv gi gfs inodestart nib -∗
    is_sleeplock_gen gil gisl (i_lock (ientry kk)) "inode"%string
                     (ic_tok cn kk) (slh_tok (icfg_isl kk)) -∗
    sleeplocked_q gisl s -∗
    sl_pid (i_lock (ientry kk)) ↦₄ pidv -∗
    ic_deposit cn kk (DepShr s dev inum gy) -∗
    i_dev (ientry kk) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry kk) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry kk) ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart kk inum dn bm -∗
    ity_shot gy (di_type dn) -∗
    inode_ref_short kk (qi + s)%Qp qi dev inum -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    p_pid (proc_addr jx) ↦₄{DfracOwn (1/4)} pidv -∗
    (p_pid (proc_addr jx) ↦₄{DfracOwn (1/4)} pidv -∗
       proc_priv gf (proc_addr jx) pidv (upd_upt V P1)) -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    iref_slots 1 -∗
    log_op g u -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    (pa_stk sp0 5) ↦₈ w5 -∗
    (pa_stk sp0 6) ↦₈ w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nfx jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ bp jj) -∗
    (pa_stk sp0 27) ↦₈ w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ be jj) -∗
    (pa_stk sp0 30) ↦₈ w30 -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots bn 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          iref_slots SpecSysUnlink.sys_unlink_slots -∗
          proc_priv gf (proc_addr jx) pidv (upd_upt V P') -∗
          ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hiblk
           Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr HMs1 HMs2
           HMs3 Hal Heb Hupt1.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hbio #Hlog Hseam Hgen #Hitab #Hitinv
             #Hesck #Hireg #Hslkk Hslkd Hslpid Hdep Hidev Hiinum Hivalid Hload
             #Hshot Hkeep Hsbb Hsbi Hsbs Hbmres Hpidq Hpre #Hprocs #Hdev #Hgeo
             #Hdlk Hbsl Hir Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27
             HbE H30 Hcont".
    iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nfx with "Hnm14 Hnm2") as "HbNj".
    iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
    iApply (Tails.su_tail_bad (CID0 := CID0) gs jx gl gu gd gk pd pav pu bn g
              gfs gi cn gtl gil gisl cov logstart bmapstart inodestart nib size
              dev used kk qi s gy inum dn bm u pidv (DfracOwn (1/4)) dqb dqs
              m M sp0 K eb b lks w4 w5 w6 w27 w30 bd bnf bp be
              HKup HKeo HK30 Kpop Hkk Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
              Hiblk Hiblog Hinb Hcovb Hiu Hj Hgl Hlkempty Hsp0 HMsp HMthr
              HMs1 HMs2 HMs3 Hal
              with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen Hitab
                    Hitinv Hesck Hireg Hslkk Hslkd Hslpid Hdep Hidev Hiinum
                    Hivalid Hload Hshot Hkeep Hsbb Hsbi Hbmres Hpidq Hprocs
                    Hdev Hgeo Hdlk Hbsl Hop Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj
                    HbP H27 HbE H30 [Hcont Hpre Hsbs Hir]").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDy) "%Hqy". iIntros (mf used') "%Hcsf %Ha0f Hcg Hown Htce Hcce
                                     Hpc Hpidq Hsbb Hsbi Hbmres Hbsl Hislot".
    iDestruct ("Hpre" with "Hpidq") as "Hpriv".
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf used' P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
              Hbsl Hsbb Hsbi Hsbs Hbmres [Hir Hislot] Hpriv [%]").
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
      (size : Z) (dev : mword 32) (used1 : gset Z)
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
    sie_cap_gpr M (K - 30) b (proc_addr jx) -∗
    cpu_own 0 eb (proc_addr jx) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (SU + 0x30)) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    bslots bn 3 -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used1 -∗
    kalloc_env ga None -∗
    procs_inv gs -∗
    iref_slots 1 -∗
    proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
    inode_held_ty dpv T_DIR -∗
    log_opS g n1 Sb1 -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
    (pa_stk sp0 4) ↦₈ w4 -∗
    (pa_stk sp0 5) ↦₈ w5 -∗
    (pa_stk sp0 6) ↦₈ w6 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ bd jj) -∗
    ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nf jj) -∗
    ([∗ list] jj ∈ seq 0 2,
       pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ bnm0 (14 + jj)%nat) -∗
    ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ bp jj) -∗
    (pa_stk sp0 27) ↦₈ w27 -∗
    ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ be jj) -∗
    (pa_stk sp0 30) ↦₈ w30 -∗
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
       ⌜dir_ok icfg_nib dnd datd⌝ -∗
       ⌜dir_dots_ix (bv_unsigned dinum) dnd datd⌝ -∗
       ⌜dir_orphan_clean dnd datd⌝ -∗
       ⌜bname 14 nf <> dot_name⌝ -∗
       ⌜bname 14 nf <> dotdot_name⌝ -∗
       ⌜dir_first datd (dir_nrec (bv_unsigned (di_size dnd)))
                  (bname 14 nf) = Some kk⌝ -∗
       sie_cap_gpr M2 (K - 30) b (proc_addr jx) -∗
       cpu_own 0 eb (proc_addr jx) b lks -∗
       pc_is (mword_of_int (SU + 0x72)) -∗
       fs_crash_seam cov logstart -∗
       gen_cert -∗
       bslots bn 3 -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
       bitmap_res gfs bmapstart cov logstart size used1 -∗
       proc_priv gf (proc_addr jx) pid (upd_upt V P1) -∗
       (* ---- [dp], LOCKED and OPEN ---- *)
       is_sleeplock_gen gild gisld (i_lock (ientry kd)) "inode"%string
                        (ic_tok cn kd) (slh_tok (icfg_isl kd)) -∗
       sleeplocked_q gisld sd -∗
       sl_pid (i_lock (ientry kd)) ↦₄ pid -∗
       ic_deposit cn kd (DepShr sd dev dinum gyd) -∗
       i_dev (ientry kd) ↦₄{DfracOwn (1/2)} dev -∗
       i_inum (ientry kd) ↦₄{DfracOwn (1/2)} dinum -∗
       i_valid (ientry kd) ↦₄ valid_word true -∗
       dir_links (bv_unsigned dinum) dnd datd -∗
       dinode_at gi dinum dnd -∗
       inode_meta (ientry kd) dnd -∗
       inode_addrs (ientry kd) (bm_cells bmd) -∗
       ind_res gfs bmd -∗
       inode_blocks gfs bmd datd -∗
       ity_shot gyd (di_type dnd) -∗
       inode_ref_short kd (qdi + sd)%Qp qdi dev dinum -∗
       (* ---- [ip], REFERENCED (dirlookup's iget) ---- *)
       inode_ref ks qs dev
         (zero_extend' 32 (dir_inum datd kk : mword 16) : mword 32) -∗
       log_opS g n1 Sb1 -∗
       (* ---- the frame, with slot 4 filled and slot 27 SPLIT ---- *)
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ w5 -∗
       (pa_stk sp0 6) ↦₈ w6 -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 8) jj ↦ₘ bd jj) -∗
       ([∗ list] jj ∈ seq 0 14, pa_add (pa_stk sp0 10) jj ↦ₘ nf jj) -∗
       ([∗ list] jj ∈ seq 0 2,
          pa_add (pa_add (pa_stk sp0 10) 14) jj ↦ₘ bnm0 (14 + jj)%nat) -∗
       ([∗ list] jj ∈ seq 0 128, pa_add (pa_stk sp0 26) jj ↦ₘ bp jj) -∗
       (pa_stk sp0 27) ↦₄ lo -∗
       (pa_add (pa_stk sp0 27) 4) ↦₄
         (mword_of_int (Z.of_nat (16 * kk)) : mword 32) -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 29) jj ↦ₘ be jj) -∗
       (pa_stk sp0 30) ↦₈ w30 -∗
       (* the caller's own exit, handed BACK *)
       wp_next (CID0 := CIDs) true (proc_addr jx) (fun (CIDx : CpuId) =>
         ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
             ⌜callee_saved m mf⌝ -∗
             ⌜uptd_ext (pv_upt V) P'⌝ -∗
             sie_cap_gpr mf K b (proc_addr jx) -∗
             cpu_own 0 eb (proc_addr jx) b lks -∗
             trap_csrs_ext eb -∗
             cpu_claim_ext eb (proc_addr jx) -∗
             pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
             bslots bn 3 -∗
             sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
             sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
             sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
             bitmap_res gfs bmapstart cov logstart size used' -∗
             iref_slots SpecSysUnlink.sys_unlink_slots -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P') -∗
             ⌜sys_unlink_ret (mf !!! Regidx Ra0 : mword 64)⌝ -∗
             WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
          ⌜callee_saved m mf⌝ -∗
          ⌜uptd_ext (pv_upt V) P'⌝ -∗
          sie_cap_gpr mf K b (proc_addr jx) -∗
          cpu_own 0 eb (proc_addr jx) b lks -∗
          trap_csrs_ext eb -∗
          cpu_claim_ext eb (proc_addr jx) -∗
          pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
          bslots bn 3 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
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
    iIntros "Hcg Hown #Htext #Hdata Hpc #Hpanic #Hbio #Hlog Hseam Hgen
             #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks #Hireg
             Hsbb Hsbi Hsbs Hbmres #Hkenv #Hprocs Hir Hpriv Hheld HopS
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
      "(%Hdpe & %Hkd & %Hdinumc & Hrefdp & #Hshotd)".
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
    iDestruct (su_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
    (* the process block, opened for the callees' pid fraction *)
    iDestruct (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpriv") as "[Hpnc Href]".
    iDestruct (proc_priv_nocwd_cwd_pid gf (proc_addr jx) pid (upd_upt V P1)
                 with "Hpnc") as "(Hcwd & Hpidq & Hpback)".
    (* THE CLOSER, built once: every arm below hands the pid quarter back
       and wants the block whole, and nothing between here and the seam
       touches the cwd half. *)
    iAssert (p_pid (proc_addr jx) ↦₄{DfracOwn (1/4)} pid -∗
             proc_priv gf (proc_addr jx) pid (upd_upt V P1))%I
      with "[Hcwd Hpback Href]" as "Hpre".
    { iIntros "Hpidq".
      iDestruct ("Hpback" $! (pv_cwd V) with "Hcwd Hpidq") as "Hpnc".
      iEval (rewrite su_upd_cwd_upt) in "Hpnc".
      iApply (proc_priv_split_cwd gf (proc_addr jx) pid (upd_upt V P1)).
      iSplitL "Hpnc"; [iExact "Hpnc" | iExact "Href"]. }
    (* the register facts the whole block rides on *)
    assert (HMs1 : (M !!! Regidx Rs1 : mword 64) = dpv)
      by exact (su_regs_s1 _ _ _ _ _ _ Hregs).
    assert (HMsp : su_sp sp0 M) by exact (su_regs_sp _ _ _ _ _ _ Hregs).
    iPoseProof (suli_030 with "Htext") as "Hi30".
    iPoseProof (suli_034 with "Htext") as "Hi34".
    iPoseProof (suli_038 with "Htext") as "Hi38".
    iPoseProof (suli_03c with "Htext") as "Hi3c".
    iPoseProof (suli_040 with "Htext") as "Hi40".
    iPoseProof (suli_044 with "Htext") as "Hi44".
    (* ===== +0x30 jal ra,ilock ===== *)
    iApply (wp_jal_s_sconf (CID := CID0) (mword_of_int (SU + 0x30)) Rra
              (mword_of_int 2089618 : mword 21) M (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi30").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x30) : mword 64) 4)]> M).
    assert (Hjil : add_vec (mword_of_int (SU + 0x30) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089618 : mword 21))
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
              gyd dev dinum pid (DfracOwn (1/4)) dqs R0 (K - 30)%nat eb b lks
              ltac:(exact Kil) Hkd Hgeom Hist0 Hdiblk Hdinb Hj Hgl HR0a0
              (Hlb "bcache"%string)
              with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hitinv Hescd Hireg
                    Hslkd0 Hshrd Hsbi Hpidq Hprocs Hdev Hgeo Hdlk Hbs1").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID2 Hq2 mil dnd bmd fld)
      "%Hcsil Hcg Hown _ _ Hpc Hpidq Hsbi Hbs1 Hslkdd Hslpid Hdep
       Hidev Hiinum Hivalid Hload #Hshotl %Hfld".
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi34").
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
              (mword_of_int 1656 : mword 12) R1 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi38").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (R1 !!! Regidx Ra1)
                     (sign_extend' 64 (mword_of_int 1656 : mword 12)))]> R1).
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3c").
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
              (mword_of_int 2091020 : mword 21) R3 (K - 30)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi40").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SU + 0x40) : mword 64) 4)]> R3).
    assert (Hjnc1 : add_vec (mword_of_int (SU + 0x40) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091020 : mword 21))
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
    iApply (Namecmp.wp_namecmp_sconf (CID := CID6) R4 nf su_dot_f
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
                with "Hcg Hpc Hi44").
      iIntros (CID8 Hq8). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgbad1) in "Hpc".
      iDestruct (cpu_own_transport CID7 CID8 0 eb (proc_addr jx) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (su_w2_bad (CID0 := CID8) gf gs jx gl gu gd gk pd pav pu bn g gfs
                gi cn gtl gild gisld cov logstart bmapstart inodestart nib size
                dev used1 kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd n1 pid
                dqb dqs dqbs V P1 m mn1 sp0 K eb b lks w4 w5 w6 w27 w30
                bd nf bnm0 bp be
                Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                (su_regs_sp _ _ _ _ _ _ Hn1regs) (su_regs_thr _ _ _ _ _ _ Hn1regs)
                ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn1regs); exact Hdpe)
                (su_regs_s2 _ _ _ _ _ _ Hn1regs)
                (su_regs_s3 _ _ _ _ _ _ Hn1regs) Hal Heb Hupt1
                with "Hcg Hown Htext Hpc Hpanic Hbio Hlog Hseam Hgen Hitab
                      Hitinv Hescd Hireg Hslkd0 Hslkdd Hslpid Hdep Hidev
                      Hiinum Hivalid Hload Hshotl Hkeepd Hsbb Hsbi Hsbs
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
                with "Hcg Hpc Hi44").
      iIntros (CID8 Hq8) "Hcg Hpc".
      assert (Hpp48 : add_vec_int (mword_of_int (SU + 0x44) : mword 64) 4
                      = mword_of_int (SU + 0x48)) by pcw.
      iEval (rewrite Hpp48) in "Hpc".
      iClear "Hi30 Hi34 Hi38 Hi3c Hi40 Hi44".
      iPoseProof (suli_048 with "Htext") as "Hi48".
      iPoseProof (suli_04c with "Htext") as "Hi4c".
      iPoseProof (suli_050 with "Htext") as "Hi50".
      iPoseProof (suli_054 with "Htext") as "Hi54".
      iPoseProof (suli_058 with "Htext") as "Hi58".
      (* ===== +0x48 auipc a1,2 ===== *)
      iApply (wp_auipc_s_sconf (CID := CID8) (mword_of_int (SU + 0x48)) Ra1
                (mword_of_int 2 : mword 20) mn1 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi48").
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
                (mword_of_int 1644 : mword 12) R5 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4c").
      iIntros (CID10 Hq10) "Hcg Hpc".
      set (R6 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (R5 !!! Regidx Ra1)
                       (sign_extend' 64 (mword_of_int 1644 : mword 12)))]> R5).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi50").
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
                (mword_of_int 2091000 : mword 21) R7 (K - 30)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (R8 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (SU + 0x54) : mword 64) 4)]> R7).
      assert (Hjnc2 : add_vec (mword_of_int (SU + 0x54) : mword 64)
                        (sign_extend' 64 (mword_of_int 2091000 : mword 21))
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
      iApply (Namecmp.wp_namecmp_sconf (CID := CID12) R8 nf su_dotdot_f
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
                  with "Hcg Hpc Hi58").
        iIntros (CID14 Hq14). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgbad2) in "Hpc".
        iDestruct (cpu_own_transport CID13 CID14 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID14)
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (su_w2_bad (CID0 := CID14) gf gs jx gl gu gd gk pd pav pu bn g
                  gfs gi cn gtl gild gisld cov logstart bmapstart inodestart
                  nib size dev used1 kd (qd/2)%Qp (qd/2)%Qp gyd dinum dnd bmd
                  n1 pid dqb dqs dqbs V P1 m mn2 sp0 K eb b lks
                  w4 w5 w6 w27 w30 bd nf bnm0 bp be
                  Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0
                  Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty Hsp0
                  (su_regs_sp _ _ _ _ _ _ Hn2regs)
                  (su_regs_thr _ _ _ _ _ _ Hn2regs)
                  ltac:(rewrite (su_regs_s1 _ _ _ _ _ _ Hn2regs); exact Hdpe)
                  (su_regs_s2 _ _ _ _ _ _ Hn2regs)
                  (su_regs_s3 _ _ _ _ _ _ Hn2regs) Hal Heb Hupt1
                  with "Hcg Hown Htext Hpc Hpanic Hbio Hlog Hseam Hgen Hitab
                        Hitinv Hescd Hireg Hslkd0 Hslkdd Hslpid Hdep Hidev
                        Hiinum Hivalid Hload Hshotl Hkeepd Hsbb Hsbi Hsbs
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
                  with "Hcg Hpc Hi58").
        iIntros (CID14 Hq14) "Hcg Hpc".
        assert (Hpp5c : add_vec_int (mword_of_int (SU + 0x58) : mword 64) 4
                        = mword_of_int (SU + 0x5c)) by pcw.
        iEval (rewrite Hpp5c) in "Hpc".
        iClear "Hi48 Hi4c Hi50 Hi54 Hi58".
        iPoseProof (suli_05c with "Htext") as "Hi5c".
        iPoseProof (suli_05e with "Htext") as "Hi5e".
        iPoseProof (suli_062 with "Htext") as "Hi62".
        iPoseProof (suli_066 with "Htext") as "Hi66".
        iPoseProof (suli_068 with "Htext") as "Hi68".
        iPoseProof (suli_06c with "Htext") as "Hi6c".
        iPoseProof (suli_06e with "Htext") as "Hi6e".
        (* ===== +0x5c c.sdsp s2,208(sp) -- slot 4, saved LATER ===== *)
        assert (Hd4 : add_vec (mn2 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64
                           (concat_vec (mword_of_int 26 : mword 6) ('b"000")))
                      = pa_stk sp0 4)
          by (rewrite (su_regs_sp _ _ _ _ _ _ Hn2regs); apply su_frm4).
        iEval (rewrite -Hd4) in "Hf4".
        iApply (wp_csdsp_s_sconf (CID := CID14) (mword_of_int (SU + 0x5c))
                  (mword_of_int 26 : mword 6) Rs2 mn2 (K - 30)%nat w4 b
                  with "Hcg Hpc Hi5c Hf4").
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
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
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
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi62").
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
                  with "Hcg Hpc Hi66").
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
                  (mword_of_int 2091002 : mword 21) R11 (K - 30)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi68").
        iIntros (CID19 Hq19) "Hcg Hpc".
        set (R12 := <[Regidx Rra := regval_into_reg
                       (add_vec_int (mword_of_int (SU + 0x68) : mword 64) 4)]> R11).
        assert (Hjdl : add_vec (mword_of_int (SU + 0x68) : mword 64)
                         (sign_extend' 64 (mword_of_int 2091002 : mword 21))
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
        iDestruct "Hload" as (datd)
          "(%Hiok & %Hdok & %Hddix & %Hdoc & Hdlnk & Hdiat & Hmeta & Haddrs &
            Hind & Hblocks)".
        pose proof Hiok as Hiok0.
        destruct Hiok as (Hbmwf & Hbmcv & Hbmc & Htynz & Hszcap & Hiokrest).
        assert (Hinums : dir_inums_ok datd
                           (dir_nrec (bv_unsigned (di_size dnd))) nib)
          by (rewrite Hcnib; exact (Hdok Htydz)).
        iAssert (iref_slot) with "[Hir]" as "Hislot".
        { rewrite /iref_slot. iExact "Hir". }
        iDestruct (cpu_own_transport CID13 CID19 0 eb (proc_addr jx) b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Dirlookup.wp_dirlookup_sconf (CID := CID19) gs jx gl gu gd gk
                  pd pav pu bn gfs gi cn gtl ga gf cov logstart nib dev
                  (ientry kd) bmd datd dnd nf true (word_hi w27) pid
                  (DfracOwn (1/4)) (DfracOwn (1/2)) (DfracOwn 1)
                  R12 (K - 30)%nat eb b lks
                  ltac:(exact Kdl) Htydir Hgeom Hbmwf Hbmcv Hszcap Hinums
                  Hj Hgl HR12a0
                  ltac:(cbn [negb]; apply (proj2 (eq_vec_false_iff _ _));
                        exact Hoffnz)
                  Heb (Hlb "bcache"%string)
                  with "Hcg Hown Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta
                        [Haddrs Hind] Hblocks [Hnm14] [H27hi] Hpidq Hprocs
                        Hdev Hgeo Hdlk Hbs1 Hitab Hitinv Hescrows Hislot").
        { rewrite /inode_map. iFrame "Haddrs Hind". }
        { iEval (rewrite HR12a1). iExact "Hnm14". }
        { cbn [negb]. iEval (rewrite HR12a2). iExact "H27hi". }
        iIntros (CID20 Hq20 mdl found kk kslot qs)
          "%Hcsdl Hcg Hown Hpc Hidev Hmeta Hmap Hblocks Hnm14 Hpidq Hbs1 Hres".
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
          iDestruct "Hres" as "((%Hfst & %Hkslot & %Hdla0) & Hchild & H27hi)".
          iEval (rewrite HR12a2) in "H27hi".
          (* ===== +0x6c c.mv s2,a0 -- s2 = ip ===== *)
          iApply (wp_cmv_s_sconf (CID := CID20) (mword_of_int (SU + 0x6c))
                    Rs2 Ra0 mdl (K - 30)%nat b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc Hi6c").
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
                    with "Hcg Hpc Hi6e").
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
                    with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcg Hown Hpc Hseam Hgen [Hbs1 Hbs2] Hsbb Hsbi Hsbs Hbmres
                    Hpriv Hslkd0 Hslkdd Hslpid Hdep Hidev Hiinum Hivalid
                    Hdlnk Hdiat Hmeta Haddrs Hind Hblocks Hshotl Hkeepd
                    Hchild HopS Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP
                    H27lo H27hi HbE H30 [Hcont]").
          { exact HR13regs. }
          { exact Hkd. }
          { exact Hkslot. }
          { exact Hdinb. }
          { exact Htydir. }
          { exact Hiok0. }
          { exact Hdok. }
          { exact Hddix. }
          { exact Hdoc. }
          { exact Hnotdot. }
          { exact Hnotdd. }
          { exact Hfst. }
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
                    with "Hcg Hpc Hi6c").
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
                    with "Hcg Hpc Hi6e").
          iIntros (CID22 Hq22). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgargd) in "Hpc".
          (* the buffers and the bundle, put back for the tail *)
          iDestruct (su_nm_join (pa_stk sp0 10) bnm0 nf with "Hnm14 Hnm2")
            as "HbNj".
          iDestruct (su_bytes_name (pa_stk sp0 10) 16 with "HbNj") as (bnf) "HbNj".
          iDestruct (su_off_join sp0 (word_lo w27) (word_hi w27) Hal27
                       with "H27lo H27hi") as "H27".
          iAssert (ic_loaded gfs gi cov logstart kd dinum dnd bmd)
            with "[Hdlnk Hdiat Hmeta Haddrs Hind Hblocks]" as "Hload".
          { rewrite /ic_loaded. iExists datd. iFrame "Hdlnk Hdiat Hmeta
              Haddrs Hind Hblocks". iPureIntro. split_and!;
              [ exact Hiok0 | exact Hdok | exact Hddix | exact Hdoc ]. }
          iDestruct (cpu_own_transport CID20 CID22 0 eb (proc_addr jx) b
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iApply (Tails.su_tail_d (CID0 := CID22) gs jx gl gu gd gk pd pav pu
                    bn g gfs gi cn gtl gild gisld cov logstart bmapstart
                    inodestart nib size dev used1 kd (qd/2)%Qp (qd/2)%Qp gyd
                    dinum dnd bmd n1 pid (DfracOwn (1/4)) dqb dqs
                    m R13 sp0 K eb b lks w5 w6 (word_of_words (word_lo w27)
                    (word_hi w27)) w30 bd bnf bp be
                    Kiup Keo K30 Kpop Hkd Hgeom Hsize Hbm0 Hbmcov Hbmlog
                    Hist0 Hdiblk Hdiblog Hdinb Hcovb Hiu Hj Hgl Hlkempty
                    Hsp0 HR13sp HR13thr HR13s1 HR13s3 Hal
                    with "Hcg Hown [] [] Htext Hpc Hpanic Hbio Hlog Hseam Hgen
                          Hitab Hitinv Hescd Hireg Hslkd0 Hslkdd Hslpid Hdep
                          Hidev Hiinum Hivalid Hload Hshotl Hkeepd Hsbb Hsbi
                          Hbmres Hpidq Hprocs Hdev Hgeo Hdlk [Hbs1 Hbs2]
                          [HopS] Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD HbNj HbP H27
                          HbE H30
                          [Hcont Hpre Hsbs Hislot]").
          { rewrite Heb /trap_csrs_ext. done. }
          { rewrite Heb /cpu_claim_ext. done. }
          { iApply su_bs3. iFrame "Hbs1 Hbs2". }
          { rewrite /log_op. iExists Sb1. iExact "HopS". }
          iEval (rewrite /wp_next).
          iIntros (CIDy) "%Hqy". iIntros (mf used') "%Hcsf %Ha0f Hcg Hown Htce
                                           Hcce Hpc Hpidq Hsbb Hsbi Hbmres
                                           Hbsl Hislot2".
          iDestruct ("Hpre" with "Hpidq") as "Hpriv".
          iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
          iApply ("Hcont" $! mf used' P1 with "[%] [%] Hcg Hown Htce Hcce Hpc
                    Hbsl Hsbb Hsbi Hsbs Hbmres [Hislot Hislot2] Hpriv [%]").
          { exact Hcsf. }
          { exact Hupt1. }
          { rewrite su_slots2. change 2%nat with (1 + 1)%nat.
            rewrite iref_slots_op. rewrite /iref_slot. iFrame. }
          { left. rewrite Ha0f. reflexivity. }
  Qed.

End ProofSysUnlinkBody.

End SysUnlinkProof.
