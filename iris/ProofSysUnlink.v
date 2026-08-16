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
From Kernel Require KernelSyms.
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

End ProofSysUnlinkBody.

End SysUnlinkProof.
