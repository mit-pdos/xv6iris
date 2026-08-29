(* UProofInitLib.v -- init's EIGHT SYSCALL STUBS and [putc], proved.
   (claude-notes/projects/user-init.md; the contracts are USpecInit.v.)

   The stubs are eight instances of UmodeStub.v's protocol-generic
   [wp_uv_stub_head] / [wp_uv_stub_tail] pair: each is [li a7,N; ecall;
   ret] and differs only in the address, the number, and which arm of
   [xv6_init_protocol] the ecall is fed.  [exit] has no tail -- its arm is
   [emp] and it does not come back.

   [putc] is the bottom of the printf cone and the only function in init
   that writes memory outside a spill: it stores its [char] argument into
   its own frame at [s0-17] and hands that one byte to [write].  That the
   byte handed over is the byte the caller passed is what discharges the
   [W] observation. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo
               UmodeInitIo UmodeFetch.
Require Import WpUmodeLeaf WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame UmodeStub.
Require Import UCodeInit USpecInit.
Require User.InitSyms User.InitInstrs User.InitData.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Import ListNotations.
Set Printing Depth 40.


(* ===================================================================== *)
(* §0 Two image helpers.                                                  *)
(*                                                                        *)
(* HOIST CANDIDATES, both beside [uM_only] in UmodeAbi.v / [uM_store] in   *)
(* WpUmodeStore.v: [uM_only_store8] (UProofEcho.v) is the k = 8 case of    *)
(* the first, and the second is what carries a spilled word across the     *)
(* stores that follow it.                                                 *)
(* ===================================================================== *)

Lemma uM_only_storek (M : gmap Z (bv 8)) (a k lo n : Z) (v : mword 64) :
  0 <= k -> lo <= a -> a + k <= lo + n -> uM_only M (uM_store M a k v) lo n.
Proof.
  intros Hk H1 H2. split.
  - intros key Hkey. exact (uM_store_is_Some M a k v key Hkey).
  - intros key Hkey. apply uM_store_lookup_ne.
    intros j Hj. pose proof (Nat2Z.is_nonneg j).
    assert (Z.of_nat j < k) by lia. lia.
Qed.

Lemma uM_only_store8 (M : gmap Z (bv 8)) (a lo n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n -> uM_only M (uM_store8 M a v) lo n.
Proof. intros H1 H2. exact (uM_only_storek M a 8 lo n v ltac:(lia) H1 H2). Qed.

(* a byte window survives any image change whose own window misses it *)
Lemma uM_bytes_only {n : N} (M M' : gmap Z (bv 8)) (a lo len : Z) (k : nat)
    (w : bv n) :
  uM_only M M' lo len ->
  (a + Z.of_nat k <= lo \/ lo + len <= a) ->
  uM_bytes M a k w -> uM_bytes M' a k w.
Proof.
  intros [_ E] Hdisj Hb j Hj.
  rewrite (E (a + Z.of_nat j) ltac:(pose proof (Nat2Z.is_nonneg j); lia)).
  exact (Hb j Hj).
Qed.

Section UProofInitLib.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  (* user code runs AS the thread: ambient context, and a
     reschedule moves the hart, never the context. *)
  Context `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).
  Context (W : Z -> list (bv 8) -> iProp Σ).

  Local Notation Pinit := (xv6_init_protocol C pt Q W).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §1 THE STUBS.                                                        *)
  (* ------------------------------------------------------------------- *)

  (* dup, fork *)
  Lemma wp_init_pureret_gen (CIDp : CpuId) (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :
    uinstr pt M (mword_of_int entry) true
      (C_LI (mword_of_int n : mword 6, Regidx a7_idx)) ->
    uinstr pt M (mword_of_int (entry + 2)) false (ECALL tt) ->
    uinstr pt M (mword_of_int (entry + 6)) true (C_JR (Regidx ra_idx)) ->
    (mword_of_int n : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int n : mword 6))) ->
    add_vec_int (mword_of_int entry : mword 64) 2 = mword_of_int (entry + 2) ->
    add_vec_int (mword_of_int (entry + 2) : mword 64) 4 = mword_of_int (entry + 6) ->
    uint (mword_of_int n : mword 64) = n ->
    (forall (g : regfile) (va : mword 64) (Mx : gmap Z (bv 8)),
       Pinit n g va Mx = uinit_arm_pureret C pt g va Mx) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uv_cap_gpr (CID := CIDp) C pt Pinit M m -∗
    pc_is (CID := CIDp) (mword_of_int entry) -∗
    (∀ (CID : CpuId) (ret : mword 64),
       uv_cap_gpr (CID := CID) C pt Pinit M
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui1 Hui2 Hui3 Hwv Hpc2 Hpc6 Hn Hsem Hret2.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_stub_head C pt CIDp Pinit entry n M m Hui1 Hui2 Hwv Hpc2 Hn
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    rewrite Hsem. rewrite /uinit_arm_pureret /usys_ret.
    iIntros (CID2 ret) "Hrun".
    iEval (rewrite Hpc6) in "Hrun".
    iApply (wp_uv_stub_tail C pt CID2 Pinit entry n M m ret Hui3 Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* open, mknod *)
  Lemma wp_init_strret_gen (CIDp : CpuId) (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :
    uinstr pt M (mword_of_int entry) true
      (C_LI (mword_of_int n : mword 6, Regidx a7_idx)) ->
    uinstr pt M (mword_of_int (entry + 2)) false (ECALL tt) ->
    uinstr pt M (mword_of_int (entry + 6)) true (C_JR (Regidx ra_idx)) ->
    (mword_of_int n : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int n : mword 6))) ->
    add_vec_int (mword_of_int entry : mword 64) 2 = mword_of_int (entry + 2) ->
    add_vec_int (mword_of_int (entry + 2) : mword 64) 4 = mword_of_int (entry + 6) ->
    uint (mword_of_int n : mword 64) = n ->
    (forall (g : regfile) (va : mword 64) (Mx : gmap Z (bv 8)),
       Pinit n g va Mx = uinit_arm_strret C pt g va Mx) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uio_str_arg pt M (uint (m !!! Regidx a0_idx)) ->
    uv_cap_gpr (CID := CIDp) C pt Pinit M m -∗
    pc_is (CID := CIDp) (mword_of_int entry) -∗
    (∀ (CID : CpuId) (ret : mword 64),
       uv_cap_gpr (CID := CID) C pt Pinit M
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui1 Hui2 Hui3 Hwv Hpc2 Hpc6 Hn Hsem Hret2 Hpath.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_stub_head C pt CIDp Pinit entry n M m Hui1 Hui2 Hwv Hpc2 Hn
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    rewrite Hsem. rewrite /uinit_arm_strret.
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int n : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    iSplitR. { iPureIntro. rewrite Ha0. exact Hpath. }
    rewrite /usys_ret.
    iIntros (CID2 ret) "Hrun".
    iEval (rewrite Hpc6) in "Hrun".
    iApply (wp_uv_stub_tail C pt CID2 Pinit entry n M m ret Hui3 Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* --- the instances -------------------------------------------------- *)

  Lemma wp_init_dup (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_pureret_body (CID := CIDp) C pt Q W InitSyms.dup SYS_dup M m.
  Proof.
    intros Hpre Hsem. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hpc Hcont".
    iEval (change (mword_of_int InitSyms.dup : mword 64)
             with (mword_of_int 0x3ea : mword 64)) in "Hpc".
    iApply (wp_init_pureret_gen CIDp 0x3ea SYS_dup M m
              (ui_init_3ea pt M (ilay_text pt Hlay) Htext)
              (ui_init_3ec pt M (ilay_text pt Hlay) Htext)
              (ui_init_3f0 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hsem Hret2
              with "Hcg Hpc Hcont").
  Qed.

  Lemma wp_init_fork (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_pureret_body (CID := CIDp) C pt Q W InitSyms.fork SYS_fork M m.
  Proof.
    intros Hpre Hsem. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hpc Hcont".
    iEval (change (mword_of_int InitSyms.fork : mword 64)
             with (mword_of_int 0x36a : mword 64)) in "Hpc".
    iApply (wp_init_pureret_gen CIDp 0x36a SYS_fork M m
              (ui_init_36a pt M (ilay_text pt Hlay) Htext)
              (ui_init_36c pt M (ilay_text pt Hlay) Htext)
              (ui_init_370 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hsem Hret2
              with "Hcg Hpc Hcont").
  Qed.

  Lemma wp_init_open (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_strret_body (CID := CIDp) C pt Q W InitSyms.open SYS_open M m.
  Proof.
    intros Hpre Hsem Hpath. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hpc Hcont".
    iEval (change (mword_of_int InitSyms.open : mword 64)
             with (mword_of_int 0x3b2 : mword 64)) in "Hpc".
    iApply (wp_init_strret_gen CIDp 0x3b2 SYS_open M m
              (ui_init_3b2 pt M (ilay_text pt Hlay) Htext)
              (ui_init_3b4 pt M (ilay_text pt Hlay) Htext)
              (ui_init_3b8 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hsem Hret2 Hpath
              with "Hcg Hpc Hcont").
  Qed.

  Lemma wp_init_mknod (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_strret_body (CID := CIDp) C pt Q W InitSyms.mknod SYS_mknod M m.
  Proof.
    intros Hpre Hsem Hpath. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hpc Hcont".
    iEval (change (mword_of_int InitSyms.mknod : mword 64)
             with (mword_of_int 0x3ba : mword 64)) in "Hpc".
    iApply (wp_init_strret_gen CIDp 0x3ba SYS_mknod M m
              (ui_init_3ba pt M (ilay_text pt Hlay) Htext)
              (ui_init_3bc pt M (ilay_text pt Hlay) Htext)
              (ui_init_3c0 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hsem Hret2 Hpath
              with "Hcg Hpc Hcont").
  Qed.

  Lemma wp_init_wait (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_wait_body (CID := CIDp) C pt Q W M m.
  Proof.
    intros Hpre Hnull. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hpc Hcont".
    iEval (change (mword_of_int InitSyms.wait : mword 64)
             with (mword_of_int 0x37a : mword 64)) in "Hpc".
    iApply (wp_uv_stub_head C pt CIDp Pinit 0x37a SYS_wait M m
              (ui_init_37a pt M (ilay_text pt Hlay) Htext)
              (ui_init_37c pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    rewrite (init_proto_wait C pt Q W). rewrite /uinit_arm_waitnull.
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_wait : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    iSplitR. { iPureIntro. rewrite Ha0. exact Hnull. }
    rewrite /usys_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Eret : add_vec_int (mword_of_int (0x37a + 2) : mword 64) 4
                   = mword_of_int (0x37a + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_uv_stub_tail C pt CID2 Pinit 0x37a SYS_wait M m ret
              (ui_init_380 pt M (ilay_text pt Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  Lemma wp_init_write (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (bs : list (bv 8)) :
    wp_init_write_body (CID := CIDp) C pt Q W M m bs.
  Proof.
    intros Hpre Hbuf Hbs Hlen. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg Hw Hpc Hcont".
    iEval (change (mword_of_int InitSyms.write : mword 64)
             with (mword_of_int 0x392 : mword 64)) in "Hpc".
    iApply (wp_uv_stub_head C pt CIDp Pinit 0x392 SYS_write M m
              (ui_init_392 pt M (ilay_text pt Hlay) Htext)
              (ui_init_394 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont Hw]").
    iIntros "#Hcap".
    rewrite (init_proto_write C pt Q W). rewrite /uinit_arm_write.
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha1 : <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m
                    !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha2 : <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m
                    !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    rewrite Ha0 Ha1 Ha2.
    iSplitR. { iPureIntro. exact Hbuf. }
    iSplitL "Hw". { iExists bs. iSplitR; [ iPureIntro; exact (conj Hbs Hlen) | ]. iExact "Hw". }
    rewrite /usys_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Eret : add_vec_int (mword_of_int (0x392 + 2) : mword 64) 4
                   = mword_of_int (0x392 + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_uv_stub_tail C pt CID2 Pinit 0x392 SYS_write M m ret
              (ui_init_398 pt M (ilay_text pt Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  Lemma wp_init_exec (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (path : list (bv 8)) (args : list (list (bv 8))) :
    wp_init_exec_body (CID := CIDp) C pt Q W M m path args.
  Proof.
    intros Hpre Hargs. destruct Hpre as (Hlay & Htext & Hret2).
    iIntros "Hcg HQ Hpc Hcont".
    iEval (change (mword_of_int InitSyms.exec : mword 64)
             with (mword_of_int 0x3aa : mword 64)) in "Hpc".
    iApply (wp_uv_stub_head C pt CIDp Pinit 0x3aa SYS_exec M m
              (ui_init_3aa pt M (ilay_text pt Hlay) Htext)
              (ui_init_3ac pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont HQ]").
    iIntros "#Hcap".
    rewrite (init_proto_exec C pt Q W). rewrite /uinit_arm_execret.
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_exec : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha1 : <[Regidx a7_idx := (mword_of_int SYS_exec : mword 64)]> m
                    !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    rewrite Ha0 Ha1.
    iExists path, args.
    iSplitR. { iPureIntro. exact Hargs. }
    iSplitL "HQ". { iExact "HQ". }
    rewrite /usys_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Eret : add_vec_int (mword_of_int (0x3aa + 2) : mword 64) 4
                   = mword_of_int (0x3aa + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_uv_stub_tail C pt CID2 Pinit 0x3aa SYS_exec M m ret
              (ui_init_3b0 pt M (ilay_text pt Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  Lemma wp_init_exit (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_init_exit_body (CID := CIDp) C pt Q W M m.
  Proof.
    intros Hlay Htext.
    iIntros "Hcg Hpc".
    iEval (change (mword_of_int InitSyms.exit : mword 64)
             with (mword_of_int 0x372 : mword 64)) in "Hpc".
    iApply (wp_uv_stub_head C pt CIDp Pinit 0x372 SYS_exit M m
              (ui_init_372 pt M (ilay_text pt Hlay) Htext)
              (ui_init_374 pt M (ilay_text pt Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    iIntros "#Hcap".
    rewrite (init_proto_exit C pt Q W). done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 putc(fd, c).                                                       *)
  (*                                                                      *)
  (*   41a c.addi sp,-32   41c sd ra,24   41e sd s0,16   420 addi s0,sp,32 *)
  (*   422 sb a1,-17(s0)   426 li a2,1    428 addi a1,s0,-17  42c jal write *)
  (*   430 ld ra,24        432 ld s0,16   434 addi sp,32  436 ret          *)
  (*                                                                      *)
  (* The [sb] is the only 1-byte access in init and the reason              *)
  (* UmodeAbi's slot lemma had to become width-generic: [s0-17] is not      *)
  (* 8-aligned.  The buffer handed to [write] is that byte, which is what   *)
  (* discharges the [W] observation.                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_init_putc (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (c : bv 8) :
    wp_init_putc_body (CID := CIDp) C pt Q W M m sp0 c.
  Proof.
    intros Hlay Htext Hsp Hst Hfr Hc Hret2.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hhi.
    unfold init_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhi.
    assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
      by (rewrite moi_of_uint; exact Hsp).
    assert (HkT : forall (kk : Z) (bb : bv 8),
              InitInstrs.init_bytes !! kk = Some bb -> kk < uint sp0 - 32)
      by (intros kk bb Hkb; pose proof (init_bytes_key_lt kk bb Hkb); lia).
    iIntros "Hcg Hw Hpc Hcont".
    iEval (change (mword_of_int InitSyms.putc : mword 64)
             with (mword_of_int 0x41a : mword 64)) in "Hpc".

    (* ---- 0x41a  c.addi sp,sp,-32 ---- *)
    assert (Hw41a : (mword_of_int (uint sp0 - 32) : mword 64)
                    = add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                      : mword 64) = mword_of_int (-32))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Pinit M m (mword_of_int 0x41a)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 5)
              (mword_of_int (uint sp0 - 32))
              (ui_init_41a pt M (ilay_text pt Hlay) Htext)
              ltac:(vm_compute; discriminate) Hw41a
              with "Hcg Hpc").
    iIntros (K1) "Hcg Hpc".
    set (m1 := <[Regidx (mword_of_int 2 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64)]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (upd_eq m (Regidx (mword_of_int 2 : mword 5))
                  (regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64))).
    assert (E41a : add_vec_int (mword_of_int 0x41a : mword 64) 2
                   = mword_of_int 0x41c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E41a) in "Hpc".

    (* ---- 0x41c  c.sdsp ra,24(sp) ---- *)
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt K1 Pinit M m1 sp0 (mword_of_int 0x41c)
              (mword_of_int 3 : mword 6) ra_idx 32 24
              (ui_init_41c pt M (ilay_text pt Hlay) Htext) Hst
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K2) "Hcg Hpc".
    iEval (rewrite Hra1) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 32 + 24) (m !!! Regidx ra_idx)).
    assert (Ho1 : uM_only M M1 (uint sp0 - 32) 32)
      by (rewrite /M1; apply uM_only_store8; lia).
    assert (Ht1 : init_text_sub M1)
      by exact (uM_only_img InitInstrs.init_bytes M M1 (uint sp0 - 32) 32 HkT Ho1 Htext).
    assert (Hs1 : uv_stack pt M1 sp0 32)
      by exact (uM_only_stack pt M M1 sp0 32 (uint sp0 - 32) 32 Ho1 Hst).
    assert (E41c : add_vec_int (mword_of_int 0x41c : mword 64) 2
                   = mword_of_int 0x41e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E41c) in "Hpc".

    (* ---- 0x41e  c.sdsp s0,16(sp) ---- *)
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt K2 Pinit M1 m1 sp0 (mword_of_int 0x41e)
              (mword_of_int 2 : mword 6) s0_idx 32 16
              (ui_init_41e pt M1 (ilay_text pt Hlay) Ht1) Hs1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K3) "Hcg Hpc".
    iEval (rewrite Hs01) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 32 + 16) (m !!! Regidx s0_idx)).
    assert (Ho2 : uM_only M1 M2 (uint sp0 - 32) 32)
      by (rewrite /M2; apply uM_only_store8; lia).
    assert (Ht2 : init_text_sub M2)
      by exact (uM_only_img InitInstrs.init_bytes M1 M2 (uint sp0 - 32) 32 HkT Ho2 Ht1).
    assert (Hs2 : uv_stack pt M2 sp0 32)
      by exact (uM_only_stack pt M1 M2 sp0 32 (uint sp0 - 32) 32 Ho2 Hs1).
    assert (E41e : add_vec_int (mword_of_int 0x41e : mword 64) 2
                   = mword_of_int 0x420)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E41e) in "Hpc".

    (* ---- 0x420  c.addi4spn s0,sp,32 ---- *)
    assert (Hw420 : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { assert (Hcst : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Pinit M2 m1 (mword_of_int 0x420)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (mword_of_int (uint sp0))
              (ui_init_420 pt M2 (ilay_text pt Hlay) Ht2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw420
              with "Hcg Hpc").
    iIntros (K4) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (Hs0_2 : m2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq m1 (Regidx s0_idx)
                  (regval_into_reg (mword_of_int (uint sp0) : mword 64))).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = m !!! Regidx a1_idx).
    { exact (eq_trans (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                         ltac:(vm_compute; discriminate))
                      (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx a1_idx) _
                         ltac:(vm_compute; discriminate))). }
    assert (E420 : add_vec_int (mword_of_int 0x420 : mword 64) 2
                   = mword_of_int 0x422)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E420) in "Hpc".

    (* ---- 0x422  sb a1,-17(s0) ---- *)
    destruct (uv_stack_byte_moi pt M2 sp0 32 15 (mword_of_int (uint sp0 - 17))
                Hs2 ltac:(lia) ltac:(lia) ltac:(f_equal; lia))
      as (Hu15 & (w15 & Hl15 & Hst15 & Hld15) & Hcan15 & (b15 & Hb15)).
    assert (Hu17 : uint (mword_of_int (uint sp0 - 17) : mword 64) = uint sp0 - 17)
      by (apply uint_moi; unfold Z64; lia).
    rewrite Hu17 in Hb15.
    assert (Hva422 : (mword_of_int (uint sp0 - 17) : mword 64)
                     = add_vec (m2 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 4079 : mword 12))).
    { assert (Hcst : (sign_extend' 64 (mword_of_int 4079 : mword 12) : mword 64)
                     = mword_of_int (-17))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hs0_2. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_sb C pt Pinit M2 m2 (mword_of_int 0x422)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              w15 (mword_of_int (uint sp0 - 17)) (m2 !!! Regidx a1_idx) b15
              (ui_init_422 pt M2 (ilay_text pt Hlay) Ht2)
              Hva422 eq_refl
              Hl15 Hst15 Hcan15
              ltac:(rewrite Hu17; exact Hb15)
              with "Hcg Hpc").
    iIntros (K5) "Hcg Hpc".
    set (M3 := uM_store M2 (uint (mword_of_int (uint sp0 - 17) : mword 64)) 1
                 (m2 !!! Regidx a1_idx)).
    assert (EM3 : M3 = uM_store M2 (uint sp0 - 17) 1 (m !!! Regidx a1_idx))
      by (rewrite /M3; rewrite Hu17; rewrite Ha1_2; reflexivity).
    assert (Ho3 : uM_only M2 M3 (uint sp0 - 32) 32)
      by (rewrite EM3; apply (uM_only_storek M2 (uint sp0 - 17) 1); lia).
    assert (Ht3 : init_text_sub M3)
      by exact (uM_only_img InitInstrs.init_bytes M2 M3 (uint sp0 - 32) 32 HkT Ho3 Ht2).
    assert (Hs3 : uv_stack pt M3 sp0 32)
      by exact (uM_only_stack pt M2 M3 sp0 32 (uint sp0 - 32) 32 Ho3 Hs2).
    (* the byte that went in *)
    assert (Hbyte : M3 !! (uint sp0 - 17) = Some c).
    { rewrite EM3.
      pose proof (uM_store_lookup M2 (uint sp0 - 17) 1 (m !!! Regidx a1_idx) 0
                    ltac:(cbn; lia)) as Hlk.
      rewrite Z.add_0_r in Hlk. rewrite Hlk. rewrite Hc. reflexivity. }
    assert (E422 : add_vec_int (mword_of_int 0x422 : mword 64) 4
                   = mword_of_int 0x426)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E422) in "Hpc".

    (* ---- 0x426  c.li a2,1 ---- *)
    iApply (wp_uv_cli C pt Pinit M3 m2 (mword_of_int 0x426)
              (mword_of_int 1 : mword 6) a2_idx (mword_of_int 1)
              (ui_init_426 pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K6) "Hcg Hpc".
    set (m3 := <[Regidx a2_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m2).
    assert (E426 : add_vec_int (mword_of_int 0x426 : mword 64) 2
                   = mword_of_int 0x428)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E426) in "Hpc".

    (* ---- 0x428  addi a1,s0,-17 ---- *)
    assert (Hs0_3 : m3 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (eq_trans (upd_ne m2 (Regidx a2_idx) (Regidx s0_idx) _
                            ltac:(vm_compute; discriminate)) Hs0_2).
    assert (Hw428 : (mword_of_int (uint sp0 - 17) : mword 64)
                    = add_vec (m3 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 4079 : mword 12))).
    { assert (Hcst : (sign_extend' 64 (mword_of_int 4079 : mword 12) : mword 64)
                     = mword_of_int (-17))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hs0_3. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Pinit M3 m3 (mword_of_int 0x428)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (mword_of_int (uint sp0 - 17))
              (ui_init_428 pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate) Hw428
              with "Hcg Hpc").
    iIntros (K7) "Hcg Hpc".
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 17) : mword 64)]> m3).
    assert (E428 : add_vec_int (mword_of_int 0x428 : mword 64) 4
                   = mword_of_int 0x42c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E428) in "Hpc".

    (* ---- 0x42c  jal write ---- *)
    iApply (wp_uv_jal C pt Pinit M3 m4 (mword_of_int 0x42c)
              (mword_of_int 2096998 : mword 21) ra_idx
              (mword_of_int 0x392) (mword_of_int 0x430)
              (ui_init_42c pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (K8) "Hcg Hpc".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x430 : mword 64)]> m4).
    iEval (change (mword_of_int 0x392 : mword 64)
             with (mword_of_int InitSyms.write : mword 64)) in "Hpc".

    (* ---- write(fd, s0-17, 1) ---- *)
    assert (Hm5ra : m5 !!! Regidx ra_idx = (mword_of_int 0x430 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x430 : mword 64))).
    assert (Hm5a1 : m5 !!! Regidx a1_idx = (mword_of_int (uint sp0 - 17) : mword 64))
      by exact (eq_trans (upd_ne m4 (Regidx ra_idx) (Regidx a1_idx) _
                            ltac:(vm_compute; discriminate))
                         (upd_eq m3 (Regidx a1_idx)
                            (regval_into_reg (mword_of_int (uint sp0 - 17) : mword 64)))).
    assert (Hm5a2 : m5 !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
    { refine (eq_trans (upd_ne m4 (Regidx ra_idx) (Regidx a2_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m3 (Regidx a1_idx) (Regidx a2_idx) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m2 (Regidx a2_idx)
               (regval_into_reg (mword_of_int 1 : mword 64))). }
    assert (Hm5a0 : m5 !!! Regidx a0_idx = m !!! Regidx a0_idx).
    { refine (eq_trans (upd_ne m4 (Regidx ra_idx) (Regidx a0_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m3 (Regidx a1_idx) (Regidx a0_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m2 (Regidx a2_idx) (Regidx a0_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hu1 : uint (mword_of_int 1 : mword 64) = 1)
      by (vm_compute; reflexivity).
    assert (Hrdbuf : uv_rd pt M3 (uint sp0 - 17) 1).
    { constructor.
      - lia.
      - lia.
      - change (2 ^ 38) with 274877906944. lia.
      - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.
        rewrite Z.add_0_r. exists w15. exact (conj Hl15 Hld15).
      - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.
        rewrite Z.add_0_r. exists c. exact Hbyte. }
    assert (Hpre5 : init_layout pt /\ init_text_sub M3 /\
                    is_aligned_vaddr (Virtaddr (m5 !!! Regidx ra_idx)) 2 = true).
    { split_and!; [ exact Hlay | exact Ht3
                  | rewrite Hm5ra; vm_compute; reflexivity ]. }
    assert (Hbuf5 : uv_rd pt M3 (uint (m5 !!! Regidx a1_idx))
                              (uint (m5 !!! Regidx a2_idx)))
      by (rewrite Hm5a1 Hm5a2 Hu17 Hu1; exact Hrdbuf).
    assert (Hbs5 : ubuf_at M3 (uint (m5 !!! Regidx a1_idx)) [c])
      by (rewrite Hm5a1 Hu17; exact (ubuf_at_1 M3 (uint sp0 - 17) c Hbyte)).
    assert (Hlen5 : Z.of_nat (length [c]) = uint (m5 !!! Regidx a2_idx))
      by (rewrite Hm5a2 Hu1; reflexivity).
    iApply (wp_init_write K8 M3 m5 [c] Hpre5 Hbuf5 Hbs5 Hlen5
              with "Hcg [Hw] Hpc [Hcont]").
    { rewrite Hm5a0. iExact "Hw". }
    iIntros (K9 ret) "Hcg Hpc".
    set (m6 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m5)).
    iEval (rewrite Hm5ra) in "Hpc".

    (* ---- 0x430  c.ldsp ra,24(sp) ---- *)
    assert (Hm6sp : m6 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne _ (Regidx a7_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne _ (Regidx a1_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne _ (Regidx a2_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne _ (Regidx s0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hsp1. }
    (* what the two slots read back *)
    assert (Hbra : uM_bytes M3 (uint sp0 - 32 + 24) 8 (m !!! Regidx ra_idx)).
    { apply (uM_bytes_only M2 M3 (uint sp0 - 32 + 24) (uint sp0 - 17) 1 8);
        [ rewrite EM3; apply (uM_only_storek M2 (uint sp0 - 17) 1); lia | lia | ].
      apply (uM_bytes_only M1 M2 (uint sp0 - 32 + 24) (uint sp0 - 32 + 16) 8 8);
        [ rewrite /M2; apply uM_only_store8; lia | lia | ].
      rewrite /M1. exact (uM_store8_bytes M (uint sp0 - 32 + 24) _). }
    assert (Hbs0 : uM_bytes M3 (uint sp0 - 32 + 16) 8 (m !!! Regidx s0_idx)).
    { apply (uM_bytes_only M2 M3 (uint sp0 - 32 + 16) (uint sp0 - 17) 1 8);
        [ rewrite EM3; apply (uM_only_storek M2 (uint sp0 - 17) 1); lia | lia | ].
      rewrite /M2. exact (uM_store8_bytes M1 (uint sp0 - 32 + 16) _). }
    iApply (wp_uv_frame_load C pt K9 Pinit M3 m6 sp0 (mword_of_int 0x430)
              (mword_of_int 3 : mword 6) ra_idx 32 24 (m !!! Regidx ra_idx)
              (ui_init_430 pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate) Hs3
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hm6sp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 M3 (uint sp0 - 32 + 24) _ Hbra))
              with "Hcg Hpc").
    iIntros (KA) "Hcg Hpc".
    set (m7 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> m6).
    assert (E430 : add_vec_int (mword_of_int 0x430 : mword 64) 2
                   = mword_of_int 0x432)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E430) in "Hpc".

    (* ---- 0x432  c.ldsp s0,16(sp) ---- *)
    assert (Hm7sp : m7 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne m6 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hm6sp).
    iApply (wp_uv_frame_load C pt KA Pinit M3 m7 sp0 (mword_of_int 0x432)
              (mword_of_int 2 : mword 6) s0_idx 32 16 (m !!! Regidx s0_idx)
              (ui_init_432 pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate) Hs3
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hm7sp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(symmetry; exact (uM_word_w8 M3 (uint sp0 - 32 + 16) _ Hbs0))
              with "Hcg Hpc").
    iIntros (KB) "Hcg Hpc".
    set (m8 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> m7).
    assert (E432 : add_vec_int (mword_of_int 0x432 : mword 64) 2
                   = mword_of_int 0x434)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E432) in "Hpc".

    (* ---- 0x434  c.addi16sp sp,sp,32 ---- *)
    assert (Hm8sp : m8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne m7 (Regidx s0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hm7sp).
    assert (Hw434 : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (m8 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hm8sp. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Pinit M3 m8 (mword_of_int 0x434)
              (mword_of_int 2 : mword 6) (mword_of_int (uint sp0))
              (ui_init_434 pt M3 (ilay_text pt Hlay) Ht3) Hw434
              with "Hcg Hpc").
    iIntros (KC) "Hcg Hpc".
    set (m9 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m8).
    assert (E434 : add_vec_int (mword_of_int 0x434 : mword 64) 2
                   = mword_of_int 0x436)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E434) in "Hpc".

    (* ---- 0x436  c.jr ra ---- *)
    assert (Hm9ra : m9 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { refine (eq_trans (upd_ne m8 (Regidx csp_rs1) (Regidx ra_idx) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m7 (Regidx s0_idx) (Regidx ra_idx) _
                          ltac:(vm_compute; discriminate)) _).
      exact (upd_eq m6 (Regidx ra_idx) (regval_into_reg (m !!! Regidx ra_idx))). }
    iApply (wp_uv_cjr C pt Pinit M3 m9 (mword_of_int 0x436)
              ra_idx (m !!! Regidx ra_idx)
              (ui_init_436 pt M3 (ilay_text pt Hlay) Ht3)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hm9ra; unfold ret_pc; symmetry;
                    exact (update_bit0_zero_of_aligned2 _ Hret2))
              with "Hcg Hpc").
    iIntros (KD) "Hcg Hpc".

    (* ---- the two postconditions ---- *)
    iApply ("Hcont" $! KD m9 M3 with "[] [] Hcg Hpc").
    - iPureIntro. intros r Hr.
      (* sp and s0 are restored; every other register written is CALLER-saved,
         so it cannot be one of the indices [Hr] admits. *)
      assert (Hne : forall k : Z,
                ucallee_saved_idx (mword_of_int k : mword 5) = false ->
                Regidx r <> Regidx (mword_of_int k : mword 5)).
      { intros k Hk Heq. injection Heq as Heq'.
        rewrite Heq' in Hr. rewrite Hk in Hr. discriminate. }
      destruct (decide (r = (mword_of_int 2 : mword 5))) as [ -> | Hr2 ].
      { transitivity (mword_of_int (uint sp0) : mword 64).
        - exact (upd_eq m8 (Regidx csp_rs1)
                   (regval_into_reg (mword_of_int (uint sp0) : mword 64))).
        - rewrite <- Hsp. exact (moi_of_uint _). }
      destruct (decide (r = (mword_of_int 8 : mword 5))) as [ -> | Hr8 ].
      { refine (eq_trans (upd_ne m8 (Regidx csp_rs1) (Regidx s0_idx) _
                            ltac:(vm_compute; discriminate)) _).
        exact (upd_eq m7 (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      assert (Hn2 : Regidx r <> Regidx (mword_of_int 2 : mword 5))
        by (intro He; apply Hr2; injection He; auto).
      assert (Hn8 : Regidx r <> Regidx (mword_of_int 8 : mword 5))
        by (intro He; apply Hr8; injection He; auto).
      rewrite (upd_ne m8 (Regidx csp_rs1) (Regidx r) _ Hn2).
      rewrite (upd_ne m7 (Regidx s0_idx) (Regidx r) _ Hn8).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx r) _
                 (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _
                 (Hne 10 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx r) _
                 (Hne 17 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne m4 (Regidx ra_idx) (Regidx r) _
                 (Hne 1 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne m3 (Regidx a1_idx) (Regidx r) _
                 (Hne 11 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne m2 (Regidx a2_idx) (Regidx r) _
                 (Hne 12 ltac:(vm_compute; reflexivity))).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hn8).
      exact (upd_ne m (Regidx (mword_of_int 2 : mword 5)) (Regidx r) _ Hn2).
    - iPureIntro.
      exact (uM_only_trans M M2 M3 (uint sp0 - 32) 32
               (uM_only_trans M M1 M2 (uint sp0 - 32) 32 Ho1 Ho2) Ho3).
  Qed.

End UProofInitLib.
