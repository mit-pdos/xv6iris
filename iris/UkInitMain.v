(* ===================================================================== *)
(* UkInitMain.v -- init's [main] and [start].                              *)
(*                                                                        *)
(* main is the first program in this tier that DOES NOT TERMINATE, and the *)
(* first that forks.  Its shape:                                           *)
(*                                                                        *)
(*   0x00..0x2e  prologue; open("console") or the mknod repair arm at 0x64;*)
(*               two dups; the "init: starting sh" pointer into s2         *)
(*   0x32        the RESTART loop head: printf, fork                        *)
(*   0x44        the WAIT loop head: wait(0), and the two back edges        *)
(*   0x84 0xaa 0x52   the three dying arms: printf a diagnostic, exit(1)    *)
(*   0x96        the CHILD arm: exec("sh", argv), which only returns on     *)
(*               failure, and then dies at 0xaa                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeInit.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkInit.
Require Import UkInitPutc.
Require Import UkInitVprintf.
Require Import UkInitLit.
Require Import UkInitPrintf.
Require Import UkFork.
Require Import UkRunBr.

Local Open Scope Z_scope.
Import Defs.

Section UkInitMain.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).


  (* --------------------------------------------------------------------- *)
  (* THE THREE DYING ARMS.  Each is [printf(<literal>); exit(1)] and none    *)
  (* returns, so each is a WP with no continuation at all -- which is also   *)
  (* why they need no frame word and no register fact beyond the budget.     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_die_df (hdf : CpuId) (mdf0 : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗
    urun γt γd γs hdf mdf0 (mword_of_int 0x84) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdf : init_lit_ok 0x990 18%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str γt 0x990 18%nat Hokdf ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdf".
    (* ---- 0x84  auipc a0 ; 0x88  addi a0,a0,-1780 -- the literal ---- *)
    assert (Eadf : add_vec (add_vec (mword_of_int 0x84 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2316 : mword 12))
                   = mword_of_int 0x990)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hdf mdf0 (mword_of_int 0x84)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x84 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_84 with "Hcode"). }
    assert (E84 : add_vec_int (mword_of_int 0x84 : mword 64) 4
                 = mword_of_int 0x88)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E84.
    iIntros (hdf1) "Hrun".
    set (df1 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0x84 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mdf0).
    iApply (wp_uk_addi γt γd γs hdf1 df1 (mword_of_int 0x88)
              (mword_of_int 2316 : mword 12) a0_idx a0_idx
              (mword_of_int 0x990) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mdf0 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Eadf))
              with "[] Hrun").
    { iApply (uis_init_88 with "Hcode"). }
    assert (E88 : add_vec_int (mword_of_int 0x88 : mword 64) 4
                 = mword_of_int 0x8c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E88.
    iIntros (hdf2) "Hrun".
    set (df2 := <[Regidx a0_idx := regval_into_reg
                    (mword_of_int 0x990 : mword 64)]> df1).
    (* ---- 0x8c  jal ra,0x7c0 <printf> ---- *)
    iApply (wp_uk_jal γt γd γs hdf2 df2 (mword_of_int 0x8c)
              (mword_of_int 1844 : mword 21) ra_idx
              (mword_of_int InitSyms.printf) (mword_of_int 0x90) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_8c with "Hcode"). }
    iIntros (hdf3) "Hrun".
    set (df3 := <[Regidx ra_idx := regval_into_reg
                    (mword_of_int 0x90 : mword 64)]> df2).
    assert (Hradf : df3 !!! Regidx ra_idx
                    = (mword_of_int 0x90 : mword 64))
      by exact (upd_eq df2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha0df : df3 !!! Regidx a0_idx = mword_of_int 0x990).
    { rewrite /df3 (upd_ne df2 (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /df2. exact (upd_eq df1 (Regidx a0_idx) (regval_into_reg _)). }
    iApply (wp_kinit_printf γt γd γs 0x990 18%nat (init_lit 0x990) hdf3 df3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x990 18%nat j Hokdf Hj) Ha0df
              with "Hcode Hstrdf Hrun").
    iIntros (hdf4 df4) "%Hcsdf Hrun".
    assert (Eretdf : ret_pc (df3 !!! Regidx ra_idx)
                     = (mword_of_int 0x90 : mword 64))
      by (rewrite Hradf; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdf.
    (* ---- 0x90  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs hdf4 df4 (mword_of_int 0x90)
              (mword_of_int 1 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_90 with "Hcode"). }
    assert (E90 : add_vec_int (mword_of_int 0x90 : mword 64) 2
                 = mword_of_int 0x92)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90.
    iIntros (hdf5) "Hrun".
    set (df5 := <[Regidx a0_idx := regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6)
                     : mword 64)]> df4).
    (* ---- 0x92  jal ra,0x372 <exit> -- no continuation ---- *)
    iApply (wp_uk_jal γt γd γs hdf5 df5 (mword_of_int 0x92)
              (mword_of_int 736 : mword 21) ra_idx
              (mword_of_int InitSyms.exit) (mword_of_int 0x96) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_92 with "Hcode"). }
    iIntros (hdf6) "Hrun".
    iApply (wp_kinit_exit γt γd γs hdf6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_de (hde : CpuId) (mde0 : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗
    urun γt γd γs hde mde0 (mword_of_int 0xaa) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokde : init_lit_ok 0x9b0 21%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str γt 0x9b0 21%nat Hokde ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrde".
    (* ---- 0xaa  auipc a0 ; 0xae  addi a0,a0,-1786 -- the literal ---- *)
    assert (Eade : add_vec (add_vec (mword_of_int 0xaa : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2310 : mword 12))
                   = mword_of_int 0x9b0)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hde mde0 (mword_of_int 0xaa)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0xaa : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_aa with "Hcode"). }
    assert (Eaa : add_vec_int (mword_of_int 0xaa : mword 64) 4
                 = mword_of_int 0xae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaa.
    iIntros (hde1) "Hrun".
    set (de1 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0xaa : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mde0).
    iApply (wp_uk_addi γt γd γs hde1 de1 (mword_of_int 0xae)
              (mword_of_int 2310 : mword 12) a0_idx a0_idx
              (mword_of_int 0x9b0) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mde0 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Eade))
              with "[] Hrun").
    { iApply (uis_init_ae with "Hcode"). }
    assert (Eae : add_vec_int (mword_of_int 0xae : mword 64) 4
                 = mword_of_int 0xb2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae.
    iIntros (hde2) "Hrun".
    set (de2 := <[Regidx a0_idx := regval_into_reg
                    (mword_of_int 0x9b0 : mword 64)]> de1).
    (* ---- 0xb2  jal ra,0x7c0 <printf> ---- *)
    iApply (wp_uk_jal γt γd γs hde2 de2 (mword_of_int 0xb2)
              (mword_of_int 1806 : mword 21) ra_idx
              (mword_of_int InitSyms.printf) (mword_of_int 0xb6) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_b2 with "Hcode"). }
    iIntros (hde3) "Hrun".
    set (de3 := <[Regidx ra_idx := regval_into_reg
                    (mword_of_int 0xb6 : mword 64)]> de2).
    assert (Hrade : de3 !!! Regidx ra_idx
                    = (mword_of_int 0xb6 : mword 64))
      by exact (upd_eq de2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha0de : de3 !!! Regidx a0_idx = mword_of_int 0x9b0).
    { rewrite /de3 (upd_ne de2 (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /de2. exact (upd_eq de1 (Regidx a0_idx) (regval_into_reg _)). }
    iApply (wp_kinit_printf γt γd γs 0x9b0 21%nat (init_lit 0x9b0) hde3 de3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9b0 21%nat j Hokde Hj) Ha0de
              with "Hcode Hstrde Hrun").
    iIntros (hde4 de4) "%Hcsde Hrun".
    assert (Eretde : ret_pc (de3 !!! Regidx ra_idx)
                     = (mword_of_int 0xb6 : mword 64))
      by (rewrite Hrade; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretde.
    (* ---- 0xb6  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs hde4 de4 (mword_of_int 0xb6)
              (mword_of_int 1 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_b6 with "Hcode"). }
    assert (Eb6 : add_vec_int (mword_of_int 0xb6 : mword 64) 2
                 = mword_of_int 0xb8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb6.
    iIntros (hde5) "Hrun".
    set (de5 := <[Regidx a0_idx := regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6)
                     : mword 64)]> de4).
    (* ---- 0xb8  jal ra,0x372 <exit> -- no continuation ---- *)
    iApply (wp_uk_jal γt γd γs hde5 de5 (mword_of_int 0xb8)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int InitSyms.exit) (mword_of_int 0xbc) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_b8 with "Hcode"). }
    iIntros (hde6) "Hrun".
    iApply (wp_kinit_exit γt γd γs hde6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_dw (hdw : CpuId) (mdw0 : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗
    urun γt γd γs hdw mdw0 (mword_of_int 0x52) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdw : init_lit_ok 0x9c8 29%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str γt 0x9c8 29%nat Hokdw ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdw".
    (* ---- 0x52  auipc a0 ; 0x56  addi a0,a0,-1674 -- the literal ---- *)
    assert (Eadw : add_vec (add_vec (mword_of_int 0x52 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2422 : mword 12))
                   = mword_of_int 0x9c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hdw mdw0 (mword_of_int 0x52)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x52 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_52 with "Hcode"). }
    assert (E52 : add_vec_int (mword_of_int 0x52 : mword 64) 4
                 = mword_of_int 0x56)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52.
    iIntros (hdw1) "Hrun".
    set (dw1 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0x52 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mdw0).
    iApply (wp_uk_addi γt γd γs hdw1 dw1 (mword_of_int 0x56)
              (mword_of_int 2422 : mword 12) a0_idx a0_idx
              (mword_of_int 0x9c8) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mdw0 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Eadw))
              with "[] Hrun").
    { iApply (uis_init_56 with "Hcode"). }
    assert (E56 : add_vec_int (mword_of_int 0x56 : mword 64) 4
                 = mword_of_int 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E56.
    iIntros (hdw2) "Hrun".
    set (dw2 := <[Regidx a0_idx := regval_into_reg
                    (mword_of_int 0x9c8 : mword 64)]> dw1).
    (* ---- 0x5a  jal ra,0x7c0 <printf> ---- *)
    iApply (wp_uk_jal γt γd γs hdw2 dw2 (mword_of_int 0x5a)
              (mword_of_int 1894 : mword 21) ra_idx
              (mword_of_int InitSyms.printf) (mword_of_int 0x5e) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_5a with "Hcode"). }
    iIntros (hdw3) "Hrun".
    set (dw3 := <[Regidx ra_idx := regval_into_reg
                    (mword_of_int 0x5e : mword 64)]> dw2).
    assert (Hradw : dw3 !!! Regidx ra_idx
                    = (mword_of_int 0x5e : mword 64))
      by exact (upd_eq dw2 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha0dw : dw3 !!! Regidx a0_idx = mword_of_int 0x9c8).
    { rewrite /dw3 (upd_ne dw2 (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /dw2. exact (upd_eq dw1 (Regidx a0_idx) (regval_into_reg _)). }
    iApply (wp_kinit_printf γt γd γs 0x9c8 29%nat (init_lit 0x9c8) hdw3 dw3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9c8 29%nat j Hokdw Hj) Ha0dw
              with "Hcode Hstrdw Hrun").
    iIntros (hdw4 dw4) "%Hcsdw Hrun".
    assert (Eretdw : ret_pc (dw3 !!! Regidx ra_idx)
                     = (mword_of_int 0x5e : mword 64))
      by (rewrite Hradw; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdw.
    (* ---- 0x5e  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs hdw4 dw4 (mword_of_int 0x5e)
              (mword_of_int 1 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_5e with "Hcode"). }
    assert (E5e : add_vec_int (mword_of_int 0x5e : mword 64) 2
                 = mword_of_int 0x60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5e.
    iIntros (hdw5) "Hrun".
    set (dw5 := <[Regidx a0_idx := regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6)
                     : mword 64)]> dw4).
    (* ---- 0x60  jal ra,0x372 <exit> -- no continuation ---- *)
    iApply (wp_uk_jal γt γd γs hdw5 dw5 (mword_of_int 0x60)
              (mword_of_int 786 : mword 21) ra_idx
              (mword_of_int InitSyms.exit) (mword_of_int 0x64) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_60 with "Hcode"). }
    iIntros (hdw6) "Hrun".
    iApply (wp_kinit_exit γt γd γs hdw6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE CHILD ARM @0x96: exec("sh", argv).                                  *)
  (*                                                                        *)
  (*   0x96 auipc a1 ; 0x9a addi a1,a1,-150   -- argv, at 0x1000            *)
  (*   0x9e auipc a0 ; 0xa2 addi a0,a0,-1782  -- "sh", at 0x9a8             *)
  (*   0xa6 jal <exec>                                                       *)
  (*                                                                        *)
  (* A SUCCESSFUL exec never comes back to this WP -- the new program runs   *)
  (* under a slot minted for its own image, which is not this proof's        *)
  (* business.  [UsysMemOk]'s exec row therefore states the FAILURE arm      *)
  (* only ([r = -1], image and permissions unchanged), and that arm falls    *)
  (* into the 0xaa diagnostic.  So this lemma needs nothing about the argv   *)
  (* array or the "sh" string: they are addresses in registers, and the      *)
  (* only path back through here is the one where the kernel looked at       *)
  (* neither.                                                                *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_child (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗
    urun γt γd γs h m (mword_of_int 0x96) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexec & _ & _).
    (* ---- 0x96  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs h m (mword_of_int 0x96)
              (mword_of_int 1 : mword 20) a1_idx
              (add_vec (mword_of_int 0x96 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_96 with "Hcode"). }
    assert (E96 : add_vec_int (mword_of_int 0x96 : mword 64) 4
                  = mword_of_int 0x9a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96.
    iIntros (hc1) "Hrun".
    set (mc1 := <[Regidx a1_idx := regval_into_reg
                    (add_vec (mword_of_int 0x96 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> m).
    (* ---- 0x9a  addi a1,a1,-150 -- argv ---- *)
    assert (Eargv : add_vec (add_vec (mword_of_int 0x96 : mword 64)
                               (auipc_off (mword_of_int 1 : mword 20)))
                      (sign_extend' 64 (mword_of_int 3946 : mword 12))
                    = mword_of_int 0x1000)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs hc1 mc1 (mword_of_int 0x9a)
              (mword_of_int 3946 : mword 12) a1_idx a1_idx
              (mword_of_int 0x1000) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m (Regidx a1_idx) (regval_into_reg _));
                    exact (eq_sym Eargv))
              with "[] Hrun").
    { iApply (uis_init_9a with "Hcode"). }
    assert (E9a : add_vec_int (mword_of_int 0x9a : mword 64) 4
                  = mword_of_int 0x9e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9a.
    iIntros (hc2) "Hrun".
    set (mc2 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int 0x1000 : mword 64)]> mc1).
    (* ---- 0x9e  auipc a0,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs hc2 mc2 (mword_of_int 0x9e)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x9e : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_9e with "Hcode"). }
    assert (E9e : add_vec_int (mword_of_int 0x9e : mword 64) 4
                  = mword_of_int 0xa2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9e.
    iIntros (hc3) "Hrun".
    set (mc3 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0x9e : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mc2).
    (* ---- 0xa2  addi a0,a0,-1782 -- "sh" ---- *)
    assert (Esh : add_vec (add_vec (mword_of_int 0x9e : mword 64)
                             (auipc_off (mword_of_int 1 : mword 20)))
                    (sign_extend' 64 (mword_of_int 2314 : mword 12))
                  = mword_of_int 0x9a8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs hc3 mc3 (mword_of_int 0xa2)
              (mword_of_int 2314 : mword 12) a0_idx a0_idx
              (mword_of_int 0x9a8) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mc2 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Esh))
              with "[] Hrun").
    { iApply (uis_init_a2 with "Hcode"). }
    assert (Ea2 : add_vec_int (mword_of_int 0xa2 : mword 64) 4
                  = mword_of_int 0xa6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea2.
    iIntros (hc4) "Hrun".
    set (mc4 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int 0x9a8 : mword 64)]> mc3).
    (* ---- 0xa6  jal ra,0x3aa <exec> ---- *)
    iApply (wp_uk_jal γt γd γs hc4 mc4 (mword_of_int 0xa6)
              (mword_of_int 772 : mword 21) ra_idx
              (mword_of_int InitSyms.exec) (mword_of_int 0xaa)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexec; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexec; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_a6 with "Hcode"). }
    iIntros (hc5) "Hrun".
    set (mc5 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0xaa : mword 64)]> mc4).
    assert (Hrac5 : mc5 !!! Regidx ra_idx = (mword_of_int 0xaa : mword 64))
      by exact (upd_eq mc4 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- exec("sh", argv) -- and it FAILED, or we would not be here ---- *)
    iApply (wp_kinit_exec γt γd γs hc5 mc5 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hc6) "Hrun".
    assert (Eretc : ret_pc (mc5 !!! Regidx ra_idx)
                    = (mword_of_int 0xaa : mword 64))
      by (rewrite Hrac5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretc.
    (* ---- 0xaa  "init: exec sh failed" ; exit(1) ---- *)
    iApply (wp_kinit_main_die_de hc6 _ n with "Hcode Hro Hrun").
  Qed.

End UkInitMain.
