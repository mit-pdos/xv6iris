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

  (* init's four literals, by base.  Lengths: 18, 18, 21, 29. *)
  Local Notation LIT_START := 0x978.   (* "init: starting sh\n"            *)
  Local Notation LIT_FORK  := 0x990.   (* "init: fork failed\n"            *)
  Local Notation LIT_EXEC  := 0x9b0.   (* "init: exec sh failed\n"         *)
  Local Notation LIT_WAIT  := 0x9c8.   (* "init: wait returned an error\n" *)


  (* --------------------------------------------------------------------- *)
  (* THE THREE DYING ARMS.  Each is [printf(<literal>); exit(1)] and none    *)
  (* returns, so each is a WP with no continuation at all -- which is also   *)
  (* why they need no frame word and no register fact beyond the budget.     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_die_df (gt gd gs : gname) (hdf : CpuId) (mdf0 : regfile) (n : nat) :
    init_code gt -∗ init_rodata gt -∗
    urun gt gd gs hdf mdf0 (mword_of_int 0x84) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdf : init_lit_ok 0x990 18%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str gt 0x990 18%nat Hokdf ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdf".
    (* ---- 0x84  auipc a0 ; 0x88  addi a0,a0,-1780 -- the literal ---- *)
    assert (Eadf : add_vec (add_vec (mword_of_int 0x84 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2316 : mword 12))
                   = mword_of_int 0x990)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc gt gd gs hdf mdf0 (mword_of_int 0x84)
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
    iApply (wp_uk_addi gt gd gs hdf1 df1 (mword_of_int 0x88)
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
    iApply (wp_uk_jal gt gd gs hdf2 df2 (mword_of_int 0x8c)
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
    iApply (wp_kinit_printf gt gd gs 0x990 18%nat (init_lit 0x990) hdf3 df3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x990 18%nat j Hokdf Hj) Ha0df
              with "Hcode Hstrdf Hrun").
    iIntros (hdf4 df4) "%Hcsdf Hrun".
    assert (Eretdf : ret_pc (df3 !!! Regidx ra_idx)
                     = (mword_of_int 0x90 : mword 64))
      by (rewrite Hradf; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdf.
    (* ---- 0x90  c.li a0,1 ---- *)
    iApply (wp_uk_cli gt gd gs hdf4 df4 (mword_of_int 0x90)
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
    iApply (wp_uk_jal gt gd gs hdf5 df5 (mword_of_int 0x92)
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
    iApply (wp_kinit_exit gt gd gs hdf6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_de (gt gd gs : gname) (hde : CpuId) (mde0 : regfile) (n : nat) :
    init_code gt -∗ init_rodata gt -∗
    urun gt gd gs hde mde0 (mword_of_int 0xaa) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokde : init_lit_ok 0x9b0 21%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str gt 0x9b0 21%nat Hokde ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrde".
    (* ---- 0xaa  auipc a0 ; 0xae  addi a0,a0,-1786 -- the literal ---- *)
    assert (Eade : add_vec (add_vec (mword_of_int 0xaa : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2310 : mword 12))
                   = mword_of_int 0x9b0)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc gt gd gs hde mde0 (mword_of_int 0xaa)
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
    iApply (wp_uk_addi gt gd gs hde1 de1 (mword_of_int 0xae)
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
    iApply (wp_uk_jal gt gd gs hde2 de2 (mword_of_int 0xb2)
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
    iApply (wp_kinit_printf gt gd gs 0x9b0 21%nat (init_lit 0x9b0) hde3 de3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9b0 21%nat j Hokde Hj) Ha0de
              with "Hcode Hstrde Hrun").
    iIntros (hde4 de4) "%Hcsde Hrun".
    assert (Eretde : ret_pc (de3 !!! Regidx ra_idx)
                     = (mword_of_int 0xb6 : mword 64))
      by (rewrite Hrade; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretde.
    (* ---- 0xb6  c.li a0,1 ---- *)
    iApply (wp_uk_cli gt gd gs hde4 de4 (mword_of_int 0xb6)
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
    iApply (wp_uk_jal gt gd gs hde5 de5 (mword_of_int 0xb8)
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
    iApply (wp_kinit_exit gt gd gs hde6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_dw (gt gd gs : gname) (hdw : CpuId) (mdw0 : regfile) (n : nat) :
    init_code gt -∗ init_rodata gt -∗
    urun gt gd gs hdw mdw0 (mword_of_int 0x52) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdw : init_lit_ok 0x9c8 29%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str gt 0x9c8 29%nat Hokdw ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdw".
    (* ---- 0x52  auipc a0 ; 0x56  addi a0,a0,-1674 -- the literal ---- *)
    assert (Eadw : add_vec (add_vec (mword_of_int 0x52 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2422 : mword 12))
                   = mword_of_int 0x9c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc gt gd gs hdw mdw0 (mword_of_int 0x52)
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
    iApply (wp_uk_addi gt gd gs hdw1 dw1 (mword_of_int 0x56)
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
    iApply (wp_uk_jal gt gd gs hdw2 dw2 (mword_of_int 0x5a)
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
    iApply (wp_kinit_printf gt gd gs 0x9c8 29%nat (init_lit 0x9c8) hdw3 dw3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9c8 29%nat j Hokdw Hj) Ha0dw
              with "Hcode Hstrdw Hrun").
    iIntros (hdw4 dw4) "%Hcsdw Hrun".
    assert (Eretdw : ret_pc (dw3 !!! Regidx ra_idx)
                     = (mword_of_int 0x5e : mword 64))
      by (rewrite Hradw; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdw.
    (* ---- 0x5e  c.li a0,1 ---- *)
    iApply (wp_uk_cli gt gd gs hdw4 dw4 (mword_of_int 0x5e)
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
    iApply (wp_uk_jal gt gd gs hdw5 dw5 (mword_of_int 0x60)
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
    iApply (wp_kinit_exit gt gd gs hdw6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
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
  Lemma wp_kinit_main_child (gt gd gs : gname) (h : CpuId) (m : regfile) (n : nat) :
    init_code gt -∗ init_rodata gt -∗
    urun gt gd gs h m (mword_of_int 0x96) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexec & _ & _).
    (* ---- 0x96  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc gt gd gs h m (mword_of_int 0x96)
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
    iApply (wp_uk_addi gt gd gs hc1 mc1 (mword_of_int 0x9a)
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
    iApply (wp_uk_auipc gt gd gs hc2 mc2 (mword_of_int 0x9e)
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
    iApply (wp_uk_addi gt gd gs hc3 mc3 (mword_of_int 0xa2)
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
    iApply (wp_uk_jal gt gd gs hc4 mc4 (mword_of_int 0xa6)
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
    iApply (wp_kinit_exec gt gd gs hc5 mc5 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hc6) "Hrun".
    assert (Eretc : ret_pc (mc5 !!! Regidx ra_idx)
                    = (mword_of_int 0xaa : mword 64))
      by (rewrite Hrac5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretc.
    (* ---- 0xaa  "init: exec sh failed" ; exit(1) ---- *)
    iApply (wp_kinit_main_die_de gt gd gs hc6 _ n with "Hcode Hro Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* WHAT CROSSES THE FORK.  The child needs init's text and its read-only   *)
  (* image at ITS OWN names, and both are [utext_img] at a constant map, so  *)
  (* [forkable_utext_map] gives them.  Nothing else crosses: main's frame    *)
  (* words are never read again (main does not return), and the break is     *)
  (* carried by the leaf itself.                                             *)
  (* --------------------------------------------------------------------- *)
  Local Instance forkable_init_img :
    Forkable (fun gt _ _ => (init_code gt ∗ init_rodata gt)%I).
  Proof.
    eapply Forkable_ext;
      [ | apply (forkable_sep
                   (fun gt _ _ => ([∗ map] a ↦ b ∈ InitInstrs.init_bytes,
                                     utext gt a b)%I)
                   (fun gt _ _ => ([∗ map] a ↦ b ∈ init_ro, utext gt a b)%I)
                   (forkable_utext_map InitInstrs.init_bytes)
                   (forkable_utext_map init_ro)) ].
    intros gt gd gs. rewrite /init_code /init_rodata /utext_img. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* fork's STUB @0x36a -- the one syscall entry whose contract returns      *)
  (* TWICE.  Both arms come back through the same [c.jr ra] at 0x370, the    *)
  (* child's under its own names, which is why the payload has to carry the  *)
  (* catalog: without [init_code γt'] the child cannot even walk its return. *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_fork (szv : Z) (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun γt γd γs h m (mword_of_int InitSyms.fork) avail -∗
    ((∀ (h' : CpuId) (r : mword 64),
        ⌜ r <> (mword_of_int 0 : mword 64) ⌝ -∗
        (init_code γt ∗ init_rodata γt) -∗ usz γs szv -∗
        urun γt γd γs h'
          (<[Regidx a0_idx := r]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang)) ∗
     (∀ (gt' gd' gs' : gname) (h' : CpuId),
        (init_code gt' ∗ init_rodata gt') -∗ usz gs' szv -∗
        urun gt' gd' gs' h'
          (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hsz Hrun [Hpar Hchi]".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hfork & _ & _ & _ & _).
    rewrite Hfork.
    (* ---- 0x36a  c.li a7,1 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x36a)
              (mword_of_int 1 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_36a with "Hcode"). }
    assert (E36a : add_vec_int (mword_of_int 0x36a : mword 64) 2
                   = mword_of_int 0x36c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em1 : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 1 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E36a Em1.
    iIntros (h1) "Hrun".
    set (mf1 := <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m).
    (* ---- 0x36c  ecall -- the leaf that returns twice ---- *)
    iApply (wp_uk_ecall_fork γt γd γs h1 mf1 (mword_of_int 0x36c) avail szv
              (fun gt _ _ => (init_code gt ∗ init_rodata gt)%I)
              ltac:(unfold mf1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 1 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hsz Hrun").
    { iApply (uis_init_36c with "Hcode"). }
    { iFrame "Hcode Hro". }
    assert (E36c : add_vec_int (mword_of_int 0x36c : mword 64) 4
                   = mword_of_int 0x370)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E36c.
    assert (Hraf : forall (M : regfile) (v : mword 64),
               M = <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m ->
               M !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { intros M v ->.
      exact (upd_ne m (Regidx a7_idx) (Regidx ra_idx) _
               ltac:(vm_compute; discriminate)). }
    iSplitL "Hpar".
    - (* the PARENT resumes under the names it already had *)
      iIntros (hp r) "%Hrnz Hpay Hsz Hrun".
      set (mp := <[Regidx a0_idx := r]> mf1).
      assert (Hrap : mp !!! Regidx ra_idx = m !!! Regidx ra_idx).
      { rewrite /mp (upd_ne mf1 (Regidx a0_idx) (Regidx ra_idx) r
                       ltac:(vm_compute; discriminate)).
        exact (Hraf mf1 r eq_refl). }
      iDestruct "Hpay" as "[#Hcp #Hrp]".
      iApply (wp_uk_cjr γt γd γs hp mp (mword_of_int 0x370) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrap; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_370 with "Hcp"). }
      iIntros (hp2) "Hrun".
      iApply ("Hpar" $! hp2 r with "[] [] Hsz Hrun").
      { iPureIntro. exact Hrnz. }
      { iFrame "Hcp Hrp". }
    - (* ...and the CHILD under fresh ones *)
      iIntros (gt' gd' gs' hc) "Hpay Hsz Hrun".
      set (mk := <[Regidx a0_idx := (mword_of_int 0 : mword 64)]> mf1).
      assert (Hrak : mk !!! Regidx ra_idx = m !!! Regidx ra_idx).
      { rewrite /mk (upd_ne mf1 (Regidx a0_idx) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (Hraf mf1 (mword_of_int 0) eq_refl). }
      iDestruct "Hpay" as "[#Hck #Hrk]".
      iApply (wp_uk_cjr gt' gd' gs' hc mk (mword_of_int 0x370) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrak; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_370 with "Hck"). }
      iIntros (hc2) "Hrun".
      iApply ("Hchi" $! gt' gd' gs' hc2 with "[] Hsz Hrun").
      { iFrame "Hck Hrk". }
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE TWO LOOPS, UNDER ONE Löb.                                          *)
  (*                                                                        *)
  (* main has two heads -- the restart head at 0x32 and the wait head at     *)
  (* 0x44 -- and neither dominates the other: 0x4a's [beq a0,s1] jumps back  *)
  (* to 0x32, 0x4e's [bge a0,x0] back to 0x44, and the restart arm falls     *)
  (* through into the wait head.  So they close TOGETHER, as the two         *)
  (* conjuncts of one [iLöb], and the [∧] is doing real work: it lets both   *)
  (* arms use the SAME [usz], which a [∗] would have to split.               *)
  (*                                                                        *)
  (* THE INVARIANT IS ONE REGISTER PIN.  s2 holds the "init: starting sh"    *)
  (* pointer; everything else the loop needs is inside [urun].  In           *)
  (* particular nothing is assumed about what wait RETURNS: its result is    *)
  (* compared against s1, and all three outcomes -- the child was reaped, an *)
  (* orphan was reaped, the call failed -- are legal continuations of init.  *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_loop (szv : Z) (n : nat) :
    init_code γt -∗ init_rodata γt -∗
    ((∀ (h : CpuId) (m : regfile),
        ⌜ m !!! Regidx s2_idx = mword_of_int LIT_START ⌝ -∗
        usz γs szv -∗
        urun γt γd γs h m (mword_of_int 0x32) (12 + (12 + (4 + n))) -∗
        WP (Loop : expr riscv_lang))
     ∧ (∀ (h : CpuId) (m : regfile),
          ⌜ m !!! Regidx s2_idx = mword_of_int LIT_START ⌝ -∗
          usz γs szv -∗
          urun γt γd γs h m (mword_of_int 0x44) (12 + (12 + (4 + n))) -∗
          WP (Loop : expr riscv_lang))).
  Proof.
    iIntros "#Hcode #Hro".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & Hfork & Hwait & _ & _ & _).
    assert (HokS : init_lit_ok LIT_START 18%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str γt LIT_START 18%nat HokS
                 ltac:(vm_compute; reflexivity) with "Hro") as "#HstrS".
    iLöb as "IH".
    iSplit.
    - (* ==================== the RESTART head @0x32 ==================== *)
      iIntros (h m) "%Hs2 Hsz Hrun".
      iApply (wp_uk_cmv γt γd γs h m (mword_of_int 0x32) a0_idx s2_idx
                (add_vec zero_reg (m !!! Regidx s2_idx)) (12 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
      { iApply (uis_init_32 with "Hcode"). }
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2
                    = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E32.
      iIntros (hl1) "Hrun".
      set (ml1 := <[Regidx a0_idx
                    := regval_into_reg
                         (add_vec zero_reg (m !!! Regidx s2_idx))]> m).
      assert (Ha0l1 : ml1 !!! Regidx a0_idx = mword_of_int LIT_START).
      { rewrite (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
        rewrite Hs2. apply add_vec_zero_l. }
      (* ---- 0x34  jal ra,0x7c0 <printf> ---- *)
      iApply (wp_uk_jal γt γd γs hl1 ml1 (mword_of_int 0x34)
                (mword_of_int 1932 : mword 21) ra_idx
                (mword_of_int InitSyms.printf) (mword_of_int 0x38)
                (12 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hprintf; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hprintf; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_34 with "Hcode"). }
      iIntros (hl2) "Hrun".
      set (ml2 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x38 : mword 64)]> ml1).
      assert (Hral2 : ml2 !!! Regidx ra_idx = (mword_of_int 0x38 : mword 64))
        by exact (upd_eq ml1 (Regidx ra_idx) (regval_into_reg _)).
      assert (Ha0l2 : ml2 !!! Regidx a0_idx = mword_of_int LIT_START).
      { rewrite <- Ha0l1.
        exact (upd_ne ml1 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). }
      iApply (wp_kinit_printf γt γd γs LIT_START 18%nat (init_lit LIT_START)
                hl2 ml2 n
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(lia)
                (fun j Hj => init_lit_nopct LIT_START 18%nat j HokS Hj) Ha0l2
                with "Hcode HstrS Hrun").
      iIntros (hl3 ml3) "%Hcsl Hrun".
      assert (Eretl : ret_pc (ml2 !!! Regidx ra_idx)
                      = (mword_of_int 0x38 : mword 64))
        by (rewrite Hral2; apply bv_eq; vm_compute; reflexivity).
      rewrite Eretl.
      assert (Hs2l3 : ml3 !!! Regidx s2_idx = mword_of_int LIT_START).
      { rewrite (Hcsl s2_idx ltac:(vm_compute; reflexivity)).
        rewrite <- Hs2.
        rewrite /ml2 (upd_ne ml1 (Regidx ra_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /ml1. exact (upd_ne m (Regidx a0_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate)). }
      (* ---- 0x38  jal ra,0x36a <fork> ---- *)
      iApply (wp_uk_jal γt γd γs hl3 ml3 (mword_of_int 0x38)
                (mword_of_int 818 : mword 21) ra_idx
                (mword_of_int InitSyms.fork) (mword_of_int 0x3c)
                (12 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hfork; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hfork; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_38 with "Hcode"). }
      iIntros (hl4) "Hrun".
      set (ml4 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x3c : mword 64)]> ml3).
      assert (Hral4 : ml4 !!! Regidx ra_idx = (mword_of_int 0x3c : mword 64))
        by exact (upd_eq ml3 (Regidx ra_idx) (regval_into_reg _)).
      assert (Hs2l4 : ml4 !!! Regidx s2_idx = mword_of_int LIT_START).
      { rewrite <- Hs2l3.
        exact (upd_ne ml3 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). }
      assert (Eretf : ret_pc (ml4 !!! Regidx ra_idx)
                      = (mword_of_int 0x3c : mword 64))
        by (rewrite Hral4; apply bv_eq; vm_compute; reflexivity).
      iApply (wp_kinit_fork szv hl4 ml4 (12 + (12 + (4 + n)))
                with "Hcode Hro Hsz Hrun").
      rewrite Eretf.
      iSplitR "".
      + (* ------------- the PARENT: r <> 0 ------------- *)
        iIntros (hp r) "%Hrnz [#Hcp #Hrp] Hsz Hrun".
        set (mp0 := <[Regidx a0_idx := r]>
                      (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> ml4)).
        assert (Ha0p0 : mp0 !!! Regidx a0_idx = r)
          by exact (upd_eq _ (Regidx a0_idx) r).
        assert (Hs2p0 : mp0 !!! Regidx s2_idx = mword_of_int LIT_START).
        { rewrite <- Hs2l4.
          rewrite /mp0 (upd_ne _ (Regidx a0_idx) (Regidx s2_idx) r
                          ltac:(vm_compute; discriminate)).
          exact (upd_ne ml4 (Regidx a7_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)). }
        (* ---- 0x3c  c.mv s1,a0 ---- *)
        iApply (wp_uk_cmv γt γd γs hp mp0 (mword_of_int 0x3c) s1_idx a0_idx
                  (add_vec zero_reg (mp0 !!! Regidx a0_idx))
                  (12 + (12 + (4 + n)))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
        { iApply (uis_init_3c with "Hcode"). }
        assert (E3cp : add_vec_int (mword_of_int 0x3c : mword 64) 2
                       = mword_of_int 0x3e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3cp.
        iIntros (hp1) "Hrun".
        set (mp1 := <[Regidx s1_idx
                      := regval_into_reg
                           (add_vec zero_reg (mp0 !!! Regidx a0_idx))]> mp0).
        assert (Ha0p1 : mp1 !!! Regidx a0_idx = r).
        { rewrite <- Ha0p0.
          exact (upd_ne mp0 (Regidx s1_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)). }
        assert (Hs2p1 : mp1 !!! Regidx s2_idx = mword_of_int LIT_START).
        { rewrite <- Hs2p0.
          exact (upd_ne mp0 (Regidx s1_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)). }
        (* ---- 0x3e  blt a0,x0,0x84 -- fork may have FAILED ---- *)
        assert (Etgt3e : add_vec (mword_of_int 0x3e : mword 64)
                           (sign_extend' 64 (mword_of_int 70 : mword 13))
                         = mword_of_int 0x84)
          by (apply bv_eq; vm_compute; reflexivity).
        destruct (uv_btaken BLT (mp1 !!! Regidx a0_idx) zero_reg) eqn:Hblt.
        * (* fork failed: the diagnostic at 0x84 *)
          iApply (wp_uk_btype0 γt γd γs hp1 mp1 (mword_of_int 0x3e)
                    (mword_of_int 70 : mword 13) a0_idx BLT true
                    (mword_of_int 0x84) (12 + (12 + (4 + n)))
                    (eq_sym Hblt) (eq_sym Etgt3e)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_init_3e with "Hcode"). }
          iIntros (hp2) "Hrun".
          iApply (wp_kinit_main_die_df γt γd γs hp2 _ n with "Hcode Hro Hrun").
        * (* fork succeeded: this is the parent, so a0 <> 0 too.
             THE LATER COMES FROM HERE.  The path 0x32 -> printf -> fork ->
             0x3c -> 0x42 -> 0x44 falls THROUGH into the wait head; it is
             not a back edge, so nothing on it hands out a [▷] on its own,
             and without one the Löb hypothesis is unusable at 0x44.  Taking
             this branch through [wp_uk_btype0_later] supplies it. *)
          iApply (wp_uk_btype0_later γt γd γs hp1 mp1 (mword_of_int 0x3e)
                    (mword_of_int 70 : mword 13) a0_idx BLT false
                    (add_vec (mword_of_int 0x3e : mword 64)
                       (sign_extend' 64 (mword_of_int 70 : mword 13)))
                    (12 + (12 + (4 + n)))
                    (eq_sym Hblt) eq_refl ltac:(discriminate)
                    with "[] Hrun").
          { iApply (uis_init_3e with "Hcode"). }
          assert (E3ep : add_vec_int (mword_of_int 0x3e : mword 64) 4
                         = mword_of_int 0x42)
            by (apply bv_eq; vm_compute; reflexivity).
          iNext. rewrite E3ep.
          iIntros (hp2) "Hrun".
          (* ---- 0x42  c.beqz a0,0x96 -- NOT taken: r <> 0 ---- *)
          assert (Hbzp : false = eq_vec (mp1 !!! Regidx a0_idx) zero_reg).
          { rewrite Ha0p1. symmetry. apply eq_vec_false_iff.
            rewrite zero_reg_moi. exact Hrnz. }
          iApply (wp_uk_cbeqz γt γd γs hp2 mp1 (mword_of_int 0x42)
                    (mword_of_int 42 : mword 8) (mword_of_int 2 : mword 3)
                    a0_idx false
                    (add_vec (mword_of_int 0x42 : mword 64)
                       (sign_extend' 64
                          (sign_extend' 13
                             (concat_vec (mword_of_int 42 : mword 8) ('b"0")))))
                    (12 + (12 + (4 + n)))
                    ltac:(vm_compute; reflexivity) Hbzp eq_refl
                    ltac:(discriminate)
                    with "[] Hrun").
          { iApply (uis_init_42 with "Hcode"). }
          assert (E42p : add_vec_int (mword_of_int 0x42 : mword 64) 2
                         = mword_of_int 0x44)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E42p.
          iIntros (hp3) "Hrun".
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! hp3 mp1 with "[] Hsz Hrun").
          iPureIntro. exact Hs2p1.
      + (* ------------- the CHILD: r = 0 ------------- *)
        iIntros (gt' gd' gs' hc) "[#Hck #Hrk] Hsz Hrun".
        set (mc0 := <[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
                      (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> ml4)).
        assert (Ha0c0 : mc0 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
          by exact (upd_eq _ (Regidx a0_idx) _).
        (* ---- 0x3c  c.mv s1,a0 ---- *)
        iApply (wp_uk_cmv gt' gd' gs' hc mc0 (mword_of_int 0x3c) s1_idx a0_idx
                  (add_vec zero_reg (mc0 !!! Regidx a0_idx))
                  (12 + (12 + (4 + n)))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
        { iApply (uis_init_3c with "Hck"). }
        assert (E3cc : add_vec_int (mword_of_int 0x3c : mword 64) 2
                       = mword_of_int 0x3e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3cc.
        iIntros (hc1) "Hrun".
        set (mc1 := <[Regidx s1_idx
                      := regval_into_reg
                           (add_vec zero_reg (mc0 !!! Regidx a0_idx))]> mc0).
        assert (Ha0c1 : mc1 !!! Regidx a0_idx = (mword_of_int 0 : mword 64)).
        { rewrite <- Ha0c0.
          exact (upd_ne mc0 (Regidx s1_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)). }
        (* ---- 0x3e  blt a0,x0 -- a0 is 0, so NOT taken ---- *)
        assert (Hbltc : false = uv_btaken BLT (mc1 !!! Regidx a0_idx) zero_reg).
        { rewrite Ha0c1. cbn [uv_btaken]. rewrite zero_reg_moi.
          assert (H0 : 0 <= 0 < Z63) by (unfold Z63; lia).
          rewrite (moi_lt_s 0 0 H0 H0). reflexivity. }
        iApply (wp_uk_btype0 gt' gd' gs' hc1 mc1 (mword_of_int 0x3e)
                  (mword_of_int 70 : mword 13) a0_idx BLT false
                  (add_vec (mword_of_int 0x3e : mword 64)
                     (sign_extend' 64 (mword_of_int 70 : mword 13)))
                  (12 + (12 + (4 + n)))
                  Hbltc eq_refl ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_init_3e with "Hck"). }
        assert (E3ec : add_vec_int (mword_of_int 0x3e : mword 64) 4
                       = mword_of_int 0x42)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3ec.
        iIntros (hc2) "Hrun".
        (* ---- 0x42  c.beqz a0,0x96 -- TAKEN: this is the child ---- *)
        assert (Hbzc : true = eq_vec (mc1 !!! Regidx a0_idx) zero_reg).
        { rewrite Ha0c1 zero_reg_moi. symmetry.
          apply eq_vec_true_iff. reflexivity. }
        assert (Etgt42 : (mword_of_int 0x96 : mword 64)
                         = add_vec (mword_of_int 0x42 : mword 64)
                             (sign_extend' 64
                                (sign_extend' 13
                                   (concat_vec (mword_of_int 42 : mword 8)
                                      ('b"0")))))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_uk_cbeqz gt' gd' gs' hc2 mc1 (mword_of_int 0x42)
                  (mword_of_int 42 : mword 8) (mword_of_int 2 : mword 3)
                  a0_idx true (mword_of_int 0x96) (12 + (12 + (4 + n)))
                  ltac:(vm_compute; reflexivity) Hbzc Etgt42
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_init_42 with "Hck"). }
        iIntros (hc3) "Hrun".
        iApply (wp_kinit_main_child gt' gd' gs' hc3 mc1 n
                  with "Hck Hrk Hrun").
    - (* ==================== the WAIT head @0x44 ==================== *)
      iIntros (h m) "%Hs2 Hsz Hrun".
      (* ---- 0x44  c.li a0,0 -- the NULL status pointer ---- *)
      iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x44)
                (mword_of_int 0 : mword 6) a0_idx (12 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_init_44 with "Hcode"). }
      assert (E44 : add_vec_int (mword_of_int 0x44 : mword 64) 2
                    = mword_of_int 0x46)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E44.
      iIntros (hw1) "Hrun".
      set (mw1 := <[Regidx a0_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 0 : mword 6)
                          : mword 64)]> m).
      assert (Hs2w1 : mw1 !!! Regidx s2_idx = mword_of_int LIT_START).
      { rewrite <- Hs2.
        exact (upd_ne m (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). }
      (* ---- 0x46  jal ra,0x37a <wait> ---- *)
      iApply (wp_uk_jal γt γd γs hw1 mw1 (mword_of_int 0x46)
                (mword_of_int 820 : mword 21) ra_idx
                (mword_of_int InitSyms.wait) (mword_of_int 0x4a)
                (12 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hwait; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hwait; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_46 with "Hcode"). }
      iIntros (hw2) "Hrun".
      set (mw2 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x4a : mword 64)]> mw1).
      assert (Hraw2 : mw2 !!! Regidx ra_idx = (mword_of_int 0x4a : mword 64))
        by exact (upd_eq mw1 (Regidx ra_idx) (regval_into_reg _)).
      assert (Hs2w2 : mw2 !!! Regidx s2_idx = mword_of_int LIT_START).
      { rewrite <- Hs2w1.
        exact (upd_ne mw1 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). }
      assert (Ha0w2 : uint (mw2 !!! Regidx a0_idx) = 0).
      { rewrite (upd_ne mw1 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
        vm_compute. reflexivity. }
      (* ---- wait(0) ---- *)
      iApply (wp_kinit_wait γt γd γs hw2 mw2 (12 + (12 + (4 + n))) Ha0w2
                with "Hcode Hrun").
      iIntros (hw3 ret) "Hrun".
      assert (Eretw : ret_pc (mw2 !!! Regidx ra_idx)
                      = (mword_of_int 0x4a : mword 64))
        by (rewrite Hraw2; apply bv_eq; vm_compute; reflexivity).
      rewrite Eretw.
      set (mw3 := <[Regidx a0_idx := ret]>
                    (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> mw2)).
      assert (Hs2w3 : mw3 !!! Regidx s2_idx = mword_of_int LIT_START).
      { rewrite <- Hs2w2.
        rewrite /mw3 (upd_ne _ (Regidx a0_idx) (Regidx s2_idx) ret
                        ltac:(vm_compute; discriminate)).
        exact (upd_ne mw2 (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). }
      (* ---- 0x4a  beq a0,s1,0x32 -- BACK EDGE to the restart head ---- *)
      assert (Etgt4a : add_vec (mword_of_int 0x4a : mword 64)
                         (sign_extend' 64 (mword_of_int 8168 : mword 13))
                       = mword_of_int 0x32)
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (uv_btaken BEQ (mw3 !!! Regidx s1_idx)
                  (mw3 !!! Regidx a0_idx)) eqn:Hbeq.
      * (* the child we forked was reaped: round again from 0x32 *)
        iApply (wp_uk_btype_later γt γd γs hw3 mw3 (mword_of_int 0x4a)
                  (mword_of_int 8168 : mword 13) a0_idx s1_idx BEQ true
                  (mword_of_int 0x32) (12 + (12 + (4 + n)))
                  (eq_sym Hbeq) (eq_sym Etgt4a)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_init_4a with "Hcode"). }
        iNext. iIntros (hw4) "Hrun".
        iDestruct "IH" as "[IH1 _]".
        iApply ("IH1" $! hw4 mw3 with "[] Hsz Hrun").
        iPureIntro. exact Hs2w3.
      * (* somebody else's child, or an error *)
        iApply (wp_uk_btype_later γt γd γs hw3 mw3 (mword_of_int 0x4a)
                  (mword_of_int 8168 : mword 13) a0_idx s1_idx BEQ false
                  (add_vec (mword_of_int 0x4a : mword 64)
                     (sign_extend' 64 (mword_of_int 8168 : mword 13)))
                  (12 + (12 + (4 + n)))
                  (eq_sym Hbeq) eq_refl ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_init_4a with "Hcode"). }
        assert (E4a : add_vec_int (mword_of_int 0x4a : mword 64) 4
                      = mword_of_int 0x4e)
          by (apply bv_eq; vm_compute; reflexivity).
        iNext. rewrite E4a. iIntros (hw4) "Hrun".
        (* ---- 0x4e  bge a0,x0,0x44 -- BACK EDGE to the wait head ---- *)
        assert (Etgt4e : add_vec (mword_of_int 0x4e : mword 64)
                           (sign_extend' 64 (mword_of_int 8182 : mword 13))
                         = mword_of_int 0x44)
          by (apply bv_eq; vm_compute; reflexivity).
        destruct (uv_btaken BGE (mw3 !!! Regidx a0_idx) zero_reg) eqn:Hbge.
        + (* an orphan: keep waiting *)
          iApply (wp_uk_btype0_later γt γd γs hw4 mw3 (mword_of_int 0x4e)
                    (mword_of_int 8182 : mword 13) a0_idx BGE true
                    (mword_of_int 0x44) (12 + (12 + (4 + n)))
                    (eq_sym Hbge) (eq_sym Etgt4e)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_init_4e with "Hcode"). }
          iNext. iIntros (hw5) "Hrun".
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! hw5 mw3 with "[] Hsz Hrun").
          iPureIntro. exact Hs2w3.
        + (* wait itself failed: the diagnostic at 0x52 *)
          iApply (wp_uk_btype0_later γt γd γs hw4 mw3 (mword_of_int 0x4e)
                    (mword_of_int 8182 : mword 13) a0_idx BGE false
                    (add_vec (mword_of_int 0x4e : mword 64)
                       (sign_extend' 64 (mword_of_int 8182 : mword 13)))
                    (12 + (12 + (4 + n)))
                    (eq_sym Hbge) eq_refl ltac:(discriminate)
                    with "[] Hrun").
          { iApply (uis_init_4e with "Hcode"). }
          assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 4
                        = mword_of_int 0x52)
            by (apply bv_eq; vm_compute; reflexivity).
          iNext. rewrite E4e. iIntros (hw5) "Hrun".
          iApply (wp_kinit_main_die_dw γt γd γs hw5 _ n with "Hcode Hro Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* main FROM 0x1e -- the two dups, the literal pointer, and into the loop. *)
  (* Both arms of the console test rejoin HERE: the fall-through when open   *)
  (* succeeded, and the [c.j] at 0x82 when the mknod repair arm has run.     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_from_1e (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun γt γd γs h m (mword_of_int 0x1e) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hsz Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hdup & _ & _ & _ & _ & _).
    (* ---- 0x1e  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x1e)
              (mword_of_int 0 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_1e with "Hcode"). }
    assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2
                  = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1e.
    iIntros (hq1) "Hrun".
    set (mq1 := <[Regidx a0_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> m).
    (* ---- 0x20  jal ra,0x3ea <dup> ---- *)
    iApply (wp_uk_jal γt γd γs hq1 mq1 (mword_of_int 0x20)
              (mword_of_int 970 : mword 21) ra_idx
              (mword_of_int InitSyms.dup) (mword_of_int 0x24) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hdup; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hdup; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_20 with "Hcode"). }
    iIntros (hq2) "Hrun".
    set (mq2 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x24 : mword 64)]> mq1).
    assert (Hraq2 : mq2 !!! Regidx ra_idx = (mword_of_int 0x24 : mword 64))
      by exact (upd_eq mq1 (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kinit_dup γt γd γs hq2 mq2 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hq3 r1) "Hrun".
    assert (Eq2 : ret_pc (mq2 !!! Regidx ra_idx)
                  = (mword_of_int 0x24 : mword 64))
      by (rewrite Hraq2; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq2.
    set (mq3 := <[Regidx a0_idx := r1]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq2)).
    (* ---- 0x24  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs hq3 mq3 (mword_of_int 0x24)
              (mword_of_int 0 : mword 6) a0_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_24 with "Hcode"). }
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24.
    iIntros (hq4) "Hrun".
    set (mq4 := <[Regidx a0_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> mq3).
    (* ---- 0x26  jal ra,0x3ea <dup> ---- *)
    iApply (wp_uk_jal γt γd γs hq4 mq4 (mword_of_int 0x26)
              (mword_of_int 964 : mword 21) ra_idx
              (mword_of_int InitSyms.dup) (mword_of_int 0x2a) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hdup; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hdup; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_26 with "Hcode"). }
    iIntros (hq5) "Hrun".
    set (mq5 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x2a : mword 64)]> mq4).
    assert (Hraq5 : mq5 !!! Regidx ra_idx = (mword_of_int 0x2a : mword 64))
      by exact (upd_eq mq4 (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kinit_dup γt γd γs hq5 mq5 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hq6 r2) "Hrun".
    assert (Eq5 : ret_pc (mq5 !!! Regidx ra_idx)
                  = (mword_of_int 0x2a : mword 64))
      by (rewrite Hraq5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq5.
    set (mq6 := <[Regidx a0_idx := r2]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq5)).
    (* ---- 0x2a  auipc s2,0x1 ; 0x2e addi s2,s2,-1714 -- the literal ---- *)
    iApply (wp_uk_auipc γt γd γs hq6 mq6 (mword_of_int 0x2a)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x2a : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20)))
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_2a with "Hcode"). }
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 4
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2a.
    iIntros (hq7) "Hrun".
    set (mq7 := <[Regidx s2_idx := regval_into_reg
                    (add_vec (mword_of_int 0x2a : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mq6).
    assert (Elit : add_vec (add_vec (mword_of_int 0x2a : mword 64)
                              (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2382 : mword 12))
                   = mword_of_int LIT_START)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs hq7 mq7 (mword_of_int 0x2e)
              (mword_of_int 2382 : mword 12) s2_idx s2_idx
              (mword_of_int LIT_START) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mq6 (Regidx s2_idx) (regval_into_reg _));
                    exact (eq_sym Elit))
              with "[] Hrun").
    { iApply (uis_init_2e with "Hcode"). }
    assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4
                  = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2e.
    iIntros (hq8) "Hrun".
    set (mq8 := <[Regidx s2_idx
                  := regval_into_reg (mword_of_int LIT_START : mword 64)]> mq7).
    assert (Hs2q8 : mq8 !!! Regidx s2_idx = mword_of_int LIT_START)
      by exact (upd_eq mq7 (Regidx s2_idx) (regval_into_reg _)).
    (* ---- 0x32: the restart head, and main never comes back ---- *)
    iDestruct (wp_kinit_main_loop szv n with "Hcode Hro") as "[Hloop _]".
    iApply ("Hloop" $! hq8 mq8 with "[] Hsz Hrun").
    iPureIntro. exact Hs2q8.
  Qed.



  (* --------------------------------------------------------------------- *)
  (* THE CONSOLE REPAIR ARM @0x64: the console device node does not exist    *)
  (* yet, so make it and open it again.  Rejoins the main line at 0x1e.      *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_repair (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun γt γd γs h m (mword_of_int 0x64) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hsz Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & Hmknod & _ & _ & _ & _ & _ & _).
    (* ---- 0x64  c.li a2,0 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x64)
              (mword_of_int 0 : mword 6) a2_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_64 with "Hcode"). }
    assert (E64 : add_vec_int (mword_of_int 0x64 : mword 64) 2
                  = mword_of_int 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E64.
    iIntros (hr1) "Hrun".
    set (mr1 := <[Regidx a2_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> m).
    (* ---- 0x66  c.li a1,1 -- CONSOLE ---- *)
    iApply (wp_uk_cli γt γd γs hr1 mr1 (mword_of_int 0x66)
              (mword_of_int 1 : mword 6) a1_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_66 with "Hcode"). }
    assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2
                  = mword_of_int 0x68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E66.
    iIntros (hr2) "Hrun".
    set (mr2 := <[Regidx a1_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> mr1).
    (* ---- 0x68  auipc a0 ; 0x6c  addi -- 0x970 ---- *)
    assert (Er68 : add_vec (add_vec (mword_of_int 0x68 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                   (sign_extend' 64 (mword_of_int 2312 : mword 12))
                 = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hr2 mr2 (mword_of_int 0x68)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x68 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_68 with "Hcode"). }
    assert (Eur68 : add_vec_int (mword_of_int 0x68 : mword 64) 4
                   = mword_of_int 0x6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eur68.
    iIntros (hr2a) "Hrun".
    set (mr2a := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0x68 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mr2).
    iApply (wp_uk_addi γt γd γs hr2a mr2a (mword_of_int 0x6c)
              (mword_of_int 2312 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mr2 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Er68))
              with "[] Hrun").
    { iApply (uis_init_6c with "Hcode"). }
    assert (Eir68 : add_vec_int (mword_of_int 0x6c : mword 64) 4
                   = mword_of_int 0x70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eir68.
    iIntros (hr2b) "Hrun".
    set (mr2b := <[Regidx a0_idx := regval_into_reg
                    (mword_of_int 0x970 : mword 64)]> mr2a).
    (* ---- 0x70  jal ra,0x3ba <mknod> ---- *)
    iApply (wp_uk_jal γt γd γs hr2b mr2b (mword_of_int 0x70)
              (mword_of_int 842 : mword 21) ra_idx
              (mword_of_int InitSyms.mknod) (mword_of_int 0x74)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmknod; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmknod; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_70 with "Hcode"). }
    iIntros (hr3) "Hrun".
    set (mr3 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x74 : mword 64)]> mr2b).
    assert (Hrar3 : mr3 !!! Regidx ra_idx = (mword_of_int 0x74 : mword 64))
      by exact (upd_eq mr2b (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kinit_mknod γt γd γs hr3 mr3 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hr4 rr1) "Hrun".
    assert (Er3 : ret_pc (mr3 !!! Regidx ra_idx)
                  = (mword_of_int 0x74 : mword 64))
      by (rewrite Hrar3; apply bv_eq; vm_compute; reflexivity).
    rewrite Er3.
    set (mr4 := <[Regidx a0_idx := rr1]>
                  (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> mr3)).
    (* ---- 0x74  c.li a1,2 -- O_RDWR ---- *)
    iApply (wp_uk_cli γt γd γs hr4 mr4 (mword_of_int 0x74)
              (mword_of_int 2 : mword 6) a1_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_74 with "Hcode"). }
    assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2
                  = mword_of_int 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E74.
    iIntros (hr5) "Hrun".
    set (mr5 := <[Regidx a1_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 2 : mword 6)
                        : mword 64)]> mr4).
    (* ---- 0x76  auipc a0 ; 0x7a  addi -- 0x970 ---- *)
    assert (Er76 : add_vec (add_vec (mword_of_int 0x76 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                   (sign_extend' 64 (mword_of_int 2298 : mword 12))
                 = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hr5 mr5 (mword_of_int 0x76)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x76 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_76 with "Hcode"). }
    assert (Eur76 : add_vec_int (mword_of_int 0x76 : mword 64) 4
                   = mword_of_int 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eur76.
    iIntros (hr5a) "Hrun".
    set (mr5a := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0x76 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mr5).
    iApply (wp_uk_addi γt γd γs hr5a mr5a (mword_of_int 0x7a)
              (mword_of_int 2298 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mr5 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Er76))
              with "[] Hrun").
    { iApply (uis_init_7a with "Hcode"). }
    assert (Eir76 : add_vec_int (mword_of_int 0x7a : mword 64) 4
                   = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eir76.
    iIntros (hr5b) "Hrun".
    set (mr5b := <[Regidx a0_idx := regval_into_reg
                    (mword_of_int 0x970 : mword 64)]> mr5a).
    (* ---- 0x7e  jal ra,0x3b2 <open> ---- *)
    iApply (wp_uk_jal γt γd γs hr5b mr5b (mword_of_int 0x7e)
              (mword_of_int 820 : mword 21) ra_idx
              (mword_of_int InitSyms.open) (mword_of_int 0x82)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hopen; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hopen; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_7e with "Hcode"). }
    iIntros (hr6) "Hrun".
    set (mr6 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x82 : mword 64)]> mr5b).
    assert (Hrar6 : mr6 !!! Regidx ra_idx = (mword_of_int 0x82 : mword 64))
      by exact (upd_eq mr5b (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kinit_open γt γd γs hr6 mr6 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hr7 rr2) "Hrun".
    assert (Er6 : ret_pc (mr6 !!! Regidx ra_idx)
                  = (mword_of_int 0x82 : mword 64))
      by (rewrite Hrar6; apply bv_eq; vm_compute; reflexivity).
    rewrite Er6.
    set (mr7 := <[Regidx a0_idx := rr2]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mr6)).
    (* ---- 0x82  c.j 0x1e -- back to the main line ---- *)
    assert (Etgt82 : (mword_of_int 0x1e : mword 64)
                     = add_vec (mword_of_int 0x82 : mword 64)
                         (sign_extend' 64
                            (sign_extend' 21
                               (concat_vec (mword_of_int 1998 : mword 11)
                                  ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs hr7 mr7 (mword_of_int 0x82)
              (mword_of_int 1998 : mword 11) (mword_of_int 0x1e)
              (12 + (12 + (4 + n)))
              Etgt82 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_82 with "Hcode"). }
    iIntros (hr8) "Hrun".
    iApply (wp_kinit_main_from_1e szv hr8 mr7 n with "Hcode Hro Hsz Hrun").
  Qed.



  (* --------------------------------------------------------------------- *)
  (* main @0x0.  The prologue takes a four-word frame and spills ra, s0, s1  *)
  (* and s2 into it -- and NEVER READS THEM AGAIN, because main does not     *)
  (* return.  They are dropped here rather than threaded through the loop.   *)
  (*                                                                        *)
  (* Then open("console", O_RDWR), and BOTH arms of its test are walked: the *)
  (* success path falls through to 0x1e, the failure path goes to the mknod  *)
  (* repair arm at 0x64, which rejoins at 0x1e.  Nothing is assumed about    *)
  (* which one the kernel takes.                                             *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun γt γd γs h m (mword_of_int InitSyms.main)
      (4 + (12 + (12 + (4 + n)))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hsz Hrun".
    destruct init_syms_pins
      as (_ & Hmain & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    rewrite Hmain.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 32 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) 4 (12 + (12 + (4 + n)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_00 with "Hcode"). }
    iIntros "Hframe".
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E00.
    iIntros (hm0) "Hrun".
    set (mm1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hspm1 : mm1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_4_open with "Hframe")
      as "(_ & [%v1 Hv1] & [%v2 Hv2] & [%v3 Hv3] & [%v4 Hv4])".
    (* ---- 0x2 0x4 0x6 0x8: spill ra, s0, s1, s2 ---- *)
    iApply (wp_uk_csdsp γt γd γs hm0 mm1 (mword_of_int 0x2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) v1
              (12 + (12 + (4 + n)))
              ltac:(rewrite Hspm1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hv1 Hrun").
    { iApply (uis_init_02 with "Hcode"). }
    iIntros "Hv1".
    assert (E02 : add_vec_int (mword_of_int 0x2 : mword 64) 2
                  = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02. iIntros (hm1) "Hrun".
    iApply (wp_uk_csdsp γt γd γs hm1 mm1 (mword_of_int 0x4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) v2
              (12 + (12 + (4 + n)))
              ltac:(rewrite Hspm1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hv2 Hrun").
    { iApply (uis_init_04 with "Hcode"). }
    iIntros "Hv2".
    assert (E04 : add_vec_int (mword_of_int 0x4 : mword 64) 2
                  = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04. iIntros (hm2) "Hrun".
    iApply (wp_uk_csdsp γt γd γs hm2 mm1 (mword_of_int 0x6)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24) v3
              (12 + (12 + (4 + n)))
              ltac:(rewrite Hspm1 Hsp32 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hv3 Hrun").
    { iApply (uis_init_06 with "Hcode"). }
    iIntros "Hv3".
    assert (E06 : add_vec_int (mword_of_int 0x6 : mword 64) 2
                  = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06. iIntros (hm3) "Hrun".
    iApply (wp_uk_csdsp γt γd γs hm3 mm1 (mword_of_int 0x8)
              (mword_of_int 0 : mword 6) s2_idx (uint sp0 - 32) v4
              (12 + (12 + (4 + n)))
              ltac:(rewrite Hspm1 Hsp32 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hv4 Hrun").
    { iApply (uis_init_08 with "Hcode"). }
    iIntros "Hv4".
    assert (E08 : add_vec_int (mword_of_int 0x8 : mword 64) 2
                  = mword_of_int 0xa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08. iIntros (hm4) "Hrun".
    (* ---- 0xa  c.addi4spn s0,sp,32 ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) ltac:(apply Z.leb_le; reflexivity) Hlt4).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 4))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs hm4 mm1 (mword_of_int 0xa)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx sp0
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hspm1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_init_0a with "Hcode"). }
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2
                  = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a. iIntros (hm5) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg sp0]> mm1).
    (* ---- 0xc  c.li a1,2 -- O_RDWR ---- *)
    iApply (wp_uk_cli γt γd γs hm5 mm2 (mword_of_int 0xc)
              (mword_of_int 2 : mword 6) a1_idx (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_0c with "Hcode"). }
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c. iIntros (hm6) "Hrun".
    set (mm3 := <[Regidx a1_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 2 : mword 6)
                        : mword 64)]> mm2).
    (* ---- 0xe  auipc a0,0x1 ; 0x12  addi a0,a0,-1694 -- "console" ---- *)
    assert (Econ : add_vec (add_vec (mword_of_int 0xe : mword 64)
                              (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2402 : mword 12))
                   = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hm6 mm3 (mword_of_int 0xe)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0xe : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20)))
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_0e with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 4
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e. iIntros (hm7) "Hrun".
    set (mm4 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0xe : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mm3).
    iApply (wp_uk_addi γt γd γs hm7 mm4 (mword_of_int 0x12)
              (mword_of_int 2402 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mm3 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Econ))
              with "[] Hrun").
    { iApply (uis_init_12 with "Hcode"). }
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12. iIntros (hm8) "Hrun".
    set (mm5 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int 0x970 : mword 64)]> mm4).
    (* ---- 0x16  jal ra,0x3b2 <open> ---- *)
    iApply (wp_uk_jal γt γd γs hm8 mm5 (mword_of_int 0x16)
              (mword_of_int 924 : mword 21) ra_idx
              (mword_of_int InitSyms.open) (mword_of_int 0x1a)
              (12 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hopen; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hopen; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_16 with "Hcode"). }
    iIntros (hm9) "Hrun".
    set (mm6 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x1a : mword 64)]> mm5).
    assert (Hram6 : mm6 !!! Regidx ra_idx = (mword_of_int 0x1a : mword 64))
      by exact (upd_eq mm5 (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kinit_open γt γd γs hm9 mm6 (12 + (12 + (4 + n)))
              with "Hcode Hrun").
    iIntros (hm10 ro) "Hrun".
    assert (Em6 : ret_pc (mm6 !!! Regidx ra_idx)
                  = (mword_of_int 0x1a : mword 64))
      by (rewrite Hram6; apply bv_eq; vm_compute; reflexivity).
    rewrite Em6.
    set (mm7 := <[Regidx a0_idx := ro]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mm6)).
    (* ---- 0x1a  blt a0,x0,0x64 -- did the console exist? ---- *)
    assert (Etgt1a : add_vec (mword_of_int 0x1a : mword 64)
                       (sign_extend' 64 (mword_of_int 74 : mword 13))
                     = mword_of_int 0x64)
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (uv_btaken BLT (mm7 !!! Regidx a0_idx) zero_reg) eqn:Hblt0.
    - (* it did not: make it, then open it again *)
      iApply (wp_uk_btype0 γt γd γs hm10 mm7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT true
                (mword_of_int 0x64) (12 + (12 + (4 + n)))
                (eq_sym Hblt0) (eq_sym Etgt1a)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_1a with "Hcode"). }
      iIntros (hm11) "Hrun".
      iApply (wp_kinit_main_repair szv hm11 mm7 n with "Hcode Hro Hsz Hrun").
    - (* it did: straight on to the dups *)
      iApply (wp_uk_btype0 γt γd γs hm10 mm7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT false
                (add_vec (mword_of_int 0x1a : mword 64)
                   (sign_extend' 64 (mword_of_int 74 : mword 13)))
                (12 + (12 + (4 + n)))
                (eq_sym Hblt0) eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_init_1a with "Hcode"). }
      assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4
                    = mword_of_int 0x1e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1a. iIntros (hm11) "Hrun".
      iApply (wp_kinit_main_from_1e szv hm11 mm7 n with "Hcode Hro Hsz Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* start @0xbc -- the ELF entry point.  Two words of frame, then main,     *)
  (* which never returns; the [jal exit] at 0xc8 is unreachable and is not   *)
  (* walked (there is no continuation to walk it from).                      *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_start (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun γt γd γs h m (mword_of_int InitSyms.start)
      (2 + (4 + (12 + (12 + (4 + n))))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hsz Hrun".
    destruct init_syms_pins
      as (Hstart & Hmain & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    rewrite Hstart.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xbc  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0xbc)
              (mword_of_int 48 : mword 6) 2 (4 + (12 + (12 + (4 + n))))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_bc with "Hcode"). }
    iIntros "Hframe".
    assert (Ebc : add_vec_int (mword_of_int 0xbc : mword 64) 2
                  = mword_of_int 0xbe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp Ebc.
    iIntros (hs0) "Hrun".
    set (ms1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsps1 : ms1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_2 γd sp0) as "[Hopen _]".
    iDestruct ("Hopen" with "Hframe") as "(_ & [%u1 Hu1] & [%u2 Hu2])".
    (* ---- 0xbe  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs0 ms1 (mword_of_int 0xbe)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) u1
              (4 + (12 + (12 + (4 + n))))
              ltac:(rewrite Hsps1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu1 Hrun").
    { iApply (uis_init_be with "Hcode"). }
    iIntros "Hu1".
    assert (Ebe : add_vec_int (mword_of_int 0xbe : mword 64) 2
                  = mword_of_int 0xc0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ebe. iIntros (hs1) "Hrun".
    (* ---- 0xc0  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs hs1 ms1 (mword_of_int 0xc0)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) u2
              (4 + (12 + (12 + (4 + n))))
              ltac:(rewrite Hsps1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu2 Hrun").
    { iApply (uis_init_c0 with "Hcode"). }
    iIntros "Hu2".
    assert (Ec0 : add_vec_int (mword_of_int 0xc0 : mword 64) 2
                  = mword_of_int 0xc2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ec0. iIntros (hs2) "Hrun".
    (* ---- 0xc2  c.addi4spn s0,sp,16 ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) ltac:(apply Z.leb_le; reflexivity) Hlt2).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 2))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs hs2 ms1 (mword_of_int 0xc2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx sp0
              (4 + (12 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsps1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_init_c2 with "Hcode"). }
    assert (Ec2 : add_vec_int (mword_of_int 0xc2 : mword 64) 2
                  = mword_of_int 0xc4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ec2. iIntros (hs3) "Hrun".
    set (ms2 := <[Regidx s0_idx := regval_into_reg sp0]> ms1).
    (* ---- 0xc4  jal ra,0x0 <main> -- and main never returns ---- *)
    iApply (wp_uk_jal γt γd γs hs3 ms2 (mword_of_int 0xc4)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int InitSyms.main) (mword_of_int 0xc8)
              (4 + (12 + (12 + (4 + n))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_c4 with "Hcode"). }
    iIntros (hs4) "Hrun".
    iApply (wp_kinit_main szv hs4 _ n with "Hcode Hro Hsz Hrun").
  Qed.

End UkInitMain.
