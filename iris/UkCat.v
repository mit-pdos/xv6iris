(* ===================================================================== *)
(* UkCat.v -- the `cat` program's SYSCALL STUB layer.                      *)
(*                                                                        *)
(* usys.S's three-instruction bodies: the number into a7, [ecall],         *)
(* return.  Five of them, and the row each takes is the whole of what      *)
(* distinguishes them:                                                    *)
(*                                                                        *)
(*   open, close, write   the QUIET row -- none of the three writes a user *)
(*                        byte, so the heap comes back as it went in.      *)
(*                        write READS the buffer, but the row does not     *)
(*                        make the caller own it: nothing the kernel does  *)
(*                        to its own copy is visible here.                 *)
(*   exit                 the arm with no continuation                     *)
(*   read                 THE ONE THAT WRITES.  The caller hands in the    *)
(*                        whole count as a run it owns and gets the whole  *)
(*                        count back at SOME contents; see                 *)
(*                        [UkRunSys.wp_uk_ecall_read] for why owning less  *)
(*                        would not do.                                    *)
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
Require Import RegFile.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.CatInstrs.
Local Open Scope Z_scope.
Import Defs.

Local Open Scope Z_scope.
Import Defs.

Section UkCat.
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


  Lemma wp_kcat_open (h : CpuId) (m : regfile) (avail : nat) :
    cat_code γt -∗
    urun γt γd γs h m (mword_of_int CatSyms.open) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hopen.
    (* ---- 0x3ec  c.li a7,15 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ec)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ec with "Hcode"). }
    assert (E0open : add_vec_int (mword_of_int 0x3ec : mword 64) 2
                   = mword_of_int 0x3ee)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emopen : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 15 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0open Emopen.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    (* ---- 0x3ee  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3ee) 15 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ee with "Hcode"). }
    assert (E1open : add_vec_int (mword_of_int 0x3ee : mword 64) 4
                   = mword_of_int 0x3f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1open.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f2  c.jr ra ---- *)
    assert (Hraopen : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3f2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraopen; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3f2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kcat_close (h : CpuId) (m : regfile) (avail : nat) :
    cat_code γt -∗
    urun γt γd γs h m (mword_of_int CatSyms.close) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hclose.
    (* ---- 0x3d4  c.li a7,21 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3d4)
              (mword_of_int 21 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3d4 with "Hcode"). }
    assert (E0close : add_vec_int (mword_of_int 0x3d4 : mword 64) 2
                   = mword_of_int 0x3d6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emclose : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 21 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0close Emclose.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    (* ---- 0x3d6  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3d6) 21 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3d6 with "Hcode"). }
    assert (E1close : add_vec_int (mword_of_int 0x3d6 : mword 64) 4
                   = mword_of_int 0x3da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1close.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3da  c.jr ra ---- *)
    assert (Hraclose : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 21 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3da) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraclose; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3da with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kcat_write (h : CpuId) (m : regfile) (avail : nat) :
    cat_code γt -∗
    urun γt γd γs h m (mword_of_int CatSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwrite & Hopen & Hclose & _).
    rewrite Hwrite.
    (* ---- 0x3cc  c.li a7,16 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3cc)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3cc with "Hcode"). }
    assert (E0write : add_vec_int (mword_of_int 0x3cc : mword 64) 2
                   = mword_of_int 0x3ce)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emwrite : <[Regidx a7_idx
                     := regval_into_reg
                          (sign_extend' 64 (mword_of_int 16 : mword 6)
                           : mword 64)]> m
                   = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0write Emwrite.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x3ce  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3ce) 16 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ce with "Hcode"). }
    assert (E1write : add_vec_int (mword_of_int 0x3ce : mword 64) 4
                   = mword_of_int 0x3d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1write.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3d2  c.jr ra ---- *)
    assert (Hrawrite : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3d2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrawrite; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3d2 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* exit @0x3ac -- no continuation.                                        *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_exit (h : CpuId) (m : regfile) (avail : nat) :
    cat_code γt -∗
    urun γt γd γs h m (mword_of_int CatSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    rewrite Hexit.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ac)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3ac with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0x3ac : mword 64) 2
                  = mword_of_int 0x3ae)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eme : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 2 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0e Eme.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    iApply (wp_uk_ecall_exit γt γd γs h1 m1 (mword_of_int 0x3ae) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ae with "Hcode"). }
  Qed.

  (* --------------------------------------------------------------------- *)
  (* read @0x3c4 -- THE STUB THAT WRITES.  The caller hands in the whole    *)
  (* count as a run it owns and gets the whole count back at SOME contents; *)
  (* the row does not say which bytes moved, does not say how many, and     *)
  (* does not tie either to the value returned.                             *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_read (a : Z) (cnt : nat) (f : nat -> bv 8)
      (h : CpuId) (m : regfile) (avail : nat) :
    m !!! Regidx a1_idx = (mword_of_int a : mword 64) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cnt ->
    cat_code γt -∗
    ubytes γd a cnt f -∗
    urun γt γd γs h m (mword_of_int CatSyms.read) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (g : nat -> bv 8),
       ubytes γd a cnt g -∗
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1 Hcnt. iIntros "#Hcode Hbs Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hread & _ & _ & _ & _).
    rewrite Hread.
    (* ---- 0x3c4  c.li a7,5 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3c4)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_3c4 with "Hcode"). }
    assert (E0r : add_vec_int (mword_of_int 0x3c4 : mword 64) 2
                  = mword_of_int 0x3c6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Emr : <[Regidx a7_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 5 : mword 6)
                          : mword 64)]> m
                  = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0r Emr.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    (* the buffer pointer and the count survive the write to a7 *)
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int a : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcntr : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0
                               : mword 32) = Z.of_nat cnt).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hcnt. }
    (* ---- 0x3c6  ecall -- the row that MOVES THE IMAGE ---- *)
    iApply (wp_uk_ecall_read γt γd γs h1 m1 (mword_of_int 0x3c6) a cnt f avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 5 : mword 64));
                    vm_compute; reflexivity)
              Ha1r Hcntr ltac:(vm_compute; reflexivity)
              with "[] Hbs Hrun").
    { iApply (uis_cat_3c6 with "Hcode"). }
    assert (E1r : add_vec_int (mword_of_int 0x3c6 : mword 64) 4
                  = mword_of_int 0x3ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1r.
    iIntros (h2 ret g) "Hbs Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3ca  c.jr ra ---- *)
    assert (Hrar : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3ca) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_3ca with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret g with "Hbs Hrun").
  Qed.

End UkCat.
