(* ===================================================================== *)
(* UkInit.v -- the `init` program on the separation-logic heap.            *)
(*                                                                        *)
(* Three things make init different from sync and echo:                    *)
(*                                                                        *)
(*   IT DOES NOT TERMINATE.  main's restart loop and its inner wait loop   *)
(*   both run forever, so main and start have no continuation and no       *)
(*   postcondition, and the two loops close through [iLoeb] and            *)
(*   [wp_uk_btype_later] -- the first unbounded loops in this tier.        *)
(*                                                                        *)
(*   IT ASSUMES NOTHING ABOUT WHAT THE KERNEL RETURNS.  Every arm of every *)
(*   test in main is reachable, because init handles each failure itself:  *)
(*   mknod when the console is missing, and a diagnostic printf + exit(1)  *)
(*   when fork, exec or wait fails.                                        *)
(*                                                                        *)
(*   IT PRINTS.  The whole printf cone (printf -> vprintf -> putc ->       *)
(*   write) is verified here for a format string containing no '%', which  *)
(*   is what all four of init's literals are -- so printf is a glorified   *)
(*   write(1, s, len).                                                     *)
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

Section UkInit.
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

  (* ===================================================================== *)
  (* THE SYSCALL STUBS.  usys.S's three-instruction bodies: the number into *)
  (* a7, [ecall], return.  Eight of them, and the row each takes is the     *)
  (* whole of what distinguishes them:                                      *)
  (*                                                                        *)
  (*   open, mknod, dup, write   the QUIET row -- none of the four writes    *)
  (*                             a user byte, so the heap comes back as it   *)
  (*                             went in                                     *)
  (*   exit                      the arm with no continuation                *)
  (*   wait                      the null-status-pointer arm: init passes    *)
  (*                             a null pointer, so nothing is copied out    *)
  (*   exec                      the failure arm, which is the only one      *)
  (*                             that returns here at all                    *)
  (*   fork                      two successors; see the fork leaf           *)
  (* ===================================================================== *)
  Lemma wp_kinit_open (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.open) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_3b2 with "Hcode") as "#C3b2".
    iDestruct (uis_init_3b4 with "Hcode") as "#C3b4".
    iDestruct (uis_init_3b8 with "Hcode") as "#C3b8".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C3b2 Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x3b2 : mword 64) 2
                 = mword_of_int 0x3b4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    (* ---- 0x3b4  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3b4) 15 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "C3b4 Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3b8  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C3b8 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kinit_mknod (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.mknod) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_3ba with "Hcode") as "#C3ba".
    iDestruct (uis_init_3bc with "Hcode") as "#C3bc".
    iDestruct (uis_init_3c0 with "Hcode") as "#C3c0".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ba)
              (mword_of_int 17 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C3ba Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x3ba : mword 64) 2
                 = mword_of_int 0x3bc)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 17 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m).
    (* ---- 0x3bc  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3bc) 17 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 17 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "C3bc Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x3bc : mword 64) 4
                 = mword_of_int 0x3c0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3c0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3c0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C3c0 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kinit_dup (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.dup) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_3ea with "Hcode") as "#C3ea".
    iDestruct (uis_init_3ec with "Hcode") as "#C3ec".
    iDestruct (uis_init_3f0 with "Hcode") as "#C3f0".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C3ea Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    (* ---- 0x3ec  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x3ec) 10 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "C3ec Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C3f0 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kinit_write (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_392 with "Hcode") as "#C392".
    iDestruct (uis_init_394 with "Hcode") as "#C394".
    iDestruct (uis_init_398 with "Hcode") as "#C398".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwrite.
    (* ---- 0x392  c.li a7,16 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x392)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C392 Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x392 : mword 64) 2
                 = mword_of_int 0x394)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x394  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x394) 16 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "C394 Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x394 : mword 64) 4
                 = mword_of_int 0x398)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x398  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x398) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C398 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kinit_exit (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    iDestruct (uis_init_372 with "Hcode") as "#C372".
    iDestruct (uis_init_374 with "Hcode") as "#C374".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexit.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x372)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C372 Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x372 : mword 64) 2
                 = mword_of_int 0x374)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    iApply (wp_uk_ecall_exit γt γd γs h1 m1 (mword_of_int 0x374) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "C374 Hrun").
  Qed.

  Lemma wp_kinit_exec (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.exec) avail -∗
    (* exec only comes back when it FAILED, and then it returns -1 *)
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
            (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_3aa with "Hcode") as "#C3aa".
    iDestruct (uis_init_3ac with "Hcode") as "#C3ac".
    iDestruct (uis_init_3b0 with "Hcode") as "#C3b0".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexec.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3aa)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C3aa Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x3aa : mword 64) 2
                 = mword_of_int 0x3ac)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 7 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    iApply (wp_uk_ecall_exec γt γd γs h1 m1 (mword_of_int 0x3ac) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "C3ac Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x3ac : mword 64) 4
                 = mword_of_int 0x3b0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 7 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x3b0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C3b0 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* init calls [wait] with a NULL status pointer, which is the only arm
     this tier can carry: the kernel's own [addr != 0] test means nothing
     is copied out, so the heap comes back untouched. *)
  Lemma wp_kinit_wait (h : CpuId) (m : regfile) (avail : nat) :
    uint (m !!! Regidx a0_idx) = 0 ->
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.wait) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hz.
    iIntros "#Hcode Hrun Hcont".
    iDestruct (uis_init_37a with "Hcode") as "#C37a".
    iDestruct (uis_init_37c with "Hcode") as "#C37c".
    iDestruct (uis_init_380 with "Hcode") as "#C380".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwait.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x37a)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "C37a Hrun").
    assert (E0 : add_vec_int (mword_of_int 0x37a : mword 64) 2
                 = mword_of_int 0x37c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 3 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m).
    assert (Ha0 : uint (m1 !!! Regidx a0_idx) = 0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 3 : mword 64) ltac:(vm_compute; discriminate)).
      exact Hz. }
    iApply (wp_uk_ecall_wait_null γt γd γs h1 m1 (mword_of_int 0x37c) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 3 : mword 64));
                    vm_compute; reflexivity)
              Ha0 ltac:(vm_compute; reflexivity)
              with "C37c Hrun").
    assert (E1 : add_vec_int (mword_of_int 0x37c : mword 64) 4
                 = mword_of_int 0x380)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 3 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x380) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "C380 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

End UkInit.
