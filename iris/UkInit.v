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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3b2 with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3b4 with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ba)
              (mword_of_int 17 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ba with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3bc with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3c0 with "Hcode"). }
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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3ec with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwrite.
    (* ---- 0x392  c.li a7,16 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x392)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_392 with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_394 with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_398 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma wp_kinit_exit (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexit.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x372)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_372 with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_374 with "Hcode"). }
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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexec.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x3aa)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3aa with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3ac with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_3b0 with "Hcode"). }
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
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwait.
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x37a)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_37a with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_37c with "Hcode"). }
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
              with "[] Hrun").
    { iApply (uis_init_380 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.


  (* ===================================================================== *)
  (* THE PRINTF CONE.  init's four format strings contain no '%', so the    *)
  (* whole cone is [printf(fmt) = write(1, fmt, strlen fmt)] spelled out    *)
  (* one character at a time: printf marshals its (unused) varargs and      *)
  (* tail-calls vprintf, vprintf walks the string and hands each byte to    *)
  (* putc, and putc spills that byte into its own frame and writes ONE      *)
  (* byte.  Nothing in the cone touches the caller's memory: every store    *)
  (* lands in a frame the function took off the free stack and gave back,   *)
  (* and write is the QUIET row.                                           *)
  (* ===================================================================== *)

  (* a callee-saved register is none of the ones a caller may clobber *)
  Local Lemma ucs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* putc(fd, c) @0x41a -- ulib's one-byte write.                            *)
  (*                                                                        *)
  (*   c.addi sp,sp,-32 ; c.sdsp ra,24(sp) ; c.sdsp s0,16(sp)                *)
  (*   c.addi4spn s0,sp,32 ; sb a1,-17(s0) ; c.li a2,1 ; addi a1,s0,-17      *)
  (*   jal <write> ; c.ldsp ra,24(sp) ; c.ldsp s0,16(sp)                     *)
  (*   c.addi16sp sp,sp,32 ; c.jr ra                                         *)
  (*                                                                        *)
  (* THE BYTE GOES IN THE FRAME.  [sb a1,-17(s0)] with s0 = the entry sp     *)
  (* lands at [sp0-17], which is byte 7 of the frame word at [sp0-24] --     *)
  (* hence the [uword_8] split and the [uword_of_bytes_8] reassembly, and    *)
  (* hence the fact that putc's whole memory effect is INSIDE the four       *)
  (* words it borrowed.  The caller gets its free stack back at the same     *)
  (* [avail] and learns nothing about the frame's contents, which is why     *)
  (* the post is [ucallee_saved] and nothing else.                           *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_putc (h : CpuId) (m : regfile) (n : nat) :
    init_code γt -∗
    urun γt γd γs h m (mword_of_int InitSyms.putc) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    destruct init_syms_pins
      as (_ & _ & _ & _ & Hputc & _ & _ & _ & _ & _ & _ & Hwrite & _).
    rewrite Hputc.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 32 <= uint sp0) by (clear -Hroom'; lia).
    (* the frame's bottom, and the round trip back up *)
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4))) = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    (* HR IS ITS OWN ASSERT, and [Hlt4]'s [lia] runs under [clear -].  Both
       matter.  [bv_unsigned_in_range 64 sp0] fixes the width index at [64 :
       N] while the goal's [bv_unsigned sp0] carries [sp0]'s own [Z_idx 64]
       -- convertible, but TWO ATOMS to [lia], which is why splicing the
       range in directly makes the goal unprovable rather than slow.  And a
       bare [lia] here reifies the whole [envs_entails Δ Q]: this one ran
       four minutes before failing. *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd4 : (0 <= 8 * Z.of_nat 4)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) Hd4 Hlt4).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Eb7 : (uint sp0 - 17)%Z = (uint sp0 - 24 + 7)%Z) by lia.
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x41a  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0x41a)
              (mword_of_int 32 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_41a with "Hcode"). }
    iIntros "Hframe".
    assert (E41a : add_vec_int (mword_of_int 0x41a : mword 64) 2
                   = mword_of_int 0x41c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E41a.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    (* the four words of the frame, by name -- DIRECTED, never [rewrite
       ustack_4]: that fires on the whole [envs_entails Δ Q] *)
    iDestruct (ustack_4_open with "Hframe")
      as "(_ & [%vra Hwra] & [%vs0 Hws0] & [%vb Hwb] & Hw32)".
    (* ---- 0x41c  c.sdsp ra,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0x41c)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(rewrite Hsp1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hwra Hrun").
    { iApply (uis_init_41c with "Hcode"). }
    iIntros "Hwra".
    assert (E41c : add_vec_int (mword_of_int 0x41c : mword 64) 2
                   = mword_of_int 0x41e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41c.
    iIntros (h2) "Hrun".
    (* ---- 0x41e  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0x41e)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(rewrite Hsp1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hws0 Hrun").
    { iApply (uis_init_41e with "Hcode"). }
    iIntros "Hws0".
    assert (E41e : add_vec_int (mword_of_int 0x41e : mword 64) 2
                   = mword_of_int 0x420)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41e.
    iIntros (h3) "Hrun".
    (* the two spilled values, as they will come back out *)
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- 0x420  c.addi4spn s0,sp,32 -- s0 := the ENTRY sp ---- *)
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 4))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0x420)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx sp0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_init_420 with "Hcode"). }
    assert (E420 : add_vec_int (mword_of_int 0x420 : mword 64) 2
                   = mword_of_int 0x422)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E420.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hs02 : m2 !!! Regidx s0_idx = sp0)
      by exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg sp0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x422  sb a1,-17(s0) -- the byte, into BYTE 7 of the third word ---- *)
    assert (Hoff17 : uoff_i12 (mword_of_int 4079 : mword 12) = -17)
      by (vm_compute; reflexivity).
    iDestruct (uword_byte7_acc γd (uint sp0 - 24) (uint sp0 - 17) vb Eb7
                 with "Hwb") as "(Hb7 & Hwbc)".
    iApply (wp_uk_sb γt γd γs h4 m2 (mword_of_int 0x422)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (uint sp0 - 17) (nth_byte vb 7%nat) n
              ltac:(rewrite Hs02 Hoff17; lia)
              with "[] Hb7 Hrun").
    { iApply (uis_init_422 with "Hcode"). }
    iIntros "Hb7".
    assert (E422 : add_vec_int (mword_of_int 0x422 : mword 64) 4
                   = mword_of_int 0x426)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E422.
    iIntros (h5) "Hrun".
    (* ...and the frame word is whole again, at SOME value *)
    iDestruct ("Hwbc" with "Hb7") as "Hwb".
    (* ---- 0x426  c.li a2,1 ---- *)
    iApply (wp_uk_cli γt γd γs h5 m2 (mword_of_int 0x426)
              (mword_of_int 1 : mword 6) a2_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_426 with "Hcode"). }
    assert (E426 : add_vec_int (mword_of_int 0x426 : mword 64) 2
                   = mword_of_int 0x428)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E426.
    iIntros (h6) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m2).
    assert (Hs03 : m3 !!! Regidx s0_idx = sp0).
    { rewrite <- Hs02.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x428  addi a1,s0,-17 ---- *)
    iApply (wp_uk_addi γt γd γs h6 m3 (mword_of_int 0x428)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (add_vec (m3 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 4079 : mword 12))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_init_428 with "Hcode"). }
    assert (E428 : add_vec_int (mword_of_int 0x428 : mword 64) 4
                   = mword_of_int 0x42c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E428.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (m3 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 4079 : mword 12)))]> m3).
    (* ---- 0x42c  jal ra,0x392 <write> ---- *)
    iApply (wp_uk_jal γt γd γs h7 m4 (mword_of_int 0x42c)
              (mword_of_int 2096998 : mword 21) ra_idx
              (mword_of_int InitSyms.write) (mword_of_int 0x430) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwrite; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_42c with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x430 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0x430 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- write(fd, sp0-17, 1) -- the QUIET row: no heap effect at all ---- *)
    iApply (wp_kinit_write h8 m5 n with "Hcode Hrun").
    iIntros (h9 ret) "Hrun".
    assert (Eret : ret_pc (m5 !!! Regidx ra_idx) = (mword_of_int 0x430 : mword 64))
      by (rewrite Hra5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m6 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)).
    (* every callee-saved register still holds its ENTRY value: the walk
       has written sp, s0, a2, a1, ra, a7 and a0, and of those only sp and
       s0 are callee-saved -- and both are about to be restored *)
    assert (Hsp6 : m6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite /m6 (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) ret
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne _ (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne _ (Regidx a2_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Hcs6 : forall r : mword 5, ucallee_saved_idx r = true ->
                     Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
                     m6 !!! Regidx r = m !!! Regidx r).
    (* NAMED disequalities, and [apply] before [vm_compute].  Written the
       obvious way -- [upd_ne _ (Regidx a0_idx) (Regidx r) ret ltac:(exact
       (ucs_ne r _ Hr ltac:(vm_compute; reflexivity)))] -- the INNER tactic
       runs while [ucs_ne]'s second register is still an evar, so
       [vm_compute] is handed [ucallee_saved_idx ?q = false].  That is the
       "inline [ltac:] in argument position" trap, and it cost two kills at
       41 GB and 49 GB before it was read as one.  [apply] first fixes the
       register from the goal; nothing here is spliced into a term. *)
    { intros r Hr Hrsp Hrs0.
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      rewrite /m6 (upd_ne (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)
                     (Regidx a0_idx) (Regidx r) ret Na0).
      rewrite (upd_ne m5 (Regidx a7_idx) (Regidx r)
                 (mword_of_int 16 : mword 64) Na7).
      rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx r)
                     (regval_into_reg (mword_of_int 0x430 : mword 64)) Nra).
      rewrite /m4 (upd_ne m3 (Regidx a1_idx) (Regidx r)
                     (regval_into_reg
                        (add_vec (m3 !!! Regidx s0_idx)
                           (sign_extend' 64 (mword_of_int 4079 : mword 12)))) Na1).
      rewrite /m3 (upd_ne m2 (Regidx a2_idx) (Regidx r)
                     (regval_into_reg
                        (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)) Na2).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg sp0) Hrs0).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4))))
                     Hrsp).
      reflexivity. }
    (* ---- 0x430  c.ldsp ra,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h9 m6 (mword_of_int 0x430)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8)
              (m1 !!! Regidx ra_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_init_430 with "Hcode"). }
    iIntros "Hwra".
    assert (E430 : add_vec_int (mword_of_int 0x430 : mword 64) 2
                   = mword_of_int 0x432)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E430.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx ra_idx := regval_into_reg (m1 !!! Regidx ra_idx)]> m6).
    assert (Hsp7 : m7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp6.
      exact (upd_ne m6 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x432  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h10 m7 (mword_of_int 0x432)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16)
              (m1 !!! Regidx s0_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp7 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_init_432 with "Hcode"). }
    iIntros "Hws0".
    assert (E432 : add_vec_int (mword_of_int 0x432 : mword 64) 2
                   = mword_of_int 0x434)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E432.
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx s0_idx := regval_into_reg (m1 !!! Regidx s0_idx)]> m7).
    assert (Hsp8 : m8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp7.
      exact (upd_ne m7 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x434  c.addi16sp sp,sp,32 -- THE POP: the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h11 m8 (mword_of_int 0x434)
              (mword_of_int 2 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hwb Hw32] Hrun").
    { iApply (uis_init_434 with "Hcode"). }
    { rewrite Hsp8 Hup.
      iApply (ustack_4_close γd sp0 Hal8 with "[Hwra] [Hws0] Hwb Hw32").
      { iExists (m1 !!! Regidx ra_idx). iExact "Hwra". }
      { iExists (m1 !!! Regidx s0_idx). iExact "Hws0". } }
    assert (E434 : add_vec_int (mword_of_int 0x434 : mword 64) 2
                   = mword_of_int 0x436)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp8 Hup E434.
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx csp_rs1 := regval_into_reg sp0]> m8).
    assert (Hra9 : m9 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_eq m6 (Regidx ra_idx) (regval_into_reg _)).
      exact Hra1. }
    (* ---- 0x436  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h12 m9 (mword_of_int 0x436) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra9; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_436 with "Hcode"). }
    iIntros (h13) "Hrun".
    iApply ("Hcont" $! h13 m9 with "[] Hrun").
    iPureIntro. intros r Hr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Hrsp | Hrsp].
    { rewrite Hrsp /m9 (upd_eq m8 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity. }
    rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx r)
                   (regval_into_reg sp0) Hrsp).
    destruct (decide (Regidx r = Regidx s0_idx)) as [Hrs0 | Hrs0].
    { rewrite Hrs0 /m8
        (upd_eq m7 (Regidx s0_idx) (regval_into_reg (m1 !!! Regidx s0_idx))).
      rewrite Hs01. reflexivity. }
    rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx s0_idx)) Hrs0).
    assert (Nra : Regidx r <> Regidx ra_idx)
      by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
    rewrite /m7 (upd_ne m6 (Regidx ra_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx ra_idx)) Nra).
    exact (Hcs6 r Hr Hrsp Hrs0).
  Qed.

End UkInit.
