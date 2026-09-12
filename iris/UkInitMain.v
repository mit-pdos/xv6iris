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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeInit.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UkInit.
Require Import UkInitLit.
Require Import UkInitPrintf.
Require Import UkFork.
Require Import UkRunBr.

Local Open Scope Z_scope.
Import Defs.

Require Import UserCwd.
Require Import UserChildren.  (* [uch_any] -- init's own half of its children
                                 set, index-free: fork MOVES the set, so the
                                 fragment travels with init's cwd from the
                                 entry constructor to the fork stub, and
                                 nothing on the walk reads it. *)
Require FsImg.  (* [FsImg.ROOTINO]: init is born in the root and never
                   chdirs, so its working directory is that inum forever --
                   which is what makes its exec of the RELATIVE "sh" name a
                   file.  QUALIFIED: this file has no other business with
                   the file-system tower. *)
Require Import FdSlots.  (* [fdstate] -- the head is stated at one *)
Require Import UInitFd.  (* the console prologue's ledger rows and INIT'S
                            HEAD, at an ABSTRACT descriptor state *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UsysMemOk. (* [USYS_exec] -- excluded by the minting law *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
Require Import UartNames.    (* [cons_names] *)
Require Import UserConsole.  (* [upos] / [upos_alloc] -- the console position
                                pair init mints per child *)
Section UkInitMain.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* WHAT THE WALK NEEDS OF THE PAYLOAD is that it does not read the exit
     status ([UkRun.ukn_const]), as a CLASS so that it reaches the exit
     ecall without an argument at every call site.  /init's OWN payload is
     the trivial one and its entry constructor says so
     ([UInitKernel.init_uexec_slot]); the CHILD it forks to exec sh runs
     at the console reader token instead ([UserConsole.ucons_pay]), and
     these lemmas are walked by both records. *)
  Context `{Hpay : !ukn_const N}.
  (* the console ring's cameras: init mints the POSITION PAIR it lends each
     child out of them ([UserConsole.upos_alloc]) *)
  Context `{!uartGhostG Σ}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

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

  (* THE ARGUMENT ROWS THE THREE CONSOLE LEAVES TAKE.  A pinned open or
     mknod is about the PATH in argument 0 and the mode words beside it,
     so [UkInit.uki_open_absent_leaf] and its two siblings name them; each
     is one register lookup through the chain of writes the walk built, and
     the chain is closed by computation.  [unfold] the [set] names first --
     [rewrite] does not see through a local definition. *)
  Local Ltac argrow :=
    repeat (rewrite upd_ne; [| vm_compute; discriminate ]);
    rewrite upd_eq; apply bv_eq; vm_compute; reflexivity.

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
  Lemma wp_kinit_main_die_df (N' : uk_names Σ) `{!ukn_const N'} (hdf : CpuId) (mdf0 : regfile) (n : nat) :
    udepw_law 16 -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    urun N' hdf mdf0 (mword_of_int 0x84) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hwr #Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdf : init_lit_ok 0x990 18%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str (ukn_t N') 0x990 18%nat Hokdf ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdf".
    (* ---- 0x84  auipc a0 ; 0x88  addi a0,a0,-1780 -- the literal ---- *)
    assert (Eadf : add_vec (add_vec (mword_of_int 0x84 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2316 : mword 12))
                   = mword_of_int 0x990)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc N' hdf mdf0 (mword_of_int 0x84)
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
    iApply (wp_uk_addi N' hdf1 df1 (mword_of_int 0x88)
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
    iApply (wp_uk_jal N' hdf2 df2 (mword_of_int 0x8c)
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
    iApply (wp_kinit_printf N' 0x990 18%nat (init_lit 0x990) hdf3 df3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x990 18%nat j Hokdf Hj) Ha0df
              with "Hwr Hcode Hstrdf Hrun").
    iIntros (hdf4 df4) "%Hcsdf Hrun".
    assert (Eretdf : ret_pc (df3 !!! Regidx ra_idx)
                     = (mword_of_int 0x90 : mword 64))
      by (rewrite Hradf; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdf.
    (* ---- 0x90  c.li a0,1 ---- *)
    iApply (wp_uk_cli N' hdf4 df4 (mword_of_int 0x90)
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
    iApply (wp_uk_jal N' hdf5 df5 (mword_of_int 0x92)
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
    iApply (wp_kinit_exit N' hdf6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_de (N' : uk_names Σ) `{!ukn_const N'} (hde : CpuId) (mde0 : regfile) (n : nat) :
    udepw_law 16 -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    urun N' hde mde0 (mword_of_int 0xaa) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hwr #Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokde : init_lit_ok 0x9b0 21%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str (ukn_t N') 0x9b0 21%nat Hokde ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrde".
    (* ---- 0xaa  auipc a0 ; 0xae  addi a0,a0,-1786 -- the literal ---- *)
    assert (Eade : add_vec (add_vec (mword_of_int 0xaa : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2310 : mword 12))
                   = mword_of_int 0x9b0)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc N' hde mde0 (mword_of_int 0xaa)
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
    iApply (wp_uk_addi N' hde1 de1 (mword_of_int 0xae)
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
    iApply (wp_uk_jal N' hde2 de2 (mword_of_int 0xb2)
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
    iApply (wp_kinit_printf N' 0x9b0 21%nat (init_lit 0x9b0) hde3 de3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9b0 21%nat j Hokde Hj) Ha0de
              with "Hwr Hcode Hstrde Hrun").
    iIntros (hde4 de4) "%Hcsde Hrun".
    assert (Eretde : ret_pc (de3 !!! Regidx ra_idx)
                     = (mword_of_int 0xb6 : mword 64))
      by (rewrite Hrade; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretde.
    (* ---- 0xb6  c.li a0,1 ---- *)
    iApply (wp_uk_cli N' hde4 de4 (mword_of_int 0xb6)
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
    iApply (wp_uk_jal N' hde5 de5 (mword_of_int 0xb8)
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
    iApply (wp_kinit_exit N' hde6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kinit_main_die_dw (N' : uk_names Σ) `{!ukn_const N'} (hdw : CpuId) (mdw0 : regfile) (n : nat) :
    udepw_law 16 -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    urun N' hdw mdw0 (mword_of_int 0x52) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hwr #Hcode #Hro Hrun".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokdw : init_lit_ok 0x9c8 29%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str (ukn_t N') 0x9c8 29%nat Hokdw ltac:(vm_compute; reflexivity)
                 with "Hro") as "#Hstrdw".
    (* ---- 0x52  auipc a0 ; 0x56  addi a0,a0,-1674 -- the literal ---- *)
    assert (Eadw : add_vec (add_vec (mword_of_int 0x52 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2422 : mword 12))
                   = mword_of_int 0x9c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc N' hdw mdw0 (mword_of_int 0x52)
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
    iApply (wp_uk_addi N' hdw1 dw1 (mword_of_int 0x56)
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
    iApply (wp_uk_jal N' hdw2 dw2 (mword_of_int 0x5a)
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
    iApply (wp_kinit_printf N' 0x9c8 29%nat (init_lit 0x9c8) hdw3 dw3 n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia) (fun j Hj => init_lit_nopct 0x9c8 29%nat j Hokdw Hj) Ha0dw
              with "Hwr Hcode Hstrdw Hrun").
    iIntros (hdw4 dw4) "%Hcsdw Hrun".
    assert (Eretdw : ret_pc (dw3 !!! Regidx ra_idx)
                     = (mword_of_int 0x5e : mword 64))
      by (rewrite Hradw; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretdw.
    (* ---- 0x5e  c.li a0,1 ---- *)
    iApply (wp_uk_cli N' hdw4 dw4 (mword_of_int 0x5e)
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
    iApply (wp_uk_jal N' hdw5 dw5 (mword_of_int 0x60)
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
    iApply (wp_kinit_exit N' hdw6 _ (12 + (12 + (4 + n))) with "Hcode Hrun").
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
  Lemma wp_kinit_main_child (T : iProp Σ) (stc : fdstate) (cn : cons_names)
      (γ : gname) (np : nat)
      (N' : uk_names Σ) (h : CpuId) (m : regfile) (n : nat) :
    (* THE CHILD'S RECORD IS KEYED AT SH'S PAYLOAD, which is what its exec
       hands the new image ([UkInit.init_exec_sup_pos]) and what a KILL
       gives init back ([UexecRet.uexec_pay_arm]). *)
    ukn_pay N' = ucons_pay cn γ T ->
    init_deps T -∗
    init_code (ukn_t N') -∗
    (* the exec deposit's supplier -- [UkInit.init_exec_sup]: init's child
       arm ecalls exec("sh", argv), whose bundle READS THE KEY (the path
       and the argument vector, out of the image) and is therefore not
       payable through [UkRun.udep]'s key-free law.  It is init's OWN
       supply, at its own two argument registers and at the one working
       directory it ever has, and it is LENT the heap and the fd authority
       so a pinned bundle can read them. *)
    init_exec_sup_lend cn T stc -∗
    init_rodata (ukn_t N') -∗
    (* ...AND THE ARGUMENT VECTOR, at the child's own data name: the
       supplier reads init's sixteen persisted .data bytes back into facts
       about the process image, which is what pins [na = 1] and the one
       argument's length -- and hence prices the exec'd program's frames.
       It crosses the fork with the text and the rodata
       ([UkFork.forkable_ubyteq_map]). *)
    init_argv (ukn_d N') -∗
    (* ...AND THE CHILD'S OWN HALF OF ITS WORKING DIRECTORY.  The exec leaf
       is cwd-indexed ([UkInit.wp_kinit_exec]) because a pinned bundle is
       about a PATH and "sh" is relative; the child was forked at the
       root, and nothing between the fork and the ecall moves it. *)
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    (* ...AND THE DESCRIPTOR HEAD.  exec copies the table, so the exec'd
       program's entry constructor speaks about THIS process's slots -- and
       it is told one row about them, the head's own three arms
       ([UkSh.ush_fd0]).  The head is what travels, whole, and it is SPENT
       here: the one path past a returning exec is the diagnostic and
       exit(1). *)
    ufd_head T stc (ukn_fd N') -∗
    (* ...AND THE POSITION ITS PARENT LENT IT at the fork
       ([UkFork.wp_uk_ecall_fork]'s [Rc]).  It is SPENT here: the exec
       supply is a wand from it, and what crosses into sh's own run is
       [PinnedExec]'s linear [Pay]. *)
    upos γ np -∗
    urun N' h m (mword_of_int 0x96) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpeq.
    (* the walk's own class, off the record's payload: [ucons_pay] does not
       read the exit status ([UserConsole.ucons_pay_const]) *)
    pose proof (ukn_const_of_eq N' (ucons_pay cn γ T) Hpeq
                  (ucons_pay_const cn γ T)) as Hcst'.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs #Hro #Hargv Hcwd Hstd Hpos Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexec & _ & _).
    (* ---- 0x96  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc N' h m (mword_of_int 0x96)
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
    iApply (wp_uk_addi N' hc1 mc1 (mword_of_int 0x9a)
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
    iApply (wp_uk_auipc N' hc2 mc2 (mword_of_int 0x9e)
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
    iApply (wp_uk_addi N' hc3 mc3 (mword_of_int 0xa2)
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
    iApply (wp_uk_jal N' hc4 mc4 (mword_of_int 0xa6)
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
    (* THE DEPOSIT, out of init's own supply: the two argument registers
       are pinned by the four instructions above, and the working
       directory is the one the fragment names. *)
    iApply (wp_kinit_exec N' hc5 mc5 (12 + (12 + (4 + n))) FsImg.ROOTINO
              with "Hcode Hrun Hcwd [Hstd Hpos]").
    { iApply ("Hxs" $! γ np N' (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> mc5)
                (mword_of_int 0x3ac) with "[%] [%] [%] Hro Hargv Hstd Hpos").
      - exact Hpeq.
      - rewrite (upd_ne mc5 (Regidx a7_idx) (Regidx a0_idx)
                   (mword_of_int 7 : mword 64)
                   ltac:(vm_compute; discriminate)).
        rewrite /mc5 (upd_ne mc4 (Regidx ra_idx) (Regidx a0_idx) _
                        ltac:(vm_compute; discriminate)).
        exact (upd_eq mc3 (Regidx a0_idx) _).
      - rewrite (upd_ne mc5 (Regidx a7_idx) (Regidx a1_idx)
                   (mword_of_int 7 : mword 64)
                   ltac:(vm_compute; discriminate)).
        rewrite /mc5 (upd_ne mc4 (Regidx ra_idx) (Regidx a1_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mc4 (upd_ne mc3 (Regidx a0_idx) (Regidx a1_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mc3 (upd_ne mc2 (Regidx a0_idx) (Regidx a1_idx) _
                        ltac:(vm_compute; discriminate)).
        exact (upd_eq mc1 (Regidx a1_idx) _). }
    iIntros (hc6) "Hcwd Hrun".
    assert (Eretc : ret_pc (mc5 !!! Regidx ra_idx)
                    = (mword_of_int 0xaa : mword 64))
      by (rewrite Hrac5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretc.
    (* ---- 0xaa  "init: exec sh failed" ; exit(1) ---- *)
    iApply (wp_kinit_main_die_de N' hc6 _ n with "Hwr Hcode Hro Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* WHAT CROSSES THE FORK.  The child needs init's text and its read-only   *)
  (* image at ITS OWN names, and both are [utext_img] at a constant map, so  *)
  (* [forkable_utext_map] gives them.  Nothing else crosses: main's frame    *)
  (* words are never read again (main does not return), and the break is     *)
  (* carried by the leaf itself.                                             *)
  (* --------------------------------------------------------------------- *)
  Local Instance forkable_init_img :
    Forkable (fun gt gd _ =>
                (init_code gt ∗ init_rodata gt ∗ init_argv gd)%I).
  Proof.
    eapply Forkable_ext;
      [ | apply (forkable_sep
                   (fun gt _ _ => ([∗ map] a ↦ b ∈ InitInstrs.init_bytes,
                                     utext gt a b)%I)
                   (fun gt gd _ =>
                      (([∗ map] a ↦ b ∈ init_ro, utext gt a b)
                       ∗ ([∗ map] a ↦ b ∈ init_argv_map,
                            ubyteq gd DfracDiscarded a b))%I)
                   (forkable_utext_map InitInstrs.init_bytes)
                   (forkable_sep
                      (fun gt _ _ => ([∗ map] a ↦ b ∈ init_ro, utext gt a b)%I)
                      (fun _ gd _ => ([∗ map] a ↦ b ∈ init_argv_map,
                                        ubyteq gd DfracDiscarded a b)%I)
                      (forkable_utext_map init_ro)
                      (forkable_ubyteq_map init_argv_map))) ].
    intros gt gd gs.
    rewrite /init_code /init_rodata /init_argv /utext_img. reflexivity.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* fork's STUB @0x36a -- the one syscall entry whose contract returns      *)
  (* TWICE.  Both arms come back through the same [c.jr ra] at 0x370, the    *)
  (* child's under its own names, which is why the payload has to carry the  *)
  (* catalog: without [init_code] at the child's text name the child cannot  *)
(* even walk its return.                                                   *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_fork (T : iProp Σ) `{!Persistent T} (stc : fdstate)
      (cn : cons_names) (γ : gname) (np : nat)
      (szv : Z) (h : CpuId) (m : regfile) (avail : nat)
      (Sc : gset gname) :
    init_code γt -∗ init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    (* THE CHILD'S EXIT PAYLOAD, at the kill status: the console reader
       token (or the taint) that init hands the shell, and that a KILLED
       shell still gives back ([UexecRet]'s deposit is taken at every
       trap).  It crosses HERE because [UkFork.wp_uk_ecall_fork] is where
       a parent pays what its child's exit will owe. *)
    ucons_pay cn γ T (-1) -∗
    (* ...AND WHAT INIT LENDS THE CHILD BESIDE IT: the program half of the
       console position pair ([UserConsole.upos]), which the child carries
       to its exec and sh holds in [UkSh.ush_pstate] thereafter.  It
       crosses on [UkFork.wp_uk_ecall_fork]'s [Rc], not in the payload:
       the payload is what comes BACK, the lend is what goes out. *)
    upos γ np -∗
    (* THE LEDGER.  fork copies the descriptor table, so the child wakes
       on the parent's, and the child is the arm that execs sh -- which
       needs a ledger of its own to hand on.  [UkFork.wp_uk_ecall_fork]
       mints the child's half at the parent's own [l], so both halves
       leave at the same states -- so what each side leaves with is the SAME
       head at its own name, which is how the console reaches the shell. *)
    ufd_head T stc γfd -∗
    (* the working directory, index-free: fork keeps it and init never
       reads it, but the child's half is minted at the parent's value and
       the leaf needs one to name ([UkFork.wp_uk_ecall_fork]) *)
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    (* ...AND ITS OWN HALF OF ITS CHILDREN SET, AT THE SET ITSELF: fork
       MOVES it and an update needs both halves, and init is a program that
       READS the answer -- the child it forks is the one it waits for, so
       the pid arm's token is what its wait redeems
       ([UkFork.wp_uk_ecall_fork] at [Q := fun _ => True]; L7 puts the
       console-input resource in that payload). *)
    UserChildren.uch γch Sc -∗
    urun N h m (mword_of_int InitSyms.fork) avail -∗
    ((∀ (h' : CpuId) (r : mword 64),
        ⌜ r <> (mword_of_int 0 : mword 64) ⌝ -∗
        (* FORK'S TWO ARMS, relayed: it failed and the set did not move, or
           it returned the child's pid with the quarter of that child's
           generation a later wait() redeems. *)
        ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ UserChildren.uch γch Sc)
         ∨ ∃ (γc : gname) (pidv : mword 32),
             ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
             child_tok γc pidv (ucons_pay cn γ T) ∗
             UserChildren.uch γch (Sc ∪ {[γc]})) -∗
        (init_code γt ∗ init_rodata γt ∗ init_argv γd) -∗ usz γs szv -∗
        ufd_head T stc γfd -∗
        UserCwd.ucwd γcwd FsImg.ROOTINO -∗
        urun N h'
          (<[Regidx a0_idx := r]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang)) ∗
     (∀ (N' : uk_names Σ) (h' : CpuId),
        (* THE CHILD'S RECORD IS KEYED AT THE PAYLOAD ITS PARENT CHOSE
           ([UkFork]'s child arm gives the equation). *)
        ⌜ ukn_pay N' = ucons_pay cn γ T ⌝ -∗
        (init_code (ukn_t N') ∗ init_rodata (ukn_t N') ∗ init_argv (ukn_d N'))
          -∗ usz (ukn_s N') szv -∗
        ufd_head T stc (ukn_fd N') -∗
        (* ...AND THE POSITION IT WAS LENT *)
        upos γ np -∗
        UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
        urun N' h'
          (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro #Hargv Hsz HQ Hpos Hstd Hcwd Hch Hrun [Hpar Hchi]".
    (* the list the head is at, and the arm's way back -- usable at EITHER
       ghost name, which is what the child's half needs *)
    iDestruct (ufd_head_open with "Hstd") as (l) "[Hstd #Hback]".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hfork & _ & _ & _ & _).
    rewrite Hfork.
    (* ---- 0x36a  c.li a7,1 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x36a)
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
    (* init holds no descriptor handles at this point -- NOT because its
       console descriptors are opened later (they are not: the open is at
       0x16, the two dups at 0x20 and 0x26, all of them BEFORE this fork at
       0x38) but because it DROPS them: [wp_kinit_open] discards the handle
       the tracked open leaf mints and [wp_kinit_dup] goes through
       [UkRunSys.wp_uk_ecall_dup_untracked], which mints none.  So the
       handle set fork carries across is empty and both extra premises are
       [emp]. *)
    iApply (wp_uk_ecall_fork N h1 mf1 (mword_of_int 0x36c) avail szv
              l ∅ FsImg.ROOTINO Sc (ucons_pay cn γ T) (upos γ np)
              (fun gt gd _ =>
                 (init_code gt ∗ init_rodata gt ∗ init_argv gd)%I)
              ltac:(unfold mf1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 1 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] HQ Hpos [] Hsz Hstd [] Hcwd Hch Hrun").
    { iApply (uis_init_36c with "Hcode"). }
    { iFrame "Hcode Hro Hargv". }
    { rewrite big_sepM_empty. done. }
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
      iIntros (hp r) "%Hrnz Hans Hpay Hsz Hstd _ Hcwd Hrun".
      set (mp := <[Regidx a0_idx := r]> mf1).
      assert (Hrap : mp !!! Regidx ra_idx = m !!! Regidx ra_idx).
      { rewrite /mp (upd_ne mf1 (Regidx a0_idx) (Regidx ra_idx) r
                       ltac:(vm_compute; discriminate)).
        exact (Hraf mf1 r eq_refl). }
      iDestruct "Hpay" as "(#Hcp & #Hrp & #Hap)".
      iApply (wp_uk_cjr N hp mp (mword_of_int 0x370) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrap; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_370 with "Hcp"). }
      iIntros (hp2) "Hrun".
      iApply ("Hpar" $! hp2 r with "[] Hans [] Hsz [Hstd] Hcwd Hrun").
      { iPureIntro. exact Hrnz. }
      { iFrame "Hcp Hrp Hap". }
      { iApply ("Hback" with "Hstd"). }
    - (* ...and the CHILD under fresh ones.  Its ledger is dropped: init's
         child execs, and nothing before the exec allocates. *)
      (* the child's own children fragment is [∅] and init's child execs
         before it forks, so nothing here reads it *)
      iIntros (N' hc γ') "%Hpeq _ Hpos Hpay Hsz Hstd _ Hcwd _ Hrun".
      set (mk := <[Regidx a0_idx := (mword_of_int 0 : mword 64)]> mf1).
      assert (Hrak : mk !!! Regidx ra_idx = m !!! Regidx ra_idx).
      { rewrite /mk (upd_ne mf1 (Regidx a0_idx) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (Hraf mf1 (mword_of_int 0) eq_refl). }
      iDestruct "Hpay" as "(#Hck & #Hrk & #Hak)".
      iApply (wp_uk_cjr N' hc mk (mword_of_int 0x370) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hrak; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_370 with "Hck"). }
      iIntros (hc2) "Hrun".
      iApply ("Hchi" $! N' hc2 with "[%] [] Hsz [Hstd] Hpos Hcwd Hrun").
      { exact Hpeq. }
      { iFrame "Hck Hrk Hak". }
      { iApply ("Hback" with "Hstd"). }
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
  (* THE RESTART HEAD'S INVARIANT IS ONE REGISTER PIN.  s2 holds the        *)
  (* "init: starting sh" pointer; everything else it needs is inside        *)
  (* [urun].  Nothing is assumed about what wait RETURNS: its result is     *)
  (* compared against s1, and all three outcomes -- the child was reaped,   *)
  (* an orphan was reaped, the call failed -- are legal continuations.      *)
  (*                                                                        *)
  (* THE WAIT HEAD'S CARRIES THE SHELL IT IS WAITING FOR.  Between the fork  *)
  (* and the [beq a0,s1] that leaves this loop, init holds a QUARTER of the  *)
  (* generation it forked ([ChildTok.child_tok] at this program's trivial    *)
  (* payload), that generation is in the children set its half pins, and s1  *)
  (* holds its pid sign-extended.  Those three are what turn "wait returned  *)
  (* s1" into "the shell I started is the process that exited":              *)
  (* [ChildTok.gen_uniq_tok] against the answer's uniqueness summary names   *)
  (* the generation, and [ChildTok.gen_pay] then redeems the payload.  On an *)
  (* orphan the SAME token refutes the identification                        *)
  (* ([ChildTok.exit_tok_tok_ne]), which is what keeps the shell in the set  *)
  (* across a round.  L7 puts the console-input resource in the payload, and *)
  (* this is where it comes back.                                            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_loop (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names) (szv : Z) (n : nat) :
    init_deps T -∗
    init_code γt -∗
    (* the exec deposit's supplier -- [UkInit.init_exec_sup]: init's child
       arm ecalls exec("sh", argv), whose bundle READS THE KEY (the path
       and the argument vector, out of the image) and is therefore not
       payable through [UkRun.udep]'s key-free law.  It is init's OWN
       supply, at its own two argument registers and at the one working
       directory it ever has, and it is LENT the heap and the fd authority
       so a pinned bundle can read them. *)
    init_exec_sup_lend cn T stc -∗
    init_rodata γt -∗
    init_argv γd -∗
    ((∀ (h : CpuId) (m : regfile),
        ⌜ m !!! Regidx s2_idx = mword_of_int LIT_START ⌝ -∗
        usz γs szv -∗
        ufd_head T stc γfd -∗
        UserCwd.ucwd γcwd FsImg.ROOTINO -∗
        UserChildren.uch_any γch -∗
        (* THE RESTART HEAD HOLDS THE CONSOLE INPUT: no shell of init's is
           running here, so the reader token (or the taint) is init's own
           again, and the round below lends it to the shell it forks
           ([UserConsole.uinit_lend]). *)
        uinit_tok cn T -∗
        urun N h m (mword_of_int 0x32) (12 + (12 + (4 + n))) -∗
        WP (Loop : expr riscv_lang))
     ∧ (∀ (h : CpuId) (m : regfile) (cs : gset gname)
          (γ γsh : gname) (pidsh : mword 32),
          ⌜ m !!! Regidx s2_idx = mword_of_int LIT_START ⌝ -∗
          ⌜ m !!! Regidx s1_idx = (sign_extend' 64 pidsh : mword 64) ⌝ -∗
          ⌜ γsh ∈ cs ⌝ -∗
          (* THE SHELL'S PID IS NOT -1, off the [blt] the fork arm took to
             get here.  It is what refutes the arm where wait returned -1
             AND the [beq] against s1 was taken -- that arm would leave
             this loop for the restart head with the console input still
             out on loan. *)
          ⌜ (sign_extend' 64 pidsh : mword 64) <> (mword_of_int (-1) : mword 64) ⌝ -∗
          usz γs szv -∗
          ufd_head T stc γfd -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          UserChildren.uch γch cs -∗
          (* THE WAIT HEAD HOLDS THE SHELL INSTEAD: the console input is in
             the payload of the generation this quarter names, and the reap
             below is what brings it back ([ChildTok.gen_pay],
             [UserConsole.uinit_redeem]). *)
          child_tok γsh pidsh (ucons_pay cn γ T) -∗
          urun N h m (mword_of_int 0x44) (12 + (12 + (4 + n))) -∗
          WP (Loop : expr riscv_lang))).
  Proof.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs #Hro #Hargv".
    destruct init_syms_pins
      as (_ & _ & Hprintf & _ & _ & _ & _ & _ & Hfork & Hwait & _ & _ & _).
    assert (HokS : init_lit_ok LIT_START 18%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (init_lit_str γt LIT_START 18%nat HokS
                 ltac:(vm_compute; reflexivity) with "Hro") as "#HstrS".
    iLöb as "IH".
    iSplit.
    - (* ==================== the RESTART head @0x32 ==================== *)
      iIntros (h m) "%Hs2 Hsz Hstd Hcwd Hch Htk Hrun".
      iApply (wp_uk_cmv N h m (mword_of_int 0x32) a0_idx s2_idx
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
      iApply (wp_uk_jal N hl1 ml1 (mword_of_int 0x34)
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
      iApply (wp_kinit_printf N LIT_START 18%nat (init_lit LIT_START)
                hl2 ml2 n
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(lia)
                (fun j Hj => init_lit_nopct LIT_START 18%nat j HokS Hj) Ha0l2
                with "Hwr Hcode HstrS Hrun").
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
      iApply (wp_uk_jal N hl3 ml3 (mword_of_int 0x38)
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
      (* the set the fork moves has to be NAMED, because the answer says
         what it became and the wait head is indexed by it *)
      iDestruct "Hch" as (Sc) "Hch".
      (* THE MINT, once per round: a FRESH pair per child, because the
         dead shell's half would otherwise still agree against the live
         one's ([UserConsole.upos_alloc]).  [uinit_lend] does both halves
         of the round's handover -- it mints the pair at the token's
         CURRENT position and builds the shell's exit payload out of the
         token, leaving init the program half to lend. *)
      iMod (uinit_lend cn T (-1) with "Htk") as (γ np) "[HQ Hpos]".
      iApply (wp_kinit_fork T stc cn γ np szv hl4 ml4 (12 + (12 + (4 + n))) Sc
                with "Hcode Hro Hargv Hsz HQ Hpos Hstd Hcwd Hch Hrun").
      rewrite Eretf.
      iSplitR "".
      + (* ------------- the PARENT: r <> 0 ------------- *)
        iIntros (hp r) "%Hrnz Hans (#Hcp & #Hrp & #Hap) Hsz Hstd Hcwd Hrun".
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
        iApply (wp_uk_cmv N hp mp0 (mword_of_int 0x3c) s1_idx a0_idx
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
          iApply (wp_uk_btype0 N hp1 mp1 (mword_of_int 0x3e)
                    (mword_of_int 70 : mword 13) a0_idx BLT true
                    (mword_of_int 0x84) (12 + (12 + (4 + n)))
                    (eq_sym Hblt) (eq_sym Etgt3e)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_init_3e with "Hcode"). }
          iIntros (hp2) "Hrun".
          iApply (wp_kinit_main_die_df N hp2 _ n with "Hwr Hcode Hro Hrun").
        * (* fork succeeded: this is the parent, so a0 <> 0 too.
             THE LATER COMES FROM HERE.  The path 0x32 -> printf -> fork ->
             0x3c -> 0x42 -> 0x44 falls THROUGH into the wait head; it is
             not a back edge, so nothing on it hands out a [▷] on its own,
             and without one the Löb hypothesis is unusable at 0x44.  Taking
             this branch through [wp_uk_btype0_later] supplies it. *)
          iApply (wp_uk_btype0_later N hp1 mp1 (mword_of_int 0x3e)
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
          iApply (wp_uk_cbeqz N hp2 mp1 (mword_of_int 0x42)
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
          (* THE FORK SUCCEEDED, so the answer is on its pid arm: the -1
             disjunct cannot be, because the [blt] above was not taken. *)
          iDestruct "Hans" as "[[%Hrm1 Hch] | (%γsh & %pidsh & %Hrpid & Htok & Hch)]".
          { exfalso. rewrite Ha0p1 Hrm1 in Hblt. vm_compute in Hblt.
            discriminate Hblt. }
          assert (Hs1p1 : mp1 !!! Regidx s1_idx
                          = (sign_extend' 64 pidsh : mword 64)).
          { rewrite /mp1 (upd_eq mp0 (Regidx s1_idx) (regval_into_reg _)).
            rewrite Ha0p0 Hrpid. apply add_vec_zero_l. }
          (* THE PID IS NOT -1, off the [blt] this branch did not take:
             fork's answer is [sign_extend' 64 pidsh] and a negative one
             would have jumped to the diagnostic. *)
          assert (Hpnz : (sign_extend' 64 pidsh : mword 64)
                         <> (mword_of_int (-1) : mword 64)).
          { intros Hc. rewrite Ha0p1 Hrpid Hc in Hblt.
            vm_compute in Hblt. discriminate Hblt. }
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! hp3 mp1 (Sc ∪ {[γsh]}) γ γsh pidsh
                    with "[] [] [] [] Hsz Hstd Hcwd Hch Htok Hrun").
          { iPureIntro. exact Hs2p1. }
          { iPureIntro. exact Hs1p1. }
          { iPureIntro. set_solver. }
          { iPureIntro. exact Hpnz. }
      + (* ------------- the CHILD: r = 0 ------------- *)
        iIntros (N' hc) "%Hpeq (#Hck & #Hrk & #Hak) Hsz Hstd Hpos Hcwd Hrun".
        (* the child's walk runs at ITS payload's class, which is the
           shell's ([UserConsole.ucons_pay_const]) *)
        pose proof (ukn_const_of_eq N' (ucons_pay cn γ T) Hpeq
                      (ucons_pay_const cn γ T)) as Hcst'.
        set (mc0 := <[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
                      (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> ml4)).
        assert (Ha0c0 : mc0 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
          by exact (upd_eq _ (Regidx a0_idx) _).
        (* ---- 0x3c  c.mv s1,a0 ---- *)
        iApply (wp_uk_cmv N' hc mc0 (mword_of_int 0x3c) s1_idx a0_idx
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
        iApply (wp_uk_btype0 N' hc1 mc1 (mword_of_int 0x3e)
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
        iApply (wp_uk_cbeqz N' hc2 mc1 (mword_of_int 0x42)
                  (mword_of_int 42 : mword 8) (mword_of_int 2 : mword 3)
                  a0_idx true (mword_of_int 0x96) (12 + (12 + (4 + n)))
                  ltac:(vm_compute; reflexivity) Hbzc Etgt42
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_init_42 with "Hck"). }
        iIntros (hc3) "Hrun".
        iApply (wp_kinit_main_child T stc cn γ np N' hc3 mc1 n Hpeq
                  with "[$Hwr $Hwl15 $Hwl17] Hck Hxs Hrk Hak Hcwd Hstd Hpos Hrun").
    - (* ==================== the WAIT head @0x44 ==================== *)
      iIntros (h m cs γ γsh pidsh) "%Hs2 %Hs1 %Hin %Hpnz Hsz Hstd Hcwd Hch Htok Hrun".
      (* ---- 0x44  c.li a0,0 -- the NULL status pointer ---- *)
      iApply (wp_uk_cli N h m (mword_of_int 0x44)
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
      (* s1 -- the pid of the shell this loop is waiting for -- is written
         once, at 0x3c before the loop, and nothing between here and the
         [beq] touches it *)
      assert (Hs1w1 : mw1 !!! Regidx s1_idx = (sign_extend' 64 pidsh : mword 64)).
      { rewrite <- Hs1.
        exact (upd_ne m (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). }
      (* ---- 0x46  jal ra,0x37a <wait> ---- *)
      iApply (wp_uk_jal N hw1 mw1 (mword_of_int 0x46)
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
      assert (Hs1w2 : mw2 !!! Regidx s1_idx = (sign_extend' 64 pidsh : mword 64)).
      { rewrite <- Hs1w1.
        exact (upd_ne mw1 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). }
      assert (Ha0w2 : uint (mw2 !!! Regidx a0_idx) = 0).
      { rewrite (upd_ne mw1 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
        vm_compute. reflexivity. }
      (* ---- wait(0) ---- *)
      iApply (wp_kinit_wait N Hpsok_free hw2 mw2 (12 + (12 + (4 + n))) cs Ha0w2
                with "Hcode Hrun Hch").
      iIntros (hw3 ret cs') "Hans Hrun Hch".
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
      assert (Hs1w3 : mw3 !!! Regidx s1_idx = (sign_extend' 64 pidsh : mword 64)).
      { rewrite <- Hs1w2.
        rewrite /mw3 (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) ret
                        ltac:(vm_compute; discriminate)).
        exact (upd_ne mw2 (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). }
      assert (Ha0w3 : mw3 !!! Regidx a0_idx = ret)
        by exact (upd_eq _ (Regidx a0_idx) ret).
      (* the answer, opened once for the three arms below: the return value
         is an [int] sign-extended, and either nothing was reaped or a
         generation left the set with its escrow. *)
      iDestruct "Hans" as (rv xs) "[%Hret Hwa]".
      (* ---- 0x4a  beq a0,s1,0x32 -- BACK EDGE to the restart head ---- *)
      assert (Etgt4a : add_vec (mword_of_int 0x4a : mword 64)
                         (sign_extend' 64 (mword_of_int 8168 : mword 13))
                       = mword_of_int 0x32)
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (uv_btaken BEQ (mw3 !!! Regidx s1_idx)
                  (mw3 !!! Regidx a0_idx)) eqn:Hbeq.
      * (* the child we forked was reaped: round again from 0x32 *)
        iApply (wp_uk_btype_later N hw3 mw3 (mword_of_int 0x4a)
                  (mword_of_int 8168 : mword 13) a0_idx s1_idx BEQ true
                  (mword_of_int 0x32) (12 + (12 + (4 + n)))
                  (eq_sym Hbeq) (eq_sym Etgt4a)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_init_4a with "Hcode"). }
        iNext. iIntros (hw4) "Hrun".
        (* THE REDEMPTION.  The pid that came back is s1, the pid of the
           shell this loop forked; on the reaping arm the answer's
           uniqueness summary says no OTHER child of init carries it, so
           the generation reaped IS the shell's and its escrow pairs with
           the token init has held since the fork
           ([ChildTok.gen_uniq_tok], then [ChildTok.gen_pay_timeless]).
           This program's payload is trivial, so what comes back is [True];
           L7's console-input resource arrives through exactly this step.
           On the -1 arm nothing was reaped -- init is exiting on a killed
           shell's behalf next round -- and the token is simply dropped. *)
        assert (Hs1ret : (sign_extend' 64 pidsh : mword 64) = ret).
        { rewrite <- Hs1w3, <- Ha0w3. apply eq_vec_true_iff. exact Hbeq. }
        iDestruct "Hwa" as "[[%Hm1 %Hcseq] | (%γ' & %Hcseq & Hesc & #Huq)]".
        { (* NOTHING WAS REAPED AND THE [beq] AGAINST s1 WAS TAKEN, so the
             shell's pid is -1 -- which the fork arm refuted on the way in.
             The arm matters: taking it would re-enter the restart head
             with the console input still held by a live shell. *)
          exfalso. apply Hpnz.
          rewrite Hs1ret Hret Hm1. exact UexecRet.sext_neg1_64. }
        assert (Hrvp : rv = pidsh).
        { apply sext64_32_inj. rewrite <- Hret. exact (eq_sym Hs1ret). }
        subst rv.
        iDestruct (gen_uniq_tok cs pidsh γ' γsh (ucons_pay cn γ T) Hin
                     with "Huq Htok") as %->.
        (* THE REDEMPTION: the shell's payload comes back at the status it
           exited with -- or at -1 if it was killed -- and either way it is
           the console reader token or the taint
           ([UserConsole.uinit_redeem]).  This is the round's close. *)
        iMod (gen_pay_timeless with "Htok Hesc") as "HQ".
        iDestruct (uinit_redeem cn γ T xs with "HQ") as "Htk".
        iDestruct "IH" as "[IH1 _]".
        iApply ("IH1" $! hw4 mw3 with "[] Hsz Hstd Hcwd [Hch] Htk Hrun").
        { iPureIntro. exact Hs2w3. }
        iApply (UserChildren.uch_any_of with "Hch").
      * (* somebody else's child, or an error *)
        iApply (wp_uk_btype_later N hw3 mw3 (mword_of_int 0x4a)
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
          iApply (wp_uk_btype0_later N hw4 mw3 (mword_of_int 0x4e)
                    (mword_of_int 8182 : mword 13) a0_idx BGE true
                    (mword_of_int 0x44) (12 + (12 + (4 + n)))
                    (eq_sym Hbge) (eq_sym Etgt4e)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_init_4e with "Hcode"). }
          iNext. iIntros (hw5) "Hrun".
          (* AN ORPHAN, AND THE SHELL IS STILL A CHILD.  The pid that came
             back is not s1, so whatever generation left the set was not the
             one init holds a token for ([ChildTok.exit_tok_tok_ne]) -- which
             is what lets the next round be entered at the same invariant. *)
          assert (Hs1ne : (sign_extend' 64 pidsh : mword 64) <> ret).
          { rewrite <- Hs1w3, <- Ha0w3. apply eq_vec_false_iff. exact Hbeq. }
          iAssert (⌜γsh ∈ cs'⌝ ∗ UserChildren.uch γch cs' ∗
                   child_tok γsh pidsh (ucons_pay cn γ T))%I
            with "[Hwa Hch Htok]" as "(%Hin' & Hch & Htok)".
          { iDestruct "Hwa" as "[[%Hm1 %Hcseq] | (%γ' & %Hcseq & Hesc & _)]".
            - iFrame "Hch Htok". iPureIntro. rewrite Hcseq. exact Hin.
            - iDestruct (exit_tok_tok_ne γ' γsh rv pidsh xs (ucons_pay cn γ T)
                           ltac:(intro Hc; apply Hs1ne;
                                 rewrite Hret Hc; reflexivity)
                           with "Hesc Htok") as %Hne.
              iFrame "Hch Htok". iPureIntro. rewrite Hcseq. set_solver. }
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! hw5 mw3 cs' γ γsh pidsh
                    with "[] [] [] [] Hsz Hstd Hcwd Hch Htok Hrun").
          { iPureIntro. exact Hs2w3. }
          { iPureIntro. exact Hs1w3. }
          { iPureIntro. exact Hin'. }
          { iPureIntro. exact Hpnz. }
        + (* wait itself failed: the diagnostic at 0x52 *)
          iApply (wp_uk_btype0_later N hw4 mw3 (mword_of_int 0x4e)
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
          iApply (wp_kinit_main_die_dw N hw5 _ n with "Hwr Hcode Hro Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* main FROM 0x1e -- the two dups, the literal pointer, and into the loop. *)
  (* Both arms of the console test rejoin HERE: the fall-through when open   *)
  (* succeeded, and the [c.j] at 0x82 when the mknod repair arm has run.     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_from_1e (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names)
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    stc <> FdClosed ->
    init_deps T -∗
    init_code γt -∗
    (* the exec deposit's supplier -- [UkInit.init_exec_sup]: init's child
       arm ecalls exec("sh", argv), whose bundle READS THE KEY (the path
       and the argument vector, out of the image) and is therefore not
       payable through [UkRun.udep]'s key-free law.  It is init's OWN
       supply, at its own two argument registers and at the one working
       directory it ever has, and it is LENT the heap and the fd authority
       so a pinned bundle can read them. *)
    init_exec_sup_lend cn T stc -∗
    init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    (* THE HEAD, as the console test left it; the two dups below keep it *)
    ufd_head T stc γfd -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch_any γch -∗
    (* THE CONSOLE INPUT, on its way to the restart head: the reader token
       or the taint, which init lends to each shell it forks
       ([UserConsole.uinit_lend]). *)
    uinit_tok cn T -∗
    urun N h m (mword_of_int 0x1e) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs #Hro #Hargv Hsz Hstd Hcwd Hch Htk Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hdup & _ & _ & _ & _ & _).
    (* ---- 0x1e  c.li a0,0 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x1e)
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
    iApply (wp_uk_jal N hq1 mq1 (mword_of_int 0x20)
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
    (* the argument IS 0 -- the [c.li a0,0] at 0x1e put it there *)
    assert (Ha0q2 : bv_signed (trunc32 (mq2 !!! Regidx a0_idx)) = Z.of_nat 0).
    { rewrite /mq2 (upd_ne mq1 (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1 (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
      vm_compute; reflexivity. }
    iApply (wp_kinit_dup_head N Hpsok_free T stc hq2 mq2 (12 + (12 + (4 + n)))
              Hne Ha0q2 with "Hcode Hrun Hstd").
    iIntros (hq3 r1) "Hstd Hrun".
    assert (Eq2 : ret_pc (mq2 !!! Regidx ra_idx)
                  = (mword_of_int 0x24 : mword 64))
      by (rewrite Hraq2; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq2.
    set (mq3 := <[Regidx a0_idx := r1]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq2)).
    (* ---- 0x24  c.li a0,0 ---- *)
    iApply (wp_uk_cli N hq3 mq3 (mword_of_int 0x24)
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
    iApply (wp_uk_jal N hq4 mq4 (mword_of_int 0x26)
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
    (* ...and again, from the [c.li a0,0] at 0x24 *)
    assert (Ha0q5 : bv_signed (trunc32 (mq5 !!! Regidx a0_idx)) = Z.of_nat 0).
    { rewrite /mq5 (upd_ne mq4 (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq4 (upd_eq mq3 (Regidx a0_idx) (regval_into_reg _)).
      vm_compute; reflexivity. }
    iApply (wp_kinit_dup_head N Hpsok_free T stc hq5 mq5 (12 + (12 + (4 + n)))
              Hne Ha0q5 with "Hcode Hrun Hstd").
    iIntros (hq6 r2) "Hstd Hrun".
    assert (Eq5 : ret_pc (mq5 !!! Regidx ra_idx)
                  = (mword_of_int 0x2a : mword 64))
      by (rewrite Hraq5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq5.
    set (mq6 := <[Regidx a0_idx := r2]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq5)).
    (* ---- 0x2a  auipc s2,0x1 ; 0x2e addi s2,s2,-1714 -- the literal ---- *)
    iApply (wp_uk_auipc N hq6 mq6 (mword_of_int 0x2a)
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
    iApply (wp_uk_addi N hq7 mq7 (mword_of_int 0x2e)
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
    iDestruct (wp_kinit_main_loop T stc cn szv n
                 with "[$Hwr $Hwl15 $Hwl17] Hcode Hxs Hro Hargv")
      as "[Hloop _]".
    iApply ("Hloop" $! hq8 mq8 with "[] Hsz Hstd Hcwd Hch Htk Hrun").
    iPureIntro. exact Hs2q8.
  Qed.



  (* --------------------------------------------------------------------- *)
  (* THE CONSOLE REPAIR ARM @0x64: the console device node does not exist    *)
  (* yet, so make it and open it again.  Rejoins the main line at 0x1e.      *)
  (* --------------------------------------------------------------------- *)
  (* --------------------------------------------------------------------- *)
  (* THE REPAIR ARM'S TAIL @0x74: open("console", O_RDWR) again, then the     *)
  (* [c.j 0x1e] back to the main line.  Split out because the mknod's THREE   *)
  (* answers all reach it -- the node exists, or the credential came back, or *)
  (* the taint -- and [UkInit.uki_open2] is the one shape they collapse to,   *)
  (* so this walk is proved once instead of three times.                      *)
  (*                                                                         *)
  (* INIT NEVER TESTS THIS OPEN: 0x82 is [c.j 0x1e], an unconditional jump    *)
  (* with a0 dropped, so the head's three arms are what leaves here.          *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_main_repair_tail (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names)
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    stc <> FdClosed ->
    init_deps T -∗
    init_code γt -∗
    init_exec_sup_lend cn T stc -∗
    init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    uki_open2 N T stc -∗
    uki_open2_in N T -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch_any γch -∗
    (* THE CONSOLE INPUT, on its way to the restart head: the reader token
       or the taint, which init lends to each shell it forks
       ([UserConsole.uinit_lend]). *)
    uinit_tok cn T -∗
    urun N h m (mword_of_int 0x74) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne.
    rewrite /uki_open2.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs #Hro #Hargv Hsz Hop2 Hin Hcwd Hch Htk Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    set (mr4 := m). set (hr4 := h).
    (* ---- 0x74  c.li a1,2 -- O_RDWR ---- *)
    iApply (wp_uk_cli N hr4 mr4 (mword_of_int 0x74)
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
    iApply (wp_uk_auipc N hr5 mr5 (mword_of_int 0x76)
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
    iApply (wp_uk_addi N hr5a mr5a (mword_of_int 0x7a)
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
    iApply (wp_uk_jal N hr5b mr5b (mword_of_int 0x7e)
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
    assert (Hargs6 : mr6 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
                     /\ mr6 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold mr6, mr5b, mr5a, mr5, mr4. split; argrow. }
    iApply ("Hop2" $! hr6 mr6 ((12 + (12 + (4 + n)))%nat)
              with "Hcode Hro [%] Hrun Hcwd Hin");
      [ exact Hargs6 | ].
    iIntros (hr7 rr2) "Hstd Hcwd Hrun".
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
    iApply (wp_uk_cj N hr7 mr7 (mword_of_int 0x82)
              (mword_of_int 1998 : mword 11) (mword_of_int 0x1e)
              (12 + (12 + (4 + n)))
              Etgt82 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_82 with "Hcode"). }
    iIntros (hr8) "Hrun".
    iApply (wp_kinit_main_from_1e T stc cn szv hr8 mr7 n Hne
              with "[$Hwr $Hwl15 $Hwl17] Hcode Hxs Hro Hargv Hsz Hstd Hcwd Hch Htk Hrun").
  Qed.

  Lemma wp_kinit_main_repair (T Cns : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names)
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    stc <> FdClosed ->
    init_deps T -∗
    init_code γt -∗
    (* the exec deposit's supplier, AS A WAND FROM THE CONSOLE CREDENTIAL
       ([UkInit.init_cons_sup]): which credential the shell is handed is
       decided by the mknod below, so the supply is only assembled after
       it -- see [UkInit.init_cons_sup]'s note. *)
    init_cons_sup cn T Cns stc -∗
    (* ...and THE MKNOD STEP the first open left, whichever of the three
       things it is ([UkInit.uki_mknod_hit_leaf]) *)
    uki_mknod_hit_leaf N T Cns stc -∗
    init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    (* WHAT THE FIRST OPEN LEFT of the LEDGER: all-closed, or the taint.
       BOTH reach this arm -- /init's [blt] at 0x1a tests the return value,
       and under the taint nothing is known about it. *)
    uki_open2_in N T -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch_any γch -∗
    (* THE CONSOLE INPUT, on its way to the restart head: the reader token
       or the taint, which init lends to each shell it forks
       ([UserConsole.uinit_lend]). *)
    uinit_tok cn T -∗
    urun N h m (mword_of_int 0x64) (12 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs Hmkl #Hro #Hargv Hsz Hin Hcwd Hch Htk Hrun".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & Hmknod & _ & _ & _ & _ & _ & _).
    (* ---- 0x64  c.li a2,0 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x64)
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
    iApply (wp_uk_cli N hr1 mr1 (mword_of_int 0x66)
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
    iApply (wp_uk_auipc N hr2 mr2 (mword_of_int 0x68)
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
    iApply (wp_uk_addi N hr2a mr2a (mword_of_int 0x6c)
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
    iApply (wp_uk_jal N hr2b mr2b (mword_of_int 0x70)
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
    assert (Er3 : ret_pc (mr3 !!! Regidx ra_idx)
                  = (mword_of_int 0x74 : mword 64))
      by (rewrite Hrar3; apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x70  the mknod itself: the ONE place /init's own WRITE pays a
       step of the application's claim.  Under the credential it is the
       PINNED bundle; under the taint there is no pin and the generic stub
       walks it. ---- *)
    assert (Hargs3 : mr3 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
                     /\ mr3 !!! Regidx a1_idx = (mword_of_int 1 : mword 64)
                     /\ mr3 !!! Regidx a2_idx = (mword_of_int 0 : mword 64)).
    { unfold mr3, mr2b, mr2a, mr2, mr1. split_and!; argrow. }
    iApply ("Hmkl" $! hr3 mr3 ((12 + (12 + (4 + n)))%nat)
              with "Hcode Hro [%] Hrun Hcwd");
      [ exact Hargs3 | ].
    iIntros (hr4 rr1) "Hans Hcwd Hrun".
    rewrite Er3.
    (* THE SECOND OPEN AND THE EXEC SUPPLY COME OUT OF THE SAME ANSWER: the
       node exists (the pinned open, and the flag as the credential), the
       mknod failed (the SEAL, and the dead walk again), or the taint. *)
    iAssert (uki_open2 N T stc ∗ init_exec_sup_lend cn T stc)%I
      with "[Hans]" as "[Hop2 #Hxsl]".
    { iDestruct "Hxs" as "#[Hw Ht]".
      iDestruct "Hans" as "[[Hc HC] | [[%K' (Habs & HK & HC)] | #HT]]".
      - iSplitL "Hc";
          [ iApply (uki_open2_of_console N T stc with "Hwl15 Hc") | ].
        iApply ("Hw" with "HC").
      - iSplitL "Habs HK";
          [ iApply (uki_open2_of_absent N T K' stc with "Hwl15 Habs HK") | ].
        iApply ("Hw" with "HC").
      - iSplitR;
          [ iApply (uki_open2_taint_arm N T stc with "Hwl15 HT") | ].
        iApply ("Hw" with "[]"). iApply ("Ht" with "HT"). }
    iApply (wp_kinit_main_repair_tail T stc cn szv hr4 _ n Hne
              with "[$Hwr $Hwl15 $Hwl17] Hcode Hxsl Hro Hargv Hsz Hop2 Hin Hcwd Hch Htk Hrun").
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
  Lemma wp_kinit_main (T Cns : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names)
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    stc <> FdClosed ->
    init_deps T -∗
    init_code γt -∗
    (* the exec deposit's supplier -- [UkInit.init_exec_sup]: init's child
       arm ecalls exec("sh", argv), whose bundle READS THE KEY (the path
       and the argument vector, out of the image) and is therefore not
       payable through [UkRun.udep]'s key-free law.  It is init's OWN
       supply, at its own two argument registers and at the one working
       directory it ever has, and it is LENT the heap and the fd authority
       so a pinned bundle can read them. *)
    (* ...AS A WAND FROM THE CONSOLE CREDENTIAL ([UkInit.init_cons_sup]),
       because which credential the shell gets is decided by the dance
       below and not at /init's entry. *)
    init_cons_sup cn T Cns stc -∗
    (* THE CONSOLE DANCE, at whichever arm the application's boot resource
       decided ([UkInit.init_cons_dance]): the miss route's two leaves WITH
       their credential, or the flag route's pinned open and its
       credential-free mknod. *)
    init_cons_dance N T Cns stc -∗
    init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    (* the all-closed ledger /init is born with *)
    ustd γfd ufd_l0 -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch_any γch -∗
    (* THE CONSOLE INPUT, on its way to the restart head: the reader token
       or the taint, which init lends to each shell it forks
       ([UserConsole.uinit_lend]). *)
    uinit_tok cn T -∗
    urun N h m (mword_of_int InitSyms.main)
      (4 + (12 + (12 + (4 + n)))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs Hdance #Hro #Hargv Hsz Hstd Hcwd Hch Htk Hrun".
    iDestruct (uki_open1_of_dance N T Cns stc
                 with "[$Hwr $Hwl15 $Hwl17] Hdance") as "Hop1".
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
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x0)
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
    iApply (wp_uk_csdsp N hm0 mm1 (mword_of_int 0x2)
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
    iApply (wp_uk_csdsp N hm1 mm1 (mword_of_int 0x4)
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
    iApply (wp_uk_csdsp N hm2 mm1 (mword_of_int 0x6)
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
    iApply (wp_uk_csdsp N hm3 mm1 (mword_of_int 0x8)
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
    iApply (wp_uk_caddi4spn N hm4 mm1 (mword_of_int 0xa)
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
    iApply (wp_uk_cli N hm5 mm2 (mword_of_int 0xc)
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
    iApply (wp_uk_auipc N hm6 mm3 (mword_of_int 0xe)
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
    iApply (wp_uk_addi N hm7 mm4 (mword_of_int 0x12)
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
    iApply (wp_uk_jal N hm8 mm5 (mword_of_int 0x16)
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
    (* ---- 0x16  the FIRST open, AT THE PIN THAT MISSES ---- *)
    assert (Hargsm6 : mm6 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
                      /\ mm6 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold mm6, mm5, mm4, mm3. split; argrow. }
    iApply ("Hop1" $! hm9 mm6 ((12 + (12 + (4 + n)))%nat)
              with "Hcode Hro [%] Hrun Hcwd Hstd");
      [ exact Hargsm6 | ].
    iIntros (hm10 ro) "Hans Hcwd Hrun".
    assert (Em6 : ret_pc (mm6 !!! Regidx ra_idx)
                  = (mword_of_int 0x1a : mword 64))
      by (rewrite Hram6; apply bv_eq; vm_compute; reflexivity).
    rewrite Em6.
    set (mm7 := <[Regidx a0_idx := ro]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mm6)).
    assert (Ha0m7 : mm7 !!! Regidx a0_idx = ro)
      by exact (upd_eq _ (Regidx a0_idx) ro).
    (* ---- 0x1a  blt a0,x0,0x64 -- did the console exist? ---- *)
    assert (Etgt1a : add_vec (mword_of_int 0x1a : mword 64)
                       (sign_extend' 64 (mword_of_int 74 : mword 13))
                     = mword_of_int 0x64)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4
                  = mword_of_int 0x1e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite /uki_open1_out.
    iDestruct "Hans"
      as "[(%Hro & Hstd & HC) | [(%Hro & Hstd & Hmk) | (Hstd & #HT & Hmk)]]".
    - (* THE NODE WAS ALREADY THERE and the open SUCCEEDED (the FLAG arm's
         own first open): the branch is NOT taken and /init falls through
         to the dups at 0x1e with fd 0 the console. *)
      assert (Hblt0 : uv_btaken BLT (mm7 !!! Regidx a0_idx) zero_reg = false)
        by (rewrite Ha0m7 Hro; vm_compute; reflexivity).
      iApply (wp_uk_btype0 N hm10 mm7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT false
                (add_vec (mword_of_int 0x1a : mword 64)
                   (sign_extend' 64 (mword_of_int 74 : mword 13)))
                (12 + (12 + (4 + n)))
                (eq_sym Hblt0) eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_init_1a with "Hcode"). }
      rewrite E1a. iIntros (hm11) "Hrun".
      iDestruct "Hxs" as "#[Hw _]".
      iDestruct ("Hw" with "HC") as "#Hxsl".
      iApply (wp_kinit_main_from_1e T stc cn szv hm11 mm7 n Hne
                with "[$Hwr $Hwl15 $Hwl17] Hcode Hxsl Hro Hargv Hsz [Hstd] Hcwd Hch Htk Hrun").
      iApply (ufd_head_l1 with "Hstd").
    - (* THE CALL RETURNED [-1] -- the pin missed, or the node is there and
         the allocation failed (FACT 3) -- so the branch is TAKEN. *)
      assert (Hblt0 : uv_btaken BLT (mm7 !!! Regidx a0_idx) zero_reg = true)
        by (rewrite Ha0m7 Hro; vm_compute; reflexivity).
      iApply (wp_uk_btype0 N hm10 mm7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT true
                (mword_of_int 0x64) (12 + (12 + (4 + n)))
                (eq_sym Hblt0) (eq_sym Etgt1a)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_1a with "Hcode"). }
      iIntros (hm11) "Hrun".
      iApply (wp_kinit_main_repair T Cns stc cn szv hm11 mm7 n Hne
                with "[$Hwr $Hwl15 $Hwl17] Hcode Hxs Hmk Hro Hargv Hsz [Hstd] Hcwd Hch Htk Hrun").
      rewrite /uki_open2_in. by iLeft.
    - (* THE TAINT: nothing is known about the return value, so both ways
         of the branch are walked and both reach the head's third arm. *)
      destruct (uv_btaken BLT (mm7 !!! Regidx a0_idx) zero_reg) eqn:Hblt0.
      + iApply (wp_uk_btype0 N hm10 mm7 (mword_of_int 0x1a)
                  (mword_of_int 74 : mword 13) a0_idx BLT true
                  (mword_of_int 0x64) (12 + (12 + (4 + n)))
                  (eq_sym Hblt0) (eq_sym Etgt1a)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_init_1a with "Hcode"). }
        iIntros (hm11) "Hrun".
        iApply (wp_kinit_main_repair T Cns stc cn szv hm11 mm7 n Hne
                  with "[$Hwr $Hwl15 $Hwl17] Hcode Hxs Hmk Hro Hargv Hsz [Hstd] Hcwd Hch Htk Hrun").
        rewrite /uki_open2_in. iRight. iFrame "Hstd HT".
      + iApply (wp_uk_btype0 N hm10 mm7 (mword_of_int 0x1a)
                  (mword_of_int 74 : mword 13) a0_idx BLT false
                  (add_vec (mword_of_int 0x1a : mword 64)
                     (sign_extend' 64 (mword_of_int 74 : mword 13)))
                  (12 + (12 + (4 + n)))
                  (eq_sym Hblt0) eq_refl ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_init_1a with "Hcode"). }
        rewrite E1a. iIntros (hm11) "Hrun".
        iDestruct (init_cons_sup_taint cn T Cns stc with "Hxs HT") as "#Hxsl".
        iApply (wp_kinit_main_from_1e T stc cn szv hm11 mm7 n Hne
                  with "[$Hwr $Hwl15 $Hwl17] Hcode Hxsl Hro Hargv Hsz [Hstd] Hcwd Hch Htk Hrun").
        iDestruct "Hstd" as (l) "Hstd".
        iApply (ufd_head_taint with "HT Hstd").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* start @0xbc -- the ELF entry point.  Two words of frame, then main,     *)
  (* which never returns; the [jal exit] at 0xc8 is unreachable and is not   *)
  (* walked (there is no continuation to walk it from).                      *)
  (* --------------------------------------------------------------------- *)
  (* THE CREDENTIAL AND THE LEAVES ENTER HERE, as premises: E2's boot arm
     supplies them out of the era-0 claim ([AppEcho.echo_init_key] is that
     claim WITH the key beside it), and the nine application laws
     [UInitCons] SS8 takes as premises are discharged at echo's era by the
     named [AppEcho] lemmas ([UInitCons.init_cons_laws_echo]).

     THE ENTRY LEDGER IS A PREMISE TOO, at [UInitFd.ufd_l0].  /init is born
     with an all-closed table (userinit's [fdt0]) and [take NSTD fdt0] IS
     [ufd_l0] -- but nothing below the entry constructor states it, so the
     obligation belongs to the constructor ([UInitKernel.init_uexec_slot])
     and E2 discharges it there, exactly as it discharges [uvis_cwd W =
     ROOTINO]. *)
  Lemma wp_kinit_start (T Cns : iProp Σ) `{!Persistent T} `{!Timeless T}
      (stc : fdstate) (cn : cons_names)
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    stc <> FdClosed ->
    init_deps T -∗
    init_code γt -∗
    (* the exec deposit's supplier -- [UkInit.init_exec_sup]: init's child
       arm ecalls exec("sh", argv), whose bundle READS THE KEY (the path
       and the argument vector, out of the image) and is therefore not
       payable through [UkRun.udep]'s key-free law.  It is init's OWN
       supply, at its own two argument registers and at the one working
       directory it ever has, and it is LENT the heap and the fd authority
       so a pinned bundle can read them. *)
    (* ...AS A WAND FROM THE CONSOLE CREDENTIAL: see
       [UkInit.init_cons_sup]. *)
    init_cons_sup cn T Cns stc -∗
    init_cons_dance N T Cns stc -∗
    init_rodata γt -∗ init_argv γd -∗ usz γs szv -∗
    ustd γfd ufd_l0 -∗
    UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    UserChildren.uch_any γch -∗
    (* THE CONSOLE INPUT, on its way to the restart head: the reader token
       or the taint, which init lends to each shell it forks
       ([UserConsole.uinit_lend]). *)
    uinit_tok cn T -∗
    urun N h m (mword_of_int InitSyms.start)
      (2 + (4 + (12 + (12 + (4 + n))))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne.
    iIntros "#(Hwr & Hwl15 & Hwl17) #Hcode #Hxs Hcl #Hro #Hargv Hsz Hstd Hcwd Hch Htk Hrun".
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
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0xbc)
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
    iApply (wp_uk_csdsp N hs0 ms1 (mword_of_int 0xbe)
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
    iApply (wp_uk_csdsp N hs1 ms1 (mword_of_int 0xc0)
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
    iApply (wp_uk_caddi4spn N hs2 ms1 (mword_of_int 0xc2)
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
    iApply (wp_uk_jal N hs3 ms2 (mword_of_int 0xc4)
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
    iApply (wp_kinit_main T Cns stc cn szv hs4 _ n Hne
              with "[$Hwr $Hwl15 $Hwl17] Hcode Hxs Hcl Hro Hargv Hsz Hstd Hcwd Hch Htk Hrun").
  Qed.

End UkInitMain.
