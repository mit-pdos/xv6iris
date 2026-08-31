(* ===================================================================== *)
(* UkInitFs.v -- INIT'S CONSOLE PREAMBLE, WALKED ON THE ENRICHED TIER      *)
(* (fd-row pilot, prover stage P5).                                        *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md; the prover plan   *)
(* is the "## FD-ROW PILOT" section of                                     *)
(* claude-notes/projects/fs-syscall-specs.md.                              *)
(*                                                                         *)
(* WHAT THIS FILE IS.  Upstream's [UkInit.v] / [UkInitMain.v] walk init on  *)
(* [UkRun.urun], where a syscall's return is an unconstrained [∀ r] and    *)
(* the file system is invisible.  This file re-walks THE SAME INSTRUCTIONS  *)
(* on [UexecRetFs.urun_fs] beside [FsFdMirror.mcur], so that each of the    *)
(* preamble's five syscalls steps the mirror by its own enriched row -- and *)
(* the walk therefore REFINES the pure pilot chain: at the end of the       *)
(* slice the mirror says fd 0 is the console device the mknod created, and  *)
(* fds 1 and 2 are its dups.                                                *)
(*                                                                         *)
(* NOTHING OF UPSTREAM'S IS EDITED.  [UkInit.v], [UkInitMain.v] and the     *)
(* catalog [UCodeInit.v] are REQUIRED, not touched: the instruction facts   *)
(* ([uis_init_XX]), the symbol pins ([init_syms_pins]) and the read-only    *)
(* image ([init_rodata]) are shared with the plain walk, and the plain walk *)
(* stays exactly as it is.                                                  *)
(*                                                                         *)
(* THE SLICE, and why it starts where it does.  The walk runs from main's   *)
(* CONSOLE ARM at 0xc -- [c.li a1,2] (O_RDWR), the "console" pointer, the   *)
(* [jal open], the [blt] test, the mknod repair arm at 0x64 with its second *)
(* open, and the two [dup(0)] calls -- to the restart-loop head at 0x32.    *)
(* main's PROLOGUE (0x0..0xa: the frame push and the four [c.sdsp] spills)  *)
(* is fs-inert and is deliberately NOT re-walked: the spills go through     *)
(* [UkStore.wp_uk_store_later], a SECOND engine driver, so re-walking them  *)
(* would cost a second engine seal for zero fs content.  The cost of        *)
(* extending is recorded in the worklist.                                   *)
(*                                                                         *)
(* HONEST ARM ACCOUNTING.                                                   *)
(*   - The [blt] at 0x1a is walked on BOTH arms.  Its fall-through arm      *)
(*     (the first open SUCCEEDED) is REFUTED, not assumed away: at era 0    *)
(*     "console" does not resolve, so the open row forces r1 = -1, so the   *)
(*     branch is taken.  That refutation is the machine-level reading of    *)
(*     [pilot_console_pure]'s first conclusion.                             *)
(*   - mknod's return is IGNORED, exactly as init ignores it; the chain     *)
(*     recovers it from the second open's success (the walk that resolved   *)
(*     forces mknod's success arm).                                         *)
(*   - Each syscall keeps its own [<> -1] guard.  Nothing here claims a     *)
(*     syscall succeeds -- what is proven is that it cannot succeed         *)
(*     WRONGLY.                                                             *)
(*                                                                         *)
(* THE LEAF RULE.  This file requires [FdRowPilot], hence [FsImgCheck]: it  *)
(* is an image-check CONSUMER and must stay a LEAF -- nothing may require   *)
(* it.  (So must [FdRowMint]; the two are siblings, neither requires the    *)
(* other.)                                                                  *)
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
Local Open Scope Z_scope.
Import Defs.
Require Import UkInit.
Require Import UkInitLit.
Require Import UkInitPrintf.
Require Import UkFork.
Require Import UkRunBr.
Require Import UkInitMain.
(* ...UkInitMain.v's block above, VERBATIM; the pilot's own imports below. *)
Require Import TfUser.
Require Import UsysMemOk.
Require Import UexecRet.     (* [tf_of]/[tf_of_num]/[tf_of_arg0..2] *)
Require Import ConsoleInv.      (* [CONSOLE] *)
Require Import SpecSysMknodAU.  (* [dev_arg] *)
Require Import SpecSysOpenAU.   (* [om_arg] *)
Require Import FdSlots.         (* [fdstate] *)
Require Import FsAbs.           (* [anode]/[MkAnode]/[ADev] *)
Require Import FsFdMirror.
Require Import UexecRetFs.
Require Import UkRunSysFs.
Require Import UkRunFsLeaf.
Require Import FdRowPilot.

Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 THE "console" LITERAL, AS A TEXT STRING.                            *)
(*                                                                        *)
(* init's path argument is the read-only byte run at 0x970, and it is the  *)
(* pilot's [console_str] -- ONE [vm_compute] over the tracked image says   *)
(* so.  This is what ties the machine walk's argument to the pure chain's  *)
(* path, and it is why the enriched leaf takes a TEXT string rather than   *)
(* P2's writable [ustrq]: 0x970 is in the program's read-only image, so a  *)
(* [ustrq] premise there would be UNSATISFIABLE at the state init runs in. *)
(* ===================================================================== *)

Definition console_lit_ok : bool :=
  forallb (fun j : nat =>
             match init_ro !! (0x970 + Z.of_nat j)%Z with
             | Some b => bool_decide (b = ustr_bytes console_str j)
             | None => false
             end)
          (seq 0 (length console_str))
  && match init_ro !! (0x970 + Z.of_nat (length console_str))%Z with
     | Some b => bool_decide (b = ubyte0)
     | None => false
     end.

Lemma console_lit_ok_holds : console_lit_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma console_str_len : length console_str = 7%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma console_lit_body (j : nat) :
  (j < length console_str)%nat ->
  init_ro !! (0x970 + Z.of_nat j)%Z = Some (ustr_bytes console_str j).
Proof.
  intros Hj.
  pose proof console_lit_ok_holds as H. unfold console_lit_ok in H.
  apply andb_true_iff in H as [H _].
  rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  destruct (init_ro !! (0x970 + Z.of_nat j)%Z) as [b |] eqn:Hb;
    [| discriminate H ].
  apply bool_decide_eq_true in H. rewrite H. reflexivity.
Qed.

Lemma console_lit_nul :
  init_ro !! (0x970 + Z.of_nat (length console_str))%Z = Some ubyte0.
Proof.
  pose proof console_lit_ok_holds as H. unfold console_lit_ok in H.
  apply andb_true_iff in H as [_ H].
  destruct (init_ro !! (0x970 + Z.of_nat (length console_str))%Z)
    as [b |] eqn:Hb; [| discriminate H ].
  apply bool_decide_eq_true in H. rewrite H. reflexivity.
Qed.

Lemma console_str_nonul (j : nat) :
  (j < length console_str)%nat -> ustr_bytes console_str j <> ubyte0.
Proof.
  intros Hj.
  rewrite console_str_len in Hj.
  destruct j as [ | [ | [ | [ | [ | [ | [ | j ] ] ] ] ] ] ]; try lia;
    (intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
     discriminate Hc).
Qed.

Lemma console_str_forall_nonul :
  Forall (fun b : bv 8 => b <> unul) console_str.
Proof.
  rewrite /console_str /fname_console.
  repeat (constructor;
          [ intro Hc; apply (f_equal bv_unsigned) in Hc;
            vm_compute in Hc; discriminate Hc | ]).
  constructor.
Qed.

(* ===================================================================== *)
(* THE WALK, over the two engine seals.                                   *)
(* ===================================================================== *)
Module UkInitFsWalk (R : FDROW_UKFS_RETIRE) (S : FDROW_UKFS_STEP).

Module L := FdRowUkfsLeaf R S.

Section UkInitFs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).

  Local Notation LIT_START := 0x978.

  (* the literal, as the enriched leaf's path resource *)
  Lemma init_console_ustrt :
    init_rodata γt -∗ L.ustrt γt 0x970 console_str.
  Proof.
    iIntros "#Hro". rewrite /L.ustrt.
    iSplitR; [ iPureIntro; exact console_str_forall_nonul | ].
    iSplitR.
    { iPureIntro. rewrite console_str_len. cbv [UMAXPATH]. lia. }
    rewrite /init_rodata.
    iApply (utext_str_of_img γt init_ro 0x970 (length console_str)
              (ustr_bytes console_str)
              console_str_nonul
              ltac:(vm_compute; reflexivity)
              console_lit_body console_lit_nul with "Hro").
  Qed.

  (* =================================================================== *)
  (* §1 THE THREE ENRICHED SYSCALL STUBS.                                 *)
  (*                                                                      *)
  (* usys.S's three-instruction bodies ([c.li a7,N]; [ecall]; [c.jr ra]),  *)
  (* on [urun_fs].  open and mknod are PATH rows and take the leaf that    *)
  (* pins the fetched string; dup is the NON-PATH enriched row, whose      *)
  (* argument 0 is a descriptor number.                                    *)
  (* =================================================================== *)

  Lemma wp_kinit_open_fs (γm : gname) (h : CpuId) (m : regfile)
      (u : umirror) (pl : list (bv 8)) (avail : nat) :
    init_code γt -∗
    L.ustrt γt (uint (m !!! Regidx a0_idx)) pl -∗
    urun_fs γm γt γd γs h m (mword_of_int InitSyms.open) avail -∗
    mcur γm u -∗
    (∀ (h' : CpuId) (ret : mword 64) (u' : umirror),
       ⌜ufs_open_at pl (m !!! Regidx a1_idx) ret u u'⌝ -∗
       mcur γm u' -∗
       urun_fs γm γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hstr Hrun Hmc Hcont".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0x3b2)
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
    assert (Ha0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate)).
    assert (Ha1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate)).
    iAssert (L.ustrt γt (uint (m1 !!! Regidx a0_idx)) pl) as "#Hstr1".
    { rewrite Ha0. iExact "Hstr". }
    (* ---- 0x3b4  ecall -- the ENRICHED open row ---- *)
    iApply (L.wp_uk_ecall_fs_text γm γt γd γs h1 m1 (mword_of_int 0x3b4)
              FsFdMirror.USYS_open u pl avail
              ltac:(unfold m1;
                    rewrite tf_of_num;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hmc Hstr1").
    { iApply (uis_init_3b4 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret u') "%Hstep Hmc Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- the tie, read at the caller's own argument words ---- *)
    assert (Hopen_row : ufs_open_at pl (m !!! Regidx a1_idx) ret u u').
    { unfold ufs_step_at in Hstep.
      destruct (decide (FsFdMirror.USYS_open = FsFdMirror.USYS_open))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      assert (Harg : ufs_arg (tf_of m1 (mword_of_int 0x3b4)) 1
                     = m !!! Regidx a1_idx)
        by (unfold ufs_arg; rewrite tf_of_arg1; exact Ha1).
      rewrite Harg in Hstep. exact Hstep. }
    (* ---- 0x3b8  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (L.wp_uk_cjr_run_fs γm γt γd γs h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret u' with "[%] Hmc Hrun").
    exact Hopen_row.
  Qed.

  Lemma wp_kinit_mknod_fs (γm : gname) (h : CpuId) (m : regfile)
      (u : umirror) (pl : list (bv 8)) (avail : nat) :
    init_code γt -∗
    L.ustrt γt (uint (m !!! Regidx a0_idx)) pl -∗
    urun_fs γm γt γd γs h m (mword_of_int InitSyms.mknod) avail -∗
    mcur γm u -∗
    (∀ (h' : CpuId) (ret : mword 64) (u' : umirror),
       ⌜ufs_mknod_at pl (dev_arg (m !!! Regidx a1_idx))
          (dev_arg (m !!! Regidx a2_idx)) ret u u'⌝ -∗
       mcur γm u' -∗
       urun_fs γm γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hstr Hrun Hmc Hcont".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hmknod & _ & _ & _ & _ & _ & _).
    rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0x3ba)
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
    assert (Ha0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate)).
    assert (Ha1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate)).
    assert (Ha2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate)).
    iAssert (L.ustrt γt (uint (m1 !!! Regidx a0_idx)) pl) as "#Hstr1".
    { rewrite Ha0. iExact "Hstr". }
    (* ---- 0x3bc  ecall -- the ENRICHED mknod row ---- *)
    iApply (L.wp_uk_ecall_fs_text γm γt γd γs h1 m1 (mword_of_int 0x3bc)
              FsFdMirror.USYS_mknod u pl avail
              ltac:(unfold m1;
                    rewrite tf_of_num;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 17 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hmc Hstr1").
    { iApply (uis_init_3bc with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0x3bc : mword 64) 4
                 = mword_of_int 0x3c0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret u') "%Hstep Hmc Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hmk_row : ufs_mknod_at pl (dev_arg (m !!! Regidx a1_idx))
                        (dev_arg (m !!! Regidx a2_idx)) ret u u').
    { unfold ufs_step_at in Hstep.
      destruct (decide (FsFdMirror.USYS_mknod = FsFdMirror.USYS_open))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_mknod = FsFdMirror.USYS_mknod))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      assert (Harg1 : ufs_arg (tf_of m1 (mword_of_int 0x3bc)) 1
                      = m !!! Regidx a1_idx)
        by (unfold ufs_arg; rewrite tf_of_arg1; exact Ha1).
      assert (Harg2 : ufs_arg (tf_of m1 (mword_of_int 0x3bc)) 2
                      = m !!! Regidx a2_idx)
        by (unfold ufs_arg; rewrite tf_of_arg2; exact Ha2).
      rewrite Harg1 Harg2 in Hstep. exact Hstep. }
    (* ---- 0x3c0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (L.wp_uk_cjr_run_fs γm γt γd γs h2 m2 (mword_of_int 0x3c0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3c0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret u' with "[%] Hmc Hrun").
    exact Hmk_row.
  Qed.

  Lemma wp_kinit_dup_fs (γm : gname) (h : CpuId) (m : regfile)
      (u : umirror) (avail : nat) :
    init_code γt -∗
    urun_fs γm γt γd γs h m (mword_of_int InitSyms.dup) avail -∗
    mcur γm u -∗
    (∀ (h' : CpuId) (ret : mword 64) (u' : umirror),
       ⌜ufs_dup_at (m !!! Regidx a0_idx) ret u u'⌝ -∗
       mcur γm u' -∗
       urun_fs γm γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hmc Hcont".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hdup & _ & _ & _ & _ & _).
    rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0x3ea)
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
    assert (Ha0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate)).
    (* ---- 0x3ec  ecall -- the ENRICHED dup row (no path) ---- *)
    iApply (L.wp_uk_ecall_fs_nopath γm γt γd γs h1 m1 (mword_of_int 0x3ec)
              FsFdMirror.USYS_dup u avail
              ltac:(unfold m1;
                    rewrite tf_of_num;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hmc").
    { iApply (uis_init_3ec with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret u') "%Hstep Hmc Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hdup_row : ufs_dup_at (m !!! Regidx a0_idx) ret u u').
    { unfold ufs_step_at in Hstep.
      destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_open))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_mknod))
        as [Hc | _]; [ discriminate Hc |].
      destruct (decide (FsFdMirror.USYS_dup = FsFdMirror.USYS_dup))
        as [_ | Hc]; [| exfalso; exact (Hc eq_refl) ].
      assert (Harg0 : ufs_arg (tf_of m1 (mword_of_int 0x3ec)) 0
                      = m !!! Regidx a0_idx)
        by (unfold ufs_arg; rewrite tf_of_arg0; exact Ha0).
      rewrite Harg0 in Hstep. exact Hstep. }
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (L.wp_uk_cjr_run_fs γm γt γd γs h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret u' with "[%] Hmc Hrun").
    exact Hdup_row.
  Qed.

  (* =================================================================== *)
  (* §2 THE TWO DUPS AND THE LITERAL: 0x1e -> 0x32.                       *)
  (* =================================================================== *)
  Lemma wp_kinit_dups_fs (γm : gname) (h : CpuId) (m : regfile)
      (u : umirror) (avail : nat) :
    init_code γt -∗
    urun_fs γm γt γd γs h m (mword_of_int 0x1e) avail -∗
    mcur γm u -∗
    (∀ (h' : CpuId) (m' : regfile) (ud1 ud2 : umirror)
       (vf rd1 rd2 : mword 64),
       ⌜bv_signed vf = 0
        /\ ufs_dup_at vf rd1 u ud1
        /\ ufs_dup_at vf rd2 ud1 ud2
        /\ m' !!! Regidx s2_idx = (mword_of_int LIT_START : mword 64)⌝ -∗
       mcur γm ud2 -∗
       urun_fs γm γt γd γs h' m' (mword_of_int 0x32) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hmc Hcont".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hdup & _ & _ & _ & _ & _).
    (* ---- 0x1e  c.li a0,0 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0x1e)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_1e with "Hcode"). }
    assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2
                  = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1e.
    iIntros (hq1) "Hrun".
    set (vf := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                : mword 64)).
    set (mq1 := <[Regidx a0_idx := vf]> m).
    (* ---- 0x20  jal ra,dup ---- *)
    iApply (L.wp_uk_jal_run_fs γm γt γd γs hq1 mq1 (mword_of_int 0x20)
              (mword_of_int 970 : mword 21) ra_idx
              (mword_of_int InitSyms.dup) (mword_of_int 0x24) avail
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
    assert (Ha0q2 : mq2 !!! Regidx a0_idx = vf).
    { unfold mq2, mq1.
      exact (eq_trans
               (upd_ne mq1 (Regidx ra_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x24 : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq m (Regidx a0_idx) vf)). }
    iApply (wp_kinit_dup_fs γm hq2 mq2 u avail with "Hcode Hrun Hmc").
    iIntros (hq3 rd1 ud1) "%Hd1 Hmc Hrun".
    rewrite Ha0q2 in Hd1.
    assert (Eq2 : ret_pc (mq2 !!! Regidx ra_idx)
                  = (mword_of_int 0x24 : mword 64))
      by (rewrite Hraq2; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq2.
    set (mq3 := <[Regidx a0_idx := rd1]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq2)).
    (* ---- 0x24  c.li a0,0 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs hq3 mq3 (mword_of_int 0x24)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_24 with "Hcode"). }
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24.
    iIntros (hq4) "Hrun".
    set (mq4 := <[Regidx a0_idx := vf]> mq3).
    (* ---- 0x26  jal ra,dup ---- *)
    iApply (L.wp_uk_jal_run_fs γm γt γd γs hq4 mq4 (mword_of_int 0x26)
              (mword_of_int 964 : mword 21) ra_idx
              (mword_of_int InitSyms.dup) (mword_of_int 0x2a) avail
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
    assert (Ha0q5 : mq5 !!! Regidx a0_idx = vf).
    { unfold mq5, mq4.
      exact (eq_trans
               (upd_ne mq4 (Regidx ra_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x2a : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq mq3 (Regidx a0_idx) vf)). }
    iApply (wp_kinit_dup_fs γm hq5 mq5 ud1 avail with "Hcode Hrun Hmc").
    iIntros (hq6 rd2 ud2) "%Hd2 Hmc Hrun".
    rewrite Ha0q5 in Hd2.
    assert (Eq5 : ret_pc (mq5 !!! Regidx ra_idx)
                  = (mword_of_int 0x2a : mword 64))
      by (rewrite Hraq5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eq5.
    set (mq6 := <[Regidx a0_idx := rd2]>
                  (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> mq5)).
    (* ---- 0x2a  auipc s2 ; 0x2e  addi s2 -- the "starting sh" literal ---- *)
    iApply (L.wp_uk_auipc_run_fs γm γt γd γs hq6 mq6 (mword_of_int 0x2a)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x2a : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20)))
              avail
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
    iApply (L.wp_uk_addi_run_fs γm γt γd γs hq7 mq7 (mword_of_int 0x2e)
              (mword_of_int 2382 : mword 12) s2_idx s2_idx
              (mword_of_int LIT_START) avail
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
    iApply ("Hcont" $! hq8 mq8 ud1 ud2 vf rd1 rd2 with "[%] Hmc Hrun").
    split_and!.
    - unfold vf. vm_compute. reflexivity.
    - exact Hd1.
    - exact Hd2.
    - exact (upd_eq mq7 (Regidx s2_idx)
               (regval_into_reg (mword_of_int LIT_START : mword 64))).
  Qed.

  (* =================================================================== *)
  (* §3 THE REPAIR ARM: 0x64 -> (mknod, open) -> 0x1e -> 0x32.            *)
  (* =================================================================== *)
  Lemma wp_kinit_repair_fs (γm : gname) (h : CpuId) (m : regfile)
      (u1 : umirror) (avail : nat) :
    init_code γt -∗ init_rodata γt -∗
    urun_fs γm γt γd γs h m (mword_of_int 0x64) avail -∗
    mcur γm u1 -∗
    (∀ (h' : CpuId) (m' : regfile) (u2 u3 ud1 ud2 : umirror)
       (wma wmi vom3 vf r2 r3 rd1 rd2 : mword 64),
       ⌜ufs_mknod_at console_str (dev_arg wma) (dev_arg wmi) r2 u1 u2
        /\ bv_unsigned wma mod 2 ^ 16 = CONSOLE
        /\ bv_unsigned wmi mod 2 ^ 16 = 0
        /\ ufs_open_at console_str vom3 r3 u2 u3
        /\ om_arg vom3 = 2
        /\ bv_signed vf = 0
        /\ ufs_dup_at vf rd1 u3 ud1
        /\ ufs_dup_at vf rd2 ud1 ud2
        /\ m' !!! Regidx s2_idx = (mword_of_int LIT_START : mword 64)⌝ -∗
       mcur γm ud2 -∗
       urun_fs γm γt γd γs h' m' (mword_of_int 0x32) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun Hmc Hcont".
    iDestruct (init_console_ustrt with "Hro") as "#Hstr".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & Hmknod & _ & _ & _ & _ & _ & _).
    (* ---- 0x64  c.li a2,0 ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0x64)
              (mword_of_int 0 : mword 6) a2_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_64 with "Hcode"). }
    assert (E64 : add_vec_int (mword_of_int 0x64 : mword 64) 2
                  = mword_of_int 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E64.
    iIntros (hr1) "Hrun".
    set (wmi := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                 : mword 64)).
    set (mr1 := <[Regidx a2_idx := wmi]> m).
    (* ---- 0x66  c.li a1,1 -- CONSOLE ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs hr1 mr1 (mword_of_int 0x66)
              (mword_of_int 1 : mword 6) a1_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_66 with "Hcode"). }
    assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2
                  = mword_of_int 0x68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E66.
    iIntros (hr2) "Hrun".
    set (wma := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                 : mword 64)).
    set (mr2 := <[Regidx a1_idx := wma]> mr1).
    (* ---- 0x68  auipc a0 ; 0x6c  addi a0 -- 0x970 ---- *)
    assert (Er68 : add_vec (add_vec (mword_of_int 0x68 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                   (sign_extend' 64 (mword_of_int 2312 : mword 12))
                 = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (L.wp_uk_auipc_run_fs γm γt γd γs hr2 mr2 (mword_of_int 0x68)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x68 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) avail
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
    iApply (L.wp_uk_addi_run_fs γm γt γd γs hr2a mr2a (mword_of_int 0x6c)
              (mword_of_int 2312 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) avail
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
    (* ---- 0x70  jal ra,mknod ---- *)
    iApply (L.wp_uk_jal_run_fs γm γt γd γs hr2b mr2b (mword_of_int 0x70)
              (mword_of_int 842 : mword 21) ra_idx
              (mword_of_int InitSyms.mknod) (mword_of_int 0x74) avail
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
    assert (Ha0r3 : mr3 !!! Regidx a0_idx
                    = regval_into_reg (mword_of_int 0x970 : mword 64)).
    { unfold mr3, mr2b.
      exact (eq_trans
               (upd_ne mr2b (Regidx ra_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x74 : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq mr2a (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x970 : mword 64)))). }
    assert (Ha1r3 : mr3 !!! Regidx a1_idx = wma).
    { unfold mr3, mr2b, mr2a, mr2.
      rewrite (upd_ne mr2b (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr2a (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr2 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mr1 (Regidx a1_idx) wma). }
    assert (Ha2r3 : mr3 !!! Regidx a2_idx = wmi).
    { unfold mr3, mr2b, mr2a, mr2, mr1.
      rewrite (upd_ne mr2b (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr2a (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr2 (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr1 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx a2_idx) wmi). }
    iAssert (L.ustrt γt (uint (mr3 !!! Regidx a0_idx)) console_str)
      as "#Hstr3".
    { rewrite Ha0r3.
      assert (Hu : uint (regval_into_reg (mword_of_int 0x970 : mword 64))
                   = 0x970) by (vm_compute; reflexivity).
      rewrite Hu. iExact "Hstr". }
    iApply (wp_kinit_mknod_fs γm hr3 mr3 u1 console_str avail
              with "Hcode Hstr3 Hrun Hmc").
    iIntros (hr4 r2 u2) "%Hmk Hmc Hrun".
    rewrite Ha1r3 Ha2r3 in Hmk.
    assert (Er3 : ret_pc (mr3 !!! Regidx ra_idx)
                  = (mword_of_int 0x74 : mword 64))
      by (rewrite Hrar3; apply bv_eq; vm_compute; reflexivity).
    rewrite Er3.
    set (mr4 := <[Regidx a0_idx := r2]>
                  (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> mr3)).
    (* ---- 0x74  c.li a1,2 -- O_RDWR ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs hr4 mr4 (mword_of_int 0x74)
              (mword_of_int 2 : mword 6) a1_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_74 with "Hcode"). }
    assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2
                  = mword_of_int 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E74.
    iIntros (hr5) "Hrun".
    set (vom3 := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                  : mword 64)).
    set (mr5 := <[Regidx a1_idx := vom3]> mr4).
    (* ---- 0x76  auipc a0 ; 0x7a  addi -- 0x970 ---- *)
    assert (Er76 : add_vec (add_vec (mword_of_int 0x76 : mword 64)
                     (auipc_off (mword_of_int 1 : mword 20)))
                   (sign_extend' 64 (mword_of_int 2298 : mword 12))
                 = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (L.wp_uk_auipc_run_fs γm γt γd γs hr5 mr5 (mword_of_int 0x76)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0x76 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) avail
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
    iApply (L.wp_uk_addi_run_fs γm γt γd γs hr5a mr5a (mword_of_int 0x7a)
              (mword_of_int 2298 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) avail
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
    (* ---- 0x7e  jal ra,open ---- *)
    iApply (L.wp_uk_jal_run_fs γm γt γd γs hr5b mr5b (mword_of_int 0x7e)
              (mword_of_int 820 : mword 21) ra_idx
              (mword_of_int InitSyms.open) (mword_of_int 0x82) avail
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
    assert (Ha0r6 : mr6 !!! Regidx a0_idx
                    = regval_into_reg (mword_of_int 0x970 : mword 64)).
    { unfold mr6, mr5b.
      exact (eq_trans
               (upd_ne mr5b (Regidx ra_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x82 : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq mr5a (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x970 : mword 64)))). }
    assert (Ha1r6 : mr6 !!! Regidx a1_idx = vom3).
    { unfold mr6, mr5b, mr5a, mr5.
      rewrite (upd_ne mr5b (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr5a (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mr5 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mr4 (Regidx a1_idx) vom3). }
    iAssert (L.ustrt γt (uint (mr6 !!! Regidx a0_idx)) console_str)
      as "#Hstr6".
    { rewrite Ha0r6.
      assert (Hu : uint (regval_into_reg (mword_of_int 0x970 : mword 64))
                   = 0x970) by (vm_compute; reflexivity).
      rewrite Hu. iExact "Hstr". }
    iApply (wp_kinit_open_fs γm hr6 mr6 u2 console_str avail
              with "Hcode Hstr6 Hrun Hmc").
    iIntros (hr7 r3 u3) "%Hop3 Hmc Hrun".
    rewrite Ha1r6 in Hop3.
    assert (Er6 : ret_pc (mr6 !!! Regidx ra_idx)
                  = (mword_of_int 0x82 : mword 64))
      by (rewrite Hrar6; apply bv_eq; vm_compute; reflexivity).
    rewrite Er6.
    set (mr7 := <[Regidx a0_idx := r3]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mr6)).
    (* ---- 0x82  c.j 0x1e -- back to the main line ---- *)
    assert (Etgt82 : (mword_of_int 0x1e : mword 64)
                     = add_vec (mword_of_int 0x82 : mword 64)
                         (sign_extend' 64
                            (sign_extend' 21
                               (concat_vec (mword_of_int 1998 : mword 11)
                                  ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (L.wp_uk_cj_run_fs γm γt γd γs hr7 mr7 (mword_of_int 0x82)
              (mword_of_int 1998 : mword 11) (mword_of_int 0x1e) avail
              Etgt82 ltac:(vm_compute; reflexivity) with "[] Hrun").
    { iApply (uis_init_82 with "Hcode"). }
    iIntros (hr8) "Hrun".
    iApply (wp_kinit_dups_fs γm hr8 mr7 u3 avail with "Hcode Hrun Hmc").
    iIntros (hr9 m' ud1 ud2 vf rd1 rd2) "%Hdups Hmc Hrun".
    destruct Hdups as (Hvf & Hd1 & Hd2 & Hs2).
    iApply ("Hcont" $! hr9 m' u2 u3 ud1 ud2 wma wmi vom3 vf r2 r3 rd1 rd2
              with "[%] Hmc Hrun").
    split_and!.
    - exact Hmk.
    - unfold wma. vm_compute. reflexivity.
    - unfold wmi. vm_compute. reflexivity.
    - exact Hop3.
    - unfold vom3. vm_compute. reflexivity.
    - exact Hvf.
    - exact Hd1.
    - exact Hd2.
    - exact Hs2.
  Qed.

  (* =================================================================== *)
  (* §4 THE CONSOLE ARM: 0xc -> 0x32, both arms of the [blt] walked.      *)
  (* =================================================================== *)
  Lemma wp_kinit_console_arm_fs (γm : gname) (h : CpuId) (m : regfile)
      (u0 : umirror) (avail : nat) :
    era0_seed u0 ->
    init_code γt -∗ init_rodata γt -∗
    urun_fs γm γt γd γs h m (mword_of_int 0xc) avail -∗
    mcur γm u0 -∗
    (∀ (h' : CpuId) (m' : regfile) (u2 u3 : umirror)
       (r3 rd1 rd2 : mword 64),
       ⌜r3 <> (mword_of_int (-1) : mword 64) ->
        rd1 <> (mword_of_int (-1) : mword 64) ->
        rd2 <> (mword_of_int (-1) : mword 64) ->
        um_fdt u3 !! 0%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ um_fdt u3 !! 1%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ um_fdt u3 !! 2%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ (exists i : Z,
              um_resolve u2 console_str = Some i
              /\ um_av u3 !! i = Some (MkAnode (ADev CONSOLE 0) 1%nat))⌝ -∗
       ⌜m' !!! Regidx s2_idx = (mword_of_int LIT_START : mword 64)⌝ -∗
       mcur γm u3 -∗
       urun_fs γm γt γd γs h' m' (mword_of_int 0x32) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hseed.
    iIntros "#Hcode #Hro Hrun Hmc Hcont".
    iDestruct (init_console_ustrt with "Hro") as "#Hstr".
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    (* ---- 0xc  c.li a1,2 -- O_RDWR ---- *)
    iApply (L.wp_uk_cli_run_fs γm γt γd γs h m (mword_of_int 0xc)
              (mword_of_int 2 : mword 6) a1_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_0c with "Hcode"). }
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    iIntros (hm6) "Hrun".
    set (vom1 := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                  : mword 64)).
    set (mm3 := <[Regidx a1_idx := vom1]> m).
    (* ---- 0xe  auipc a0 ; 0x12  addi a0 -- "console" ---- *)
    assert (Econ : add_vec (add_vec (mword_of_int 0xe : mword 64)
                              (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 2402 : mword 12))
                   = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (L.wp_uk_auipc_run_fs γm γt γd γs hm6 mm3 (mword_of_int 0xe)
              (mword_of_int 1 : mword 20) a0_idx
              (add_vec (mword_of_int 0xe : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_init_0e with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 4
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e.
    iIntros (hm7) "Hrun".
    set (mm4 := <[Regidx a0_idx := regval_into_reg
                    (add_vec (mword_of_int 0xe : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mm3).
    iApply (L.wp_uk_addi_run_fs γm γt γd γs hm7 mm4 (mword_of_int 0x12)
              (mword_of_int 2402 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mm3 (Regidx a0_idx) (regval_into_reg _));
                    exact (eq_sym Econ))
              with "[] Hrun").
    { iApply (uis_init_12 with "Hcode"). }
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12.
    iIntros (hm8) "Hrun".
    set (mm5 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int 0x970 : mword 64)]> mm4).
    (* ---- 0x16  jal ra,open ---- *)
    iApply (L.wp_uk_jal_run_fs γm γt γd γs hm8 mm5 (mword_of_int 0x16)
              (mword_of_int 924 : mword 21) ra_idx
              (mword_of_int InitSyms.open) (mword_of_int 0x1a) avail
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
    assert (Ha0m6 : mm6 !!! Regidx a0_idx
                    = regval_into_reg (mword_of_int 0x970 : mword 64)).
    { unfold mm6, mm5.
      exact (eq_trans
               (upd_ne mm5 (Regidx ra_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x1a : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq mm4 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x970 : mword 64)))). }
    assert (Ha1m6 : mm6 !!! Regidx a1_idx = vom1).
    { unfold mm6, mm5, mm4, mm3.
      rewrite (upd_ne mm5 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mm4 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mm3 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx a1_idx) vom1). }
    iAssert (L.ustrt γt (uint (mm6 !!! Regidx a0_idx)) console_str)
      as "#Hstr6".
    { rewrite Ha0m6.
      assert (Hu : uint (regval_into_reg (mword_of_int 0x970 : mword 64))
                   = 0x970) by (vm_compute; reflexivity).
      rewrite Hu. iExact "Hstr". }
    iApply (wp_kinit_open_fs γm hm9 mm6 u0 console_str avail
              with "Hcode Hstr6 Hrun Hmc").
    iIntros (hm10 r1 u1) "%Hop1 Hmc Hrun".
    rewrite Ha1m6 in Hop1.
    assert (Em6 : ret_pc (mm6 !!! Regidx ra_idx)
                  = (mword_of_int 0x1a : mword 64))
      by (rewrite Hram6; apply bv_eq; vm_compute; reflexivity).
    rewrite Em6.
    set (mm7 := <[Regidx a0_idx := r1]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mm6)).
    (* ---- THE ERA-0 FORCING: "console" does not resolve at the seed, so
       the open row's success arm is unsatisfiable and r1 = -1 ---- *)
    destruct (ufs_open_at_miss console_str vom1 r1 u0 u1
                (era0_resolve_console_miss u0 Hseed) Hop1) as [Hr1 Hu1].
    subst u1.
    assert (Ha0m7 : mm7 !!! Regidx a0_idx = r1)
      by (unfold mm7; exact (upd_eq _ (Regidx a0_idx) r1)).
    (* ---- 0x1a  blt a0,x0,0x64 -- did the console exist? ---- *)
    assert (Etgt1a : add_vec (mword_of_int 0x1a : mword 64)
                       (sign_extend' 64 (mword_of_int 74 : mword 13))
                     = mword_of_int 0x64)
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (uv_btaken BLT (mm7 !!! Regidx a0_idx) zero_reg) eqn:Hblt0.
    - (* the console was absent -- the only reachable arm at era 0 *)
      iApply (L.wp_uk_btype0_run_fs γm γt γd γs hm10 mm7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT true
                (mword_of_int 0x64) avail
                (eq_sym Hblt0) (eq_sym Etgt1a)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_init_1a with "Hcode"). }
      iIntros (hm11) "Hrun".
      iApply (wp_kinit_repair_fs γm hm11 mm7 u0 avail
                with "Hcode Hro Hrun Hmc").
      iIntros (hr9 m' u2 u3 ud1 ud2 wma wmi vom3 vf r2 r3 rd1 rd2)
        "%Hall Hmc Hrun".
      destruct Hall as (Hmk & Hma & Hmi & Hop3 & Hom & Hvf & Hd1 & Hd2 & Hs2).
      assert (Hconc :
        r3 <> (mword_of_int (-1) : mword 64) ->
        rd1 <> (mword_of_int (-1) : mword 64) ->
        rd2 <> (mword_of_int (-1) : mword 64) ->
        um_fdt ud2 !! 0%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ um_fdt ud2 !! 1%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ um_fdt ud2 !! 2%nat = Some (FdOpen true true (FdDevice CONSOLE))
        /\ (exists i : Z,
              um_resolve u2 console_str = Some i
              /\ um_av ud2 !! i = Some (MkAnode (ADev CONSOLE 0) 1%nat))).
      { intros Hne3 Hnd1 Hnd2.
        destruct (pilot_console_dups u0 u0 u2 u3 ud1 ud2 vom1 vom3 wma wmi
                    r1 r2 r3 vf vf rd1 rd2
                    Hseed Hop1 Hmk Hma Hmi Hop3 Hom Hne3
                    Hd1 Hvf Hnd1 Hd2 Hvf Hnd2)
          as (_ & _ & _ & _ & Hf0 & Hf1 & Hf2 & Hav).
        exact (conj Hf0 (conj Hf1 (conj Hf2 Hav))). }
      iApply ("Hcont" $! hr9 m' u2 ud2 r3 rd1 rd2 with "[%] [%] Hmc Hrun");
        [ exact Hconc | exact Hs2 ].
    - (* the fall-through arm is UNREACHABLE at era 0: r1 = -1 *)
      exfalso.
      rewrite Ha0m7 Hr1 in Hblt0.
      vm_compute in Hblt0. discriminate Hblt0.
  Qed.

  (* =================================================================== *)
  (* §5 THE COMPOSITION with upstream's plain tail.  The enriched          *)
  (* preamble hands its run back through [urun_fs_urun] and init's restart *)
  (* loop -- landed, plain, untouched -- runs from 0x32 exactly as before. *)
  (* =================================================================== *)
  Lemma wp_kinit_console_arm_then_loop (γm : gname) (szv : Z) (h : CpuId)
      (m : regfile) (u0 : umirror) (n : nat) :
    era0_seed u0 ->
    init_code γt -∗ init_rodata γt -∗ usz γs szv -∗
    urun_fs γm γt γd γs h m (mword_of_int 0xc) (12 + (12 + (4 + n))) -∗
    mcur γm u0 -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hseed. iIntros "#Hcode #Hro Hsz Hrun Hmc".
    iApply (wp_kinit_console_arm_fs γm h m u0 (12 + (12 + (4 + n))) Hseed
              with "Hcode Hro Hrun Hmc").
    iIntros (h' m' u2 u3 r3 rd1 rd2) "_ %Hs2 Hmc Hrun".
    iDestruct (urun_fs_urun with "Hrun") as "Hrun".
    iDestruct (UkInitMain.wp_kinit_main_loop γt γd γs szv n
                 with "Hcode Hro") as "[Hloop _]".
    iApply ("Hloop" $! h' m' with "[] Hsz Hrun").
    iPureIntro. exact Hs2.
  Qed.

End UkInitFs.
End UkInitFsWalk.
