(* ===================================================================== *)
(*  UkShDiagAt.v -- sh's "exec %s failed" DIAGNOSTIC, AT ANY COMMAND NAME  *)
(*                                                                       *)
(*  MOVED here from [UkShCat.v] (2026-09-21), where the pipe campaign      *)
(*  wrote it: it names nothing of cat's, and [UkShEcho]'s exec arm needs   *)
(*  it BELOW itself to be stated at any exec'able word list               *)
(*  ([ExecWords.exec_ok]) -- [UkShCat] imports [UkShEcho], so it could not *)
(*  stay there.  [UkShCat.wp_kshd_execfail_paid_at] keeps its statement    *)
(*  and is this lemma.                                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import UserHeap UkRun.
Require Import UkRunMem.
Require Import FdSlots UserFd.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UexecSG.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* S3  THE EXEC-FAILED DIAGNOSTIC, AT THE COMMAND NAME                    *)
(*                                                                        *)
(* [UkShDiag.wp_kshd_execfail_paid] prints [fprintf(2, "exec %s failed\n",*)
(* argv[0])] at 0xda and is stated at argv[0] = "echo": [ua_len x = 4],   *)
(* [ua_bytes x j = cmd_echo !!! j], and the law fixed at                  *)
(* [ush_execfail_law_at alt_execfail 17].  Its own header says a second   *)
(* line shape "supplies its own bytes by its own byte proof"; this is     *)
(* that walk with the name a parameter.                                   *)
(*                                                                        *)
(* THE THREE BYTE FAMILIES are the format's first window ("exec ", five   *)
(* bytes at indices 0-4 of the alternative), the ARGUMENT (indices        *)
(* 5..5+|cmd|-1) and the format's second window (" failed\n", the         *)
(* literal's own indices 7..14 landing at [p + (|cmd| - 2)]).  So the     *)
(* block's last index is [13 + |cmd|], which is echo's 17 at [|cmd| = 4]  *)
(* and cat's 16 at 3, and that number is the law's own [n].               *)
(* ===================================================================== *)
Section UkShDiagAt.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  Lemma wp_kshd_execfail_paid_at (N : uk_names Σ) `{!ukn_const N}
      (dg cmd : list (bv 8)) (Cr Cd : iProp Σ) (l : list fdstate)
      (h : CpuId) (m : regfile) (n : nat) (x : uarg) :
    UkSh.ush_fd2p l ->
    uint (m !!! Regidx s1_idx) mod 8 = 0 ->
    (* the name is at least two bytes -- the format's second window starts
       where the argument ends, and "%s" is two characters wide *)
    (2 <= length cmd)%nat ->
    ua_len x = length cmd ->
    (forall j : nat, (j < length cmd)%nat -> ua_bytes x j = cmd !!! j) ->
    (* the alternative is long enough for the whole block... *)
    (forall p : nat, (p < 13 + length cmd)%nat -> dg !! p = Some (dg !!! p)) ->
    (* ...and its bytes ARE the literal around the name *)
    (forall p : nat, (p < 5)%nat -> UkShDiag.shd_lit 0x12b8 p = dg !!! p) ->
    (forall j : nat, (j < length cmd)%nat ->
       cmd !!! j = dg !!! (5 + j)%nat) ->
    (forall p : nat, (7 <= p < 15)%nat ->
       UkShDiag.shd_lit 0x12b8 p = dg !!! (p + (length cmd - 2))%nat) ->
    UkShDiag.ush_execfail_law_at dg (13 + length cmd)%nat Cr Cd -∗
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    UkShRun.ush_ptr (ukn_d N) (uint (m !!! Regidx s1_idx) + 8) (ua_ptr x) -∗
    UkShRun.ush_str (ukn_d N) x -∗
    UserFd.ustd (ukn_fd N) l -∗
    Cr -∗
    (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0xda) (UkShDiag.ush_Dg + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hfd2 Hal Hc2 Hxlen Hxb Hdglk Hw1 Harg Hw2.
    iIntros "#Hlaw #Hcode #Hro #Hw [%Hxr #Hxs] Hstd Hc Hpay Hrun".
    iDestruct ("Hlaw" $! N l with "[%] Hc") as (Pf) "(HPf & #Hstep & #Hdone)";
      [ exact Hfd2 | ].
    replace (UkShDiag.ush_Dg + n)%nat with (10 + (12 + (4 + (n + 2))))%nat
      by (unfold UkShDiag.ush_Dg; lia).
    (* ---- 0xda  c.ld a2,8(s1) -- ecmd->argv[0] ---- *)
    iApply (UkShRun.wp_uk_cldq N h m (mword_of_int 0xda)
              (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 4 : mword 3) s1_idx a2_idx DfracDiscarded
              (uint (m !!! Regidx s1_idx) + 8) (mword_of_int (ua_ptr x))
              (10 + (12 + (4 + (n + 2))))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Hal; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_shk_da with "Hcode"). }
    iIntros "_".
    assert (Eda : add_vec_int (mword_of_int 0xda : mword 64) 2
                  = mword_of_int 0xdc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eda. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (ua_ptr x) : mword 64)]> m).
    iDestruct (UkShDiag.shd_str_of_ustr (ukn_t N) (ukn_d N) DfracDiscarded
                 (ua_ptr x) (ua_len x) (ua_bytes x)
                 with "Hxs") as "#Hs".
    assert (Hlitsdc : UkShDiag.shd_die_lits 0xdc 0xe0 0xe4 0xe6 0xea 0xec
                      (mword_of_int 1 : mword 20) (mword_of_int 476 : mword 12)
                      (mword_of_int 4044 : mword 21) (mword_of_int 2970 : mword 21)
                      (mword_of_int 0 : mword 6)
                      0x12b8 15%nat 5%nat)
      by shd_die_solve.
    set (C1 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf p)%I).
    set (C2 := (fun p : nat => UserFd.ustd (ukn_fd N) l ∗ Pf (5 + p)%nat)%I).
    set (C3 := (fun p : nat =>
                  UserFd.ustd (ukn_fd N) l
                  ∗ Pf (p + (length cmd - 2))%nat)%I).
    assert (E12 : C1 5%nat = C2 0%nat) by reflexivity.
    assert (E23 : C2 (ua_len x) = C3 (S (S 5%nat))).
    { rewrite /C2 /C3 Hxlen.
      replace (5 + length cmd)%nat with (S (S 5%nat) + (length cmd - 2))%nat
        by lia.
      reflexivity. }
    iApply (UkShDiag.wp_kshd_die_chain N false DfracDiscarded
              0xdc 0xe0 0xe4 0xe6 0xea 0xec
              (mword_of_int 1 : mword 20) (mword_of_int 476 : mword 12)
              (mword_of_int 4044 : mword 21) (mword_of_int 2970 : mword 21)
              (mword_of_int 0 : mword 6)
              0x12b8 15%nat 5%nat
              (ua_ptr x) (ua_len x) (ua_bytes x) C1 C2 C3 h1 m1 (n + 2)
              Hlitsdc
              ltac:(lia)
              ltac:(exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)))
              E12 E23
              with "[] [] [] [Hstd HPf] Hcode Hro Hs [] [] [] [] [] [] [Hpay] Hrun").
    { iModIntro. iIntros (p) "%Hp". rewrite /C1.
      rewrite (Hw1 p ltac:(lia)).
      iApply ("Hstep" $! p (dg !!! p) with "[%] [%]").
      { apply Hdglk. lia. }
      { lia. } }
    { iModIntro. iIntros (p) "%Hp". rewrite /C2. rewrite Hxlen in Hp.
      rewrite (Hxb p Hp) (Harg p Hp).
      replace (5 + S p)%nat with (S (5 + p))%nat by lia.
      iApply ("Hstep" $! (5 + p)%nat (dg !!! (5 + p)%nat) with "[%] [%]").
      { apply Hdglk. lia. }
      { lia. } }
    { iModIntro. iIntros (p) "%Hp". rewrite /C3.
      rewrite (Hw2 p ltac:(lia)).
      replace (S p + (length cmd - 2))%nat
        with (S (p + (length cmd - 2)))%nat by lia.
      iApply ("Hstep" $! (p + (length cmd - 2))%nat
                (dg !!! (p + (length cmd - 2))%nat) with "[%] [%]").
      { apply Hdglk. lia. }
      { lia. } }
    { rewrite /C1. iFrame "Hstd HPf". }
    { iApply (uis_shk_dc with "Hcode"). }
    { iApply (uis_shk_e0 with "Hcode"). }
    { iApply (uis_shk_e4 with "Hcode"). }
    { iApply (uis_shk_e6 with "Hcode"). }
    { iApply (uis_shk_ea with "Hcode"). }
    { iApply (uis_shk_ec with "Hcode"). }
    { rewrite /C3. iIntros "[Hstd HPf]".
      replace (15 + (length cmd - 2))%nat with (13 + length cmd)%nat by lia.
      iApply ("Hpay" with "Hstd"). iApply ("Hdone" with "HPf"). }
  Qed.

End UkShDiagAt.

(* WHAT [wp_kshd_execfail_paid_at] ASKS OF AN ALTERNATIVE'S BYTES, bundled:
   the block is "exec " ++ cmd ++ " failed\n" (and the prompt after it).  A
   walk that is stated at any command name carries this one premise. *)
Definition ush_execfail_bytes (dg cmd : list (bv 8)) : Prop :=
  (2 <= length cmd)%nat
  /\ (forall p : nat, (p < 13 + length cmd)%nat -> dg !! p = Some (dg !!! p))
  /\ (forall p : nat, (p < 5)%nat -> UkShDiag.shd_lit 0x12b8 p = dg !!! p)
  /\ (forall j : nat, (j < length cmd)%nat -> cmd !!! j = dg !!! (5 + j)%nat)
  /\ (forall p : nat, (7 <= p < 15)%nat ->
        UkShDiag.shd_lit 0x12b8 p = dg !!! (p + (length cmd - 2))%nat).
