(* ===================================================================== *)
(* UkGrepTree.v -- grep's ENTRY at its interaction tree: start() over     *)
(* [UkGrepMain.wp_kgrep_main_tree], and the same with the tree paid by an *)
(* environment (design: claude-notes/design/grep.md,                      *)
(* claude-notes/design/program-specs.md SS3.2/SS3.4e).                   *)
(*                                                                        *)
(* grep's main is stated DIRECTLY at the tree (there is no intermediate   *)
(* [kgrep_pay_all], unlike cat's [kcat_pay_all]), so this file is only    *)
(* the two-word start frame and the handler glue.                         *)
(*                                                                        *)
(* THE STACK.  Unlike cat's, grep's need is not a constant: grep()'s      *)
(* matcher recurses on the PATTERN ([UkGrepLoop.grep_words]), so start's  *)
(* need [grep_stack args] is a function of the arguments and the entry    *)
(* takes the free stack as [n] with [grep_stack args <= n].                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeGrep.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require User.GrepSyms.
Require Import FdSlots UserFd.
Require Import StringBytes LineWords.
Require Import ProgTree GrepTree UkTree.
Require Import UkGrepLoop UkGrepMain.
Require Import UkHandler.       (* [ep_iface] / [env_res] / [tree_pay_of_conforms] *)
Local Open Scope Z_scope.
Import Defs.

(* THE WORDS start NEEDS BELOW ITS OWN ENTRY: its two-word frame, main's
   six, then the deepest callee on the path argc selects -- fprintf's chain
   (10 + 12 + 4, [UkGrepFprintf.wp_kgrep_fprintf]) for the usage line;
   grep() at the pattern ([UkGrepLoop.grep_words]); and, once a file is
   named, printf's chain (12 + 12 + 4, [wp_kgrep_printf_s]) for the open
   failure.  The open/close/exit stubs take no stack. *)
Definition grep_stack (args : list uarg) : nat :=
  match args with
  | [] | [_] => (2 + (6 + (10 + (12 + 4))))%nat
  | [_; p] => (2 + (6 + grep_words (uarg_bytes p)))%nat
  | _ :: p :: _ =>
      (2 + (6 + Nat.max (grep_words (uarg_bytes p)) (12 + (12 + 4))))%nat
  end.

Lemma grep_stack_main (args : list uarg) :
  grep_stack args = (2 + grep_main_words args)%nat.
Proof. destruct args as [| a [| b [| c r]]]; reflexivity. Qed.

Section UkGrepTree.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  Local Notation tp := (tree_pay N (grep_prog N)).

  (* ------------------------------------------------------------------- *)
  (*  1.  start(argc, argv) @0x266, at the tree                           *)
  (*                                                                      *)
  (*  main always exits, so the [jal exit] at 0x272 is never reached.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kgrep_start_tree (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) :
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx (mword_of_int 10 : mword 5)
      = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    (grep_stack args <= n)%nat ->
    tp (grep_tree (map uarg_bytes args)) -∗
    grep_code γt -∗
    grep_rodata γt -∗
    uargv γd av args -∗
    ubytes γd GrepSyms.buf 1024 f -∗
    urun N h m (mword_of_int GrepSyms.start) n -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hptr Ha0 Ha1 Hneed.
    rewrite grep_stack_main in Hneed.
    assert (Hn : exists n' : nat, n = (2 + n')%nat)
      by (exists (n - 2)%nat; lia).
    destruct Hn as [n' ->].
    assert (Hneed' : (grep_main_words args <= n')%nat) by lia.
    iIntros "Ht #Hcode #Hro #Hargv Hbuf Hrun".
    destruct grep_syms_pins
      as (Hstart & Hmain & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
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
    (* ---- 0x266  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x266)
              (mword_of_int 48 : mword 6) 2 n'
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_266 with "Hcode"). }
    iIntros "Hframe".
    rewrite Hsp.
    rewrite (_ : add_vec_int (mword_of_int 0x266 : mword 64) 2
                 = mword_of_int 0x268);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h0) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg
                      (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_2_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2])".
    (* ---- 0x268  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0x268)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) w1 n'
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_268 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x268 : mword 64) 2
                 = mword_of_int 0x26a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0x26a  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x26a)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) w2 n'
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_26a with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x26a : mword 64) 2
                 = mword_of_int 0x26c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x26c  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x26c)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))
              n'
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_grep_26c with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x26c : mword 64) 2
                 = mword_of_int 0x26e);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0x26e  jal ra,0x1d0 <main> ---- *)
    iApply (wp_uk_jal N h3 m2 (mword_of_int 0x26e)
              (mword_of_int 2096994 : mword 21) ra_idx
              (mword_of_int GrepSyms.main) (mword_of_int 0x272) n'
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_26e with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x272 : mword 64)]> m2).
    assert (Ha0_3 : m3 !!! Regidx a0_idx
                    = mword_of_int (Z.of_nat (length args))).
    { rewrite <- Ha0.
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1.
      exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int av).
    { rewrite <- Ha1.
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1.
      exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_kgrep_main_tree N h4 m3 av args f n' Hptr Ha0_3 Ha1_3 Hneed'
              with "Ht Hcode Hro Hargv Hbuf Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2.  the entry at a handler (program-specs cut 5, lane C)            *)
  (* ------------------------------------------------------------------- *)

  (* [wp_kgrep_start_tree] with the tree paid by an ENVIRONMENT
     ([UkHandler.tree_pay_of_conforms_p]); [UkCatTree.wp_kcat_start_env]'s
     twin, less its [safe_fds] premise: grep's tree is safe at EVERY held
     set ([GrepTree.grep_tree_safe] -- every read has a positive count and
     the only close is of the descriptor its own open returned), so the
     premise is discharged here rather than asked of the caller. *)
  Lemma wp_kgrep_start_env {Dp : list nat} (I : ep_ifaceP (Dp := Dp) N (grep_prog N))
      (E : penv) (ds : gset nat)
      (h : CpuId) (m : regfile) (av : Z) (args : list uarg)
      (f : nat -> bv 8) (n : nat) :
    conforms E (grep_tree (map uarg_bytes args)) ->
    dp_in Dp ds ->
    (forall (j : nat) (g : uarg), args !! j = Some g -> ua_ptr g <> 0) ->
    m !!! Regidx (mword_of_int 10 : mword 5)
      = mword_of_int (Z.of_nat (length args)) ->
    m !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int av ->
    (grep_stack args <= n)%nat ->
    env_res N (grep_prog N) I E ds -∗
    grep_code γt -∗
    grep_rodata γt -∗
    uargv γd av args -∗
    ubytes γd GrepSyms.buf 1024 f -∗
    urun N h m (mword_of_int GrepSyms.start) n -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hc Hdp Hptr Ha0 Ha1 Hn. iIntros "Henv #Hcode #Hro #Hargv Hbuf Hrun".
    iApply (wp_kgrep_start_tree h m av args f n Hptr Ha0 Ha1 Hn
              with "[Henv] Hcode Hro Hargv Hbuf Hrun").
    iApply (tree_pay_of_conforms_p N (grep_prog N) I E ds _ Hc
              (grep_tree_safe _ _) Hdp with "Henv").
  Qed.

End UkGrepTree.
