(* ===================================================================== *)
(* UkEcho.v -- the `echo` user program on the USER-MODE-ON-KERNEL engine:  *)
(* UProofEcho.v / UProofEchoA.v's five function proofs restated as U-mode  *)
(* CONTINUATIONS ([UexecRet.ukc]) over UkLeaf.v / UkStore.v / UkLoad.v /   *)
(* UkBranch.v / UkStep.v, with every premise a fact about the KEY (the     *)
(* image [M] and the permission map [π]) -- nothing about a table, and no  *)
(* capability assumption.  UkSync.v is the same port one program smaller;  *)
(* read its header for the shape, and claude-notes/design/uk-engine.md for *)
(* the engine.                                                            *)
(*                                                                        *)
(* WHY ECHO IS THE INTERESTING ONE.  `sync` is [sync(); exit(0);] -- no    *)
(* load, no branch, no loop, no argument.  echo is nothing but those: two  *)
(* bounded loops (the argv walk and strlen's scan), a load of every argv   *)
(* slot and of every byte of every string, and three calls to a RETURNING  *)
(* syscall.  So this file is where the engine's load and branch leaves and *)
(* UkAbi.v's key-level argument area ([uk_args]) get their first consumer. *)
(*                                                                        *)
(* THE KEY-LEVEL PREMISES, and the ONE that is new beside sync's:          *)
(*                                                                        *)
(*   uk_xpage π 0            page 0 is an X page -- echo's whole text and  *)
(*                           both its rodata strings live there           *)
(*   echo_text_sub M         the dumped text is in the image              *)
(*   uk_stack π M sp0 n      the frame budget below the entry sp          *)
(*   uk_args π M av argc lo alen                                          *)
(*                           THE ARGUMENT AREA (UkAbi.v §3): argv is an    *)
(*                           8-aligned readable array of [argc] pointers,  *)
(*                           each to a readable NUL-terminated run, all of *)
(*                           it at or above [lo = uint sp0].              *)
(*                                                                        *)
(* All four are DECIDABLE facts about the key, which is what an entry gate *)
(* in UexecCond.v's shape needs.                                          *)
(*                                                                        *)
(* WHAT IS NOT A PREMISE ANY MORE, AND WHY.  On the OLD tier `write`'s     *)
(* protocol row was [UsysReadsBuf], so every call PAID [uv_rd pt M buf n]  *)
(* -- and the two rodata strings echo hands to write() therefore needed a  *)
(* readable-window premise of their own ([echo_rodata_rd], and with it     *)
(* [echo_data_sub]).  The kernel's own trap contract has no such place:    *)
(* [UexecRet.uexec_ret]'s ecall arm is                                     *)
(*   ∀ r M' π', ⌜usys_mem_ok n tf r M π M' π'⌝ -∗ uslot (bump W r M' π')   *)
(* -- ONE PURE hypothesis and no iProp -- so a caller of write owes        *)
(* nothing and must instead be safe for EVERY return value.  Echo          *)
(* DISCARDS write's result, so that ∀ costs it nothing, and the file needs *)
(* neither [echo_data_sub] nor a rodata window.                            *)
(*                                                                        *)
(* THE PRICE IS REAL AND IS RECORDED, not papered over: the old            *)
(* obligation is what forced strlen's answer to be the string's TRUE       *)
(* length, i.e. echo's one piece of functional content.  Here strlen still *)
(* returns [len] -- the proof establishes it internally, from [ucstr]'s    *)
(* dichotomy -- but nothing downstream is obliged to it.  Recovering `the  *)
(* bytes echo passes to write are its argv strings' is the [Φ] refinement  *)
(* parked in claude-notes/design/user-wp-slot.md (an iProp premise under   *)
(* the SAME ∀), and its kernel half is blocked independently at            *)
(* SpecConsolewrite's copyin.  Nothing here special-cases that ∀.          *)
(*                                                                        *)
(* WRITE IS QUIET.  [SYS_write] is 16 and [usys_window 16 = None], so it   *)
(* lands in [usys_mem_ok]'s QUIET row -- [M' = M] and [π' = π], exactly    *)
(* the row [SYS_sync] (22) takes.  Echo's loop is therefore a walk over a  *)
(* key that moves only in the register file and in strlen's own frame.     *)
(*                                                                        *)
(* THE TWO LOOPS ARE ORDINARY ROCQ INDUCTIONS on a [nat] measure, not      *)
(* [iLöb]s: both are BOUNDED (by [argc] and by the NUL's index), and       *)
(* UkBranch.v's later-FREE branch leaves exist precisely so a bounded loop *)
(* need not pay a [▷].                                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeCap UmodeAbi.
Require Import WpUmodeStore WpUmodeLoad WpUmodeBranch.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkLeaf UkStore UkLoad UkBranch.
Require Import UkAbi.        (* the generic key-level layout / argv facts *)
Require Import UCodeEcho.    (* echo's decode facts and [echo_layout] *)
Require Import TsoCtx.       (* [CurCtx]: ambient, per the WpUmode* precedent *)
Require User.EchoSyms User.EchoInstrs.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 Small pure bricks.                                                  *)
(*                                                                        *)
(* Three facts UProofEchoA.v proved [Local]ly on the old tier and that are *)
(* about bytes and images alone, so they are re-stated here rather than    *)
(* imported from a file that speaks the capability engine.                 *)
(* ===================================================================== *)

Lemma uk_bv8_range (b : bv 8) : 0 <= bv_unsigned b < Z64.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as [Hr0 Hr1].
  split; [ exact Hr0 | ].
  eapply Z.lt_le_trans; [ exact Hr1 | ].
  unfold Z64. apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma uk_bv8_zero (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

(* echo's text is all below 4096, so any store into a frame (which is at or
   above 4096 by [uk_stack]'s own [uks_lo]) leaves the image inclusion
   standing *)
Lemma echo_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  echo_text_sub M -> 4096 <= a -> echo_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (echo_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.


(* ONE 8-byte store inside the disturbed window is a [uM_only]
   (UProofEcho.v's, verbatim: it is about images alone). *)
Lemma uM_only_store8 (M : gmap Z (bv 8)) (a lo n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n -> uM_only M (uM_store8 M a v) lo n.
Proof.
  intros H1 H2. split.
  - intros k Hk. exact (uM_store8_is_Some M a v k Hk).
  - intros k Hk. apply uM_store8_lookup_ne.
    intros j Hj. pose proof (Nat2Z.is_nonneg j). lia.
Qed.

(* [upd_eq] / [upd_ne] in the shape a lookup CHAIN wants.  A register that
   survives a call is read back through a sixteen-deep insert tower, and
   [apply]ing these peels one insert per step (the durable-notes rule:
   never [rewrite upd_eq]). *)
Lemma upd_ne_tr (f : regfile) (kk jj : regidx) (v w : mword 64) :
  jj <> kk -> f !!! jj = w -> (<[kk := v]> f) !!! jj = w.
Proof. intros Hne Hw. rewrite (upd_ne f kk jj v Hne). exact Hw. Qed.

Lemma upd_eq_tr (f : regfile) (kk : regidx) (v w : mword 64) :
  v = w -> (<[kk := v]> f) !!! kk = w.
Proof. intro H. rewrite (upd_eq f kk v). exact H. Qed.

(* ===================================================================== *)
(* §0b THE ARGV INDEX CHAIN -- main's one piece of real arithmetic.       *)
(*                                                                        *)
(* The C source's                                                         *)
(*     s1 = argv + 1;  s5 = &argv[argc-1];  s4 = &argv[argc];             *)
(* compiles to seven instructions that never mention argc-1 or argc:       *)
(*                                                                        *)
(*   1a  addi   s1,a1,8           s1 = argv + 8                            *)
(*   1e  addiw  a0,a0,-2          a0 = (int32) (argc - 2)                  *)
(*   20  slli   a5,a0,0x20        \  the zero-extend-and-scale idiom:      *)
(*   24  srli   a0,a5,0x1d        /  a0 = (uint32)(argc-2) * 8             *)
(*   28  add    s5,s1,a0                                                   *)
(*   2c  addi   a1,a1,16                                                   *)
(*   2e  add    s4,a1,a0                                                   *)
(*                                                                        *)
(* UProofEcho.v §1, verbatim: it is a fact about the ISA's arithmetic and  *)
(* echo's immediates, with no tier in it at all.  Copied rather than       *)
(* imported so that this file does not depend on the old capability        *)
(* engine's proof; when that engine goes, this is where it lives.          *)
(* ===================================================================== *)

Lemma echo_argv_chain (argc av : Z) :
  2 <= argc < 2 ^ 31 -> 0 <= av -> av + 8 * argc <= 2 ^ 38 ->
  let a0_1 := sign_extend' 64
       (subrange_vec_dec
          (add_vec (mword_of_int argc : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))) 31 0) in
  let a0_2 := shift_bits_right
       (shift_bits_left a0_1
          (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
       (subrange_vec_dec (mword_of_int 29 : mword 6) (Z.sub log2_xlen 1) 0) in
  let s1   := add_vec (mword_of_int av : mword 64)
                (sign_extend' 64 (mword_of_int 8 : mword 12)) in
  let s5   := add_vec s1 a0_2 in
  let a1_1 := add_vec (mword_of_int av : mword 64)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) in
  let s4   := add_vec a1_1 a0_2 in
  a0_2 = mword_of_int (8 * (argc - 2)) /\
  s5   = mword_of_int (av + 8 * (argc - 1)) /\
  s4   = mword_of_int (av + 8 * argc).
Proof.
  intros Hargc Hav Hhi a0_1 a0_2 s1 s5 a1_1 s4.
  assert (E62 : sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))
                = (mword_of_int (-2) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (E8 : sign_extend' 64 (mword_of_int 8 : mword 12) = (mword_of_int 8 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (E16 : sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))
                = (mword_of_int 16 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Ha1 : a0_1 = mword_of_int (argc - 2)).
  { unfold a0_1. rewrite E62. apply moi_addw. unfold Z31; lia. }
  assert (Ha2 : a0_2 = mword_of_int (8 * (argc - 2))).
  { unfold a0_2. rewrite Ha1.
    rewrite (moi_shl32_shr29 (argc - 2) ltac:(unfold Z32; lia)).
    f_equal; lia. }
  split_and!.
  - exact Ha2.
  - unfold s5, s1. rewrite E8 Ha2 !moi_add. f_equal; lia.
  - unfold s4, a1_1. rewrite E16 Ha2 !moi_add. f_equal; lia.
Qed.

(* the store leaf's key premise implies the LOAD leaf's -- a writable page
   is in the map, and presence in the map IS readability (UkAbi.v §1).
   HOIST CANDIDATE: belongs in UkAbi.v §1 beside [uk_rpage_load_ok], and is
   kept here only so that adding it does not rebuild the whole slot cone. *)
Lemma uk_wpage_load_ok (pm : gmap (mword 27) uperm) (va : mword 64) :
  uk_wpage pm va -> uk_load_ok pm va.
Proof. intros (q & Hq & _). exists q. exact Hq. Qed.

(* ===================================================================== *)
(* §1 The BRIDGES from the key's layout facts to the table's.             *)
(*                                                                        *)
(* [echo_layout pt] claims TWO things about page 0 -- a fetch-ok leaf AND  *)
(* a load-ok one, because echo's rodata shares the text page.  Both come   *)
(* off the SAME [uk_xpage]: [UserPerm.perm_of_X] produces the leaf and its *)
(* fetch permission, and [UserPerm.perm_of_R] reads the load permission    *)
(* off that same leaf (R needs no bit of its own -- UserPerm.v §1's        *)
(* [perm_leaf] is [None] unless U and R are both set).  So echo's key-level*)
(* text premise is EXACTLY sync's, and the extra claim is free.            *)
(* ===================================================================== *)

Lemma echo_layout_of_key (pt : uptd) (sz : Z) (π : gmap (mword 27) uperm) :
  proc_pt_wf pt -> perm_of (ud_um pt) sz = π ->
  uk_xpage π (mword_of_int 0) -> echo_layout pt.
Proof.
  intros Hwf Hpm (q & Hq & Hx). unfold uperm_at in Hq. rewrite <- Hpm in Hq.
  destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
  constructor. exists w. split; [ exact Hw | ].
  split; [ exact Hok | exact (perm_of_R pt sz _ q w Hwf Hq Hw) ].
Qed.

(* the decode facts of UCodeEcho.v, lifted to every table realizing the key *)
Lemma uk_instr_of_echo (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (pc : mword 64) (is_rvc : bool) (i : instruction) :
  uk_xpage π (mword_of_int 0) ->
  (forall pt : uptd, echo_layout pt -> uinstr pt M pc is_rvc i) ->
  uk_instr π M pc is_rvc i.
Proof.
  intros Hx H pt sz Hwf Hpm. exact (H pt (echo_layout_of_key pt sz π Hwf Hpm Hx)).
Qed.

(* ===================================================================== *)
(* §2 The two syscall stubs.                                              *)
(* ===================================================================== *)

Section UkEcho.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context (π : gmap (mword 27) uperm).

  (* the [uinstr] fact of one echo instruction at every table of the key *)
  Local Notation UI ui M Htext Hx :=
    (uk_instr_of_echo π M _ _ _ Hx (fun pt0 Hl0 => ui pt0 M Hl0 Htext)).

  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* exit @0x332: c.li a7,2; ecall.  The contract's exit arm is [emp], so  *)
  (* the stub DIVERGES and the c.jr at 0x338 is dead code.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kecho_exit_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    ⊢ ukc π M m (mword_of_int EchoSyms.exit).
  Proof.
    intros Hx Htext.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite Hsexit.
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* 0x332  c.li a7,2 *)
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut π sz Hlo Hpm M m (mword_of_int 0x332)
              (mword_of_int 2 : mword 6) a7_idx (mword_of_int 2 : mword 64)
              (UI ui_echo_332 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw2
              with "Hb").
    assert (Epc : add_vec_int (mword_of_int 0x332 : mword 64) 2 = mword_of_int 0x334)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc.
    set (m1 := <[Regidx a7_idx := regval_into_reg (mword_of_int 2 : mword 64)]> m).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* 0x334  ecall -- SYS_exit, the [emp] arm *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 2 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (regval_into_reg (mword_of_int 2 : mword 64))).
    iApply (wp_uk_ecall C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x334)
              (UI ui_echo_334 M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x334) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x334)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x334) M π)) = USYS_exit).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hne]; [ done | exfalso; exact (Hne eq_refl) ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* write @0x352: c.li a7,16; ecall; c.jr ra.  RETURNS.  [SYS_write] is   *)
  (* 16, whose [usys_mem_ok] row is the QUIET one (M' = M, π' = π), so the *)
  (* continuation is at the SAME image with a0 := the (arbitrary) return   *)
  (* value and a7 := 16.  Nothing is claimed about the buffer -- see the   *)
  (* header.                                                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kecho_write_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
        uvb (CID := h) C pt Rut sz π M m (mword_of_int EchoSyms.write) -∗
        (∀ ret : mword 64,
           ukc π M (<[Regidx a0_idx := ret]>
                      (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite Hswrite.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* 0x352  c.li a7,16 *)
    assert (Hw16 : (mword_of_int 16 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut π sz Hlo Hpm M m (mword_of_int 0x352)
              (mword_of_int 16 : mword 6) a7_idx (mword_of_int 16 : mword 64)
              (UI ui_echo_352 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    (* normalize the [regval_into_reg] wrapper NOW, before the a0 insert is
       stacked on it *)
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 16 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x352 : mword 64) 2 = mword_of_int 0x354)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* 0x354  ecall -- SYS_write, the returning arm *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 16 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
    iApply (wp_uk_ecall C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x354)
              (UI ui_echo_354 M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x354) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x354)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x354) M π)) = 16).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (16 = USYS_exit)) as [Hne | _]; [ exfalso; discriminate Hne | ].
    destruct (decide (16 = USYS_fork)) as [Hne | _]; [ exfalso; discriminate Hne | ].
    iIntros (ret M' π') "%Hok".
    destruct (usys_mem_ok_quiet 16 _ ret _ _ _ _
                ltac:(discriminate) ltac:(discriminate) eq_refl Hok) as [-> ->].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m1 (mword_of_int 0x354) M M π π ret Hx0
               ltac:(vm_compute; reflexivity)).
    assert (Epc2 : add_vec_int (mword_of_int 0x354 : mword 64) 4 = mword_of_int 0x358)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc2.
    set (m2 := <[Regidx (mword_of_int 10) := ret]> m1).
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* 0x358  c.jr ra -- neither insert touches ra *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne m1 (Regidx (mword_of_int 10)) (Regidx (mword_of_int 1 : mword 5)) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 16) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx)
                   = ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra2. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uk_cjr C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M m2 (mword_of_int 0x358)
              (mword_of_int 1 : mword 5) (m !!! Regidx ra_idx)
              (UI ui_echo_358 M Htext Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    iApply ("Hcont" $! ret).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 strlen @0xdc -- the first verified function with a LOOP, and the   *)
  (* first that RETURNS a computed value.                                  *)
  (*                                                                       *)
  (*   dc..e2  the gcc prologue (16-byte frame; ra and s0 spilled)          *)
  (*   e4..e8  load the first byte and test it -- the empty-string arm      *)
  (*   ea      a5 := s+1, then the scan loop                                *)
  (*   f8      a0 := a3 - a0, i.e. the length, as a 32-bit subtract         *)
  (*   fc..102 the epilogue, shared verbatim by both arms                   *)
  (* ------------------------------------------------------------------- *)

  (* THE EPILOGUE @0xfc, shared by both arms of the entry test (the len = 0
     arm reaches it by the c.j at 0x106):

       fc  c.ldsp ra,8(sp) ; fe  c.ldsp s0,0(sp) ; 100 c.addi sp,sp,16
       102 c.jr ra

     The content is the two RELOADS: their [wval] is [uM_word] over the
     image the prologue left, and the epilogue must prove that equals what
     the prologue stored.  For the s0 slot that is [uM_word_store8]
     directly; for the ra slot one has to see through the s0 store first,
     whose window [sp0-16, sp0-8) is disjoint from [sp0-8, sp0).

     The exit is stated POINTWISE over the registers (x1/x2/x8 by value,
     everything else unchanged) rather than as an insert tower: the caller
     owes [ucallee_saved], whose index is a VARIABLE, and a tower cannot be
     peeled at one. *)
  Local Lemma wp_kecho_strlen_epi (M : gmap Z (bv 8))
      (mF : regfile) (sp0 v8 v0 : mword 64) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    uk_stack π M sp0 16 ->
    is_aligned_vaddr (Virtaddr v8) 2 = true ->
    mF !!! Regidx sp_idx = add_vec_int sp0 (-16) ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
        uvb (CID := h) C pt Rut sz π
          (uM_store8 (uM_store8 M (uint sp0 - 8) v8) (uint sp0 - 16) v0) mF
          (mword_of_int 0xfc) -∗
        (∀ m' : regfile,
           ⌜m' !!! Regidx sp_idx = sp0⌝ -∗
           ⌜m' !!! Regidx s0_idx = v0⌝ -∗
           ⌜forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx sp_idx ->
              Regidx r <> Regidx s0_idx -> m' !!! Regidx r = mF !!! Regidx r⌝ -∗
           ukc π (uM_store8 (uM_store8 M (uint sp0 - 8) v8) (uint sp0 - 16) v0)
             m' v8) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hst Hret2 Hsp.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo16.
    destruct (uk_stack_slot π M sp0 16 8 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot π M sp0 16 0 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    set (M1 := uM_store8 M (uint sp0 - 8) v8).
    set (M2 := uM_store8 M1 (uint sp0 - 16) v0).
    assert (Htext1 : echo_text_sub M1)
      by (unfold M1; apply echo_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : echo_text_sub M2)
      by (unfold M2; apply echo_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k)).
    { intros k Hk. unfold M2, M1.
      exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)). }
    assert (Hb8' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 8) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb8 j Hj) as (b & Hb).
      exact (Hdom _ (mk_is_Some _ _ Hb)). }
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (Hdom _ (mk_is_Some _ _ Hb)). }
    (* the ra slot reads back what the prologue stored: see through the s0
       store, whose eight bytes are strictly below this slot *)
    assert (Hw8v : v8 = uM_word M2 (uint (add_vec_int (add_vec_int sp0 (-16)) 8)) 8).
    { rewrite Hu8'. symmetry. apply (uM_bytes_inj M2 (uint sp0 - 8)).
      - apply (uM_word_bytes M2 (uint sp0 - 8) 8 ltac:(lia)).
        intros j Hj. destruct (Hb8' j Hj) as (b & Hb).
        rewrite Hu8' in Hb. exists b. exact Hb.
      - intros j Hj. unfold M2.
        rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) v0
                   (uint sp0 - 8 + Z.of_nat j) ltac:(intros i Hi; lia)).
        exact (uM_store8_bytes M (uint sp0 - 8) v8 j Hj). }
    (* ... and the s0 slot is the round trip itself *)
    assert (Hw0v : v0 = uM_word M2 (uint (add_vec_int (add_vec_int sp0 (-16)) 0)) 8).
    { rewrite Hu0'. unfold M2. symmetry. apply uM_word_store8. }
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0xfc  c.ldsp ra,8(sp) ---- *)
    assert (Hva8 : add_vec_int (add_vec_int sp0 (-16)) 8
                   = add_vec (mF !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { assert (Hs : mF !!! Regidx csp_rs1 = add_vec_int sp0 (-16)) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_cldsp C pt Rut π sz Hlo Hpm M2 mF (mword_of_int 0xfc)
              (mword_of_int 1 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-16)) 8) v8
              (UI ui_echo_fc M2 Htext2 Hx)
              ltac:(vm_compute; discriminate) Hva8
              (uk_wpage_load_ok π _ Hw8) Hcanon8 Hpg8 Hal8 Hb8' Hw8v
              with "Hb").
    set (mF1 := <[Regidx ra_idx := regval_into_reg v8]> mF).
    assert (Efc : add_vec_int (mword_of_int 0xfc : mword 64) 2 = mword_of_int 0xfe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efc.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0xfe  c.ldsp s0,0(sp) ---- *)
    assert (Hsp1 : mF1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16)).
    { exact (eq_trans
               (upd_ne mF (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg v8)
                  ltac:(vm_compute; discriminate)) Hsp). }
    assert (Hva0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (mF1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_cldsp C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M2 mF1 (mword_of_int 0xfe)
              (mword_of_int 0 : mword 6) s0_idx
              (add_vec_int (add_vec_int sp0 (-16)) 0) v0
              (UI ui_echo_fe M2 Htext2 Hx)
              ltac:(vm_compute; discriminate) Hva0
              (uk_wpage_load_ok π _ Hw0) Hcanon0 Hpg0 Hal0 Hb0' Hw0v
              with "Hb").
    set (mF2 := <[Regidx s0_idx := regval_into_reg v0]> mF1).
    assert (Efe : add_vec_int (mword_of_int 0xfe : mword 64) 2 = mword_of_int 0x100)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efe.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x100  c.addi sp,sp,16 ---- *)
    assert (Hsp2 : mF2 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { exact (eq_trans
               (upd_ne mF1 (Regidx s0_idx) (Regidx sp_idx) (regval_into_reg v0)
                  ltac:(vm_compute; discriminate)) Hsp1). }
    assert (Hwsp : sp0 = add_vec (mF2 !!! Regidx sp_idx)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))).
    { rewrite Hsp2.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc.
      (* sp back where it started.  NOTE the spelling: [uv_avi_neg]'s
         [- d] is [Z.opp d] and the [(-16)] written here is a NEGATIVE
         LITERAL -- convertible but not syntactically equal, so the
         displacement is supplied EXPLICITLY (an [apply] would have to
         invert [Z.opp] to find it, and cannot). *)
      pose proof (uks_canon _ _ _ _ Hst) as Hcan'.
      change (2 ^ 38) with 274877906944 in Hcan'.
      rewrite uint_unsigned in Hlo16, Hcan'.
      pose proof (uv_avi_neg sp0 16 ltac:(lia) ltac:(lia)) as Hb.
      assert (Hsum : add_vec_int (add_vec_int sp0 (-16)) 16 = sp0).
      { apply bv_eq.
        rewrite (uint_add_vec_int_small (add_vec_int sp0 (-16)) 16 ltac:(lia)
                   ltac:(rewrite Hb; lia)).
        rewrite Hb. lia. }
      symmetry. exact Hsum. }
    iApply (wp_uk_caddi C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M2 mF2 (mword_of_int 0x100)
              (mword_of_int 16 : mword 6) sp_idx sp0
              (UI ui_echo_100 M2 Htext2 Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (mF3 := <[Regidx sp_idx := regval_into_reg sp0]> mF2).
    assert (E100 : add_vec_int (mword_of_int 0x100 : mword 64) 2 = mword_of_int 0x102)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E100.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x102  c.jr ra ---- *)
    assert (Hra3 : mF3 !!! Regidx (mword_of_int 1 : mword 5) = v8).
    { exact (eq_trans
               (upd_ne mF2 (Regidx sp_idx) (Regidx (mword_of_int 1 : mword 5))
                  (regval_into_reg sp0) ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mF1 (Regidx s0_idx) (Regidx (mword_of_int 1 : mword 5))
                     (regval_into_reg v0) ltac:(vm_compute; discriminate))
                  (upd_eq mF (Regidx ra_idx) (regval_into_reg v8)))). }
    assert (Htgt : v8 = ret_pc (mF3 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra3. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uk_cjr C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M2 mF3 (mword_of_int 0x102)
              (mword_of_int 1 : mword 5) v8
              (UI ui_echo_102 M2 Htext2 Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    (* the three exit facts *)
    assert (HA : mF3 !!! Regidx sp_idx = sp0)
      by exact (upd_eq mF2 (Regidx sp_idx) (regval_into_reg sp0)).
    assert (HB : mF3 !!! Regidx s0_idx = v0).
    { exact (eq_trans
               (upd_ne mF2 (Regidx sp_idx) (Regidx s0_idx) (regval_into_reg sp0)
                  ltac:(vm_compute; discriminate))
               (upd_eq mF1 (Regidx s0_idx) (regval_into_reg v0))). }
    assert (HC : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx sp_idx ->
              Regidx r <> Regidx s0_idx -> mF3 !!! Regidx r = mF !!! Regidx r).
    { intros r Hra Hsp' Hs0.
      exact (eq_trans (upd_ne mF2 (Regidx sp_idx) (Regidx r) (regval_into_reg sp0) Hsp')
               (eq_trans
                  (upd_ne mF1 (Regidx s0_idx) (Regidx r) (regval_into_reg v0) Hs0)
                  (upd_ne mF (Regidx ra_idx) (Regidx r) (regval_into_reg v8) Hra))). }
    iApply ("Hcont" $! mF3 with "[%] [%] [%]");
      [ exact HA | exact HB | exact HC ].
  Qed.

  (* THE SCAN LOOP.  Head 0xee, back edge 0xf6:

       ee  c.mv   a3,a5 ; f0  c.addi a5,a5,1 ; f2  lbu a4,-1(a5)
       f6  c.bnez a4,0xee

     An ORDINARY Rocq induction on the nat measure [len-1-j], NOT an [iLöb]:
     the loop is BOUNDED by the NUL's index, and UkBranch.v's leaf is
     later-free precisely so a bounded loop need not pay a [▷].  The measure
     premise is STRICT (< n) so the n = 0 case is closed by [lia] and the
     four-instruction body is written exactly once.

     Invariant at 0xee: a5 = s+1+j with 0 <= j <= len-1.  Exit: a3 = s+len,
     at 0xf8.  Everything OTHER than a3/a4/a5 comes back POINTWISE -- an
     insert tower would change shape every iteration and could not compose
     with itself.  The image does not move at all: the loop only loads. *)
  Local Lemma wp_kecho_strlen_loop (n : nat) :
    forall (M : gmap Z (bv 8)) (mE : regfile) (s len j : Z),
      (Z.to_nat (len - 1 - j) < n)%nat ->
      uk_xpage π (mword_of_int 0) ->
      echo_text_sub M ->
      ucstr M s len ->
      uk_rd π M s (len + 1) ->
      0 <= j <= len - 1 ->
      mE !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64) ->
      ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
          ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
          uvb (CID := h) C pt Rut sz π M mE (mword_of_int 0xee) -∗
          (∀ m' : regfile,
             ⌜m' !!! Regidx a3_idx = (mword_of_int (s + len) : mword 64)⌝ -∗
             ⌜forall r : mword 5,
                Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
                Regidx r <> Regidx a5_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
             ukc π M m' (mword_of_int 0xf8)) -∗
          WP (Loop : expr riscv_lang).
  Proof.
    induction n as [ | n IH ];
      intros M mE s len j Hn Hx Htext Hstr Hrd Hj Ha5.
    { exfalso. lia. }
    pose proof (ukrd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (ukrd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    (* THE byte this iteration tests, and the dichotomy it decides *)
    assert (Hbex : exists bj : bv 8,
              M !! (s + 1 + j) = Some bj /\ (bj = ubyte0 <-> 1 + j = len)).
    { destruct (Z.eq_dec (1 + j) len) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr) as Hnul.
        replace (s + len) with (s + 1 + j) in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr (1 + j) ltac:(lia)) as (b & Hb & Hb0).
        replace (s + (1 + j)) with (s + 1 + j) in Hb by lia.
        exists b. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hb0 He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (bj & Hbj & Hbjiff).
    (* the load's own side conditions, off the readable run *)
    destruct (uk_rd_byte π M s (len + 1) (s + 1 + j)
                (mword_of_int (s + 1 + j)) Hrd ltac:(lia) eq_refl)
      as (Huva & Hokj & Hcanonj & _).
    assert (Hbyte : M !! (uint (mword_of_int (s + 1 + j) : mword 64)) = Some bj)
      by (rewrite Huva; exact Hbj).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0xee  c.mv a3,a5 ---- *)
    assert (Hmv : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec zero_reg (mE !!! Regidx a5_idx))
      by (rewrite Ha5; rewrite moi_add_zero_l; reflexivity).
    iApply (wp_uk_cmv C pt Rut π sz Hlo Hpm M mE (mword_of_int 0xee)
              a3_idx a5_idx (mword_of_int (s + 1 + j))
              (UI ui_echo_ee M Htext Hx)
              ltac:(vm_compute; discriminate) Hmv
              with "Hb").
    set (mL1 := <[Regidx a3_idx
                  := regval_into_reg (mword_of_int (s + 1 + j) : mword 64)]> mE).
    assert (Eee : add_vec_int (mword_of_int 0xee : mword 64) 2 = mword_of_int 0xf0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eee.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0xf0  c.addi a5,a5,1 ---- *)
    assert (Ha5_1 : mL1 !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64)).
    { exact (eq_trans
               (upd_ne mE (Regidx a3_idx) (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))
                  ltac:(vm_compute; discriminate)) Ha5). }
    assert (Hadd : (mword_of_int (s + 2 + j) : mword 64)
                   = add_vec (mL1 !!! Regidx a5_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
    { rewrite Ha5_1.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                    : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite moi_add. f_equal; lia. }
    iApply (wp_uk_caddi C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M mL1 (mword_of_int 0xf0)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int (s + 2 + j))
              (UI ui_echo_f0 M Htext Hx)
              ltac:(vm_compute; discriminate) Hadd
              with "Hb").
    set (mL2 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (s + 2 + j) : mword 64)]> mL1).
    assert (Ef0 : add_vec_int (mword_of_int 0xf0 : mword 64) 2 = mword_of_int 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef0.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0xf2  lbu a4,-1(a5) ---- *)
    assert (Ha5_2 : mL2 !!! Regidx a5_idx = (mword_of_int (s + 2 + j) : mword 64))
      by exact (upd_eq mL1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))).
    assert (Hva : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec (mL2 !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 4095 : mword 12))).
    { rewrite Ha5_2.
      assert (Hc : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite moi_add. f_equal; lia. }
    assert (Hwvj : (mword_of_int (bv_unsigned bj) : mword 64)
                   = zero_extend' 64 (bj : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uk_lbu C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M mL2 (mword_of_int 0xf2)
              (mword_of_int 4095 : mword 12) a5_idx a4_idx
              (mword_of_int (s + 1 + j)) (mword_of_int (bv_unsigned bj)) bj
              (UI ui_echo_f2 M Htext Hx)
              ltac:(vm_compute; discriminate) Hva Hokj Hcanonj Hbyte Hwvj
              with "Hb").
    set (mL3 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)]> mL2).
    assert (Ef2 : add_vec_int (mword_of_int 0xf2 : mword 64) 4 = mword_of_int 0xf6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef2.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    assert (Ha4 : mL3 !!! Regidx a4_idx = (mword_of_int (bv_unsigned bj) : mword 64))
      by exact (upd_eq mL2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))).
    (* what the iteration leaves of the OTHER registers *)
    assert (Hpres : forall r : mword 5,
              Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> mL3 !!! Regidx r = mE !!! Regidx r).
    { intros r H3 H4 H5.
      exact (eq_trans
               (upd_ne mL2 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)) H4)
               (eq_trans
                  (upd_ne mL1 (Regidx a5_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 2 + j) : mword 64)) H5)
                  (upd_ne mE (Regidx a3_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 1 + j) : mword 64)) H3))). }
    assert (Htgt : (mword_of_int 0xee : mword 64)
                   = add_vec (mword_of_int 0xf6)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 252 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xf6  c.bnez a4,0xee -- the ONE dichotomy of a string scan ---- *)
    destruct (Z.eq_dec (1 + j) len) as [Hend | Hne].
    - (* the byte is the NUL: fall through to 0xf8 with a3 = s + len *)
      assert (Hz : bv_unsigned bj = 0)
        by (apply uk_bv8_zero; apply Hbjiff; exact Hend).
      assert (Htk : false = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4. rewrite (moi_neq_zero (bv_unsigned bj) (uk_bv8_range bj)).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbnez C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M mL3 (mword_of_int 0xf6)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                false (mword_of_int 0xee)
                (UI ui_echo_f6 M Htext Hx)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (Ef6 : (if false then (mword_of_int 0xee : mword 64)
                     else add_vec_int (mword_of_int 0xf6 : mword 64) 2)
                    = mword_of_int 0xf8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ef6.
      assert (H3 : mL3 !!! Regidx a3_idx = (mword_of_int (s + 1 + j) : mword 64)).
      { exact (eq_trans
                 (upd_ne mL2 (Regidx a4_idx) (Regidx a3_idx)
                    (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne mL1 (Regidx a5_idx) (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))
                       ltac:(vm_compute; discriminate))
                    (upd_eq mE (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))))). }
      iApply ("Hcont" $! mL3 with "[%] [%]").
      + rewrite H3. f_equal; lia.
      + exact Hpres.
    - (* a body byte: take the back edge with j := j + 1 *)
      assert (Hnz : bv_unsigned bj <> 0)
        by (intro Hz; apply Hne; apply Hbjiff; apply uk_bv8_zero; exact Hz).
      assert (Htk : true = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4. rewrite (moi_neq_zero (bv_unsigned bj) (uk_bv8_range bj)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uk_cbnez C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M mL3 (mword_of_int 0xf6)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                true (mword_of_int 0xee)
                (UI ui_echo_f6 M Htext Hx)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      (* the taken pc is the loop head itself -- no normalization needed *)
      assert (Ha5' : mL3 !!! Regidx a5_idx
                     = (mword_of_int (s + 1 + (j + 1)) : mword 64)).
      { rewrite (upd_ne mL2 (Regidx a4_idx) (Regidx a5_idx)
                   (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                   ltac:(vm_compute; discriminate)).
        rewrite Ha5_2. f_equal; lia. }
      rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
      iPoseProof (IH M mL3 s len (j + 1) ltac:(lia) Hx Htext Hstr Hrd
                    ltac:(lia) Ha5') as "HIH".
      iApply ("HIH" $! h4 C4 pt4 Rut4 sz4 with "[%] [%] Hb");
        [ exact Hlo4 | exact Hpm4 | ].
      iIntros (m') "%Hm3 %Hmp".
      iApply ("Hcont" $! m' with "[%] [%]").
      + exact Hm3.
      + intros r H3 H4 H5. rewrite (Hmp r H3 H4 H5). exact (Hpres r H3 H4 H5).
  Qed.

  (* strlen @0xdc -- the whole function.  The two arms of the entry test
     differ only in HOW a0 gets the answer (c.li 0 vs subw); the test's
     dichotomy is [ucstr]'s, byte for byte. *)
  Lemma wp_kecho_strlen (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s len : Z) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack π M sp0 16 ->
    m !!! Regidx a0_idx = (mword_of_int s : mword 64) ->
    ucstr M s len ->
    uk_rd π M s (len + 1) ->
    0 <= len < 2 ^ 31 ->
    uint sp0 <= s ->                          (* the string is above the frame *)
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
        uvb (CID := h) C pt Rut sz π M m (mword_of_int EchoSyms.strlen) -∗
        (∀ (m' : regfile) (M' : gmap Z (bv 8)),
           ⌜ucallee_saved m m'⌝ -∗
           ⌜m' !!! Regidx a0_idx = (mword_of_int len : mword 64)⌝ -∗
           ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
           ukc π M' m' (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hsp Hst Hs Hstr Hrd Hlen Habove Hret2.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite Hsstrlen.
    change (2 ^ 31) with 2147483648 in Hlen.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo16.
    pose proof (ukrd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (ukrd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    destruct (uk_stack_slot π M sp0 16 8 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot π M sp0 16 0 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0xdc  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut π sz Hlo Hpm M m (mword_of_int 0xdc)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16))
              (UI ui_echo_dc M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (Edc : add_vec_int (mword_of_int 0xdc : mword 64) 2 = mword_of_int 0xde)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Edc.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0xde  c.sdsp ra,8(sp) ---- *)
    assert (Htg8 : add_vec_int (add_vec_int sp0 (-16)) 8
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0xde)
              (mword_of_int 1 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx)
              (UI ui_echo_de M Htext Hx)
              Htg8 Hwra Hw8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hb").
    rewrite Hu8'.
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext1 : echo_text_sub M1)
      by (unfold M1; apply echo_text_sub_store8; [ exact Htext | lia ]).
    assert (Ede : add_vec_int (mword_of_int 0xde : mword 64) 2 = mword_of_int 0xe0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ede.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0xe0  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M1 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb). unfold M1.
      exact (uM_store8_is_Some _ _ _ _ (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx s0_idx)
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M1 m1 (mword_of_int 0xe0)
              (mword_of_int 0 : mword 6) s0_idx
              (add_vec_int (add_vec_int sp0 (-16)) 0) (m !!! Regidx s0_idx)
              (UI ui_echo_e0 M1 Htext1 Hx)
              Htg0 Hws0 Hw0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hb").
    rewrite Hu0'.
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Htext2 : echo_text_sub M2)
      by (unfold M2; apply echo_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Ee0 : add_vec_int (mword_of_int 0xe0 : mword 64) 2 = mword_of_int 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee0.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* THE image postcondition, and the two transports it powers.  Both the
       string and its window live AT OR ABOVE the entry sp, and the frame is
       strictly below it, so one byte-equation carries them. *)
    assert (Heq2 : forall k : Z, uint sp0 <= k -> M2 !! k = M !! k).
    { intros k Hk. unfold M2.
      rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                 ltac:(intros i Hi; pose proof (Nat2Z.is_nonneg i); lia)).
      unfold M1.
      exact (uM_store8_lookup_ne M (uint sp0 - 8) (m !!! Regidx ra_idx) k
               ltac:(intros i Hi; pose proof (Nat2Z.is_nonneg i); lia)). }
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(intros i Hi; pose proof (Nat2Z.is_nonneg i); lia)).
        unfold M1.
        exact (uM_store8_lookup_ne M (uint sp0 - 8) (m !!! Regidx ra_idx) k
                 ltac:(intros i Hi; pose proof (Nat2Z.is_nonneg i); lia)). }
    assert (Hstr2 : ucstr M2 s len)
      by exact (ucstr_above M M2 s len (uint sp0) Heq2 Habove Hstr).
    assert (Hrd2 : uk_rd π M2 s (len + 1))
      by exact (uk_rd_above π M M2 s (len + 1) (uint sp0) Heq2 Habove Hrd).
    (* ---- 0xe2  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M2 m1 (mword_of_int 0xe2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              s0_idx (add_vec_int (add_vec_int sp0 (-16)) 16)
              (UI ui_echo_e2 M2 Htext2 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (Ee2 : add_vec_int (mword_of_int 0xe2 : mword 64) 2 = mword_of_int 0xe4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee2.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0xe4  lbu a5,0(a0) -- the first byte of the string ---- *)
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx)
                  (regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m (Regidx sp_idx) (Regidx a0_idx)
                     (regval_into_reg (add_vec_int sp0 (-16)))
                     ltac:(vm_compute; discriminate))
                  Hs)). }
    assert (Hvas : (mword_of_int s : mword 64)
                   = add_vec (m2 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha0_2.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. rewrite moi_add. f_equal; lia. }
    destruct (uk_rd_byte π M2 s (len + 1) s (mword_of_int s) Hrd2
                ltac:(lia) eq_refl)
      as (Huvas & Hokes & Hcanons & _).
    assert (Hbex : exists b0 : bv 8, M2 !! s = Some b0 /\ (b0 = ubyte0 <-> len = 0)).
    { destruct (Z.eq_dec len 0) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr2) as Hnul.
        replace (s + len) with s in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr2 0 ltac:(lia)) as (b & Hb & Hbz).
        replace (s + 0) with s in Hb by lia.
        exists b. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hbz He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (b0 & Hb0e & Hb0iff).
    assert (Hbytes : M2 !! (uint (mword_of_int s : mword 64)) = Some b0)
      by (rewrite Huvas; exact Hb0e).
    assert (Hwv0 : (mword_of_int (bv_unsigned b0) : mword 64)
                   = zero_extend' 64 (b0 : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uk_lbu C4 pt4 Rut4 π sz4 Hlo4 Hpm4 M2 m2 (mword_of_int 0xe4)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              (mword_of_int s) (mword_of_int (bv_unsigned b0)) b0
              (UI ui_echo_e4 M2 Htext2 Hx)
              ltac:(vm_compute; discriminate) Hvas Hokes Hcanons Hbytes Hwv0
              with "Hb").
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> m2).
    assert (Ee4 : add_vec_int (mword_of_int 0xe4 : mword 64) 4 = mword_of_int 0xe8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ee4.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq m2 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))
                  ltac:(vm_compute; discriminate))
               Ha0_2). }
    assert (Hsp3 : m3 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m1 (Regidx s0_idx) (Regidx sp_idx)
                     (regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16))
                     ltac:(vm_compute; discriminate))
                  (upd_eq m (Regidx sp_idx)
                     (regval_into_reg (add_vec_int sp0 (-16)))))). }
    (* what the PROLOGUE left of every register the epilogue does not restore *)
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx a5_idx -> m3 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0 Na5.
      exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)) Na5)
               (eq_trans
                  (upd_ne m1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)) Ns0)
                  (upd_ne m (Regidx sp_idx) (Regidx r)
                     (regval_into_reg (add_vec_int sp0 (-16))) Nsp))). }
    assert (Htgt104 : (mword_of_int 0x104 : mword 64)
                      = add_vec (mword_of_int 0xe8)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 14 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xe8  c.beqz a5,0x104 ---- *)
    destruct (Z.eq_dec len 0) as [Hlz | Hlne].
    - (* THE EMPTY STRING: a0 := 0 at 0x104, then jump to the epilogue *)
      subst len.
      assert (Hz : bv_unsigned b0 = 0)
        by (apply uk_bv8_zero; apply Hb0iff; reflexivity).
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3. rewrite (moi_eq_zero (bv_unsigned b0) (uk_bv8_range b0)).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbeqz C5 pt5 Rut5 π sz5 Hlo5 Hpm5 M2 m3 (mword_of_int 0xe8)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                true (mword_of_int 0x104)
                (UI ui_echo_e8 M2 Htext2 Hx)
                ltac:(vm_compute; reflexivity) Htk Htgt104
                ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
      (* ---- 0x104  c.li a0,0 ---- *)
      assert (Hwa0 : (mword_of_int 0 : mword 64)
                     = add_vec zero_reg
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cli C6 pt6 Rut6 π sz6 Hlo6 Hpm6 M2 m3 (mword_of_int 0x104)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (UI ui_echo_104 M2 Htext2 Hx)
                ltac:(vm_compute; discriminate) Hwa0
                with "Hb").
      set (m4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m3).
      assert (E104 : add_vec_int (mword_of_int 0x104 : mword 64) 2 = mword_of_int 0x106)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E104.
      rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
      (* ---- 0x106  c.j 0xfc ---- *)
      assert (Htj : (mword_of_int 0xfc : mword 64)
                    = add_vec (mword_of_int 0x106)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cj C7 pt7 Rut7 π sz7 Hlo7 Hpm7 M2 m4 (mword_of_int 0x106)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xfc)
                (UI ui_echo_106 M2 Htext2 Hx)
                Htj ltac:(vm_compute; reflexivity)
                with "Hb").
      (* ---- the epilogue ---- *)
      assert (Hsp4 : m4 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
      { exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx sp_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))
                    ltac:(vm_compute; discriminate)) Hsp3). }
      rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
      iPoseProof (wp_kecho_strlen_epi M m4 sp0
                    (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                    Hx Htext Hst Hret2 Hsp4) as "Hepi".
      iApply ("Hepi" $! h8 C8 pt8 Rut8 sz8 with "[%] [%] Hb");
        [ exact Hlo8 | exact Hpm8 | ].
      iIntros (m') "%HA %HB %HC".
      iApply ("Hcont" $! m' M2 with "[%] [%] [%]").
      + intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp. rewrite HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx r)
                    (regval_into_reg (mword_of_int 0 : mword 64)) Na0)
                 (Hpre r Nsp Ns0 Na5)).
      + rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg (mword_of_int 0 : mword 64))).
      + exact Honly.
    - (* A NON-EMPTY STRING: a5 := s+1, scan, then subw ---- *)
      assert (Hnz : bv_unsigned b0 <> 0)
        by (intro Hz; apply Hlne; apply Hb0iff; apply uk_bv8_zero; exact Hz).
      assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3. rewrite (moi_eq_zero (bv_unsigned b0) (uk_bv8_range b0)).
        symmetry. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uk_cbeqz C5 pt5 Rut5 π sz5 Hlo5 Hpm5 M2 m3 (mword_of_int 0xe8)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                false (mword_of_int 0x104)
                (UI ui_echo_e8 M2 Htext2 Hx)
                ltac:(vm_compute; reflexivity) Htk Htgt104
                ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (Ee8 : (if false then (mword_of_int 0x104 : mword 64)
                     else add_vec_int (mword_of_int 0xe8 : mword 64) 2)
                    = mword_of_int 0xea)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ee8.
      rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
      (* ---- 0xea  addi a5,a0,1 ---- *)
      assert (Hadd1 : (mword_of_int (s + 1) : mword 64)
                      = add_vec (m3 !!! Regidx a0_idx)
                          (sign_extend' 64 (mword_of_int 1 : mword 12))).
      { rewrite Ha0_3.
        assert (Hc : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc. rewrite moi_add. reflexivity. }
      iApply (wp_uk_addi C6 pt6 Rut6 π sz6 Hlo6 Hpm6 M2 m3 (mword_of_int 0xea)
                (mword_of_int 1 : mword 12) a0_idx a5_idx (mword_of_int (s + 1))
                (UI ui_echo_ea M2 Htext2 Hx)
                ltac:(vm_compute; discriminate) Hadd1
                with "Hb").
      set (m4 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (s + 1) : mword 64)]> m3).
      assert (Eea : add_vec_int (mword_of_int 0xea : mword 64) 4 = mword_of_int 0xee)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eea.
      (* ---- 0xee..0xf6  the scan loop ---- *)
      assert (Ha5_4 : m4 !!! Regidx a5_idx = (mword_of_int (s + 1 + 0) : mword 64)).
      { replace (s + 1 + 0) with (s + 1) by lia.
        exact (upd_eq m3 (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (s + 1) : mword 64))). }
      rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
      iPoseProof (wp_kecho_strlen_loop (S (Z.to_nat (len - 1))) M2 m4 s len 0
                    ltac:(lia) Hx Htext2 Hstr2 Hrd2 ltac:(lia) Ha5_4) as "Hscan".
      iApply ("Hscan" $! h7 C7 pt7 Rut7 sz7 with "[%] [%] Hb");
        [ exact Hlo7 | exact Hpm7 | ].
      iIntros (m5) "%Ha3_5 %Hpres5".
      (* ---- 0xf8  subw a0,a3,a0 ---- *)
      assert (Ha0_5 : m5 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
      { rewrite (Hpres5 a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx a0_idx)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64))
                    ltac:(vm_compute; discriminate)) Ha0_3). }
      assert (Hsub : (mword_of_int len : mword 64)
                     = sign_extend' 64
                         (sub_vec (subrange_vec_dec (m5 !!! Regidx a3_idx) 31 0
                                   : mword 32)
                                  (subrange_vec_dec (m5 !!! Regidx a0_idx) 31 0
                                   : mword 32))).
      { rewrite Ha3_5. rewrite Ha0_5.
        rewrite (moi_subw (s + len) s ltac:(unfold Z31; lia)).
        f_equal; lia. }
      rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
      iApply (wp_uk_subw C8 pt8 Rut8 π sz8 Hlo8 Hpm8 M2 m5 (mword_of_int 0xf8)
                a3_idx a0_idx a0_idx (mword_of_int len)
                (UI ui_echo_f8 M2 Htext2 Hx)
                ltac:(vm_compute; discriminate) Hsub
                with "Hb").
      set (m6 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int len : mword 64)]> m5).
      assert (Ef8 : add_vec_int (mword_of_int 0xf8 : mword 64) 4 = mword_of_int 0xfc)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ef8.
      (* ---- the epilogue ---- *)
      assert (Hsp6 : m6 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
      { rewrite (upd_ne m5 (Regidx a0_idx) (Regidx sp_idx)
                   (regval_into_reg (mword_of_int len : mword 64))
                   ltac:(vm_compute; discriminate)).
        rewrite (Hpres5 sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx sp_idx)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64))
                    ltac:(vm_compute; discriminate)) Hsp3). }
      rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
      iPoseProof (wp_kecho_strlen_epi M m6 sp0
                    (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                    Hx Htext Hst Hret2 Hsp6) as "Hepi".
      iApply ("Hepi" $! h9 C9 pt9 Rut9 sz9 with "[%] [%] Hb");
        [ exact Hlo9 | exact Hpm9 | ].
      iIntros (m') "%HA %HB %HC".
      iApply ("Hcont" $! m' M2 with "[%] [%] [%]").
      + intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp. rewrite HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na3 : Regidx r <> Regidx a3_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na4 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        rewrite (upd_ne m5 (Regidx a0_idx) (Regidx r)
                   (regval_into_reg (mword_of_int len : mword 64)) Na0).
        rewrite (Hpres5 r Na3 Na4 Na5).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx r)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64)) Na5)
                 (Hpre r Nsp Ns0 Na5)).
      + rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m5 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int len : mword 64))).
      + exact Honly.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4 main @0x0 -- the eight-register prologue, the argc guard, the argv *)
  (* index chain, and the loop.  DIVERGES (it ends in exit).               *)
  (* ------------------------------------------------------------------- *)

  (* the two image transports the prologue and the calls need, on the key *)
  Local Lemma uk_stack_only (Ma Mb : gmap Z (bv 8)) (sp0 : mword 64) (n a k : Z) :
    uM_only Ma Mb a k -> uk_stack π Ma sp0 n -> uk_stack π Mb sp0 n.
  Proof. intros [Hd _] H. exact (uk_stack_dom π Ma Mb sp0 n Hd H). Qed.

  Local Lemma uk_args_only (Ma Mb : gmap Z (bv 8)) (av argc lo a k : Z)
      (alen : Z -> Z) :
    uM_only Ma Mb a k -> a + k <= lo ->
    uk_args π Ma av argc lo alen -> uk_args π Mb av argc lo alen.
  Proof.
    intros [_ He] Hk H.
    apply (uk_args_above π Ma Mb av argc lo alen); [ | exact H ].
    intros j Hj. apply He. right. lia.
  Qed.

  (* THE PROLOGUE STORE, once.  main spills eight registers and start two,
     all by [c.sdsp rs2, d(sp)] into a slot of the budget the function just
     carved; the only things that vary are the pc, the register, the offset
     and the budget's size. *)
  Local Lemma kecho_pro_store (M : gmap Z (bv 8)) (m : regfile)
      (sp0 pc : mword 64) (uimm : mword 6) (rs2 : mword 5) (n d : Z) :
    uk_instr π M pc true (C_SDSP (uimm, Regidx rs2)) ->
    uk_stack π M sp0 n ->
    0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- n) ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
        uvb (CID := h) C pt Rut sz π M m pc -∗
        ukc π (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m
          (add_vec_int pc 2) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hui HS Hd0 Hdn Hd8 Hsp Himm.
    destruct (uk_stack_slot π M sp0 n d HS Hd0 Hdn Hd8)
      as (Hu & Hw & Hcanon & Hpg & Hal & Hb).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    iApply (wp_uk_csdsp C pt Rut π sz Hlo Hpm M m pc uimm rs2
              (add_vec_int (add_vec_int sp0 (- n)) d) (m !!! Regidx rs2)
              Hui
              ltac:(rewrite Hsp; rewrite Himm; reflexivity)
              eq_refl Hw Hcanon Hpg Hal Hb
              with "Hb").
    rewrite Hu. iExact "Hcont".
  Qed.

  (* THE EXIT TAIL @0x76: c.li a0,0; jal exit.  Reached from the argc <= 1
     arm of main's guard and from the newline path at the end of the loop --
     and from nowhere else. *)
  Local Lemma kecho_exit_tail (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    ⊢ ukc π M m (mword_of_int 0x76).
  Proof.
    intros Hx Htext.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x76  c.li a0,0 ---- *)
    assert (Hw0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut π sz Hlo Hpm M m (mword_of_int 0x76)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (UI ui_echo_76 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw0
              with "Hb").
    set (m1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 2 = mword_of_int 0x78)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x78  jal ra,0x332 <exit> -- diverges ---- *)
    assert (Htj : (mword_of_int EchoSyms.exit : mword 64)
                  = add_vec (mword_of_int 0x78)
                      (sign_extend' 64 (mword_of_int 698 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x7c : mword 64)
                  = add_vec_int (mword_of_int 0x78 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x78)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int EchoSyms.exit) (mword_of_int 0x7c)
              (UI ui_echo_78 M Htext Hx)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hb").
    iApply (wp_kecho_exit_stub M _ Hx Htext).
  Qed.

  (* THE ARGV LOOP @0x4e -- an ORDINARY Rocq induction on the nat measure
     [k] bounding [argc - 1 - i], NOT an [iLöb]: the loop is BOUNDED and
     every leaf it uses is later-free.  The loop DIVERGES (it ends in exit),
     so it has no continuation.

       4e  ld s2,0(s1)   52  c.mv a0,s2   54  jal strlen
       58  c.mv a2,a0    5a  c.mv a1,s2   5c  c.mv a0,s3   5e  jal write
       62  bne s1,s5,0x3e
        taken   3e c.mv a2,s3; 40 c.mv a1,s6; 42 c.mv a0,s3; 44 jal write
                48 c.addi s1,s1,8; 4a beq s1,s4,0x76 (never taken); -> 4e
        else    66 c.li a2,1; 68 auipc a1,1; 6c addi a1,a1,-1840
                70 c.mv a0,a2; 72 jal write; -> the exit tail

     The IMAGE moves only inside strlen's frame -- write's row is the quiet
     one -- so [uk_args] and [uk_stack] cross each iteration by
     [uk_args_only] / [uk_stack_only] and the induction is on the register
     file alone. *)
  Local Lemma kecho_loop (sp0 : mword 64) (argc av : Z) (alen : Z -> Z) (k : nat) :
    forall (Mc : gmap Z (bv 8)) (mc : regfile) (i : Z),
      uk_xpage π (mword_of_int 0) ->
      echo_text_sub Mc ->
      uk_args π Mc av argc (uint sp0) alen ->
      uk_stack π Mc sp0 80 ->
      1 <= i <= argc - 1 ->
      argc - 1 - i < Z.of_nat k ->
      mc !!! Regidx (mword_of_int 9 : mword 5)
        = (mword_of_int (av + 8 * i) : mword 64) ->
      mc !!! Regidx (mword_of_int 21 : mword 5)
        = (mword_of_int (av + 8 * (argc - 1)) : mword 64) ->
      mc !!! Regidx (mword_of_int 20 : mword 5)
        = (mword_of_int (av + 8 * argc) : mword 64) ->
      mc !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 1 : mword 64) ->
      mc !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 2352 : mword 64) ->
      mc !!! Regidx sp_idx = add_vec_int sp0 (-64) ->
      ⊢ ukc π Mc mc (mword_of_int 0x4e).
  Proof.
    induction k as [ | k IH ];
      intros Mc mc i Hx Htext Hargs Hst Hi Hk Hr9 Hr21 Hr20 Hr19 Hr22 Hrsp.
    { (* k = 0 is vacuous: the measure is STRICTLY below it *)
      exfalso. lia. }
    assert (Hk' : argc - 1 - i <= Z.of_nat k)
      by (rewrite Nat2Z.inj_succ in Hk; lia).
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    pose proof (uka_argc _ _ _ _ _ _ Hargs) as Hargcb.
    change (2 ^ 31) with 2147483648 in Hargcb.
    pose proof (uka_rd _ _ _ _ _ _ Hargs) as Hrdav.
    pose proof (ukrd_lo _ _ _ _ Hrdav) as Hav0.
    pose proof (ukrd_hi _ _ _ _ Hrdav) as Havhi.
    change (2 ^ 38) with 274877906944 in Havhi.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo80.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan80.
    change (2 ^ 38) with 274877906944 in Hcan80.
    (* the post-prologue sp, as a number.  NOTE that [uint] is NOT rewritten
       away in the hypotheses: every other bound in this proof is stated at
       [uint sp0], and [lia] would see the two spellings as two atoms. *)
    assert (Hbu : bv_unsigned sp0 = uint sp0)
      by (rewrite uint_unsigned; reflexivity).
    assert (Hu64 : uint (add_vec_int sp0 (-64)) = uint sp0 - 64).
    { rewrite uint_unsigned.
      rewrite (uv_avi_neg sp0 64 ltac:(lia) ltac:(rewrite Hbu; lia)).
      rewrite Hbu. reflexivity. }
    (* strlen's 16-byte slice, at main's post-prologue sp *)
    destruct (uk_stack_split π Mc sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    (* the argv entry at index i, and its string *)
    destruct (uk_args_str π Mc av argc (uint sp0) alen i Hargs ltac:(lia))
      as (Hplo & Hlenb & Hstrp & Hrdp).
    change (2 ^ 31) with 2147483648 in Hlenb.
    destruct (uk_args_slot π Mc av argc (uint sp0) alen i
                (mword_of_int (av + 8 * i)) Hargs ltac:(lia) eq_refl)
      as (Huva & Hokva & Hcanva & Hpgva & Halva & Hbva & Hwva).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x4e  ld s2,0(s1) -- s2 := argv[i] ---- *)
    assert (Hvai : (mword_of_int (av + 8 * i) : mword 64)
                   = add_vec (mc !!! Regidx (mword_of_int 9 : mword 5))
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hr9.
      assert (E0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite E0 moi_add. f_equal; lia. }
    iApply (wp_uk_ld C pt Rut π sz Hlo Hpm Mc mc (mword_of_int 0x4e)
              (mword_of_int 0 : mword 12) (mword_of_int 9 : mword 5)
              (mword_of_int 18 : mword 5)
              (mword_of_int (av + 8 * i)) (uk_argv_w Mc av i)
              (UI ui_echo_4e Mc Htext Hx)
              ltac:(vm_compute; discriminate) Hvai
              Hokva Hcanva Hpgva Halva Hbva Hwva
              with "Hb").
    set (n1 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (uk_argv_w Mc av i)]> mc).
    assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 4 = mword_of_int 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x52  c.mv a0,s2 ---- *)
    assert (Hs2_1 : n1 !!! Regidx (mword_of_int 18 : mword 5) = uk_argv_w Mc av i)
      by (apply upd_eq_tr; reflexivity).
    iApply (wp_uk_cmv C1 pt1 Rut1 π sz1 Hlo1 Hpm1 Mc n1 (mword_of_int 0x52)
              (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              (uk_argv_w Mc av i)
              (UI ui_echo_52 Mc Htext Hx)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_1 -uk_argv_p_w moi_add_zero_l uk_argv_p_w;
                    reflexivity)
              with "Hb").
    set (n2 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (uk_argv_w Mc av i)]> n1).
    assert (E52 : add_vec_int (mword_of_int 0x52 : mword 64) 2 = mword_of_int 0x54)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x54  jal ra,0xdc <strlen> ---- *)
    assert (Htj1 : (mword_of_int EchoSyms.strlen : mword 64)
                   = add_vec (mword_of_int 0x54)
                       (sign_extend' 64 (mword_of_int 136 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj1 : (mword_of_int 0x58 : mword 64)
                   = add_vec_int (mword_of_int 0x54 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C2 pt2 Rut2 π sz2 Hlo2 Hpm2 Mc n2 (mword_of_int 0x54)
              (mword_of_int 136 : mword 21) ra_idx
              (mword_of_int EchoSyms.strlen) (mword_of_int 0x58)
              (UI ui_echo_54 Mc Htext Hx)
              ltac:(vm_compute; discriminate) Htj1 Hwj1
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x58 : mword 64)]> n2).
    (* ---- the call: strlen(argv[i]) ---- *)
    assert (Hsp_3 : n3 !!! Regidx sp_idx = add_vec_int sp0 (-64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hrsp. }
    assert (Ha0_3 : n3 !!! Regidx a0_idx
                    = (mword_of_int (uk_argv_p Mc av i) : mword 64)).
    { rewrite uk_argv_p_w. rewrite /n3.
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /n2. apply upd_eq_tr; reflexivity. }
    assert (Hra_3 : n3 !!! Regidx ra_idx = (mword_of_int 0x58 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    iPoseProof (wp_kecho_strlen Mc n3 (add_vec_int sp0 (-64))
                  (uk_argv_p Mc av i) (alen i)
                  Hx Htext Hsp_3 Hstm Ha0_3 Hstrp Hrdp
                  ltac:(change (2 ^ 31) with 2147483648; lia)
                  ltac:(rewrite Hu64; lia)
                  ltac:(rewrite Hra_3; vm_compute; reflexivity)) as "Hstrlen".
    iApply ("Hstrlen" $! h3 C3 pt3 Rut3 sz3 with "[%] [%] Hb");
      [ exact Hlo3 | exact Hpm3 | ].
    iIntros (mp Mp) "%Hcs0 %Hpa0 %Hponly".
    rewrite Hra_3.
    rewrite Hu64 in Hponly.
    replace (uint sp0 - 64 - 16) with (uint sp0 - 80) in Hponly by lia.
    (* every image predicate, carried across strlen's frame in one step *)
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 80)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    assert (HtP : echo_text_sub Mp)
      by exact (uM_only_img EchoInstrs.echo_bytes Mc Mp (uint sp0 - 80) 16
                  HkT Hponly Htext).
    assert (HstP : uk_stack π Mp sp0 80)
      by exact (uk_stack_only Mc Mp sp0 80 (uint sp0 - 80) 16 Hponly Hst).
    assert (HargsP : uk_args π Mp av argc (uint sp0) alen)
      by exact (uk_args_only Mc Mp av argc (uint sp0) (uint sp0 - 80) 16 alen
                  Hponly ltac:(lia) Hargs).
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x58  c.mv a2,a0 ---- *)
    iApply (wp_uk_cmv C4 pt4 Rut4 π sz4 Hlo4 Hpm4 Mp mp (mword_of_int 0x58)
              (mword_of_int 12 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int (alen i) : mword 64)
              (UI ui_echo_58 Mp HtP Hx)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hpa0 moi_add_zero_l; reflexivity)
              with "Hb").
    set (n4 := <[Regidx (mword_of_int 12 : mword 5)
                 := regval_into_reg (mword_of_int (alen i) : mword 64)]> mp).
    assert (E58 : add_vec_int (mword_of_int 0x58 : mword 64) 2 = mword_of_int 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x5a  c.mv a1,s2 (s2 survived the call: it is callee-saved) ---- *)
    assert (Hs2_P : mp !!! Regidx (mword_of_int 18 : mword 5) = uk_argv_w Mc av i).
    { rewrite (Hcs0 (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n3 /n2.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hs2_1. }
    assert (Hs2_4 : n4 !!! Regidx (mword_of_int 18 : mword 5) = uk_argv_w Mc av i).
    { rewrite /n4. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hs2_P. }
    iApply (wp_uk_cmv C5 pt5 Rut5 π sz5 Hlo5 Hpm5 Mp n4 (mword_of_int 0x5a)
              (mword_of_int 11 : mword 5) (mword_of_int 18 : mword 5)
              (uk_argv_w Mc av i)
              (UI ui_echo_5a Mp HtP Hx)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_4 -uk_argv_p_w moi_add_zero_l uk_argv_p_w;
                    reflexivity)
              with "Hb").
    set (n5 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (uk_argv_w Mc av i)]> n4).
    assert (E5a : add_vec_int (mword_of_int 0x5a : mword 64) 2 = mword_of_int 0x5c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5a.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x5c  c.mv a0,s3 ---- *)
    assert (Hs3_5 : n5 !!! Regidx (mword_of_int 19 : mword 5)
                    = (mword_of_int 1 : mword 64)).
    { rewrite /n5 /n4.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      rewrite (Hcs0 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hr19. }
    iApply (wp_uk_cmv C6 pt6 Rut6 π sz6 Hlo6 Hpm6 Mp n5 (mword_of_int 0x5c)
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
              (mword_of_int 1 : mword 64)
              (UI ui_echo_5c Mp HtP Hx)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_5 moi_add_zero_l; reflexivity)
              with "Hb").
    set (n6 := <[Regidx (mword_of_int 10 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> n5).
    assert (E5c : add_vec_int (mword_of_int 0x5c : mword 64) 2 = mword_of_int 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5c.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x5e  jal ra,0x352 <write> ---- *)
    assert (Htj2 : (mword_of_int EchoSyms.write : mword 64)
                   = add_vec (mword_of_int 0x5e)
                       (sign_extend' 64 (mword_of_int 756 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj2 : (mword_of_int 0x62 : mword 64)
                   = add_vec_int (mword_of_int 0x5e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C7 pt7 Rut7 π sz7 Hlo7 Hpm7 Mp n6 (mword_of_int 0x5e)
              (mword_of_int 756 : mword 21) ra_idx
              (mword_of_int EchoSyms.write) (mword_of_int 0x62)
              (UI ui_echo_5e Mp HtP Hx)
              ltac:(vm_compute; discriminate) Htj2 Hwj2
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (n7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x62 : mword 64)]> n6).
    (* ---- the call: write(1, argv[i], strlen(argv[i])) ---- *)
    assert (Hra_7 : n7 !!! Regidx ra_idx = (mword_of_int 0x62 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    iPoseProof (wp_kecho_write_stub Mp n7 Hx HtP
                  ltac:(rewrite Hra_7; vm_compute; reflexivity)) as "Hwrite".
    iApply ("Hwrite" $! h8 C8 pt8 Rut8 sz8 with "[%] [%] Hb");
      [ exact Hlo8 | exact Hpm8 | ].
    iIntros (ret1).
    rewrite Hra_7.
    set (n8 := <[Regidx a0_idx := ret1]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n7)).
    (* the callee-saved set survived BOTH the call and the clobbers around it *)
    assert (Hcsa : ucallee_saved n1 n2)
      by (rewrite /n2; apply ucs_caller; vm_compute; reflexivity).
    assert (Hcsb : ucallee_saved n1 n3).
    { apply (ucallee_saved_trans n1 n2 n3 Hcsa).
      rewrite /n3. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsc : ucallee_saved n1 mp)
      by exact (ucallee_saved_trans n1 n3 mp Hcsb Hcs0).
    assert (Hcsd : ucallee_saved n1 n4).
    { apply (ucallee_saved_trans n1 mp n4 Hcsc).
      rewrite /n4. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcse : ucallee_saved n1 n5).
    { apply (ucallee_saved_trans n1 n4 n5 Hcsd).
      rewrite /n5. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsf : ucallee_saved n1 n6).
    { apply (ucallee_saved_trans n1 n5 n6 Hcse).
      rewrite /n6. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsg : ucallee_saved n1 n7).
    { apply (ucallee_saved_trans n1 n6 n7 Hcsf).
      rewrite /n7. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hcsh : ucallee_saved n1 n8).
    { apply (ucallee_saved_trans n1 n7 n8 Hcsg).
      apply (ucallee_saved_trans n7
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n7) n8).
      - apply ucs_caller; vm_compute; reflexivity.
      - rewrite /n8. apply ucs_caller; vm_compute; reflexivity. }
    assert (Hs1_8 : n8 !!! Regidx (mword_of_int 9 : mword 5)
                    = (mword_of_int (av + 8 * i) : mword 64)).
    { rewrite (Hcsh (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr9. }
    assert (Hs5_8 : n8 !!! Regidx (mword_of_int 21 : mword 5)
                    = (mword_of_int (av + 8 * (argc - 1)) : mword 64)).
    { rewrite (Hcsh (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr21. }
    assert (Hs4_8 : n8 !!! Regidx (mword_of_int 20 : mword 5)
                    = (mword_of_int (av + 8 * argc) : mword 64)).
    { rewrite (Hcsh (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr20. }
    assert (Hs3_8 : n8 !!! Regidx (mword_of_int 19 : mword 5)
                    = (mword_of_int 1 : mword 64)).
    { rewrite (Hcsh (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr19. }
    assert (Hs6_8 : n8 !!! Regidx (mword_of_int 22 : mword 5)
                    = (mword_of_int 2352 : mword 64)).
    { rewrite (Hcsh (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hr22. }
    assert (Hsp_8 : n8 !!! Regidx sp_idx = add_vec_int sp0 (-64)).
    { rewrite (Hcsh (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /n1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hrsp. }
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x62  bne s1,s5,0x3e -- separator or newline? ---- *)
    assert (Etgt3e : (mword_of_int 0x3e : mword 64)
                     = add_vec (mword_of_int 0x62)
                         (sign_extend' 64 (mword_of_int 8156 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec i (argc - 1)) as [Hieq | Hine].
    - (* i = argc-1: the last argument -- newline, then exit *)
      iApply (wp_uk_btype C9 pt9 Rut9 π sz9 Hlo9 Hpm9 Mp n8 (mword_of_int 0x62)
                (mword_of_int 8156 : mword 13) (mword_of_int 21 : mword 5)
                (mword_of_int 9 : mword 5) BNE false (mword_of_int 0x3e)
                (UI ui_echo_62 Mp HtP Hx)
                ltac:(cbn [uv_btaken]; rewrite Hs1_8 Hs5_8
                        (moi_neq_vec (av + 8 * i) (av + 8 * (argc - 1))
                           ltac:(unfold Z64; lia) ltac:(unfold Z64; lia))
                        Hieq Z.eqb_refl; reflexivity)
                Etgt3e ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (E62 : (if false then (mword_of_int 0x3e : mword 64)
                     else add_vec_int (mword_of_int 0x62 : mword 64) 4)
                    = mword_of_int 0x66)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E62.
      rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
      (* ---- 0x66  c.li a2,1 ---- *)
      assert (Hw1 : (mword_of_int 1 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cli CA ptA RutA π szA HloA HpmA Mp n8 (mword_of_int 0x66)
                (mword_of_int 1 : mword 6) (mword_of_int 12 : mword 5)
                (mword_of_int 1 : mword 64)
                (UI ui_echo_66 Mp HtP Hx)
                ltac:(vm_compute; discriminate) Hw1
                with "Hb").
      set (q1 := <[Regidx (mword_of_int 12 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> n8).
      assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2 = mword_of_int 0x68)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E66.
      rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
      (* ---- 0x68  auipc a1,0x1 ---- *)
      iApply (wp_uk_auipc CB ptB RutB π szB HloB HpmB Mp q1 (mword_of_int 0x68)
                (mword_of_int 1 : mword 20) (mword_of_int 11 : mword 5)
                (mword_of_int 4200 : mword 64)
                (UI ui_echo_68 Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hb").
      set (q2 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 4200 : mword 64)]> q1).
      assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 4 = mword_of_int 0x6c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E68.
      rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
      (* ---- 0x6c  addi a1,a1,-1840 -- a1 := 0x938, the "\n" literal ---- *)
      assert (Ha1_q2 : q2 !!! Regidx (mword_of_int 11 : mword 5)
                       = (mword_of_int 4200 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uk_addi CC ptC RutC π szC HloC HpmC Mp q2 (mword_of_int 0x6c)
                (mword_of_int 2256 : mword 12) (mword_of_int 11 : mword 5)
                (mword_of_int 11 : mword 5) (mword_of_int 2360 : mword 64)
                (UI ui_echo_6c Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_q2; apply bv_eq; vm_compute; reflexivity)
                with "Hb").
      set (q3 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 2360 : mword 64)]> q2).
      assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 4 = mword_of_int 0x70)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6c.
      rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
      (* ---- 0x70  c.mv a0,a2 ---- *)
      assert (Ha2_q3 : q3 !!! Regidx (mword_of_int 12 : mword 5)
                       = (mword_of_int 1 : mword 64)).
      { rewrite /q3 /q2.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        rewrite /q1. apply upd_eq_tr; reflexivity. }
      iApply (wp_uk_cmv CD ptD RutD π szD HloD HpmD Mp q3 (mword_of_int 0x70)
                (mword_of_int 10 : mword 5) (mword_of_int 12 : mword 5)
                (mword_of_int 1 : mword 64)
                (UI ui_echo_70 Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha2_q3 moi_add_zero_l; reflexivity)
                with "Hb").
      set (q4 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> q3).
      assert (E70 : add_vec_int (mword_of_int 0x70 : mword 64) 2 = mword_of_int 0x72)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E70.
      rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
      (* ---- 0x72  jal ra,0x352 <write> ---- *)
      assert (Htj3 : (mword_of_int EchoSyms.write : mword 64)
                     = add_vec (mword_of_int 0x72)
                         (sign_extend' 64 (mword_of_int 736 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwj3 : (mword_of_int 0x76 : mword 64)
                     = add_vec_int (mword_of_int 0x72 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_jal CE ptE RutE π szE HloE HpmE Mp q4 (mword_of_int 0x72)
                (mword_of_int 736 : mword 21) ra_idx
                (mword_of_int EchoSyms.write) (mword_of_int 0x76)
                (UI ui_echo_72 Mp HtP Hx)
                ltac:(vm_compute; discriminate) Htj3 Hwj3
                ltac:(vm_compute; reflexivity)
                with "Hb").
      set (q5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x76 : mword 64)]> q4).
      assert (Hra_q5 : q5 !!! Regidx ra_idx = (mword_of_int 0x76 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      rewrite /ukc. iIntros (hF CF ptF RutF szF) "%HloF %HpmF Hb".
      iPoseProof (wp_kecho_write_stub Mp q5 Hx HtP
                    ltac:(rewrite Hra_q5; vm_compute; reflexivity)) as "Hw2".
      iApply ("Hw2" $! hF CF ptF RutF szF with "[%] [%] Hb");
        [ exact HloF | exact HpmF | ].
      iIntros (ret2).
      rewrite Hra_q5.
      iApply (kecho_exit_tail Mp _ Hx HtP).
    - (* i < argc-1: the separator, then the next iteration *)
      iApply (wp_uk_btype C9 pt9 Rut9 π sz9 Hlo9 Hpm9 Mp n8 (mword_of_int 0x62)
                (mword_of_int 8156 : mword 13) (mword_of_int 21 : mword 5)
                (mword_of_int 9 : mword 5) BNE true (mword_of_int 0x3e)
                (UI ui_echo_62 Mp HtP Hx)
                ltac:(cbn [uv_btaken]; rewrite Hs1_8 Hs5_8
                        (moi_neq_vec (av + 8 * i) (av + 8 * (argc - 1))
                           ltac:(unfold Z64; lia) ltac:(unfold Z64; lia))
                        (proj2 (Z.eqb_neq (av + 8 * i) (av + 8 * (argc - 1)))
                           ltac:(lia));
                      reflexivity)
                Etgt3e ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      (* [if true then _ else _] reduces by iota, so no pc rewrite is needed *)
      rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
      (* ---- 0x3e  c.mv a2,s3 ---- *)
      iApply (wp_uk_cmv CA ptA RutA π szA HloA HpmA Mp n8 (mword_of_int 0x3e)
                (mword_of_int 12 : mword 5) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (UI ui_echo_3e Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_8 moi_add_zero_l; reflexivity)
                with "Hb").
      set (r1 := <[Regidx (mword_of_int 12 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> n8).
      assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 2 = mword_of_int 0x40)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E3e.
      rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
      (* ---- 0x40  c.mv a1,s6 ---- *)
      assert (Hs6_r1 : r1 !!! Regidx (mword_of_int 22 : mword 5)
                       = (mword_of_int 2352 : mword 64)).
      { rewrite /r1. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Hs6_8. }
      iApply (wp_uk_cmv CB ptB RutB π szB HloB HpmB Mp r1 (mword_of_int 0x40)
                (mword_of_int 11 : mword 5) (mword_of_int 22 : mword 5)
                (mword_of_int 2352 : mword 64)
                (UI ui_echo_40 Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs6_r1 moi_add_zero_l; reflexivity)
                with "Hb").
      set (r2 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (mword_of_int 2352 : mword 64)]> r1).
      assert (E40 : add_vec_int (mword_of_int 0x40 : mword 64) 2 = mword_of_int 0x42)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E40.
      rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
      (* ---- 0x42  c.mv a0,s3 ---- *)
      assert (Hs3_r2 : r2 !!! Regidx (mword_of_int 19 : mword 5)
                       = (mword_of_int 1 : mword 64)).
      { rewrite /r2 /r1.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]). exact Hs3_8. }
      iApply (wp_uk_cmv CC ptC RutC π szC HloC HpmC Mp r2 (mword_of_int 0x42)
                (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (UI ui_echo_42 Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_r2 moi_add_zero_l; reflexivity)
                with "Hb").
      set (r3 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int 1 : mword 64)]> r2).
      assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2 = mword_of_int 0x44)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E42.
      rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
      (* ---- 0x44  jal ra,0x352 <write> ---- *)
      assert (Htj3 : (mword_of_int EchoSyms.write : mword 64)
                     = add_vec (mword_of_int 0x44)
                         (sign_extend' 64 (mword_of_int 782 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwj3 : (mword_of_int 0x48 : mword 64)
                     = add_vec_int (mword_of_int 0x44 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_jal CD ptD RutD π szD HloD HpmD Mp r3 (mword_of_int 0x44)
                (mword_of_int 782 : mword 21) ra_idx
                (mword_of_int EchoSyms.write) (mword_of_int 0x48)
                (UI ui_echo_44 Mp HtP Hx)
                ltac:(vm_compute; discriminate) Htj3 Hwj3
                ltac:(vm_compute; reflexivity)
                with "Hb").
      set (r4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x48 : mword 64)]> r3).
      assert (Hra_r4 : r4 !!! Regidx ra_idx = (mword_of_int 0x48 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
      iPoseProof (wp_kecho_write_stub Mp r4 Hx HtP
                    ltac:(rewrite Hra_r4; vm_compute; reflexivity)) as "Hw2".
      iApply ("Hw2" $! hE CE ptE RutE szE with "[%] [%] Hb");
        [ exact HloE | exact HpmE | ].
      iIntros (ret2).
      rewrite Hra_r4.
      set (r5 := <[Regidx a0_idx := ret2]>
                   (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> r4)).
      assert (Hcs85 : ucallee_saved n8 r5).
      { assert (T1 : ucallee_saved n8 r1)
          by (rewrite /r1; apply ucs_caller; vm_compute; reflexivity).
        assert (T2 : ucallee_saved n8 r2).
        { apply (ucallee_saved_trans n8 r1 r2 T1).
          rewrite /r2. apply ucs_caller; vm_compute; reflexivity. }
        assert (T3 : ucallee_saved n8 r3).
        { apply (ucallee_saved_trans n8 r2 r3 T2).
          rewrite /r3. apply ucs_caller; vm_compute; reflexivity. }
        assert (T4 : ucallee_saved n8 r4).
        { apply (ucallee_saved_trans n8 r3 r4 T3).
          rewrite /r4. apply ucs_caller; vm_compute; reflexivity. }
        apply (ucallee_saved_trans n8 r4 r5 T4).
        apply (ucallee_saved_trans r4
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> r4) r5).
        - apply ucs_caller; vm_compute; reflexivity.
        - rewrite /r5. apply ucs_caller; vm_compute; reflexivity. }
      rewrite /ukc. iIntros (hF CF ptF RutF szF) "%HloF %HpmF Hb".
      (* ---- 0x48  c.addi s1,s1,8 -- i := i+1 ---- *)
      assert (Hs1_r5 : r5 !!! Regidx (mword_of_int 9 : mword 5)
                       = (mword_of_int (av + 8 * i) : mword 64)).
      { rewrite (Hcs85 (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs1_8. }
      iApply (wp_uk_caddi CF ptF RutF π szF HloF HpmF Mp r5 (mword_of_int 0x48)
                (mword_of_int 8 : mword 6) (mword_of_int 9 : mword 5)
                (mword_of_int (av + 8 * (i + 1)) : mword 64)
                (UI ui_echo_48 Mp HtP Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_r5;
                      assert (E8b : (sign_extend' 64 (sign_extend' 12
                                       (mword_of_int 8 : mword 6)) : mword 64)
                                    = mword_of_int 8)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite E8b moi_add; f_equal; lia)
                with "Hb").
      set (r6 := <[Regidx (mword_of_int 9 : mword 5)
                   := regval_into_reg (mword_of_int (av + 8 * (i + 1))
                                       : mword 64)]> r5).
      assert (E48 : add_vec_int (mword_of_int 0x48 : mword 64) 2 = mword_of_int 0x4a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E48.
      rewrite /ukc. iIntros (hG CG ptG RutG szG) "%HloG %HpmG Hb".
      (* ---- 0x4a  beq s1,s4,0x76 -- NEVER taken (i+1 <= argc-1 < argc) ---- *)
      assert (Hs1_r6 : r6 !!! Regidx (mword_of_int 9 : mword 5)
                       = (mword_of_int (av + 8 * (i + 1)) : mword 64))
        by (apply upd_eq_tr; reflexivity).
      assert (Hs4_r6 : r6 !!! Regidx (mword_of_int 20 : mword 5)
                       = (mword_of_int (av + 8 * argc) : mword 64)).
      { rewrite /r6. apply upd_ne_tr; [ vm_compute; discriminate | ].
        rewrite (Hcs85 (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs4_8. }
      iApply (wp_uk_btype CG ptG RutG π szG HloG HpmG Mp r6 (mword_of_int 0x4a)
                (mword_of_int 44 : mword 13) (mword_of_int 20 : mword 5)
                (mword_of_int 9 : mword 5) BEQ false (mword_of_int 0x76)
                (UI ui_echo_4a Mp HtP Hx)
                ltac:(cbn [uv_btaken]; rewrite Hs1_r6 Hs4_r6
                        (moi_eq_vec (av + 8 * (i + 1)) (av + 8 * argc)
                           ltac:(unfold Z64; lia) ltac:(unfold Z64; lia))
                        (proj2 (Z.eqb_neq (av + 8 * (i + 1)) (av + 8 * argc))
                           ltac:(lia));
                      reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (E4a : (if false then (mword_of_int 0x76 : mword 64)
                     else add_vec_int (mword_of_int 0x4a : mword 64) 4)
                    = mword_of_int 0x4e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E4a.
      (* ---- the next iteration: the measure strictly decreased ---- *)
      iApply (IH Mp r6 (i + 1) Hx HtP HargsP HstP
                ltac:(lia) ltac:(lia) Hs1_r6
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 21 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs5_8)
                Hs4_r6
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 19 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs3_8)
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 22 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hs6_8)
                ltac:(rewrite /r6;
                      apply upd_ne_tr; [ vm_compute; discriminate | ];
                      rewrite (Hcs85 (mword_of_int 2 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact Hsp_8)).
  Qed.

  (* main @0x0 -- the eight-register prologue, the argc guard, the argv
     index chain, then the loop.  DIVERGES. *)
  Lemma wp_kecho_main (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (argc av : Z) (alen : Z -> Z) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack π M sp0 80 ->                     (* main's 64 + strlen's 16 *)
    m !!! Regidx a0_idx = (mword_of_int argc : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int av : mword 64) ->
    uk_args π M av argc (uint sp0) alen ->
    ⊢ ukc π M m (mword_of_int EchoSyms.main).
  Proof.
    intros Hx Htext Hsp Hst Hargc Hav Hargs.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite Hsmain.
    pose proof (uka_argc _ _ _ _ _ _ Hargs) as Hargcb.
    change (2 ^ 31) with 2147483648 in Hargcb.
    pose proof (uka_rd _ _ _ _ _ _ Hargs) as Hrdav.
    pose proof (ukrd_lo _ _ _ _ Hrdav) as Hav0.
    pose proof (ukrd_hi _ _ _ _ Hrdav) as Havhi.
    change (2 ^ 38) with 274877906944 in Havhi.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo80.
    destruct (uk_stack_split π M sp0 80 64 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 64)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x00  c.addi16sp sp,-64 ---- *)
    assert (Hwsp : add_vec_int sp0 (-64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hsp' : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hsp'.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi16sp C pt Rut π sz Hlo Hpm M m (mword_of_int 0x0)
              (mword_of_int 60 : mword 6) (add_vec_int sp0 (-64))
              (UI ui_echo_00 M Htext Hx) Hwsp
              with "Hb").
    set (m1 := <[Regidx csp_rs1 := regval_into_reg (add_vec_int sp0 (-64))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-64))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg (add_vec_int sp0 (-64)))).
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2 = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E00.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x02  c.sdsp x1,56(sp) ---- *)
    iPoseProof (kecho_pro_store M m1 sp0 (mword_of_int 0x02)
                  (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) 64 56
                  (UI ui_echo_02 M Htext Hx) Hstf
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps1".
    iApply ("Hps1" $! h1 C1 pt1 Rut1 sz1 with "[%] [%] Hb");
      [ exact Hlo1 | exact Hpm1 | ].
    set (M1 := uM_store8 M (uint sp0 - 64 + 56)
                 (m1 !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Ho1 : uM_only M M1 (uint sp0 - 64) 64)
      by (rewrite /M1; apply uM_only_store8; lia).
    assert (Ht1 : echo_text_sub M1)
      by exact (uM_only_img EchoInstrs.echo_bytes M M1 (uint sp0 - 64) 64
                  HkT Ho1 Htext).
    assert (Hs1 : uk_stack π M1 sp0 64)
      by exact (uk_stack_only M M1 sp0 64 (uint sp0 - 64) 64 Ho1 Hstf).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2 = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x04  c.sdsp x8,48(sp) ---- *)
    iPoseProof (kecho_pro_store M1 m1 sp0 (mword_of_int 0x04)
                  (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) 64 48
                  (UI ui_echo_04 M1 Ht1 Hx) Hs1
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps2".
    iApply ("Hps2" $! h2 C2 pt2 Rut2 sz2 with "[%] [%] Hb");
      [ exact Hlo2 | exact Hpm2 | ].
    set (M2 := uM_store8 M1 (uint sp0 - 64 + 48)
                 (m1 !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only M M2 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M1 M2 (uint sp0 - 64) 64 Ho1).
      rewrite /M2. apply uM_only_store8; lia. }
    assert (Ht2 : echo_text_sub M2)
      by exact (uM_only_img EchoInstrs.echo_bytes M M2 (uint sp0 - 64) 64
                  HkT Ho2 Htext).
    assert (Hs2 : uk_stack π M2 sp0 64)
      by exact (uk_stack_only M M2 sp0 64 (uint sp0 - 64) 64 Ho2 Hstf).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2 = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x06  c.sdsp x9,40(sp) ---- *)
    iPoseProof (kecho_pro_store M2 m1 sp0 (mword_of_int 0x06)
                  (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5) 64 40
                  (UI ui_echo_06 M2 Ht2 Hx) Hs2
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps3".
    iApply ("Hps3" $! h3 C3 pt3 Rut3 sz3 with "[%] [%] Hb");
      [ exact Hlo3 | exact Hpm3 | ].
    set (M3 := uM_store8 M2 (uint sp0 - 64 + 40)
                 (m1 !!! Regidx (mword_of_int 9 : mword 5))).
    assert (Ho3 : uM_only M M3 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M2 M3 (uint sp0 - 64) 64 Ho2).
      rewrite /M3. apply uM_only_store8; lia. }
    assert (Ht3 : echo_text_sub M3)
      by exact (uM_only_img EchoInstrs.echo_bytes M M3 (uint sp0 - 64) 64
                  HkT Ho3 Htext).
    assert (Hs3 : uk_stack π M3 sp0 64)
      by exact (uk_stack_only M M3 sp0 64 (uint sp0 - 64) 64 Ho3 Hstf).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2 = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x08  c.sdsp x18,32(sp) ---- *)
    iPoseProof (kecho_pro_store M3 m1 sp0 (mword_of_int 0x08)
                  (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5) 64 32
                  (UI ui_echo_08 M3 Ht3 Hx) Hs3
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps4".
    iApply ("Hps4" $! h4 C4 pt4 Rut4 sz4 with "[%] [%] Hb");
      [ exact Hlo4 | exact Hpm4 | ].
    set (M4 := uM_store8 M3 (uint sp0 - 64 + 32)
                 (m1 !!! Regidx (mword_of_int 18 : mword 5))).
    assert (Ho4 : uM_only M M4 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M3 M4 (uint sp0 - 64) 64 Ho3).
      rewrite /M4. apply uM_only_store8; lia. }
    assert (Ht4 : echo_text_sub M4)
      by exact (uM_only_img EchoInstrs.echo_bytes M M4 (uint sp0 - 64) 64
                  HkT Ho4 Htext).
    assert (Hs4 : uk_stack π M4 sp0 64)
      by exact (uk_stack_only M M4 sp0 64 (uint sp0 - 64) 64 Ho4 Hstf).
    assert (E08 : add_vec_int (mword_of_int 0x08 : mword 64) 2 = mword_of_int 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x0a  c.sdsp x19,24(sp) ---- *)
    iPoseProof (kecho_pro_store M4 m1 sp0 (mword_of_int 0x0a)
                  (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5) 64 24
                  (UI ui_echo_0a M4 Ht4 Hx) Hs4
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps5".
    iApply ("Hps5" $! h5 C5 pt5 Rut5 sz5 with "[%] [%] Hb");
      [ exact Hlo5 | exact Hpm5 | ].
    set (M5 := uM_store8 M4 (uint sp0 - 64 + 24)
                 (m1 !!! Regidx (mword_of_int 19 : mword 5))).
    assert (Ho5 : uM_only M M5 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M4 M5 (uint sp0 - 64) 64 Ho4).
      rewrite /M5. apply uM_only_store8; lia. }
    assert (Ht5 : echo_text_sub M5)
      by exact (uM_only_img EchoInstrs.echo_bytes M M5 (uint sp0 - 64) 64
                  HkT Ho5 Htext).
    assert (Hs5 : uk_stack π M5 sp0 64)
      by exact (uk_stack_only M M5 sp0 64 (uint sp0 - 64) 64 Ho5 Hstf).
    assert (E0a : add_vec_int (mword_of_int 0x0a : mword 64) 2 = mword_of_int 0x0c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x0c  c.sdsp x20,16(sp) ---- *)
    iPoseProof (kecho_pro_store M5 m1 sp0 (mword_of_int 0x0c)
                  (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5) 64 16
                  (UI ui_echo_0c M5 Ht5 Hx) Hs5
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps6".
    iApply ("Hps6" $! h6 C6 pt6 Rut6 sz6 with "[%] [%] Hb");
      [ exact Hlo6 | exact Hpm6 | ].
    set (M6 := uM_store8 M5 (uint sp0 - 64 + 16)
                 (m1 !!! Regidx (mword_of_int 20 : mword 5))).
    assert (Ho6 : uM_only M M6 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M5 M6 (uint sp0 - 64) 64 Ho5).
      rewrite /M6. apply uM_only_store8; lia. }
    assert (Ht6 : echo_text_sub M6)
      by exact (uM_only_img EchoInstrs.echo_bytes M M6 (uint sp0 - 64) 64
                  HkT Ho6 Htext).
    assert (Hs6 : uk_stack π M6 sp0 64)
      by exact (uk_stack_only M M6 sp0 64 (uint sp0 - 64) 64 Ho6 Hstf).
    assert (E0c : add_vec_int (mword_of_int 0x0c : mword 64) 2 = mword_of_int 0x0e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x0e  c.sdsp x21,8(sp) ---- *)
    iPoseProof (kecho_pro_store M6 m1 sp0 (mword_of_int 0x0e)
                  (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5) 64 8
                  (UI ui_echo_0e M6 Ht6 Hx) Hs6
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps7".
    iApply ("Hps7" $! h7 C7 pt7 Rut7 sz7 with "[%] [%] Hb");
      [ exact Hlo7 | exact Hpm7 | ].
    set (M7 := uM_store8 M6 (uint sp0 - 64 + 8)
                 (m1 !!! Regidx (mword_of_int 21 : mword 5))).
    assert (Ho7 : uM_only M M7 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M6 M7 (uint sp0 - 64) 64 Ho6).
      rewrite /M7. apply uM_only_store8; lia. }
    assert (Ht7 : echo_text_sub M7)
      by exact (uM_only_img EchoInstrs.echo_bytes M M7 (uint sp0 - 64) 64
                  HkT Ho7 Htext).
    assert (Hs7 : uk_stack π M7 sp0 64)
      by exact (uk_stack_only M M7 sp0 64 (uint sp0 - 64) 64 Ho7 Hstf).
    assert (E0e : add_vec_int (mword_of_int 0x0e : mword 64) 2 = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e.
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x10  c.sdsp x22,0(sp) ---- *)
    iPoseProof (kecho_pro_store M7 m1 sp0 (mword_of_int 0x10)
                  (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5) 64 0
                  (UI ui_echo_10 M7 Ht7 Hx) Hs7
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps8".
    iApply ("Hps8" $! h8 C8 pt8 Rut8 sz8 with "[%] [%] Hb");
      [ exact Hlo8 | exact Hpm8 | ].
    set (M8 := uM_store8 M7 (uint sp0 - 64 + 0)
                 (m1 !!! Regidx (mword_of_int 22 : mword 5))).
    assert (Ho8 : uM_only M M8 (uint sp0 - 64) 64).
    { apply (uM_only_trans M M7 M8 (uint sp0 - 64) 64 Ho7).
      rewrite /M8. apply uM_only_store8; lia. }
    assert (Ht8 : echo_text_sub M8)
      by exact (uM_only_img EchoInstrs.echo_bytes M M8 (uint sp0 - 64) 64
                  HkT Ho8 Htext).
    (* the image predicates at the post-prologue image, once *)
    assert (Hst8 : uk_stack π M8 sp0 80)
      by exact (uk_stack_only M M8 sp0 80 (uint sp0 - 64) 64 Ho8 Hst).
    assert (Hargs8 : uk_args π M8 av argc (uint sp0) alen)
      by exact (uk_args_only M M8 av argc (uint sp0) (uint sp0 - 64) 64 alen
                  Ho8 ltac:(lia) Hargs).
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2 = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E10.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x12  c.addi4spn s0,sp,64 ---- *)
    assert (Hw64 : add_vec_int (add_vec_int sp0 (-64)) 64
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C9 pt9 Rut9 π sz9 Hlo9 Hpm9 M8 m1 (mword_of_int 0x12)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-64)) 64)
              (UI ui_echo_12 M8 Ht8 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw64
              with "Hb").
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-64)) 64)]> m1).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2 = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12.
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    (* ---- 0x14  c.li a5,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli CA ptA RutA π szA HloA HpmA M8 m2 (mword_of_int 0x14)
              (mword_of_int 1 : mword 6) (mword_of_int 15 : mword 5)
              (mword_of_int 1 : mword 64)
              (UI ui_echo_14 M8 Ht8 Hx)
              ltac:(vm_compute; discriminate) Hw1
              with "Hb").
    set (m3 := <[Regidx (mword_of_int 15 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m2).
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 2 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E14.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x16  bge a5,a0,0x76 -- the argc guard ---- *)
    assert (Ha5_3 : m3 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 1 : mword 64))
      by (apply upd_eq_tr; reflexivity).
    assert (Ha0_3 : m3 !!! Regidx (mword_of_int 10 : mword 5)
                    = (mword_of_int argc : mword 64)).
    { rewrite /m3 /m2.
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /m1. apply upd_ne_tr; [ vm_compute; discriminate | ].
      exact Hargc. }
    assert (Ha1_3 : m3 !!! Regidx (mword_of_int 11 : mword 5)
                    = (mword_of_int av : mword 64)).
    { rewrite /m3 /m2.
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      apply upd_ne_tr; [ vm_compute; discriminate | ].
      rewrite /m1. apply upd_ne_tr; [ vm_compute; discriminate | ].
      exact Hav. }
    assert (Etgt76 : (mword_of_int 0x76 : mword 64)
                     = add_vec (mword_of_int 0x16)
                         (sign_extend' 64 (mword_of_int 96 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.geb 1 argc) eqn:Hge.
    - (* argc <= 1: the guard is taken, straight to the exit tail *)
      iApply (wp_uk_btype CB ptB RutB π szB HloB HpmB M8 m3 (mword_of_int 0x16)
                (mword_of_int 96 : mword 13) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5) BGE true (mword_of_int 0x76)
                (UI ui_echo_16 M8 Ht8 Hx)
                ltac:(cbn [uv_btaken]; rewrite Ha5_3 Ha0_3
                        (moi_ge_s 1 argc ltac:(unfold Z63; lia)
                           ltac:(unfold Z63; lia));
                      exact (eq_sym Hge))
                Etgt76 ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      iApply (kecho_exit_tail M8 m3 Hx Ht8).
    - (* argc >= 2: the argv index chain, then the loop *)
      assert (Hargc2 : 2 <= argc).
      { destruct (Z.le_gt_cases argc 1) as [Hle | Hgt]; [ | lia ].
        exfalso. rewrite (proj2 (Z.geb_le 1 argc) Hle) in Hge. discriminate. }
      iApply (wp_uk_btype CB ptB RutB π szB HloB HpmB M8 m3 (mword_of_int 0x16)
                (mword_of_int 96 : mword 13) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5) BGE false (mword_of_int 0x76)
                (UI ui_echo_16 M8 Ht8 Hx)
                ltac:(cbn [uv_btaken]; rewrite Ha5_3 Ha0_3
                        (moi_ge_s 1 argc ltac:(unfold Z63; lia)
                           ltac:(unfold Z63; lia));
                      exact (eq_sym Hge))
                Etgt76 ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (E16 : (if false then (mword_of_int 0x76 : mword 64)
                     else add_vec_int (mword_of_int 0x16 : mword 64) 4)
                    = mword_of_int 0x1a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E16.
      (* the whole index arithmetic, discharged by §0b *)
      assert (HP1 : 2 <= argc < 2 ^ 31)
        by (change (2 ^ 31) with 2147483648; lia).
      assert (HP3 : av + 8 * argc <= 2 ^ 38)
        by (change (2 ^ 38) with 274877906944; lia).
      destruct (echo_argv_chain argc av HP1 Hav0 HP3) as (Hch1 & Hch2 & Hch3).
      assert (Hs1val : add_vec (mword_of_int av : mword 64)
                         (sign_extend' 64 (mword_of_int 8 : mword 12))
                       = (mword_of_int (av + 8 * 1) : mword 64)).
      { assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                     = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
        rewrite E8 moi_add. f_equal; lia. }
      rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
      (* ---- 0x1a  addi s1,a1,8 ---- *)
      iApply (wp_uk_addi CC ptC RutC π szC HloC HpmC M8 m3 (mword_of_int 0x1a)
                (mword_of_int 8 : mword 12) (mword_of_int 11 : mword 5)
                (mword_of_int 9 : mword 5)
                (add_vec (mword_of_int av : mword 64)
                   (sign_extend' 64 (mword_of_int 8 : mword 12)))
                (UI ui_echo_1a M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_3; reflexivity)
                with "Hb").
      set (m4 := <[Regidx (mword_of_int 9 : mword 5)
                   := regval_into_reg (add_vec (mword_of_int av : mword 64)
                        (sign_extend' 64 (mword_of_int 8 : mword 12)))]> m3).
      assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4 = mword_of_int 0x1e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1a.
      rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
      (* ---- 0x1e  c.addiw a0,a0,-2 ---- *)
      assert (Ha0_4 : m4 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int argc : mword 64)).
      { rewrite /m4. apply upd_ne_tr; [ vm_compute; discriminate | ]. exact Ha0_3. }
      iApply (wp_uk_caddiw CD ptD RutD π szD HloD HpmD M8 m4 (mword_of_int 0x1e)
                (mword_of_int 62 : mword 6) (mword_of_int 10 : mword 5)
                (sign_extend' 64
                   (subrange_vec_dec
                      (add_vec (mword_of_int argc : mword 64)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                      31 0))
                (UI ui_echo_1e M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_4; reflexivity)
                with "Hb").
      set (m5 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mword_of_int argc : mword 64)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                           31 0))]> m4).
      assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2 = mword_of_int 0x20)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1e.
      rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
      (* ---- 0x20  slli a5,a0,0x20 ---- *)
      assert (Ha0_5 : m5 !!! Regidx (mword_of_int 10 : mword 5)
                      = sign_extend' 64
                          (subrange_vec_dec
                             (add_vec (mword_of_int argc : mword 64)
                                (sign_extend' 64
                                   (sign_extend' 12 (mword_of_int 62 : mword 6))))
                             31 0))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uk_slli CE ptE RutE π szE HloE HpmE M8 m5 (mword_of_int 0x20)
                (mword_of_int 32 : mword 6) (mword_of_int 10 : mword 5)
                (mword_of_int 15 : mword 5)
                (shift_bits_left
                   (sign_extend' 64
                      (subrange_vec_dec
                         (add_vec (mword_of_int argc : mword 64)
                            (sign_extend' 64
                               (sign_extend' 12 (mword_of_int 62 : mword 6))))
                         31 0))
                   (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                (UI ui_echo_20 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_5; reflexivity)
                with "Hb").
      set (m6 := <[Regidx (mword_of_int 15 : mword 5)
                   := regval_into_reg (shift_bits_left
                        (sign_extend' 64
                           (subrange_vec_dec
                              (add_vec (mword_of_int argc : mword 64)
                                 (sign_extend' 64
                                    (sign_extend' 12 (mword_of_int 62 : mword 6))))
                              31 0))
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))]> m5).
      assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 4 = mword_of_int 0x24)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E20.
      rewrite /ukc. iIntros (hF CF ptF RutF szF) "%HloF %HpmF Hb".
      (* ---- 0x24  srli a0,a5,0x1d -- a0 := 8*(argc-2) ---- *)
      assert (Ha5_6 : m6 !!! Regidx (mword_of_int 15 : mword 5)
                      = shift_bits_left
                          (sign_extend' 64
                             (subrange_vec_dec
                                (add_vec (mword_of_int argc : mword 64)
                                   (sign_extend' 64
                                      (sign_extend' 12 (mword_of_int 62 : mword 6))))
                                31 0))
                          (subrange_vec_dec (mword_of_int 32 : mword 6)
                             (Z.sub log2_xlen 1) 0))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uk_srli CF ptF RutF π szF HloF HpmF M8 m6 (mword_of_int 0x24)
                (mword_of_int 29 : mword 6) (mword_of_int 15 : mword 5)
                (mword_of_int 10 : mword 5)
                (mword_of_int (8 * (argc - 2)))
                (UI ui_echo_24 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5_6; exact (eq_sym Hch1))
                with "Hb").
      set (m7 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int (8 * (argc - 2)) : mword 64)]> m6).
      assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 4 = mword_of_int 0x28)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E24.
      rewrite /ukc. iIntros (hG CG ptG RutG szG) "%HloG %HpmG Hb".
      (* ---- 0x28  add s5,s1,a0 ---- *)
      assert (Hs1_7 : m7 !!! Regidx (mword_of_int 9 : mword 5)
                      = add_vec (mword_of_int av : mword 64)
                          (sign_extend' 64 (mword_of_int 8 : mword 12))).
      { rewrite /m7 /m6 /m5.
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_ne_tr; [ vm_compute; discriminate | ].
        apply upd_eq_tr; reflexivity. }
      assert (Ha0_7 : m7 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int (8 * (argc - 2)) : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uk_add CG ptG RutG π szG HloG HpmG M8 m7 (mword_of_int 0x28)
                (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 21 : mword 5)
                (mword_of_int (av + 8 * (argc - 1)))
                (UI ui_echo_28 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1_7 Ha0_7 -Hch1; exact (eq_sym Hch2))
                with "Hb").
      set (m8 := <[Regidx (mword_of_int 21 : mword 5)
                   := regval_into_reg (mword_of_int (av + 8 * (argc - 1))
                                       : mword 64)]> m7).
      assert (E28 : add_vec_int (mword_of_int 0x28 : mword 64) 4 = mword_of_int 0x2c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E28.
      rewrite /ukc. iIntros (hH CH ptH RutH szH) "%HloH %HpmH Hb".
      (* ---- 0x2c  c.addi a1,a1,16 ---- *)
      assert (Ha1_8 : m8 !!! Regidx (mword_of_int 11 : mword 5)
                      = (mword_of_int av : mword 64)).
      { rewrite /m8 /m7 /m6 /m5 /m4.
        do 5 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        exact Ha1_3. }
      iApply (wp_uk_caddi CH ptH RutH π szH HloH HpmH M8 m8 (mword_of_int 0x2c)
                (mword_of_int 16 : mword 6) (mword_of_int 11 : mword 5)
                (add_vec (mword_of_int av : mword 64)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
                (UI ui_echo_2c M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_8; reflexivity)
                with "Hb").
      set (m9 := <[Regidx (mword_of_int 11 : mword 5)
                   := regval_into_reg (add_vec (mword_of_int av : mword 64)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 16 : mword 6))))]> m8).
      assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2 = mword_of_int 0x2e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E2c.
      rewrite /ukc. iIntros (hI CI ptI RutI szI) "%HloI %HpmI Hb".
      (* ---- 0x2e  add s4,a1,a0 ---- *)
      assert (Ha1_9 : m9 !!! Regidx (mword_of_int 11 : mword 5)
                      = add_vec (mword_of_int av : mword 64)
                          (sign_extend' 64
                             (sign_extend' 12 (mword_of_int 16 : mword 6))))
        by (apply upd_eq_tr; reflexivity).
      assert (Ha0_9 : m9 !!! Regidx (mword_of_int 10 : mword 5)
                      = (mword_of_int (8 * (argc - 2)) : mword 64)).
      { rewrite /m9 /m8.
        do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
        exact Ha0_7. }
      iApply (wp_uk_add CI ptI RutI π szI HloI HpmI M8 m9 (mword_of_int 0x2e)
                (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
                (mword_of_int 20 : mword 5)
                (mword_of_int (av + 8 * argc))
                (UI ui_echo_2e M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha1_9 Ha0_9 -Hch1; exact (eq_sym Hch3))
                with "Hb").
      set (m10 := <[Regidx (mword_of_int 20 : mword 5)
                    := regval_into_reg (mword_of_int (av + 8 * argc) : mword 64)]> m9).
      assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4 = mword_of_int 0x32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E2e.
      rewrite /ukc. iIntros (hJ CJ ptJ RutJ szJ) "%HloJ %HpmJ Hb".
      (* ---- 0x32  c.li s3,1 ---- *)
      iApply (wp_uk_cli CJ ptJ RutJ π szJ HloJ HpmJ M8 m10 (mword_of_int 0x32)
                (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                (mword_of_int 1 : mword 64)
                (UI ui_echo_32 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate) Hw1
                with "Hb").
      set (m11 := <[Regidx (mword_of_int 19 : mword 5)
                    := regval_into_reg (mword_of_int 1 : mword 64)]> m10).
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2 = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E32.
      rewrite /ukc. iIntros (hK CK ptK RutK szK) "%HloK %HpmK Hb".
      (* ---- 0x34  auipc s6,0x1 ---- *)
      iApply (wp_uk_auipc CK ptK RutK π szK HloK HpmK M8 m11 (mword_of_int 0x34)
                (mword_of_int 1 : mword 20) (mword_of_int 22 : mword 5)
                (mword_of_int 4148 : mword 64)
                (UI ui_echo_34 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hb").
      set (m12 := <[Regidx (mword_of_int 22 : mword 5)
                    := regval_into_reg (mword_of_int 4148 : mword 64)]> m11).
      assert (E34 : add_vec_int (mword_of_int 0x34 : mword 64) 4 = mword_of_int 0x38)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E34.
      rewrite /ukc. iIntros (hL CL ptL RutL szL) "%HloL %HpmL Hb".
      (* ---- 0x38  addi s6,s6,-1796 -- s6 := 0x930, the " " literal ---- *)
      assert (Hs6_12 : m12 !!! Regidx (mword_of_int 22 : mword 5)
                       = (mword_of_int 4148 : mword 64))
        by (apply upd_eq_tr; reflexivity).
      iApply (wp_uk_addi CL ptL RutL π szL HloL HpmL M8 m12 (mword_of_int 0x38)
                (mword_of_int 2300 : mword 12) (mword_of_int 22 : mword 5)
                (mword_of_int 22 : mword 5) (mword_of_int 2352 : mword 64)
                (UI ui_echo_38 M8 Ht8 Hx)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs6_12; apply bv_eq; vm_compute; reflexivity)
                with "Hb").
      set (m13 := <[Regidx (mword_of_int 22 : mword 5)
                    := regval_into_reg (mword_of_int 2352 : mword 64)]> m12).
      assert (E38 : add_vec_int (mword_of_int 0x38 : mword 64) 4 = mword_of_int 0x3c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E38.
      rewrite /ukc. iIntros (hM CM ptM RutM szM) "%HloM %HpmM Hb".
      (* ---- 0x3c  c.j 0x4e -- enter the loop at i = 1 ---- *)
      iApply (wp_uk_cj CM ptM RutM π szM HloM HpmM M8 m13 (mword_of_int 0x3c)
                (mword_of_int 9 : mword 11) (mword_of_int 0x4e)
                (UI ui_echo_3c M8 Ht8 Hx)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hb").
      (* ---- the loop, at i = 1 ---- *)
      iApply (kecho_loop sp0 argc av alen (Z.to_nat (argc - 1)) M8 m13 1
                Hx Ht8 Hargs8 Hst8 ltac:(lia)
                ltac:(rewrite Z2Nat.id; lia)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5;
                      do 9 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; exact Hs1val)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9;
                      do 5 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12 /m11;
                      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12;
                      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      apply upd_eq_tr; reflexivity)
                ltac:(apply upd_eq_tr; reflexivity)
                ltac:(rewrite /m13 /m12 /m11 /m10 /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2;
                      do 12 (apply upd_ne_tr; [ vm_compute; discriminate | ]);
                      exact Hsp1)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5 start @0x7c -- the ELF entry [exec()] jumps to, and THE top-level  *)
  (* statement about the echo process: from the loaded image, the argument *)
  (* area and the entry registers, the machine runs safely forever under   *)
  (* the kernel's trap services.  Prologue, then main; main DIVERGES, so   *)
  (* the jal exit at 0x88 is dead code with no [uinstr] fact.              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kecho_start (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (argc av : Z) (alen : Z -> Z) :
    uk_xpage π (mword_of_int 0) ->
    echo_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack π M sp0 96 ->                     (* start's 16 + main's 80 *)
    m !!! Regidx a0_idx = (mword_of_int argc : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int av : mword 64) ->
    uk_args π M av argc (uint sp0) alen ->
    ⊢ ukc π M m (mword_of_int EchoSyms.start).
  Proof.
    intros Hx Htext Hsp Hst Hargc Hav Hargs.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    rewrite Hsstart.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo96.
    destruct (uk_stack_split π M sp0 96 16 80 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    assert (Hbu : bv_unsigned sp0 = uint sp0)
      by (rewrite uint_unsigned; reflexivity).
    assert (Hu16 : uint (add_vec_int sp0 (-16)) = uint sp0 - 16).
    { rewrite uint_unsigned.
      rewrite (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite Hbu; lia)).
      rewrite Hbu. reflexivity. }
    assert (HkT : forall (kk : Z) (bb : bv 8),
              EchoInstrs.echo_bytes !! kk = Some bb -> kk < uint sp0 - 16)
      by (intros kk bb Hkb; pose proof (echo_bytes_key_lt kk bb Hkb); lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x7c  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { assert (Hsp' : m !!! Regidx (mword_of_int 2 : mword 5) = sp0) by exact Hsp.
      rewrite Hsp'.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut π sz Hlo Hpm M m (mword_of_int 0x7c)
              (mword_of_int 48 : mword 6) (mword_of_int 2 : mword 5)
              (add_vec_int sp0 (-16))
              (UI ui_echo_7c M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (n1 := <[Regidx (mword_of_int 2 : mword 5)
                 := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx (mword_of_int 2 : mword 5))
                  (regval_into_reg (add_vec_int sp0 (-16)))).
    assert (E7c : add_vec_int (mword_of_int 0x7c : mword 64) 2 = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x7e  c.sdsp ra,8(sp) ---- *)
    iPoseProof (kecho_pro_store M n1 sp0 (mword_of_int 0x7e)
                  (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5) 16 8
                  (UI ui_echo_7e M Htext Hx) Hstf
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps1".
    iApply ("Hps1" $! h1 C1 pt1 Rut1 sz1 with "[%] [%] Hb");
      [ exact Hlo1 | exact Hpm1 | ].
    set (N1 := uM_store8 M (uint sp0 - 16 + 8)
                 (n1 !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Ho1 : uM_only M N1 (uint sp0 - 16) 16)
      by (rewrite /N1; apply uM_only_store8; lia).
    assert (Ht1 : echo_text_sub N1)
      by exact (uM_only_img EchoInstrs.echo_bytes M N1 (uint sp0 - 16) 16
                  HkT Ho1 Htext).
    assert (Hs1 : uk_stack π N1 sp0 16)
      by exact (uk_stack_only M N1 sp0 16 (uint sp0 - 16) 16 Ho1 Hstf).
    assert (E7e : add_vec_int (mword_of_int 0x7e : mword 64) 2 = mword_of_int 0x80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x80  c.sdsp s0,0(sp) ---- *)
    iPoseProof (kecho_pro_store N1 n1 sp0 (mword_of_int 0x80)
                  (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5) 16 0
                  (UI ui_echo_80 N1 Ht1 Hx) Hs1
                  ltac:(lia) ltac:(lia) ltac:(reflexivity) Hsp1
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as "Hps2".
    iApply ("Hps2" $! h2 C2 pt2 Rut2 sz2 with "[%] [%] Hb");
      [ exact Hlo2 | exact Hpm2 | ].
    set (N2 := uM_store8 N1 (uint sp0 - 16 + 0)
                 (n1 !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Ho2 : uM_only M N2 (uint sp0 - 16) 16).
    { apply (uM_only_trans M N1 N2 (uint sp0 - 16) 16 Ho1).
      rewrite /N2. apply uM_only_store8; lia. }
    assert (Ht2 : echo_text_sub N2)
      by exact (uM_only_img EchoInstrs.echo_bytes M N2 (uint sp0 - 16) 16
                  HkT Ho2 Htext).
    assert (E80 : add_vec_int (mword_of_int 0x80 : mword 64) 2 = mword_of_int 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E80.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x82  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (n1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 π sz3 Hlo3 Hpm3 N2 n1 (mword_of_int 0x82)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16)
              (UI ui_echo_82 N2 Ht2 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    set (n2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> n1).
    assert (E82 : add_vec_int (mword_of_int 0x82 : mword 64) 2 = mword_of_int 0x84)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E82.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x84  jal ra,0x0 <main> ---- *)
    assert (Htj : (mword_of_int EchoSyms.main : mword 64)
                  = add_vec (mword_of_int 0x84)
                      (sign_extend' 64 (mword_of_int 2097020 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x88 : mword 64)
                  = add_vec_int (mword_of_int 0x84 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 π sz4 Hlo4 Hpm4 N2 n2 (mword_of_int 0x84)
              (mword_of_int 2097020 : mword 21) ra_idx
              (mword_of_int EchoSyms.main) (mword_of_int 0x88)
              (UI ui_echo_84 N2 Ht2 Hx)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x88 : mword 64)]> n2).
    (* ---- the call: main() -- diverges ----
       ORDER MATTERS: carry [uk_args] across the prologue at the OLD bound
       (where [uk_args_only]'s [a + n <= lo] holds exactly), and only then
       lower the bound to main's entry sp. *)
    assert (Hargs2 : uk_args π N2 av argc (uint sp0) alen)
      by exact (uk_args_only M N2 av argc (uint sp0) (uint sp0 - 16) 16 alen
                  Ho2 ltac:(lia) Hargs).
    assert (Hargs3 : uk_args π N2 av argc (uint (add_vec_int sp0 (-16))) alen)
      by exact (uk_args_lo_le π N2 av argc (uint sp0)
                  (uint (add_vec_int sp0 (-16))) alen ltac:(lia) Hargs2).
    assert (Hst3 : uk_stack π N2 (add_vec_int sp0 (-16)) 80)
      by exact (uk_stack_only M N2 (add_vec_int sp0 (-16)) 80
                  (uint sp0 - 16) 16 Ho2 Hstm).
    assert (Hsp3 : n3 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { rewrite /n3 /n2.
      do 2 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hsp1. }
    assert (Hargc3 : n3 !!! Regidx a0_idx = (mword_of_int argc : mword 64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hargc. }
    assert (Hav3 : n3 !!! Regidx a1_idx = (mword_of_int av : mword 64)).
    { rewrite /n3 /n2 /n1.
      do 3 (apply upd_ne_tr; [ vm_compute; discriminate | ]).
      exact Hav. }
    iApply (wp_kecho_main N2 n3 (add_vec_int sp0 (-16)) argc av alen
              Hx Ht2 Hsp3 Hst3 Hargc3 Hav3 Hargs3).
  Qed.

End UkEcho.
