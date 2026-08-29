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
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import UmodeMem UmodeFetch UmodeArith UmodeCap UmodeAbi UmodeSyscall.
Require Import WpUmodeStep WpUmodeStore WpUmodeLoad.
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

End UkEcho.
