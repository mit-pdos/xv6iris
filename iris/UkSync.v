(* ===================================================================== *)
(* UkSync.v -- the `sync` user program on the USER-MODE-ON-KERNEL engine:  *)
(* UProofSync.v's four function proofs restated as U-mode CONTINUATIONS    *)
(* ([UexecRet.ukc]) over UkLeaf.v / UkStore.v / UkStep.v, with every       *)
(* premise a fact about the KEY (the image [M] and the permission map [π]) *)
(* -- nothing about a table, and no capability assumption.                 *)
(*                                                                         *)
(* THE SHAPE.  A diverging function (exit's stub, main, start) proves      *)
(*   ⊢ ukc π M m pc                                                        *)
(* i.e. "for every hart, config, table and size realizing [π], from the     *)
(* bundle at (M, m, pc) the loop is safe" -- which is [uslot] at the        *)
(* trap-out key ([uslot_run]), so USyncKernel.v's constructor is a          *)
(* one-liner.  The returning stub takes its continuation as a [ukc] at the *)
(* return state, for every return value.                                   *)
(*                                                                         *)
(* THE KEY-LEVEL PREMISES.  [sync_layout pt] (the text page has a fetch-ok  *)
(* leaf) becomes [uk_xpage π 0] (page 0 is an X page of the key), and       *)
(* [uv_stack pt M sp n] becomes [uk_stack π M sp n] (its [us_leaf] clause   *)
(* read on the key: the budget's page is a W page).  Both are DECIDABLE    *)
(* facts about the key, which is what UexecCond.v's gate decides.  The      *)
(* bridges to the table's facts ([sync_layout_of_key], [uv_stack_of_key])  *)
(* go through UserPerm.v's leaf-bit transfers and are re-derived at every  *)
(* table the loop binds -- once per instruction, by [uk_instr_of_sync] --  *)
(* which is the price of the table being ∀-bound inside every              *)
(* continuation.                                                           *)
(*                                                                         *)
(* The proofs are UProofSync.v's, instruction for instruction, with        *)
(*   iIntros (CIDk) "Hcg Hpc"   read as   iIntros (hk Ck ptk Rutk szk) "%Hlok %Hpmk Hb" *)
(* at every continuation, and the ecall's protocol payload replaced by the *)
(* contract's own [uexec_ret] arm: exit's [emp], sync's                    *)
(* [∀ r M' π', ⌜usys_mem_ok 22 …⌝ -∗ uslot (bump …)] -- the quiet row gives *)
(* M' = M and π' = π, and [uslot_bump_run] turns the bumped slot into the   *)
(* continuation at (a0 := r, pc + 4).                                       *)
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
Require Import RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import UmodeMem UmodeCap UmodeAbi.
Require Import WpUmodeStore.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkLeaf UkStore.
Require Import UkAbi.   (* [uk_xpage] / [uk_stack]: the generic key-level layout facts *)
Require Import UCodeSync UProofSync.   (* the decode facts and [sync_text_sub_store8] *)
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 The BRIDGES from the key's layout facts to the table's.             *)
(*                                                                        *)
(* The facts themselves ([uk_xpage], [uk_wpage], [uk_stack] and its two   *)
(* budget lemmas) are PROGRAM-GENERIC and live in UkAbi.v beside          *)
(* [uk_rpage] / [uk_rd] / [uk_args]; what is sync's is only the two       *)
(* bridges below.                                                         *)
(* ===================================================================== *)

(* THE BRIDGE to the table's layout fact: an X page of the key is a
   fetch-ok leaf of every table realizing the key *)
Lemma sync_layout_of_key (pt : uptd) (sz : Z) (π : gmap (mword 27) uperm) :
  proc_pt_wf pt -> perm_of (ud_um pt) sz = π ->
  uk_xpage π (mword_of_int 0) -> sync_layout pt.
Proof.
  intros Hwf Hpm (q & Hq & Hx). unfold uperm_at in Hq. rewrite <- Hpm in Hq.
  destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
  constructor. exists w. exact (conj Hw Hok).
Qed.

(* the decode facts of UCodeSync.v, lifted to every table realizing the key *)
Lemma uk_instr_of_sync (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (pc : mword 64) (is_rvc : bool) (i : instruction) :
  uk_xpage π (mword_of_int 0) ->
  (forall pt : uptd, sync_layout pt -> uinstr pt M pc is_rvc i) ->
  uk_instr π M pc is_rvc i.
Proof.
  intros Hx H pt sz Hwf Hpm. exact (H pt (sync_layout_of_key pt sz π Hwf Hpm Hx)).
Qed.

(* ===================================================================== *)
(* §2 The four function proofs.                                           *)
(* ===================================================================== *)

Section UkSync.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context (π : gmap (mword 27) uperm).

  (* the [uinstr] fact of one sync instruction at every table of the key *)
  Local Notation UI ui M Htext Hx :=
    (uk_instr_of_sync π M _ _ _ Hx (fun pt0 Hl0 => ui pt0 M Hl0 Htext)).

  (* ------------------------------------------------------------------- *)
  (* exit @0x2c8: c.li a7,2; ecall.  The contract's exit arm is [emp].     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_exit_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage π (mword_of_int 0) ->
    sync_text_sub M ->
    ⊢ ukc π M m (mword_of_int SyncSyms.exit).
  Proof.
    intros Hx Htext.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hsexit.
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* 0x2c8  c.li a7,2 *)
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut π sz Hlo Hpm M m (mword_of_int 0x2c8)
              (mword_of_int 2 : mword 6) a7_idx (mword_of_int 2 : mword 64)
              (UI ui_sync_2c8 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw2
              with "Hb").
    assert (Epc : add_vec_int (mword_of_int 0x2c8 : mword 64) 2 = mword_of_int 0x2ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc.
    set (m1 := <[Regidx a7_idx := regval_into_reg (mword_of_int 2 : mword 64)]> m).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* 0x2ca  ecall *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 2 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (regval_into_reg (mword_of_int 2 : mword 64))).
    iApply (wp_uk_ecall C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x2ca)
              (UI ui_sync_2ca M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x2ca) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x2ca)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x2ca) M π)) = USYS_exit).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hne]; [ done | exfalso; exact (Hne eq_refl) ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sync @0x368: c.li a7,22; ecall; c.jr ra.  RETURNS: the contract's     *)
  (* returning arm, at the quiet row (M' = M, π' = π), is the continuation *)
  (* at (a0 := r, pc + 4); the c.jr then returns to the caller's ra.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_sync_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage π (mword_of_int 0) ->
    sync_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
        uvb (CID := h) C pt Rut sz π M m (mword_of_int SyncSyms.sync) -∗
        (∀ ret : mword 64,
           ukc π M (<[Regidx a0_idx := ret]>
                      (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hssync.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* 0x368  c.li a7,22 *)
    assert (Hw22 : (mword_of_int 22 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 22 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut π sz Hlo Hpm M m (mword_of_int 0x368)
              (mword_of_int 22 : mword 6) a7_idx (mword_of_int 22 : mword 64)
              (UI ui_sync_368 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw22
              with "Hb").
    (* the leaf's [regval_into_reg] wrapper is the identity: normalize the
       stored value NOW, before any further insert is stacked on it *)
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 22 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x368 : mword 64) 2 = mword_of_int 0x36a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* 0x36a  ecall -- SYS_sync, the returning arm *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 22 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int 22 : mword 64)).
    iApply (wp_uk_ecall C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x36a)
              (UI ui_sync_36a M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x36a) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x36a)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x36a) M π)) = 22).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (22 = USYS_exit)) as [Hne | _]; [ exfalso; discriminate Hne | ].
    destruct (decide (22 = USYS_fork)) as [Hne | _]; [ exfalso; discriminate Hne | ].
    iIntros (ret M' π') "%Hok".
    destruct (usys_mem_ok_quiet 22 _ ret _ _ _ _
                ltac:(discriminate) ltac:(discriminate) eq_refl Hok) as [-> ->].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m1 (mword_of_int 0x36a) M M π π ret Hx0
               ltac:(vm_compute; reflexivity)).
    assert (Epc2 : add_vec_int (mword_of_int 0x36a : mword 64) 4 = mword_of_int 0x36e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc2.
    set (m2 := <[Regidx (mword_of_int 10) := ret]> m1).
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* 0x36e  c.jr ra -- neither insert touches ra *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne m1 (Regidx (mword_of_int 10)) (Regidx (mword_of_int 1 : mword 5)) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 22) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx)
                   = ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra2. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uk_cjr C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M m2 (mword_of_int 0x36e)
              (mword_of_int 1 : mword 5) (m !!! Regidx ra_idx)
              (UI ui_sync_36e M Htext Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    iApply ("Hcont" $! ret).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* main @0x0: the gcc prologue (c.addi sp,-16; c.sdsp ra,8(sp);         *)
  (* c.sdsp s0,0(sp); c.addi4spn s0,sp,16), jal sync, c.li a0,0, jal      *)
  (* exit.  DIVERGES.                                                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_main (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    uk_xpage π (mword_of_int 0) ->
    sync_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack π M sp0 16 ->
    ⊢ ukc π M m (mword_of_int SyncSyms.main).
  Proof.
    intros Hx Htext Hsp Hst.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hsmain.
    (* the prologue's two [c.sdsp] slots: offsets d = 8 (ra) and d = 0 (s0)
       of main's own 16-byte budget, with every store-leaf side condition *)
    destruct (uk_stack_slot π M sp0 16 8 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot π M sp0 16 0 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof (uks_lo _ _ _ _ Hst) as Hflo.
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x00  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut π sz Hlo Hpm M m (mword_of_int 0x00)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16))
              (UI ui_sync_00 M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (E00 : add_vec_int (mword_of_int 0x00 : mword 64) 2 = mword_of_int 0x02)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E00.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0x02  c.sdsp ra,8(sp) ---- *)
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
    iApply (wp_uk_csdsp C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x02)
              (mword_of_int 1 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx)
              (UI ui_sync_02 M Htext Hx)
              Htg8 Hwra Hw8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hb").
    rewrite Hu8'.
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : sync_text_sub M2)
      by (unfold M2; apply sync_text_sub_store8; [ exact Htext | lia ]).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2 = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x04  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (uM_store8_is_Some M (uint sp0 - 8) (m !!! Regidx ra_idx) _
               (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M2 m1 (mword_of_int 0x04)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              (add_vec_int (add_vec_int sp0 (-16)) 0)
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (UI ui_sync_04 M2 Htext2 Hx)
              Htg0 Hws0 Hw0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hb").
    rewrite Hu0'.
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : sync_text_sub M3)
      by (unfold M3; apply sync_text_sub_store8; [ exact Htext2 | lia ]).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2 = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x06  c.addi4spn s0,sp,16 (s0 is never read again in main) ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M3 m1 (mword_of_int 0x06)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16)
              (UI ui_sync_06 M3 Htext3 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2 = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x08  jal ra,0x368 <sync> ---- *)
    assert (Htj : (mword_of_int SyncSyms.sync : mword 64)
                  = add_vec (mword_of_int 0x08)
                      (sign_extend' 64 (mword_of_int 864 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x0c : mword 64)
                  = add_vec_int (mword_of_int 0x08 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 π sz4 Hlo4 Hpm4 M3 m2 (mword_of_int 0x08)
              (mword_of_int 864 : mword 21) ra_idx
              (mword_of_int SyncSyms.sync) (mword_of_int 0x0c)
              (UI ui_sync_08 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x0c : mword 64)]> m2).
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- the call: sync() ---- *)
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0x0c)
      by exact (upd_eq m2 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x0c : mword 64))).
    assert (Hret2 : is_aligned_vaddr (Virtaddr (m3 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra3; vm_compute; reflexivity).
    iPoseProof (wp_ksync_sync_stub M3 m3 Hx Htext3 Hret2) as "Hstub".
    iApply ("Hstub" $! h5 C5 pt5 Rut5 sz5 with "[%] [%] Hb"); [ exact Hlo5 | exact Hpm5 | ].
    iIntros (ret).
    set (m4 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m3)).
    rewrite Hra3.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x0c  c.li a0,0 ---- *)
    assert (Hwa0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C6 pt6 Rut6 π sz6 Hlo6 Hpm6 M3 m4 (mword_of_int 0x0c)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (UI ui_sync_0c M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Hwa0
              with "Hb").
    set (m5 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m4).
    assert (E0c : add_vec_int (mword_of_int 0x0c : mword 64) 2 = mword_of_int 0x0e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x0e  jal ra,0x2c8 <exit> -- diverges ---- *)
    assert (Htj2 : (mword_of_int SyncSyms.exit : mword 64)
                   = add_vec (mword_of_int 0x0e)
                       (sign_extend' 64 (mword_of_int 698 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj2 : (mword_of_int 0x12 : mword 64)
                   = add_vec_int (mword_of_int 0x0e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C7 pt7 Rut7 π sz7 Hlo7 Hpm7 M3 m5 (mword_of_int 0x0e)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int SyncSyms.exit) (mword_of_int 0x12)
              (UI ui_sync_0e M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htj2 Hwj2
              ltac:(vm_compute; reflexivity)
              with "Hb").
    iApply (wp_ksync_exit_stub M3 _ Hx Htext3).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* start @0x12 -- the ELF entry: the same prologue at the 2-mod-4        *)
  (* parity, then jal main.  main DIVERGES, so the jal exit at 0x1e is     *)
  (* dead code.  THE TOP-LEVEL STATEMENT for the whole sync process.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_start (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    uk_xpage π (mword_of_int 0) ->
    sync_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack π M sp0 32 ->   (* start's own 16 + main's 16 *)
    ⊢ ukc π M m (mword_of_int SyncSyms.start).
  Proof.
    intros Hx Htext Hsp Hst.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hsstart.
    (* the 32-byte budget splits into start's own frame and main's, the
       latter sitting at the post-prologue sp = sp0-16 *)
    destruct (uk_stack_split π M sp0 32 16 16 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    destruct (uk_stack_slot π M sp0 16 8 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot π M sp0 16 0 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof (uks_lo _ _ _ _ Hstf) as Hflo.
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x12  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut π sz Hlo Hpm M m (mword_of_int 0x12)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16))
              (UI ui_sync_12 M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2 = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0x14  c.sdsp ra,8(sp) ---- *)
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
    iApply (wp_uk_csdsp C1 pt1 Rut1 π sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x14)
              (mword_of_int 1 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx)
              (UI ui_sync_14 M Htext Hx)
              Htg8 Hwra Hw8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hb").
    rewrite Hu8'.
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : sync_text_sub M2)
      by (unfold M2; apply sync_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom2 : forall a : Z, is_Some (M !! a) -> is_Some (M2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 2 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E14.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x16  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (Hdom2 _ (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 π sz2 Hlo2 Hpm2 M2 m1 (mword_of_int 0x16)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              (add_vec_int (add_vec_int sp0 (-16)) 0)
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (UI ui_sync_16 M2 Htext2 Hx)
              Htg0 Hws0 Hw0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hb").
    rewrite Hu0'.
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : sync_text_sub M3)
      by (unfold M3; apply sync_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall a : Z, is_Some (M2 !! a) -> is_Some (M3 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M2 _ _ a Ha)).
    assert (E16 : add_vec_int (mword_of_int 0x16 : mword 64) 2 = mword_of_int 0x18)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E16.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x18  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 π sz3 Hlo3 Hpm3 M3 m1 (mword_of_int 0x18)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16)
              (UI ui_sync_18 M3 Htext3 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (E18 : add_vec_int (mword_of_int 0x18 : mword 64) 2 = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E18.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x1a  jal ra,0x0 <main> ---- *)
    assert (Htj : (mword_of_int SyncSyms.main : mword 64)
                  = add_vec (mword_of_int 0x1a)
                      (sign_extend' 64 (mword_of_int 2097126 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0x1e : mword 64)
                  = add_vec_int (mword_of_int 0x1a : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 π sz4 Hlo4 Hpm4 M3 m2 (mword_of_int 0x1a)
              (mword_of_int 2097126 : mword 21) ra_idx
              (mword_of_int SyncSyms.main) (mword_of_int 0x1e)
              (UI ui_sync_1a M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x1e : mword 64)]> m2).
    (* ---- the call: main() -- diverges, so the jal exit at 0x1e is dead ---- *)
    assert (Hsp3 : m3 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { exact (eq_trans
               (upd_ne m2 (Regidx ra_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int 0x1e : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m1 (Regidx (mword_of_int 8 : mword 5)) (Regidx sp_idx)
                     (regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16))
                     ltac:(vm_compute; discriminate))
                  (upd_eq m (Regidx sp_idx)
                     (regval_into_reg (add_vec_int sp0 (-16)))))). }
    assert (Hstm3 : uk_stack π M3 (add_vec_int sp0 (-16)) 16)
      by exact (uk_stack_dom π M2 M3 _ 16 Hdom3
                  (uk_stack_dom π M M2 _ 16 Hdom2 Hstm)).
    iApply (wp_ksync_main M3 m3 (add_vec_int sp0 (-16)) Hx Htext3 Hsp3 Hstm3).
  Qed.

End UkSync.
