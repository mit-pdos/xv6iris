(* ProofVirtioDiskRwC.v -- virtio_disk_rw, phases P3 (and onward).

   The continuation of ProofVirtioDiskRwB.v.  That file proves P2.3 and
   leaves the seam [vdrw_p2_exit] at +0x0b0; this file picks it up.

     P3   descriptor / header / status / info.b formatting  +0x0b0..+0x162
     P4   ring write, fence, and THE PUBLISH                +0x162..+0x186

   A THIRD file (rather than more of ProofVirtioDiskRwB.v) purely for build
   latency, exactly as the B file is a second one: the functor is re-opened
   over the same four callee module types and instantiates the B functor
   internally, so the phases compose as if they were one file.

   P3 is a chain of ~40 straight-line instructions, so it is cut into five
   Qed-SEALED chunk lemmas of 8..14 instructions each (optimization.md: a
   monolithic threading proof grows super-linearly in #instructions).  Each
   chunk states the next one's precondition as its postcondition, in the
   ∀-continuation form -- an abstract output register file plus the handful
   of live-register equations, never a [let]-chain.

   P4/P5/P6 follow in the D/E/F files.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.
 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import WpAuipc.
Require Import WpSconfAlu WpSconfMem.
Require Import WpSmodeHalf.
Require Import DiskPtsto DiskInv.
Require Import WpVirtioDiskRwDecode.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.
Require Import VirtioDiskRwDefs.

(* ===================================================================== *)
(* §2  P3 -- +0x0b0 .. +0x162, the chain formatting.                      *)
(*                                                                       *)
(* All plain owned stores into the three descriptor bundles P2.3 handed   *)
(* over, plus [b->disk] out of the caller's [buf_own].  No invariant is   *)
(* opened and no callee is called, so this whole phase lives in a plain   *)
(* Section -- the functor re-opening happens only where P4 meets the      *)
(* protocol.                                                             *)
(* ===================================================================== *)

Section ProofVirtioDiskRwC.
  Context `{!riscvGS Σ, !sieG Σ, !diskGhostG Σ}.
  Context `{CID : CpuId}.

  Notation VRW := KernelSyms.virtio_disk_rw.

  Notation Rz  := (mword_of_int 0  : mword 5).
  Notation Rs0 := (mword_of_int 8  : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Ra6 := (mword_of_int 16 : mword 5).
  Notation Ra7 := (mword_of_int 17 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* [Regidx r <> Regidx k] for a SYMBOLIC callee-saved [r] (hypothesis in
     context) and a concrete temporary [k]: the discharge every
     cs-preservation obligation of a chunk's output needs. *)
  Local Ltac csne :=
    apply not_eq_sym, is_cs_idx_true_neq; [ vm_compute; reflexivity | assumption ].

  Local Ltac pcstep :=
    apply bv_eq; vm_compute; reflexivity.

  (* =================================================================== *)
  (* P3a  +0x0b0 .. +0x0d8  --  ops[h] = { type, reserved, sector }       *)
  (*                                                                     *)
  (*   lw a0,idx[0] ; slli a3,a0,4 ; a5 := &disk ; a4 := &ops[h]-8        *)
  (*   snez a2,s6 ; c.sw a2,8(a4) ; sw x0,12(a4) ; sd s7,16(a4)           *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3a (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (sp0 : Arch.pa) (h : nat)
      (wr sector : SailStdpp.Values.mword 64)
      (ty0 res0 : SailStdpp.Values.mword 32) (sec0 : SailStdpp.Values.mword 64) :
    (h < 8)%nat ->
    M !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Rs6 = wr ->
    M !!! Regidx Rs7 = sector ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x0b0) : mword 64) -∗
    pa_stk sp0 12 ↦₄ (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32) -∗
    d_ops h ↦₄ ty0 -∗
    pa_add disk_base (168 + 16 * h + 4) ↦₄ res0 -∗
    pa_add disk_base (168 + 16 * h + 8) ↦₈ sec0 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra3 = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x0d8) : mword 64) -∗
        pa_stk sp0 12 ↦₄ (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32) -∗
        d_ops h ↦₄ vdrw_ty wr -∗
        pa_add disk_base (168 + 16 * h + 4) ↦₄ (mword_of_int 0 : SailStdpp.Values.mword 32) -∗
        pa_add disk_base (168 + 16 * h + 8) ↦₈ sector -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hh8 Hs0 Hs6 Hs7.
    iIntros "Hcg #Htext Hpc Hidx Hty Hres Hsec Hcont".
    iPoseProof (rwi_0b0 with "Htext") as "Hi0b0".
    iPoseProof (rwi_0b4 with "Htext") as "Hi0b4".
    iPoseProof (rwi_0b8 with "Htext") as "Hi0b8".
    iPoseProof (rwi_0bc with "Htext") as "Hi0bc".
    iPoseProof (rwi_0c0 with "Htext") as "Hi0c0".
    iPoseProof (rwi_0c4 with "Htext") as "Hi0c4".
    iPoseProof (rwi_0c8 with "Htext") as "Hi0c8".
    iPoseProof (rwi_0ca with "Htext") as "Hi0ca".
    iPoseProof (rwi_0ce with "Htext") as "Hi0ce".
    iPoseProof (rwi_0d0 with "Htext") as "Hi0d0".
    iPoseProof (rwi_0d4 with "Htext") as "Hi0d4".
    (* ---- +0x0b0  lw a0,-96(s0) ---- *)
    assert (Hidxa : add_vec (M !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4000 : mword 12))
                    = (pa_stk sp0 12 : SailStdpp.Values.mword 64))
      by (rewrite Hs0; apply vdrw_idx0_addr).
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (VRW + 0x0b0) : mword 64) Ra0 Rs0
              (mword_of_int 4000 : mword 12) M av
              (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0b0 [Hidx] [-]").
    { iEval (rewrite Hidxa). iExact "Hidx". }
    iIntros "Hcg Hpc Hidx". iEval (rewrite Hidxa) in "Hidx".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32))]> M).
    change (<[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 32))]> M)
      with N1.
    assert (HN1a0 : N1 !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /N1 upd_eq; exact (vdrwc_sext32 h Hh8)).
    assert (Hp0b4 : add_vec_int (mword_of_int (VRW + 0x0b0) : mword 64) 4
                    = mword_of_int (VRW + 0x0b4)) by pcstep.
    iEval (rewrite Hp0b4) in "Hpc".
    (* ---- +0x0b4  slli a3,a0,4 ---- *)
    iApply (wp_slli_s_sconf γ Φ (mword_of_int (VRW + 0x0b4) : mword 64) Ra3 Ra0
              (mword_of_int 4 : mword 6)
              (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) N1 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /N1 upd_eq; exact (vdrwc_slli4 h Hh8))
              with "Hcg Hpc Hi0b4 [-]").
    iIntros "Hcg Hpc".
    set (N2 := <[Regidx Ra3 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> N1).
    change (<[Regidx Ra3 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> N1) with N2.
    assert (Hp0b8 : add_vec_int (mword_of_int (VRW + 0x0b4) : mword 64) 4
                    = mword_of_int (VRW + 0x0b8)) by pcstep.
    iEval (rewrite Hp0b8) in "Hpc".
    (* ---- +0x0b8 / +0x0bc  a5 := &disk ---- *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VRW + 0x0b8) : mword 64) Ra5
              (mword_of_int 30 : mword 20) N2 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0b8 [-]").
    iIntros "Hcg Hpc".
    set (N3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (VRW + 0x0b8) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (VRW + 0x0b8) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> N2) with N3.
    assert (Hp0bc : add_vec_int (mword_of_int (VRW + 0x0b8) : mword 64) 4
                    = mword_of_int (VRW + 0x0bc)) by pcstep.
    iEval (rewrite Hp0bc) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x0bc) : mword 64) Ra5 Ra5
              (mword_of_int 3088 : mword 12) N3 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0bc [-]").
    iIntros "Hcg Hpc".
    set (N4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (N3 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 3088 : mword 12)))]> N3).
    change (<[Regidx Ra5 := regval_into_reg
                  (add_vec (N3 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 3088 : mword 12)))]> N3) with N4.
    assert (HN4a5 : N4 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_eq /N3 upd_eq. unfold disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (HN4a0 : N4 !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. exact HN1a0. }
    assert (Hp0c0 : add_vec_int (mword_of_int (VRW + 0x0bc) : mword 64) 4
                    = mword_of_int (VRW + 0x0c0)) by pcstep.
    iEval (rewrite Hp0c0) in "Hpc".
    (* ---- +0x0c0 / +0x0c4 / +0x0c8  a4 := &disk + 160 + 16h ---- *)
    iApply (wp_slli_s_sconf γ Φ (mword_of_int (VRW + 0x0c0) : mword 64) Ra4 Ra0
              (mword_of_int 4 : mword 6)
              (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) N4 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HN4a0; exact (vdrwc_slli4' h Hh8))
              with "Hcg Hpc Hi0c0 [-]").
    iIntros "Hcg Hpc".
    set (N5 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> N4).
    change (<[Regidx Ra4 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> N4) with N5.
    assert (Hp0c4 : add_vec_int (mword_of_int (VRW + 0x0c0) : mword 64) 4
                    = mword_of_int (VRW + 0x0c4)) by pcstep.
    iEval (rewrite Hp0c4) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x0c4) : mword 64) Ra4 Ra4
              (mword_of_int 160 : mword 12) N5 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c4 [-]").
    iIntros "Hcg Hpc".
    set (N6 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (N5 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)))]> N5).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (N5 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 160 : mword 12)))]> N5) with N6.
    assert (HN6a4 : N6 !!! Regidx Ra4
                    = (mword_of_int (16 * Z.of_nat h + 160) : SailStdpp.Values.mword 64)).
    { rewrite /N6 upd_eq /N5 upd_eq vdrwc_sx160.
      exact (vdrwc_moi2 (16 * Z.of_nat h) 160). }
    assert (HN6a5 : N6 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq]. exact HN4a5. }
    assert (Hp0c8 : add_vec_int (mword_of_int (VRW + 0x0c4) : mword 64) 4
                    = mword_of_int (VRW + 0x0c8)) by pcstep.
    iEval (rewrite Hp0c8) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x0c8) : mword 64) Ra4 Ra5 N6 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c8 [-]").
    iIntros "Hcg Hpc".
    set (N7 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (N6 !!! Regidx Ra4) (N6 !!! Regidx Ra5))]> N6).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (N6 !!! Regidx Ra4) (N6 !!! Regidx Ra5))]> N6) with N7.
    assert (HN7a4 : N7 !!! Regidx Ra4
                    = add_vec (mword_of_int (16 * Z.of_nat h + 160)
                                 : SailStdpp.Values.mword 64)
                              (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N7 upd_eq HN6a4 HN6a5; reflexivity).
    assert (HN7s6 : N7 !!! Regidx Rs6 = wr).
    { rewrite /N7 upd_ne; [| reg_neq]. rewrite /N6 upd_ne; [| reg_neq].
      rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
      rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
      rewrite /N1 upd_ne; [| reg_neq]. exact Hs6. }
    assert (Hp0ca : add_vec_int (mword_of_int (VRW + 0x0c8) : mword 64) 2
                    = mword_of_int (VRW + 0x0ca)) by pcstep.
    iEval (rewrite Hp0ca) in "Hpc".
    (* ---- +0x0ca  snez a2,s6 ---- *)
    iDestruct (sie_cap_gpr_x0 γ N7 av (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
    iApply (wp_sltu_s_sconf γ Φ (mword_of_int (VRW + 0x0ca) : mword 64) Ra2 Rz Rs6
              (vdrw_ty64 wr) N7 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hz0 HN7s6; reflexivity)
              with "Hcg Hpc Hi0ca [-]").
    iIntros "Hcg Hpc".
    set (N8 := <[Regidx Ra2 := regval_into_reg (vdrw_ty64 wr)]> N7).
    change (<[Regidx Ra2 := regval_into_reg (vdrw_ty64 wr)]> N7) with N8.
    assert (HN8a4 : N8 !!! Regidx Ra4
                    = add_vec (mword_of_int (16 * Z.of_nat h + 160)
                                 : SailStdpp.Values.mword 64)
                              (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /N8 upd_ne; [| reg_neq]; exact HN7a4).
    assert (HN8a2 : N8 !!! Regidx Ra2 = vdrw_ty64 wr) by (rewrite /N8; apply upd_eq).
    assert (Hp0ce : add_vec_int (mword_of_int (VRW + 0x0ca) : mword 64) 4
                    = mword_of_int (VRW + 0x0ce)) by pcstep.
    iEval (rewrite Hp0ce) in "Hpc".
    (* ---- +0x0ce  c.sw a2,8(a4)   ops[h].type ---- *)
    assert (Haty : add_vec (N8 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (d_ops h : SailStdpp.Values.mword 64))
      by (rewrite HN8a4; apply vdrwc_ops_addr).
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (VRW + 0x0ce) : mword 64) Ra2 Ra4
              (mword_of_int 8 : mword 12) N8 av ty0 with "Hcg Hpc Hi0ce [Hty] [-]").
    { iEval (rewrite Haty). iExact "Hty". }
    iIntros "Hcg Hpc Hty".
    iEval (rewrite Haty) in "Hty".
    iEval (rewrite HN8a2 -/(vdrw_ty wr)) in "Hty".
    assert (Hp0d0 : add_vec_int (mword_of_int (VRW + 0x0ce) : mword 64) 2
                    = mword_of_int (VRW + 0x0d0)) by pcstep.
    iEval (rewrite Hp0d0) in "Hpc".
    (* ---- +0x0d0  sw x0,12(a4)   ops[h].reserved ---- *)
    assert (Hares : add_vec (N8 !!! Regidx Ra4)
                      (sign_extend' 64 (mword_of_int 12 : mword 12))
                    = (pa_add disk_base (168 + 16 * h + 4)%nat
                         : SailStdpp.Values.mword 64))
      by (rewrite HN8a4; apply vdrwc_ops_res_addr).
    iApply (wp_sw_zero_s_sconf γ Φ (mword_of_int (VRW + 0x0d0) : mword 64) Ra4
              (mword_of_int 12 : mword 12) N8 av res0 with "Hcg Hpc Hi0d0 [Hres] [-]").
    { iEval (rewrite Hares). iExact "Hres". }
    iIntros "Hcg Hpc Hres". iEval (rewrite Hares) in "Hres".
    assert (Hp0d4 : add_vec_int (mword_of_int (VRW + 0x0d0) : mword 64) 4
                    = mword_of_int (VRW + 0x0d4)) by pcstep.
    iEval (rewrite Hp0d4) in "Hpc".
    (* ---- +0x0d4  sd s7,16(a4)   ops[h].sector ---- *)
    assert (HN8s7 : N8 !!! Regidx Rs7 = sector).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Hs7. }
    assert (Hasec : add_vec (N8 !!! Regidx Ra4)
                      (sign_extend' 64 (mword_of_int 16 : mword 12))
                    = (pa_add disk_base (168 + 16 * h + 8)%nat
                         : SailStdpp.Values.mword 64))
      by (rewrite HN8a4; apply vdrwc_ops_sec_addr).
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (VRW + 0x0d4) : mword 64) Rs7 Ra4
              (mword_of_int 16 : mword 12) N8 av sec0 with "Hcg Hpc Hi0d4 [Hsec] [-]").
    { iEval (rewrite Hasec). iExact "Hsec". }
    iIntros "Hcg Hpc Hsec".
    iEval (rewrite Hasec HN8s7) in "Hsec".
    assert (Hp0d8 : add_vec_int (mword_of_int (VRW + 0x0d4) : mword 64) 4
                    = mword_of_int (VRW + 0x0d8)) by pcstep.
    iEval (rewrite Hp0d8) in "Hpc".
    (* ---- the seam ---- *)
    iApply ("Hcont" $! N8 with "[%] Hcg Hpc Hidx Hty Hres Hsec").
    split_and!.
    - intros r Hr.
      rewrite /N8 upd_ne; [| csne]. rewrite /N7 upd_ne; [| csne].
      rewrite /N6 upd_ne; [| csne]. rewrite /N5 upd_ne; [| csne].
      rewrite /N4 upd_ne; [| csne]. rewrite /N3 upd_ne; [| csne].
      rewrite /N2 upd_ne; [| csne]. rewrite /N1 upd_ne; [| csne]. reflexivity.
    - rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      exact HN4a0.
    - rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2; apply upd_eq.
    - rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      exact HN6a5.
  Qed.

  (* =================================================================== *)
  (* P3b  +0x0d8 .. +0x0f6  --  desc[h].{addr,len,flags}                  *)
  (*                                                                     *)
  (*   a4 := disk.desc + 16h ; a2 := &ops[h] ; c.sd a2,0(a4)             *)
  (*   a6 := disk.desc + 16h ; c.li a4,16 ; sw a4,8(a6)                  *)
  (*   c.li a1,1 ; sh a1,12(a6)                                          *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3b (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (pd : SailStdpp.Values.mword 64) (h : nat)
      (va0 : SailStdpp.Values.mword 64) (vl0 : SailStdpp.Values.mword 32)
      (vf0 : SailStdpp.Values.mword 16) :
    M !!! Regidx Ra3 = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64) ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x0d8) : mword 64) -∗
    d_desc_ptr ↦₈□ pd -∗
    d_desc pd h ↦₈ va0 -∗
    pa_add pd (16 * h + 8) ↦₄ vl0 -∗
    pa_add pd (16 * h + 12) ↦₂ vf0 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = M !!! Regidx Ra0
         /\ M1 !!! Regidx Ra3 = (mword_of_int (16 * Z.of_nat h)
                                   : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra2 = pd
         /\ M1 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x0f6) : mword 64) -∗
        d_desc pd h ↦₈ (d_ops h : SailStdpp.Values.mword 64) -∗
        pa_add pd (16 * h + 8) ↦₄ Z_to_bv 32 16 -∗
        pa_add pd (16 * h + 12) ↦₂ Z_to_bv 16 1 -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Ha3 Ha5.
    iIntros "Hcg #Htext Hpc #Hdp Hda Hdl Hdf Hcont".
    iPoseProof (rwi_0d8 with "Htext") as "Hi0d8".
    iPoseProof (rwi_0da with "Htext") as "Hi0da".
    iPoseProof (rwi_0dc with "Htext") as "Hi0dc".
    iPoseProof (rwi_0e0 with "Htext") as "Hi0e0".
    iPoseProof (rwi_0e2 with "Htext") as "Hi0e2".
    iPoseProof (rwi_0e4 with "Htext") as "Hi0e4".
    iPoseProof (rwi_0e6 with "Htext") as "Hi0e6".
    iPoseProof (rwi_0ea with "Htext") as "Hi0ea".
    iPoseProof (rwi_0ec with "Htext") as "Hi0ec".
    iPoseProof (rwi_0f0 with "Htext") as "Hi0f0".
    iPoseProof (rwi_0f2 with "Htext") as "Hi0f2".
    assert (Hdpa : add_vec (M !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc_ptr : SailStdpp.Values.mword 64)).
    { rewrite Ha5 addv_sext0. unfold d_desc_ptr. rewrite pa_add_0. reflexivity. }
    (* ---- +0x0d8  c.ld a4,0(a5) ---- *)
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VRW + 0x0d8) : mword 64) Ra4 Ra5
              (mword_of_int 0 : mword 12) M av pd (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0d8 [] [-]").
    { iEval (rewrite Hdpa). iExact "Hdp". }
    iIntros "Hcg Hpc _".
    set (Q1 := <[Regidx Ra4 := regval_into_reg pd]> M).
    change (<[Regidx Ra4 := regval_into_reg pd]> M) with Q1.
    assert (Hp0da : add_vec_int (mword_of_int (VRW + 0x0d8) : mword 64) 2
                    = mword_of_int (VRW + 0x0da)) by pcstep.
    iEval (rewrite Hp0da) in "Hpc".
    assert (HQ1a3 : Q1 !!! Regidx Ra3
                    = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /Q1 upd_ne; [| reg_neq]; exact Ha3).
    assert (HQ1a4 : Q1 !!! Regidx Ra4 = pd) by (rewrite /Q1; apply upd_eq).
    (* ---- +0x0da  c.add a4,a3 ---- *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x0da) : mword 64) Ra4 Ra3 Q1 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0da [-]").
    iIntros "Hcg Hpc".
    set (Q2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (Q1 !!! Regidx Ra4) (Q1 !!! Regidx Ra3))]> Q1).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (Q1 !!! Regidx Ra4) (Q1 !!! Regidx Ra3))]> Q1) with Q2.
    assert (HQ2a4 : Q2 !!! Regidx Ra4 = (d_desc pd h : SailStdpp.Values.mword 64)).
    { rewrite /Q2 upd_eq HQ1a4 HQ1a3. apply vdrwc_desc_addr'. }
    assert (HQ2a3 : Q2 !!! Regidx Ra3
                    = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /Q2 upd_ne; [| reg_neq]; exact HQ1a3).
    assert (HQ2a5 : Q2 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [| reg_neq]. exact Ha5. }
    assert (Hp0dc : add_vec_int (mword_of_int (VRW + 0x0da) : mword 64) 2
                    = mword_of_int (VRW + 0x0dc)) by pcstep.
    iEval (rewrite Hp0dc) in "Hpc".
    (* ---- +0x0dc / +0x0e0  a2 := &ops[h] ---- *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x0dc) : mword 64) Ra2 Ra3
              (mword_of_int 168 : mword 12) Q2 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0dc [-]").
    iIntros "Hcg Hpc".
    set (Q3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Ra3)
                     (sign_extend' 64 (mword_of_int 168 : mword 12)))]> Q2).
    change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Ra3)
                     (sign_extend' 64 (mword_of_int 168 : mword 12)))]> Q2) with Q3.
    assert (HQ3a5 : Q3 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /Q3 upd_ne; [| reg_neq]; exact HQ2a5).
    assert (Hp0e0 : add_vec_int (mword_of_int (VRW + 0x0dc) : mword 64) 4
                    = mword_of_int (VRW + 0x0e0)) by pcstep.
    iEval (rewrite Hp0e0) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x0e0) : mword 64) Ra2 Ra5 Q3 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e0 [-]").
    iIntros "Hcg Hpc".
    set (Q4 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (Q3 !!! Regidx Ra2) (Q3 !!! Regidx Ra5))]> Q3).
    change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (Q3 !!! Regidx Ra2) (Q3 !!! Regidx Ra5))]> Q3) with Q4.
    assert (HQ4a2 : Q4 !!! Regidx Ra2 = (d_ops h : SailStdpp.Values.mword 64)).
    { rewrite /Q4 upd_eq HQ3a5 /Q3 upd_eq HQ2a3. apply vdrwc_ops_val. }
    assert (HQ4a4 : Q4 !!! Regidx Ra4 = (d_desc pd h : SailStdpp.Values.mword 64)).
    { rewrite /Q4 upd_ne; [| reg_neq]. rewrite /Q3 upd_ne; [| reg_neq]. exact HQ2a4. }
    assert (Hp0e2 : add_vec_int (mword_of_int (VRW + 0x0e0) : mword 64) 2
                    = mword_of_int (VRW + 0x0e2)) by pcstep.
    iEval (rewrite Hp0e2) in "Hpc".
    (* ---- +0x0e2  c.sd a2,0(a4)   desc[h].addr := &ops[h] ---- *)
    assert (Hada : add_vec (Q4 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc pd h : SailStdpp.Values.mword 64))
      by (rewrite HQ4a4 addv_sext0; reflexivity).
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (VRW + 0x0e2) : mword 64) Ra2 Ra4
              (mword_of_int 0 : mword 12) Q4 av va0 with "Hcg Hpc Hi0e2 [Hda] [-]").
    { iEval (rewrite Hada). iExact "Hda". }
    iIntros "Hcg Hpc Hda". iEval (rewrite Hada HQ4a2) in "Hda".
    assert (Hp0e4 : add_vec_int (mword_of_int (VRW + 0x0e2) : mword 64) 2
                    = mword_of_int (VRW + 0x0e4)) by pcstep.
    iEval (rewrite Hp0e4) in "Hpc".
    (* ---- +0x0e4  c.ld a2,0(a5) ---- *)
    assert (Hdpa4 : add_vec (Q4 !!! Regidx Ra5)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = (d_desc_ptr : SailStdpp.Values.mword 64)).
    { rewrite /Q4 upd_ne; [| reg_neq]. rewrite HQ3a5 addv_sext0.
      unfold d_desc_ptr. rewrite pa_add_0. reflexivity. }
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VRW + 0x0e4) : mword 64) Ra2 Ra5
              (mword_of_int 0 : mword 12) Q4 av pd (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e4 [] [-]").
    { iEval (rewrite Hdpa4). iExact "Hdp". }
    iIntros "Hcg Hpc _".
    set (Q5 := <[Regidx Ra2 := regval_into_reg pd]> Q4).
    change (<[Regidx Ra2 := regval_into_reg pd]> Q4) with Q5.
    assert (HQ5a2 : Q5 !!! Regidx Ra2 = pd) by (rewrite /Q5; apply upd_eq).
    assert (HQ5a3 : Q5 !!! Regidx Ra3
                    = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)).
    { rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
      rewrite /Q3 upd_ne; [| reg_neq]. exact HQ2a3. }
    assert (Hp0e6 : add_vec_int (mword_of_int (VRW + 0x0e4) : mword 64) 2
                    = mword_of_int (VRW + 0x0e6)) by pcstep.
    iEval (rewrite Hp0e6) in "Hpc".
    (* ---- +0x0e6  add a6,a2,a3 ---- *)
    iApply (wp_add_s_sconf γ Φ (mword_of_int (VRW + 0x0e6) : mword 64) Ra6 Ra2 Ra3
              (d_desc pd h : SailStdpp.Values.mword 64) Q5 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HQ5a2 HQ5a3; apply vdrwc_desc_addr')
              with "Hcg Hpc Hi0e6 [-]").
    iIntros "Hcg Hpc".
    set (Q6 := <[Regidx Ra6 := regval_into_reg
                  (d_desc pd h : SailStdpp.Values.mword 64)]> Q5).
    change (<[Regidx Ra6 := regval_into_reg
                  (d_desc pd h : SailStdpp.Values.mword 64)]> Q5) with Q6.
    assert (HQ6a6 : Q6 !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64))
      by (rewrite /Q6; apply upd_eq).
    assert (Hp0ea : add_vec_int (mword_of_int (VRW + 0x0e6) : mword 64) 4
                    = mword_of_int (VRW + 0x0ea)) by pcstep.
    iEval (rewrite Hp0ea) in "Hpc".
    (* ---- +0x0ea / +0x0ec  desc[h].len := 16 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x0ea) : mword 64) Ra4
              (mword_of_int 16 : mword 6) (mword_of_int 16 : SailStdpp.Values.mword 64)
              Q6 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwc_li16 with "Hcg Hpc Hi0ea [-]").
    iIntros "Hcg Hpc".
    set (Q7 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : SailStdpp.Values.mword 64)]> Q6).
    change (<[Regidx Ra4 := regval_into_reg
                  (mword_of_int 16 : SailStdpp.Values.mword 64)]> Q6) with Q7.
    assert (HQ7a6 : Q7 !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64))
      by (rewrite /Q7 upd_ne; [| reg_neq]; exact HQ6a6).
    assert (HQ7a4 : Q7 !!! Regidx Ra4 = (mword_of_int 16 : SailStdpp.Values.mword 64))
      by (rewrite /Q7; apply upd_eq).
    assert (Hp0ec : add_vec_int (mword_of_int (VRW + 0x0ea) : mword 64) 2
                    = mword_of_int (VRW + 0x0ec)) by pcstep.
    iEval (rewrite Hp0ec) in "Hpc".
    assert (Hadl : add_vec (Q7 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (pa_add pd (16 * h + 8)%nat : SailStdpp.Values.mword 64))
      by (rewrite HQ7a6; apply vdrwc_desc_len).
    iApply (wp_sw_s_sconf γ Φ (mword_of_int (VRW + 0x0ec) : mword 64) Ra4 Ra6
              (mword_of_int 8 : mword 12) Q7 av vl0 with "Hcg Hpc Hi0ec [Hdl] [-]").
    { iEval (rewrite Hadl). iExact "Hdl". }
    iIntros "Hcg Hpc Hdl".
    iEval (rewrite Hadl HQ7a4 vdrwc_t32_16) in "Hdl".
    assert (Hp0f0 : add_vec_int (mword_of_int (VRW + 0x0ec) : mword 64) 4
                    = mword_of_int (VRW + 0x0f0)) by pcstep.
    iEval (rewrite Hp0f0) in "Hpc".
    (* ---- +0x0f0 / +0x0f2  desc[h].flags := 1 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x0f0) : mword 64) Ra1
              (mword_of_int 1 : mword 6) (mword_of_int (Z.of_nat 1) : SailStdpp.Values.mword 64)
              Q7 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwb_li1 with "Hcg Hpc Hi0f0 [-]").
    iIntros "Hcg Hpc".
    set (Q8 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int (Z.of_nat 1) : SailStdpp.Values.mword 64)]> Q7).
    change (<[Regidx Ra1 := regval_into_reg
                  (mword_of_int (Z.of_nat 1) : SailStdpp.Values.mword 64)]> Q7) with Q8.
    assert (HQ8a1 : Q8 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64))
      by (rewrite /Q8; apply upd_eq).
    assert (HQ8a6 : Q8 !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64))
      by (rewrite /Q8 upd_ne; [| reg_neq]; exact HQ7a6).
    assert (Hp0f2 : add_vec_int (mword_of_int (VRW + 0x0f0) : mword 64) 2
                    = mword_of_int (VRW + 0x0f2)) by pcstep.
    iEval (rewrite Hp0f2) in "Hpc".
    assert (Hadf : add_vec (Q8 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 12 : mword 12))
                   = (pa_add pd (16 * h + 12)%nat : SailStdpp.Values.mword 64))
      by (rewrite HQ8a6; apply vdrwc_desc_flags).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x0f2) : mword 64) Ra1 Ra6
              (mword_of_int 12 : mword 12) Q8 av vf0 with "Hcg Hpc Hi0f2 [Hdf] [-]").
    { iEval (rewrite Hadf). iExact "Hdf". }
    iIntros "Hcg Hpc Hdf".
    iEval (rewrite Hadf HQ8a1 vdrwc_t16_1) in "Hdf".
    assert (Hp0f6 : add_vec_int (mword_of_int (VRW + 0x0f2) : mword 64) 4
                    = mword_of_int (VRW + 0x0f6)) by pcstep.
    iEval (rewrite Hp0f6) in "Hpc".
    (* ---- the seam ---- *)
    iApply ("Hcont" $! Q8 with "[%] Hcg Hpc Hda Hdl Hdf").
    split_and!.
    - intros r Hr.
      rewrite /Q8 upd_ne; [| csne]. rewrite /Q7 upd_ne; [| csne].
      rewrite /Q6 upd_ne; [| csne]. rewrite /Q5 upd_ne; [| csne].
      rewrite /Q4 upd_ne; [| csne]. rewrite /Q3 upd_ne; [| csne].
      rewrite /Q2 upd_ne; [| csne]. rewrite /Q1 upd_ne; [| csne]. reflexivity.
    - rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [| reg_neq].
      rewrite /Q6 upd_ne; [| reg_neq]. rewrite /Q5 upd_ne; [| reg_neq].
      rewrite /Q4 upd_ne; [| reg_neq]. rewrite /Q3 upd_ne; [| reg_neq].
      rewrite /Q2 upd_ne; [| reg_neq]. rewrite /Q1 upd_ne; [| reg_neq]. reflexivity.
    - rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [| reg_neq].
      rewrite /Q6 upd_ne; [| reg_neq]. exact HQ5a3.
    - rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [| reg_neq].
      rewrite /Q6 upd_ne; [| reg_neq]. rewrite /Q5 upd_ne; [| reg_neq].
      rewrite /Q4 upd_ne; [| reg_neq]. exact HQ3a5.
    - exact HQ8a6.
    - rewrite /Q8 upd_ne; [| reg_neq]. rewrite /Q7 upd_ne; [| reg_neq].
      rewrite /Q6 upd_ne; [| reg_neq]. exact HQ5a2.
    - exact HQ8a1.
  Qed.

  (* =================================================================== *)
  (* P3c  +0x0f6 .. +0x124  --  desc[h].next and desc[m2].{addr,len,flags} *)
  (*                                                                     *)
  (*   lw a4,idx[1] ; sh a4,14(a6) ; a2 := &desc[m2] ; a6 := b->data      *)
  (*   sd a6,0(a2) ; a4 := &desc[m2] ; c.sw 1024,8(a4)                    *)
  (*   seqz/slliw/or ; sh a2,12(a4)                                       *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3c (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (pd : SailStdpp.Values.mword 64)
      (sp0 b : Arch.pa) (h m2 : nat) (wr : SailStdpp.Values.mword 64)
      (vn0 vf1 : SailStdpp.Values.mword 16) (va1 : SailStdpp.Values.mword 64)
      (vl1 : SailStdpp.Values.mword 32) :
    (m2 < 8)%nat ->
    M !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64) ->
    M !!! Regidx Rs6 = wr ->
    M !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra2 = pd ->
    M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64) ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x0f6) : mword 64) -∗
    d_desc_ptr ↦₈□ pd -∗
    pa_add (pa_stk sp0 12) 4 ↦₄ (mword_of_int (Z.of_nat m2) : SailStdpp.Values.mword 32) -∗
    pa_add pd (16 * h + 14) ↦₂ vn0 -∗
    d_desc pd m2 ↦₈ va1 -∗
    pa_add pd (16 * m2 + 8) ↦₄ vl1 -∗
    pa_add pd (16 * m2 + 12) ↦₂ vf1 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = M !!! Regidx Ra0
         /\ M1 !!! Regidx Ra3 = M !!! Regidx Ra3
         /\ M1 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra7 = pd⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x124) : mword 64) -∗
        pa_add (pa_stk sp0 12) 4 ↦₄ (mword_of_int (Z.of_nat m2)
                                       : SailStdpp.Values.mword 32) -∗
        pa_add pd (16 * h + 14) ↦₂ Z_to_bv 16 (Z.of_nat m2) -∗
        d_desc pd m2 ↦₈ (b_data b : SailStdpp.Values.mword 64) -∗
        pa_add pd (16 * m2 + 8) ↦₄ Z_to_bv 32 1024 -∗
        pa_add pd (16 * m2 + 12) ↦₂ vdrw_flags wr -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hm8 Hs0 Hs3 Hs6 Ha1 Ha2 Ha5 Ha6.
    iIntros "Hcg #Htext Hpc #Hdp Hidx Hdn Hda Hdl Hdf Hcont".
    iPoseProof (rwi_0f6 with "Htext") as "Hi0f6".
    iPoseProof (rwi_0fa with "Htext") as "Hi0fa".
    iPoseProof (rwi_0fe with "Htext") as "Hi0fe".
    iPoseProof (rwi_100 with "Htext") as "Hi100".
    iPoseProof (rwi_102 with "Htext") as "Hi102".
    iPoseProof (rwi_106 with "Htext") as "Hi106".
    iPoseProof (rwi_10a with "Htext") as "Hi10a".
    iPoseProof (rwi_10e with "Htext") as "Hi10e".
    iPoseProof (rwi_110 with "Htext") as "Hi110".
    iPoseProof (rwi_114 with "Htext") as "Hi114".
    iPoseProof (rwi_116 with "Htext") as "Hi116".
    iPoseProof (rwi_11a with "Htext") as "Hi11a".
    iPoseProof (rwi_11e with "Htext") as "Hi11e".
    iPoseProof (rwi_120 with "Htext") as "Hi120".
    (* ---- +0x0f6  lw a4,-92(s0) ---- *)
    assert (Hidxa : add_vec (M !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4004 : mword 12))
                    = (pa_add (pa_stk sp0 12) 4 : SailStdpp.Values.mword 64))
      by (rewrite Hs0; apply vdrwc_idx1_addr).
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (VRW + 0x0f6) : mword 64) Ra4 Rs0
              (mword_of_int 4004 : mword 12) M av
              (mword_of_int (Z.of_nat m2) : SailStdpp.Values.mword 32) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0f6 [Hidx] [-]").
    { iEval (rewrite Hidxa). iExact "Hidx". }
    iIntros "Hcg Hpc Hidx". iEval (rewrite Hidxa) in "Hidx".
    set (R1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat m2)
                                      : SailStdpp.Values.mword 32))]> M).
    change (<[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat m2)
                                      : SailStdpp.Values.mword 32))]> M) with R1.
    assert (HR1a6 : R1 !!! Regidx Ra6 = (d_desc pd h : SailStdpp.Values.mword 64))
      by (rewrite /R1 upd_ne; [| reg_neq]; exact Ha6).
    assert (Hp0fa : add_vec_int (mword_of_int (VRW + 0x0f6) : mword 64) 4
                    = mword_of_int (VRW + 0x0fa)) by pcstep.
    iEval (rewrite Hp0fa) in "Hpc".
    (* ---- +0x0fa  sh a4,14(a6)   desc[h].next := m2 ---- *)
    assert (Hadn : add_vec (R1 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 14 : mword 12))
                   = (pa_add pd (16 * h + 14)%nat : SailStdpp.Values.mword 64))
      by (rewrite HR1a6; apply vdrwc_desc_next).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x0fa) : mword 64) Ra4 Ra6
              (mword_of_int 14 : mword 12) R1 av vn0 with "Hcg Hpc Hi0fa [Hdn] [-]").
    { iEval (rewrite Hadn). iExact "Hdn". }
    iIntros "Hcg Hpc Hdn".
    iEval (rewrite Hadn) in "Hdn".
    iEval (rewrite /R1 upd_eq (vdrwc_trunc16_idx m2 Hm8)) in "Hdn".
    assert (Hp0fe : add_vec_int (mword_of_int (VRW + 0x0fa) : mword 64) 4
                    = mword_of_int (VRW + 0x0fe)) by pcstep.
    iEval (rewrite Hp0fe) in "Hpc".
    (* ---- +0x0fe  c.slli a4,a4,4 ---- *)
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (VRW + 0x0fe) : mword 64)
              (Regidx Ra4) Ra4 (mword_of_int 4 : mword 6) R1 av
              eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0fe [-]").
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (R1 !!! Regidx Ra4)
                     (subrange_vec_dec (mword_of_int 4 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> R1).
    change (<[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (R1 !!! Regidx Ra4)
                     (subrange_vec_dec (mword_of_int 4 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> R1) with R2.
    assert (HR2a4 : R2 !!! Regidx Ra4
                    = (mword_of_int (16 * Z.of_nat m2) : SailStdpp.Values.mword 64)).
    { rewrite /R2 upd_eq /R1 upd_eq. exact (vdrwc_slli4 m2 Hm8). }
    assert (HR2a2 : R2 !!! Regidx Ra2 = pd).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact Ha2. }
    assert (Hp100 : add_vec_int (mword_of_int (VRW + 0x0fe) : mword 64) 2
                    = mword_of_int (VRW + 0x100)) by pcstep.
    iEval (rewrite Hp100) in "Hpc".
    (* ---- +0x100  c.add a2,a4 ---- *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x100) : mword 64) Ra2 Ra4 R2 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi100 [-]").
    iIntros "Hcg Hpc".
    set (R3 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (R2 !!! Regidx Ra2) (R2 !!! Regidx Ra4))]> R2).
    change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (R2 !!! Regidx Ra2) (R2 !!! Regidx Ra4))]> R2) with R3.
    assert (HR3a2 : R3 !!! Regidx Ra2 = (d_desc pd m2 : SailStdpp.Values.mword 64)).
    { rewrite /R3 upd_eq HR2a2 HR2a4. apply vdrwc_desc_addr'. }
    assert (HR3s3 : R3 !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64)).
    { rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [| reg_neq]. exact Hs3. }
    assert (Hp102 : add_vec_int (mword_of_int (VRW + 0x100) : mword 64) 2
                    = mword_of_int (VRW + 0x102)) by pcstep.
    iEval (rewrite Hp102) in "Hpc".
    (* ---- +0x102  addi a6,s3,88   a6 := b->data ---- *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x102) : mword 64) Ra6 Rs3
              (mword_of_int 88 : mword 12) R3 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi102 [-]").
    iIntros "Hcg Hpc".
    set (R4 := <[Regidx Ra6 := regval_into_reg
                  (add_vec (R3 !!! Regidx Rs3)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> R3).
    change (<[Regidx Ra6 := regval_into_reg
                  (add_vec (R3 !!! Regidx Rs3)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> R3) with R4.
    assert (HR4a6 : R4 !!! Regidx Ra6 = (b_data b : SailStdpp.Values.mword 64)).
    { rewrite /R4 upd_eq HR3s3. apply vdrwc_bdata_val. }
    assert (HR4a2 : R4 !!! Regidx Ra2 = (d_desc pd m2 : SailStdpp.Values.mword 64))
      by (rewrite /R4 upd_ne; [| reg_neq]; exact HR3a2).
    assert (Hp106 : add_vec_int (mword_of_int (VRW + 0x102) : mword 64) 4
                    = mword_of_int (VRW + 0x106)) by pcstep.
    iEval (rewrite Hp106) in "Hpc".
    (* ---- +0x106  sd a6,0(a2)   desc[m2].addr := b->data ---- *)
    assert (Hada : add_vec (R4 !!! Regidx Ra2)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc pd m2 : SailStdpp.Values.mword 64))
      by (rewrite HR4a2 addv_sext0; reflexivity).
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (VRW + 0x106) : mword 64) Ra6 Ra2
              (mword_of_int 0 : mword 12) R4 av va1 with "Hcg Hpc Hi106 [Hda] [-]").
    { iEval (rewrite Hada). iExact "Hda". }
    iIntros "Hcg Hpc Hda". iEval (rewrite Hada HR4a6) in "Hda".
    assert (Hp10a : add_vec_int (mword_of_int (VRW + 0x106) : mword 64) 4
                    = mword_of_int (VRW + 0x10a)) by pcstep.
    iEval (rewrite Hp10a) in "Hpc".
    (* ---- +0x10a  ld a7,0(a5) ---- *)
    assert (HR4a5 : R4 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact Ha5. }
    assert (Hdpa : add_vec (R4 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc_ptr : SailStdpp.Values.mword 64)).
    { rewrite HR4a5 addv_sext0. unfold d_desc_ptr. rewrite pa_add_0. reflexivity. }
    iApply (wp_ld_s_sconf γ Φ (mword_of_int (VRW + 0x10a) : mword 64) Ra7 Ra5
              (mword_of_int 0 : mword 12) R4 av pd (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10a [] [-]").
    { iEval (rewrite Hdpa). iExact "Hdp". }
    iIntros "Hcg Hpc _".
    set (R5 := <[Regidx Ra7 := regval_into_reg pd]> R4).
    change (<[Regidx Ra7 := regval_into_reg pd]> R4) with R5.
    assert (HR5a7 : R5 !!! Regidx Ra7 = pd) by (rewrite /R5; apply upd_eq).
    assert (HR5a4 : R5 !!! Regidx Ra4
                    = (mword_of_int (16 * Z.of_nat m2) : SailStdpp.Values.mword 64)).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. exact HR2a4. }
    assert (Hp10e : add_vec_int (mword_of_int (VRW + 0x10a) : mword 64) 4
                    = mword_of_int (VRW + 0x10e)) by pcstep.
    iEval (rewrite Hp10e) in "Hpc".
    (* ---- +0x10e  c.add a4,a7   a4 := &desc[m2] ---- *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x10e) : mword 64) Ra4 Ra7 R5 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10e [-]").
    iIntros "Hcg Hpc".
    set (R6 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (R5 !!! Regidx Ra4) (R5 !!! Regidx Ra7))]> R5).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (R5 !!! Regidx Ra4) (R5 !!! Regidx Ra7))]> R5) with R6.
    assert (HR6a4 : R6 !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64)).
    { rewrite /R6 upd_eq HR5a4 HR5a7. apply vdrwc_desc_addr. }
    assert (Hp110 : add_vec_int (mword_of_int (VRW + 0x10e) : mword 64) 2
                    = mword_of_int (VRW + 0x110)) by pcstep.
    iEval (rewrite Hp110) in "Hpc".
    (* ---- +0x110 / +0x114  desc[m2].len := 1024 ---- *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x110) : mword 64) Ra2 Rz
              (mword_of_int 1024 : mword 12) R6 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi110 [-]").
    iIntros "Hcg Hpc".
    set (R7 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (R6 !!! Regidx Rz)
                     (sign_extend' 64 (mword_of_int 1024 : mword 12)))]> R6).
    change (<[Regidx Ra2 := regval_into_reg
                  (add_vec (R6 !!! Regidx Rz)
                     (sign_extend' 64 (mword_of_int 1024 : mword 12)))]> R6) with R7.
    iDestruct (sie_cap_gpr_x0 γ R7 av (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
    assert (Hz0' : R6 !!! Regidx Rz = (zero_reg : SailStdpp.Values.mword 64)).
    { rewrite -Hz0. rewrite /R7 upd_ne; [| reg_neq]. reflexivity. }
    assert (HR7a2 : R7 !!! Regidx Ra2
                    = add_vec (zero_reg : SailStdpp.Values.mword 64)
                        (sign_extend' 64 (mword_of_int 1024 : mword 12)))
      by (rewrite /R7 upd_eq Hz0'; reflexivity).
    assert (HR7a4 : R7 !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64))
      by (rewrite /R7 upd_ne; [| reg_neq]; exact HR6a4).
    assert (Hp114 : add_vec_int (mword_of_int (VRW + 0x110) : mword 64) 4
                    = mword_of_int (VRW + 0x114)) by pcstep.
    iEval (rewrite Hp114) in "Hpc".
    assert (Hadl : add_vec (R7 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (pa_add pd (16 * m2 + 8)%nat : SailStdpp.Values.mword 64))
      by (rewrite HR7a4; apply vdrwc_desc_len).
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (VRW + 0x114) : mword 64) Ra2 Ra4
              (mword_of_int 8 : mword 12) R7 av vl1 with "Hcg Hpc Hi114 [Hdl] [-]").
    { iEval (rewrite Hadl). iExact "Hdl". }
    iIntros "Hcg Hpc Hdl".
    iEval (rewrite Hadl HR7a2 vdrwc_t32_1024) in "Hdl".
    assert (Hp116 : add_vec_int (mword_of_int (VRW + 0x114) : mword 64) 2
                    = mword_of_int (VRW + 0x116)) by pcstep.
    iEval (rewrite Hp116) in "Hpc".
    (* ---- +0x116 / +0x11a / +0x11e  the direction flags ---- *)
    assert (HR7s6 : R7 !!! Regidx Rs6 = wr).
    { rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
      rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [| reg_neq]. exact Hs6. }
    iApply (wp_sltiu_s_sconf γ Φ (mword_of_int (VRW + 0x116) : mword 64) Ra2 Rs6
              (mword_of_int 1 : mword 12) (vdrw_fl0 wr) R7 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HR7s6; reflexivity) with "Hcg Hpc Hi116 [-]").
    iIntros "Hcg Hpc".
    set (R8 := <[Regidx Ra2 := regval_into_reg (vdrw_fl0 wr)]> R7).
    change (<[Regidx Ra2 := regval_into_reg (vdrw_fl0 wr)]> R7) with R8.
    assert (Hp11a : add_vec_int (mword_of_int (VRW + 0x116) : mword 64) 4
                    = mword_of_int (VRW + 0x11a)) by pcstep.
    iEval (rewrite Hp11a) in "Hpc".
    iApply (wp_slliw_s_sconf γ Φ (mword_of_int (VRW + 0x11a) : mword 64) Ra2 Ra2
              (mword_of_int 1 : mword 5) (vdrw_fl1 wr) R8 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite /R8 upd_eq; reflexivity) with "Hcg Hpc Hi11a [-]").
    iIntros "Hcg Hpc".
    set (R9 := <[Regidx Ra2 := regval_into_reg (vdrw_fl1 wr)]> R8).
    change (<[Regidx Ra2 := regval_into_reg (vdrw_fl1 wr)]> R8) with R9.
    assert (HR9a1 : R9 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /R9 upd_ne; [| reg_neq]. rewrite /R8 upd_ne; [| reg_neq].
      rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq].
      rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq].
      rewrite /R1 upd_ne; [| reg_neq]. exact Ha1. }
    assert (Hp11e : add_vec_int (mword_of_int (VRW + 0x11a) : mword 64) 4
                    = mword_of_int (VRW + 0x11e)) by pcstep.
    iEval (rewrite Hp11e) in "Hpc".
    iApply (wp_cor_s_sconf γ Φ (mword_of_int (VRW + 0x11e) : mword 64) Ra2 Ra2 Ra1
              (vdrw_fl2 wr) R9 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HR9a1 /R9 upd_eq; reflexivity) with "Hcg Hpc Hi11e [-]").
    iIntros "Hcg Hpc".
    set (RA := <[Regidx Ra2 := regval_into_reg (vdrw_fl2 wr)]> R9).
    change (<[Regidx Ra2 := regval_into_reg (vdrw_fl2 wr)]> R9) with RA.
    assert (HRAa2 : RA !!! Regidx Ra2 = vdrw_fl2 wr) by (rewrite /RA; apply upd_eq).
    assert (HRAa4 : RA !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64)).
    { rewrite /RA upd_ne; [| reg_neq]. rewrite /R9 upd_ne; [| reg_neq].
      rewrite /R8 upd_ne; [| reg_neq]. exact HR7a4. }
    assert (Hp120 : add_vec_int (mword_of_int (VRW + 0x11e) : mword 64) 2
                    = mword_of_int (VRW + 0x120)) by pcstep.
    iEval (rewrite Hp120) in "Hpc".
    (* ---- +0x120  sh a2,12(a4)   desc[m2].flags ---- *)
    assert (Hadf : add_vec (RA !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 12 : mword 12))
                   = (pa_add pd (16 * m2 + 12)%nat : SailStdpp.Values.mword 64))
      by (rewrite HRAa4; apply vdrwc_desc_flags).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x120) : mword 64) Ra2 Ra4
              (mword_of_int 12 : mword 12) RA av vf1 with "Hcg Hpc Hi120 [Hdf] [-]").
    { iEval (rewrite Hadf). iExact "Hdf". }
    iIntros "Hcg Hpc Hdf".
    iEval (rewrite Hadf HRAa2 -/(vdrw_flags wr)) in "Hdf".
    assert (Hp124 : add_vec_int (mword_of_int (VRW + 0x120) : mword 64) 4
                    = mword_of_int (VRW + 0x124)) by pcstep.
    iEval (rewrite Hp124) in "Hpc".
    (* ---- the seam ---- *)
    iApply ("Hcont" $! RA with "[%] Hcg Hpc Hidx Hdn Hda Hdl Hdf").
    split_and!.
    - intros r Hr.
      rewrite /RA upd_ne; [| csne]. rewrite /R9 upd_ne; [| csne].
      rewrite /R8 upd_ne; [| csne]. rewrite /R7 upd_ne; [| csne].
      rewrite /R6 upd_ne; [| csne]. rewrite /R5 upd_ne; [| csne].
      rewrite /R4 upd_ne; [| csne]. rewrite /R3 upd_ne; [| csne].
      rewrite /R2 upd_ne; [| csne]. rewrite /R1 upd_ne; [| csne]. reflexivity.
    - rewrite /RA upd_ne; [| reg_neq]. rewrite /R9 upd_ne; [| reg_neq].
      rewrite /R8 upd_ne; [| reg_neq]. rewrite /R7 upd_ne; [| reg_neq].
      rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. reflexivity.
    - rewrite /RA upd_ne; [| reg_neq]. rewrite /R9 upd_ne; [| reg_neq].
      rewrite /R8 upd_ne; [| reg_neq]. rewrite /R7 upd_ne; [| reg_neq].
      rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. reflexivity.
    - rewrite /RA upd_ne; [| reg_neq]. exact HR9a1.
    - exact HRAa4.
    - rewrite /RA upd_ne; [| reg_neq]. rewrite /R9 upd_ne; [| reg_neq].
      rewrite /R8 upd_ne; [| reg_neq]. rewrite /R7 upd_ne; [| reg_neq].
      rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      exact HR4a5.
    - rewrite /RA upd_ne; [| reg_neq]. rewrite /R9 upd_ne; [| reg_neq].
      rewrite /R8 upd_ne; [| reg_neq]. rewrite /R7 upd_ne; [| reg_neq].
      rewrite /R6 upd_ne; [| reg_neq]. exact HR5a7.
  Qed.

  (* =================================================================== *)
  (* P3d  +0x124 .. +0x14a  --  desc[m2].next, info[h].status, desc[t].addr *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3d (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (pd : SailStdpp.Values.mword 64)
      (sp0 : Arch.pa) (h m2 t : nat)
      (vn1 : SailStdpp.Values.mword 16) (sb0 : bv 8)
      (va2 : SailStdpp.Values.mword 64) :
    (h < 8)%nat -> (t < 8)%nat ->
    M !!! Regidx Rs0 = (sp0 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra3 = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra7 = pd ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x124) : mword 64) -∗
    pa_stk sp0 11 ↦₄ (mword_of_int (Z.of_nat t) : SailStdpp.Values.mword 32) -∗
    pa_add pd (16 * m2 + 14) ↦₂ vn1 -∗
    d_info_status h ↦ₘ sb0 -∗
    d_desc pd t ↦₈ va2 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = M !!! Regidx Ra0
         /\ M1 !!! Regidx Ra1 = M !!! Regidx Ra1
         /\ M1 !!! Regidx Ra2 = (mword_of_int (16 * Z.of_nat t)
                                   : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra6 = add_vec (disk_base : SailStdpp.Values.mword 64)
                                        (mword_of_int (16 * Z.of_nat h + 32))⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x14a) : mword 64) -∗
        pa_stk sp0 11 ↦₄ (mword_of_int (Z.of_nat t) : SailStdpp.Values.mword 32) -∗
        pa_add pd (16 * m2 + 14) ↦₂ Z_to_bv 16 (Z.of_nat t) -∗
        d_info_status h ↦ₘ Z_to_bv 8 255 -∗
        d_desc pd t ↦₈ (d_info_status h : SailStdpp.Values.mword 64) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hh8 Ht8 Hs0 Ha0 Ha3 Ha4 Ha5 Ha7.
    iIntros "Hcg #Htext Hpc Hidx Hdn Hst Hda Hcont".
    iPoseProof (rwi_124 with "Htext") as "Hi124".
    iPoseProof (rwi_128 with "Htext") as "Hi128".
    iPoseProof (rwi_12c with "Htext") as "Hi12c".
    iPoseProof (rwi_130 with "Htext") as "Hi130".
    iPoseProof (rwi_134 with "Htext") as "Hi134".
    iPoseProof (rwi_136 with "Htext") as "Hi136".
    iPoseProof (rwi_138 with "Htext") as "Hi138".
    iPoseProof (rwi_13c with "Htext") as "Hi13c".
    iPoseProof (rwi_13e with "Htext") as "Hi13e".
    iPoseProof (rwi_140 with "Htext") as "Hi140".
    iPoseProof (rwi_144 with "Htext") as "Hi144".
    iPoseProof (rwi_146 with "Htext") as "Hi146".
    (* ---- +0x124  lw a2,-88(s0) ---- *)
    assert (Hidxa : add_vec (M !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4008 : mword 12))
                    = (pa_stk sp0 11 : SailStdpp.Values.mword 64))
      by (rewrite Hs0; apply vdrwc_idx2_addr).
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (VRW + 0x124) : mword 64) Ra2 Rs0
              (mword_of_int 4008 : mword 12) M av
              (mword_of_int (Z.of_nat t) : SailStdpp.Values.mword 32) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi124 [Hidx] [-]").
    { iEval (rewrite Hidxa). iExact "Hidx". }
    iIntros "Hcg Hpc Hidx". iEval (rewrite Hidxa) in "Hidx".
    set (S1 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat t)
                                      : SailStdpp.Values.mword 32))]> M).
    change (<[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat t)
                                      : SailStdpp.Values.mword 32))]> M) with S1.
    assert (HS1a4 : S1 !!! Regidx Ra4 = (d_desc pd m2 : SailStdpp.Values.mword 64))
      by (rewrite /S1 upd_ne; [| reg_neq]; exact Ha4).
    assert (Hp128 : add_vec_int (mword_of_int (VRW + 0x124) : mword 64) 4
                    = mword_of_int (VRW + 0x128)) by pcstep.
    iEval (rewrite Hp128) in "Hpc".
    (* ---- +0x128  sh a2,14(a4)   desc[m2].next := t ---- *)
    assert (Hadn : add_vec (S1 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 14 : mword 12))
                   = (pa_add pd (16 * m2 + 14)%nat : SailStdpp.Values.mword 64))
      by (rewrite HS1a4; apply vdrwc_desc_next).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x128) : mword 64) Ra2 Ra4
              (mword_of_int 14 : mword 12) S1 av vn1 with "Hcg Hpc Hi128 [Hdn] [-]").
    { iEval (rewrite Hadn). iExact "Hdn". }
    iIntros "Hcg Hpc Hdn".
    iEval (rewrite Hadn) in "Hdn".
    iEval (rewrite /S1 upd_eq (vdrwc_trunc16_idx t Ht8)) in "Hdn".
    assert (Hp12c : add_vec_int (mword_of_int (VRW + 0x128) : mword 64) 4
                    = mword_of_int (VRW + 0x12c)) by pcstep.
    iEval (rewrite Hp12c) in "Hpc".
    (* ---- +0x12c / +0x130 / +0x134  a6 := &disk + 32 + 16h ---- *)
    assert (HS1a0 : S1 !!! Regidx Ra0
                    = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64))
      by (rewrite /S1 upd_ne; [| reg_neq]; exact Ha0).
    iApply (wp_slli_s_sconf γ Φ (mword_of_int (VRW + 0x12c) : mword 64) Ra6 Ra0
              (mword_of_int 4 : mword 6)
              (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64) S1 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HS1a0; exact (vdrwc_slli4' h Hh8))
              with "Hcg Hpc Hi12c [-]").
    iIntros "Hcg Hpc".
    set (S2 := <[Regidx Ra6 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> S1).
    change (<[Regidx Ra6 := regval_into_reg
                  (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)]> S1)
      with S2.
    assert (Hp130 : add_vec_int (mword_of_int (VRW + 0x12c) : mword 64) 4
                    = mword_of_int (VRW + 0x130)) by pcstep.
    iEval (rewrite Hp130) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x130) : mword 64) Ra6 Ra6
              (mword_of_int 32 : mword 12) S2 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi130 [-]").
    iIntros "Hcg Hpc".
    set (S3 := <[Regidx Ra6 := regval_into_reg
                  (add_vec (S2 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> S2).
    change (<[Regidx Ra6 := regval_into_reg
                  (add_vec (S2 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> S2) with S3.
    assert (HS3a5 : S3 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. exact Ha5. }
    assert (Hp134 : add_vec_int (mword_of_int (VRW + 0x130) : mword 64) 4
                    = mword_of_int (VRW + 0x134)) by pcstep.
    iEval (rewrite Hp134) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x134) : mword 64) Ra6 Ra5 S3 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi134 [-]").
    iIntros "Hcg Hpc".
    set (S4 := <[Regidx Ra6 := regval_into_reg
                  (add_vec (S3 !!! Regidx Ra6) (S3 !!! Regidx Ra5))]> S3).
    change (<[Regidx Ra6 := regval_into_reg
                  (add_vec (S3 !!! Regidx Ra6) (S3 !!! Regidx Ra5))]> S3) with S4.
    assert (HS4a6 : S4 !!! Regidx Ra6
                    = add_vec (disk_base : SailStdpp.Values.mword 64)
                              (mword_of_int (16 * Z.of_nat h + 32))).
    { rewrite /S4 upd_eq HS3a5 /S3 upd_eq /S2 upd_eq. apply vdrwc_info_base. }
    assert (Hp136 : add_vec_int (mword_of_int (VRW + 0x134) : mword 64) 2
                    = mword_of_int (VRW + 0x136)) by pcstep.
    iEval (rewrite Hp136) in "Hpc".
    (* ---- +0x136 / +0x138  info[h].status := 0xff ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x136) : mword 64) Ra4
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : SailStdpp.Values.mword 64)
              S4 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwb_lim1 with "Hcg Hpc Hi136 [-]").
    iIntros "Hcg Hpc".
    set (S5 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (-1) : SailStdpp.Values.mword 64)]> S4).
    change (<[Regidx Ra4 := regval_into_reg
                  (mword_of_int (-1) : SailStdpp.Values.mword 64)]> S4) with S5.
    assert (HS5a4 : S5 !!! Regidx Ra4 = (mword_of_int (-1) : SailStdpp.Values.mword 64))
      by (rewrite /S5; apply upd_eq).
    assert (HS5a6 : S5 !!! Regidx Ra6
                    = add_vec (disk_base : SailStdpp.Values.mword 64)
                              (mword_of_int (16 * Z.of_nat h + 32)))
      by (rewrite /S5 upd_ne; [| reg_neq]; exact HS4a6).
    assert (Hp138 : add_vec_int (mword_of_int (VRW + 0x136) : mword 64) 2
                    = mword_of_int (VRW + 0x138)) by pcstep.
    iEval (rewrite Hp138) in "Hpc".
    assert (Hast : add_vec (S5 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 16 : mword 12))
                   = (d_info_status h : SailStdpp.Values.mword 64))
      by (rewrite HS5a6; apply vdrwc_status_addr).
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VRW + 0x138) : mword 64) Ra4 Ra6
              (mword_of_int 16 : mword 12) S5 av sb0 with "Hcg Hpc Hi138 [Hst] [-]").
    { iEval (rewrite Hast). iExact "Hst". }
    iIntros "Hcg Hpc Hst".
    iEval (rewrite Hast HS5a4 vdrwc_t8_ff) in "Hst".
    assert (Hp13c : add_vec_int (mword_of_int (VRW + 0x138) : mword 64) 4
                    = mword_of_int (VRW + 0x13c)) by pcstep.
    iEval (rewrite Hp13c) in "Hpc".
    (* ---- +0x13c / +0x13e  a7 := &desc[t] ---- *)
    iApply (wp_cslli_s_sconf γ Φ (mword_of_int (VRW + 0x13c) : mword 64)
              (Regidx Ra2) Ra2 (mword_of_int 4 : mword 6) S5 av
              eq_refl ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi13c [-]").
    iIntros "Hcg Hpc".
    set (S6 := <[Regidx Ra2 := regval_into_reg
                  (shift_bits_left (S5 !!! Regidx Ra2)
                     (subrange_vec_dec (mword_of_int 4 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> S5).
    change (<[Regidx Ra2 := regval_into_reg
                  (shift_bits_left (S5 !!! Regidx Ra2)
                     (subrange_vec_dec (mword_of_int 4 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> S5) with S6.
    assert (HS6a2 : S6 !!! Regidx Ra2
                    = (mword_of_int (16 * Z.of_nat t) : SailStdpp.Values.mword 64)).
    { rewrite /S6 upd_eq /S5 upd_ne; [| reg_neq]. rewrite /S4 upd_ne; [| reg_neq].
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_eq. exact (vdrwc_slli4 t Ht8). }
    assert (HS6a7 : S6 !!! Regidx Ra7 = pd).
    { rewrite /S6 upd_ne; [| reg_neq]. rewrite /S5 upd_ne; [| reg_neq].
      rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3 upd_ne; [| reg_neq].
      rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1 upd_ne; [| reg_neq]. exact Ha7. }
    assert (Hp13e : add_vec_int (mword_of_int (VRW + 0x13c) : mword 64) 2
                    = mword_of_int (VRW + 0x13e)) by pcstep.
    iEval (rewrite Hp13e) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x13e) : mword 64) Ra7 Ra2 S6 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi13e [-]").
    iIntros "Hcg Hpc".
    set (S7 := <[Regidx Ra7 := regval_into_reg
                  (add_vec (S6 !!! Regidx Ra7) (S6 !!! Regidx Ra2))]> S6).
    change (<[Regidx Ra7 := regval_into_reg
                  (add_vec (S6 !!! Regidx Ra7) (S6 !!! Regidx Ra2))]> S6) with S7.
    assert (HS7a7 : S7 !!! Regidx Ra7 = (d_desc pd t : SailStdpp.Values.mword 64)).
    { rewrite /S7 upd_eq HS6a7 HS6a2. apply vdrwc_desc_addr'. }
    assert (HS7a3 : S7 !!! Regidx Ra3
                    = (mword_of_int (16 * Z.of_nat h) : SailStdpp.Values.mword 64)).
    { rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_ne; [| reg_neq]. rewrite /S4 upd_ne; [| reg_neq].
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. exact Ha3. }
    assert (HS7a5 : S7 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)).
    { rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_ne; [| reg_neq]. rewrite /S4 upd_ne; [| reg_neq]. exact HS3a5. }
    assert (Hp140 : add_vec_int (mword_of_int (VRW + 0x13e) : mword 64) 2
                    = mword_of_int (VRW + 0x140)) by pcstep.
    iEval (rewrite Hp140) in "Hpc".
    (* ---- +0x140 / +0x144  a4 := &info[h].status ---- *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x140) : mword 64) Ra4 Ra3
              (mword_of_int 48 : mword 12) S7 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi140 [-]").
    iIntros "Hcg Hpc".
    set (S8 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (S7 !!! Regidx Ra3)
                     (sign_extend' 64 (mword_of_int 48 : mword 12)))]> S7).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (S7 !!! Regidx Ra3)
                     (sign_extend' 64 (mword_of_int 48 : mword 12)))]> S7) with S8.
    assert (HS8a5 : S8 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64))
      by (rewrite /S8 upd_ne; [| reg_neq]; exact HS7a5).
    assert (Hp144 : add_vec_int (mword_of_int (VRW + 0x140) : mword 64) 4
                    = mword_of_int (VRW + 0x144)) by pcstep.
    iEval (rewrite Hp144) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x144) : mword 64) Ra4 Ra5 S8 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi144 [-]").
    iIntros "Hcg Hpc".
    set (S9 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (S8 !!! Regidx Ra4) (S8 !!! Regidx Ra5))]> S8).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (S8 !!! Regidx Ra4) (S8 !!! Regidx Ra5))]> S8) with S9.
    assert (HS9a4 : S9 !!! Regidx Ra4 = (d_info_status h : SailStdpp.Values.mword 64)).
    { rewrite /S9 upd_eq HS8a5 /S8 upd_eq HS7a3. apply vdrwc_status_val. }
    assert (HS9a7 : S9 !!! Regidx Ra7 = (d_desc pd t : SailStdpp.Values.mword 64))
      by (rewrite /S9 upd_ne; [| reg_neq]; exact HS7a7).
    assert (Hp146 : add_vec_int (mword_of_int (VRW + 0x144) : mword 64) 2
                    = mword_of_int (VRW + 0x146)) by pcstep.
    iEval (rewrite Hp146) in "Hpc".
    (* ---- +0x146  sd a4,0(a7)   desc[t].addr := &info[h].status ---- *)
    assert (Hada : add_vec (S9 !!! Regidx Ra7)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc pd t : SailStdpp.Values.mword 64))
      by (rewrite HS9a7 addv_sext0; reflexivity).
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (VRW + 0x146) : mword 64) Ra4 Ra7
              (mword_of_int 0 : mword 12) S9 av va2 with "Hcg Hpc Hi146 [Hda] [-]").
    { iEval (rewrite Hada). iExact "Hda". }
    iIntros "Hcg Hpc Hda". iEval (rewrite Hada HS9a4) in "Hda".
    assert (Hp14a : add_vec_int (mword_of_int (VRW + 0x146) : mword 64) 4
                    = mword_of_int (VRW + 0x14a)) by pcstep.
    iEval (rewrite Hp14a) in "Hpc".
    (* ---- the seam ---- *)
    iApply ("Hcont" $! S9 with "[%] Hcg Hpc Hidx Hdn Hst Hda").
    split_and!.
    - intros r Hr.
      rewrite /S9 upd_ne; [| csne]. rewrite /S8 upd_ne; [| csne].
      rewrite /S7 upd_ne; [| csne]. rewrite /S6 upd_ne; [| csne].
      rewrite /S5 upd_ne; [| csne]. rewrite /S4 upd_ne; [| csne].
      rewrite /S3 upd_ne; [| csne]. rewrite /S2 upd_ne; [| csne].
      rewrite /S1 upd_ne; [| csne]. reflexivity.
    - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_ne; [| reg_neq]. rewrite /S4 upd_ne; [| reg_neq].
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. reflexivity.
    - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      rewrite /S5 upd_ne; [| reg_neq]. rewrite /S4 upd_ne; [| reg_neq].
      rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_ne; [| reg_neq].
      rewrite /S1 upd_ne; [| reg_neq]. reflexivity.
    - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. exact HS6a2.
    - exact HS8a5.
    - rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8 upd_ne; [| reg_neq].
      rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6 upd_ne; [| reg_neq].
      exact HS5a6.
  Qed.

  (* =================================================================== *)
  (* P3e  +0x14a .. +0x162  --  desc[t].{len,flags,next}, b->disk,        *)
  (*                            info[h].b                                 *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3e (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (pd : SailStdpp.Values.mword 64)
      (b : Arch.pa) (h t : nat)
      (vl2 : SailStdpp.Values.mword 32) (vf2 vn2 : SailStdpp.Values.mword 16)
      (dsk0 : SailStdpp.Values.mword 32) (w0 : SailStdpp.Values.mword 64) :
    M !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra2 = (mword_of_int (16 * Z.of_nat t) : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra6 = add_vec (disk_base : SailStdpp.Values.mword 64)
                               (mword_of_int (16 * Z.of_nat h + 32)) ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x14a) : mword 64) -∗
    d_desc_ptr ↦₈□ pd -∗
    pa_add pd (16 * t + 8) ↦₄ vl2 -∗
    pa_add pd (16 * t + 12) ↦₂ vf2 -∗
    pa_add pd (16 * t + 14) ↦₂ vn2 -∗
    b_disk b ↦₄ dsk0 -∗
    d_info_b h ↦₈ w0 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = M !!! Regidx Ra0
         /\ M1 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x162) : mword 64) -∗
        pa_add pd (16 * t + 8) ↦₄ Z_to_bv 32 1 -∗
        pa_add pd (16 * t + 12) ↦₂ Z_to_bv 16 2 -∗
        pa_add pd (16 * t + 14) ↦₂ Z_to_bv 16 0 -∗
        b_disk b ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) -∗
        d_info_b h ↦₈ (b : SailStdpp.Values.mword 64) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hs3 Ha1 Ha2 Ha5 Ha6.
    iIntros "Hcg #Htext Hpc #Hdp Hdl Hdf Hdn Hbd Hib Hcont".
    iPoseProof (rwi_14a with "Htext") as "Hi14a".
    iPoseProof (rwi_14c with "Htext") as "Hi14c".
    iPoseProof (rwi_14e with "Htext") as "Hi14e".
    iPoseProof (rwi_150 with "Htext") as "Hi150".
    iPoseProof (rwi_152 with "Htext") as "Hi152".
    iPoseProof (rwi_156 with "Htext") as "Hi156".
    iPoseProof (rwi_15a with "Htext") as "Hi15a".
    iPoseProof (rwi_15e with "Htext") as "Hi15e".
    (* ---- +0x14a / +0x14c  a4 := &desc[t] ---- *)
    assert (Hdpa : add_vec (M !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = (d_desc_ptr : SailStdpp.Values.mword 64)).
    { rewrite Ha5 addv_sext0. unfold d_desc_ptr. rewrite pa_add_0. reflexivity. }
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VRW + 0x14a) : mword 64) Ra4 Ra5
              (mword_of_int 0 : mword 12) M av pd (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14a [] [-]").
    { iEval (rewrite Hdpa). iExact "Hdp". }
    iIntros "Hcg Hpc _".
    set (T1 := <[Regidx Ra4 := regval_into_reg pd]> M).
    change (<[Regidx Ra4 := regval_into_reg pd]> M) with T1.
    assert (HT1a4 : T1 !!! Regidx Ra4 = pd) by (rewrite /T1; apply upd_eq).
    assert (HT1a2 : T1 !!! Regidx Ra2
                    = (mword_of_int (16 * Z.of_nat t) : SailStdpp.Values.mword 64))
      by (rewrite /T1 upd_ne; [| reg_neq]; exact Ha2).
    assert (Hp14c : add_vec_int (mword_of_int (VRW + 0x14a) : mword 64) 2
                    = mword_of_int (VRW + 0x14c)) by pcstep.
    iEval (rewrite Hp14c) in "Hpc".
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (VRW + 0x14c) : mword 64) Ra4 Ra2 T1 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi14c [-]").
    iIntros "Hcg Hpc".
    set (T2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (T1 !!! Regidx Ra4) (T1 !!! Regidx Ra2))]> T1).
    change (<[Regidx Ra4 := regval_into_reg
                  (add_vec (T1 !!! Regidx Ra4) (T1 !!! Regidx Ra2))]> T1) with T2.
    assert (HT2a4 : T2 !!! Regidx Ra4 = (d_desc pd t : SailStdpp.Values.mword 64)).
    { rewrite /T2 upd_eq HT1a4 HT1a2. apply vdrwc_desc_addr'. }
    assert (HT2a1 : T2 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)).
    { rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [| reg_neq]. exact Ha1. }
    assert (Hp14e : add_vec_int (mword_of_int (VRW + 0x14c) : mword 64) 2
                    = mword_of_int (VRW + 0x14e)) by pcstep.
    iEval (rewrite Hp14e) in "Hpc".
    (* ---- +0x14e  c.sw a1,8(a4)   desc[t].len := 1 ---- *)
    assert (Hadl : add_vec (T2 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (pa_add pd (16 * t + 8)%nat : SailStdpp.Values.mword 64))
      by (rewrite HT2a4; apply vdrwc_desc_len).
    iApply (wp_csw_s_sconf γ Φ (mword_of_int (VRW + 0x14e) : mword 64) Ra1 Ra4
              (mword_of_int 8 : mword 12) T2 av vl2 with "Hcg Hpc Hi14e [Hdl] [-]").
    { iEval (rewrite Hadl). iExact "Hdl". }
    iIntros "Hcg Hpc Hdl".
    iEval (rewrite Hadl HT2a1 vdrwc_t32_1) in "Hdl".
    assert (Hp150 : add_vec_int (mword_of_int (VRW + 0x14e) : mword 64) 2
                    = mword_of_int (VRW + 0x150)) by pcstep.
    iEval (rewrite Hp150) in "Hpc".
    (* ---- +0x150 / +0x152  desc[t].flags := 2 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x150) : mword 64) Ra3
              (mword_of_int 2 : mword 6) (mword_of_int 2 : SailStdpp.Values.mword 64)
              T2 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwc_li2 with "Hcg Hpc Hi150 [-]").
    iIntros "Hcg Hpc".
    set (T3 := <[Regidx Ra3 := regval_into_reg
                  (mword_of_int 2 : SailStdpp.Values.mword 64)]> T2).
    change (<[Regidx Ra3 := regval_into_reg
                  (mword_of_int 2 : SailStdpp.Values.mword 64)]> T2) with T3.
    assert (HT3a3 : T3 !!! Regidx Ra3 = (mword_of_int 2 : SailStdpp.Values.mword 64))
      by (rewrite /T3; apply upd_eq).
    assert (HT3a4 : T3 !!! Regidx Ra4 = (d_desc pd t : SailStdpp.Values.mword 64))
      by (rewrite /T3 upd_ne; [| reg_neq]; exact HT2a4).
    assert (Hp152 : add_vec_int (mword_of_int (VRW + 0x150) : mword 64) 2
                    = mword_of_int (VRW + 0x152)) by pcstep.
    iEval (rewrite Hp152) in "Hpc".
    assert (Hadf : add_vec (T3 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 12 : mword 12))
                   = (pa_add pd (16 * t + 12)%nat : SailStdpp.Values.mword 64))
      by (rewrite HT3a4; apply vdrwc_desc_flags).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x152) : mword 64) Ra3 Ra4
              (mword_of_int 12 : mword 12) T3 av vf2 with "Hcg Hpc Hi152 [Hdf] [-]").
    { iEval (rewrite Hadf). iExact "Hdf". }
    iIntros "Hcg Hpc Hdf".
    iEval (rewrite Hadf HT3a3 vdrwc_t16_2) in "Hdf".
    assert (Hp156 : add_vec_int (mword_of_int (VRW + 0x152) : mword 64) 4
                    = mword_of_int (VRW + 0x156)) by pcstep.
    iEval (rewrite Hp156) in "Hpc".
    (* ---- +0x156  sh x0,14(a4)   desc[t].next := 0 ---- *)
    iDestruct (sie_cap_gpr_x0 γ T3 av (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
    assert (Hadn : add_vec (T3 !!! Regidx Ra4)
                     (sign_extend' 64 (mword_of_int 14 : mword 12))
                   = (pa_add pd (16 * t + 14)%nat : SailStdpp.Values.mword 64))
      by (rewrite HT3a4; apply vdrwc_desc_next).
    iApply (wp_sh_s_sconf γ Φ (mword_of_int (VRW + 0x156) : mword 64) Rz Ra4
              (mword_of_int 14 : mword 12) T3 av vn2 with "Hcg Hpc Hi156 [Hdn] [-]").
    { iEval (rewrite Hadn). iExact "Hdn". }
    iIntros "Hcg Hpc Hdn".
    iEval (rewrite Hadn Hz0 vdrwc_t16_0) in "Hdn".
    assert (Hp15a : add_vec_int (mword_of_int (VRW + 0x156) : mword 64) 4
                    = mword_of_int (VRW + 0x15a)) by pcstep.
    iEval (rewrite Hp15a) in "Hpc".
    (* ---- +0x15a  sw a1,4(s3)   b->disk := 1 ---- *)
    assert (HT3s3 : T3 !!! Regidx Rs3 = (b : SailStdpp.Values.mword 64)).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hs3. }
    assert (HT3a1 : T3 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64))
      by (rewrite /T3 upd_ne; [| reg_neq]; exact HT2a1).
    assert (Habd : add_vec (T3 !!! Regidx Rs3)
                     (sign_extend' 64 (mword_of_int 4 : mword 12))
                   = (b_disk b : SailStdpp.Values.mword 64))
      by (rewrite HT3s3; apply vdrwc_bdisk_addr).
    iApply (wp_sw_s_sconf γ Φ (mword_of_int (VRW + 0x15a) : mword 64) Ra1 Rs3
              (mword_of_int 4 : mword 12) T3 av dsk0 with "Hcg Hpc Hi15a [Hbd] [-]").
    { iEval (rewrite Habd). iExact "Hbd". }
    iIntros "Hcg Hpc Hbd".
    iEval (rewrite Habd HT3a1 vdrwc_t32_bdisk) in "Hbd".
    assert (Hp15e : add_vec_int (mword_of_int (VRW + 0x15a) : mword 64) 4
                    = mword_of_int (VRW + 0x15e)) by pcstep.
    iEval (rewrite Hp15e) in "Hpc".
    (* ---- +0x15e  sd s3,8(a6)   info[h].b := b ---- *)
    assert (HT3a6 : T3 !!! Regidx Ra6
                    = add_vec (disk_base : SailStdpp.Values.mword 64)
                              (mword_of_int (16 * Z.of_nat h + 32))).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Ha6. }
    assert (Haib : add_vec (T3 !!! Regidx Ra6)
                     (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = (d_info_b h : SailStdpp.Values.mword 64))
      by (rewrite HT3a6; apply vdrwc_infob_addr).
    iApply (wp_sd_s_sconf γ Φ (mword_of_int (VRW + 0x15e) : mword 64) Rs3 Ra6
              (mword_of_int 8 : mword 12) T3 av w0 with "Hcg Hpc Hi15e [Hib] [-]").
    { iEval (rewrite Haib). iExact "Hib". }
    iIntros "Hcg Hpc Hib".
    iEval (rewrite Haib HT3s3) in "Hib".
    assert (Hp162 : add_vec_int (mword_of_int (VRW + 0x15e) : mword 64) 4
                    = mword_of_int (VRW + 0x162)) by pcstep.
    iEval (rewrite Hp162) in "Hpc".
    (* ---- the seam ---- *)
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc Hdl Hdf Hdn Hbd Hib").
    split_and!.
    - intros r Hr.
      rewrite /T3 upd_ne; [| csne]. rewrite /T2 upd_ne; [| csne].
      rewrite /T1 upd_ne; [| csne]. reflexivity.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. reflexivity.
    - exact HT3a1.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Ha5.
  Qed.

  (* =================================================================== *)
  (* P3   +0x0b0 .. +0x162  --  the five chunks composed.                 *)
  (*                                                                     *)
  (* Takes the three descriptor bundles P2.3 allocated, the [int idx[3]]  *)
  (* local holding their indices and the caller's [b->disk] cell; leaves  *)
  (* [vdrw_chain] -- every byte of the request, at the value the code     *)
  (* wrote -- and the three registers P4/P5 still read: a0 (the head), a1 *)
  (* (the constant 1) and a5 (&disk).                                     *)
  (* =================================================================== *)
  Lemma wp_vdrw_p3 (γ : gname) (Φ : mval -> iProp Σ)
      (M : regfile) (av : nat) (pd : SailStdpp.Values.mword 64)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (h m2 t : nat) (dsk0 : SailStdpp.Values.mword 32) :
    (h < 8)%nat -> (m2 < 8)%nat -> (t < 8)%nat ->
    vdrw_regs M sp0 b wr sector ->
    sie_cap_gpr γ M av -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x0b0) : mword 64) -∗
    d_desc_ptr ↦₈□ pd -∗
    vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                 (mword_of_int (Z.of_nat t)) -∗
    free_slot_res pd h -∗ free_slot_res pd m2 -∗ free_slot_res pd t -∗
    b_disk b ↦₄ dsk0 -∗
    ( ∀ M1 : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> M1 !!! Regidx r = M !!! Regidx r)
         /\ M1 !!! Regidx Ra0 = (mword_of_int (Z.of_nat h)
                                   : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
         /\ M1 !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr γ M1 av -∗
        pc_is (mword_of_int (VRW + 0x162) : mword 64) -∗
        vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                     (mword_of_int (Z.of_nat t)) -∗
        vdrw_chain pd b h m2 t wr sector -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hh8 Hm8 Ht8 Hregs.
    destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7 & Htp).
    iIntros "Hcg #Htext Hpc #Hdp Hidx Hbh Hbm Hbt Hbd Hcont".
    (* ---- take the three bundles apart ---- *)
    iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
    iDestruct "Hbh" as "(Hdeh & Hopsh & Hsth & Hibh)".
    iDestruct "Hdeh" as (va0 vl0 vf0 vn0) "(Hda0 & Hdl0 & Hdf0 & Hdn0)".
    iDestruct "Hopsh" as (ty0 res0 sec0) "(Hty & Hres & Hsec)".
    iDestruct "Hsth" as (sb0) "Hst".
    iDestruct "Hibh" as (w0) "Hib".
    iEval (rewrite (free_slot_split pd m2)) in "Hbm".
    iDestruct "Hbm" as "[Hdem Hrestm]".
    iDestruct "Hdem" as (va1 vl1 vf1 vn1) "(Hda1 & Hdl1 & Hdf1 & Hdn1)".
    iEval (rewrite (free_slot_split pd t)) in "Hbt".
    iDestruct "Hbt" as "[Hdet Hrestt]".
    iDestruct "Hdet" as (va2 vl2 vf2 vn2) "(Hda2 & Hdl2 & Hdf2 & Hdn2)".
    (* ---- P3a ---- *)
    iApply (wp_vdrw_p3a γ Φ M av sp0 h wr sector ty0 res0 sec0
              Hh8 Hs0 Hs6 Hs7 with "Hcg Htext Hpc Hx0 Hty Hres Hsec [-]").
    iIntros (M1) "%F1 Hcg Hpc Hx0 Hty Hres Hsec".
    destruct F1 as (Hcs1 & H1a0 & H1a3 & H1a5).
    (* ---- P3b ---- *)
    iApply (wp_vdrw_p3b γ Φ M1 av pd h va0 vl0 vf0
              H1a3 H1a5 with "Hcg Htext Hpc Hdp Hda0 Hdl0 Hdf0 [-]").
    iIntros (M2) "%F2 Hcg Hpc Hda0 Hdl0 Hdf0".
    destruct F2 as (Hcs2 & H2a0 & H2a3 & H2a5 & H2a6 & H2a2 & H2a1).
    (* ---- P3c ---- *)
    iApply (wp_vdrw_p3c γ Φ M2 av pd sp0 b h m2 wr vn0 vf1 va1 vl1 Hm8
              ltac:(rewrite (Hcs2 (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs1 (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity));
                    exact Hs0)
              ltac:(rewrite (Hcs2 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs1 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    exact Hs3)
              ltac:(rewrite (Hcs2 (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs1 (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity));
                    exact Hs6)
              H2a1 H2a2 H2a5 H2a6
              with "Hcg Htext Hpc Hdp Hx1 Hdn0 Hda1 Hdl1 Hdf1 [-]").
    iIntros (M3) "%F3 Hcg Hpc Hx1 Hdn0 Hda1 Hdl1 Hdf1".
    destruct F3 as (Hcs3 & H3a0 & H3a3 & H3a1 & H3a4 & H3a5 & H3a7).
    (* ---- P3d ---- *)
    iApply (wp_vdrw_p3d γ Φ M3 av pd sp0 h m2 t vn1 sb0 va2 Hh8 Ht8
              ltac:(rewrite (Hcs3 (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs2 (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs1 (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity));
                    exact Hs0)
              ltac:(rewrite H3a0 H2a0; exact H1a0)
              ltac:(rewrite H3a3; exact H2a3)
              H3a4 H3a5 H3a7
              with "Hcg Htext Hpc Hx2 Hdn1 Hst Hda2 [-]").
    iIntros (M4) "%F4 Hcg Hpc Hx2 Hdn1 Hst Hda2".
    destruct F4 as (Hcs4 & H4a0 & H4a1 & H4a2 & H4a5 & H4a6).
    (* ---- P3e ---- *)
    iApply (wp_vdrw_p3e γ Φ M4 av pd b h t vl2 vf2 vn2 dsk0 w0
              ltac:(rewrite (Hcs4 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs3 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs2 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    rewrite (Hcs1 (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                    exact Hs3)
              ltac:(rewrite H4a1; exact H3a1) H4a2 H4a5 H4a6
              with "Hcg Htext Hpc Hdp Hdl2 Hdf2 Hdn2 Hbd Hib [-]").
    iIntros (M5) "%F5 Hcg Hpc Hdl2 Hdf2 Hdn2 Hbd Hib".
    destruct F5 as (Hcs5 & H5a0 & H5a1 & H5a5).
    (* ---- the P3/P4 seam ---- *)
    iApply ("Hcont" $! M5 with "[%] Hcg Hpc [Hx0 Hx1 Hx2 Hxp] [-]").
    { split_and!.
      - intros r Hr.
        rewrite (Hcs5 r Hr) (Hcs4 r Hr) (Hcs3 r Hr) (Hcs2 r Hr) (Hcs1 r Hr).
        reflexivity.
      - rewrite H5a0 H4a0 H3a0 H2a0. exact H1a0.
      - exact H5a1.
      - exact H5a5. }
    { rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2". iExact "Hxp". }
    rewrite /vdrw_chain.
    iFrame "Hty Hres Hsec Hda0 Hdl0 Hdf0 Hdn0 Hda1 Hdl1 Hdf1 Hdn1
            Hda2 Hdl2 Hdf2 Hdn2 Hst Hib Hbd Hrestm Hrestt".
  Qed.

End ProofVirtioDiskRwC.
