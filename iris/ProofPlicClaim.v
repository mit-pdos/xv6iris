(* ProofPlicClaim.v: whole-function WP for xv6's plic_claim() in S-mode, over
   the SIE-agnostic sie_cap bundle.  plic_claim() @ 0x800054cc asks the PLIC
   which interrupt this hart should serve:

     0x800054cc <plic_claim>:
       +0x00  1141      c.addi   sp,sp,-16     frame alloc (== cpuid/plicinit)
       +0x02  e406      c.sdsp   ra,8(sp)
       +0x04  e022      c.sdsp   s0,0(sp)
       +0x06  0800      c.addi4spn s0,sp,16
       +0x08  bfcfc0ef  jal      ra,cpuid      a0 = hart id
       +0x0c  00d5151b  slliw    a0,a0,0xd
       +0x10  0c2017b7  lui      a5,0xc201
       +0x14  97aa      c.add    a5,a5,a0      a5 = PLIC+0x201000 + hart*0x2000
       +0x16  43c8      c.lw     a0,4(a5)      a0 = *PLIC_SCLAIM(hart)
       +0x18  60a2      c.ldsp   ra,8(sp)      frame free
       +0x1a  6402      c.ldsp   s0,0(sp)
       +0x1c  0141      c.addi   sp,sp,16
       +0x1e  8082      c.ret

   The load is a CLAIM: the model's read of that register takes the best pending
   enabled source, clears its pending bit and marks it claimed.  It therefore
   runs with the device invariant open ([wp_lw_plic_dev_s_sconf], WpPlic.v) --
   every hart claims concurrently, so none may own [plic_frag] across a step.
   The mutation touches no enable word, so the kernel's plan [plic_ok]
   (PlicPlan.v) survives it, and the plan in turn is what bounds the id read
   back to 0 / UART0_IRQ / VIRTIO0_IRQ ([plic_claim_ret]).

   The hart-id address arithmetic is shared with plicinithart and plic_complete
   and lives in PlicHart.v. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import DevModel PlicPlan PlicHart DiskPtsto WpUart WpPlic SpecCpuid SpecPlicClaim.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodePlicClaim.
Import Defs.

(* ---- the decodes used only by plic_claim ---- *)





(* the value a claim leaves in a0: [c.lw] sign-extends the 32-bit register, and
   all three ids the plan admits are small and positive. *)
Lemma pq_a0_of_claim (v : bv 32) :
  plic_claim_ret_ok v ->
  plic_claim_a0_ok (extend_value false
    (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v) : mword 64).
Proof.
  intros [-> | [-> | ->]]; unfold plic_claim_a0_ok;
    [ left | right; left | right; right ]; apply bv_eq; vm_compute; reflexivity.
Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module PlicClaimProof (Cpuid : CPUID) : PLIC_CLAIM.

Section ProofPlicClaim.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.















  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plic_claim(), entry to return.    *)
  (*  Interrupts-off (see SpecPlicClaim.v's header): no [b] binder, no     *)
  (*  [wp_next] wrapper, so the ambient hart never moves and the proof     *)
  (*  reads exactly like a straight-line function -- one continuous       *)
  (*  [rewrite wp_next_off] per leaf, save for the [jal cpuid] call, whose *)
  (*  own contract likewise has no wrapper to collapse. *)
  (* =================================================================== *)
  Lemma wp_plic_claim_sconf (γd : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : mword 64)
    : wp_plic_claim_sconf_body γd γv Φ m0 n p.
  Proof.
    cbv beta delta [wp_plic_claim_sconf_body].
    intros ra_idx tp_idx a0_idx pcE ra0 ret_tgt Hhart Hn.
    (* [tp] is pinned to the hart: [rget _ tp_idx] is [cid_word] at EVERY
       register map, and the ambient hart never moves in this proof (no
       [wp_next]), so this and the bound it carries are hoisted ONCE. *)
    assert (Htp : forall mm : regfile, rget mm tp_idx = cid_word)
      by (intros mm; exact (rget_tp mm)).
    rewrite (Htp m0) in Hhart.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (R2 := <[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1).
    iIntros "Hcg #Htext Hpc #Hdinv Hcont".
    iPoseProof (pqi_00 with "Htext") as "Hi00".
    iPoseProof (pqi_02 with "Htext") as "Hi02".
    iPoseProof (pqi_04 with "Htext") as "Hi04".
    iPoseProof (pqi_06 with "Htext") as "Hi06".
    iPoseProof (pqi_08 with "Htext") as "Hi08".
    iPoseProof (pqi_0c with "Htext") as "Hi0c".
    iPoseProof (pqi_10 with "Htext") as "Hi10".
    iPoseProof (pqi_14 with "Htext") as "Hi14".
    iPoseProof (pqi_16 with "Htext") as "Hi16".
    iPoseProof (pqi_18 with "Htext") as "Hi18".
    iPoseProof (pqi_1a with "Htext") as "Hi1a".
    iPoseProof (pqi_1c with "Htext") as "Hi1c".
    iPoseProof (pqi_1e with "Htext") as "Hi1e".
    assert (Hn2 : (2 <= n)%nat) by lia.
    assert (Hcsp1 : R1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE imm_entry m0 n 2 false Hn2 Hpush
              with "Hcg Hpc Hi00 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x02)) (mword_of_int 1 : mword 6) ra_idx R1 (n - 2)%nat vr24 false
              with "Hcg Hpc Hi02 Hbra [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x04)) (mword_of_int 0 : mword 6) s0_idx R1 (n - 2)%nat vs16 false
              with "Hcg Hpc Hi04 Hbs0 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx R1 (n - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1) with R2.
    assert (HR2sp : R2 !!! Regidx csp_rs1 = sp').
    { unfold R2. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp1. }
    (* ---- 0x08: jal ra,cpuid.  [Cpuid.wp_call_cpuid_sconf_cs] is itself
       [b = false]-only (SpecCpuid.v) with no [wp_next] wrapper, matching
       plic_claim's own now-[b = false] contract exactly -- so the call
       produces its continuation directly, with nothing to collapse. ---- *)
    iApply (Cpuid.wp_call_cpuid_sconf_cs Φ (mword_of_int (KernelSyms.plic_claim + 0x08))
              (mword_of_int 2081788 : mword 21) R2 (n - 2)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi08 [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0c : ret_pc (add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x08) : mword 64) 4)
                       = (mword_of_int (KernelSyms.plic_claim + 0x0c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    assert (Hmosp : mo !!! Regidx csp_rs1 = sp')
      by (rewrite (proj1 Hmo_cs); exact HR2sp).
    (* the hart id IS [cid_word] -- no detour through [m0]'s tp slot. *)
    assert (Hmoa0 : mo !!! Regidx a0_idx = cid_word).
    { rewrite Hmo_a0 (Htp R2). exact cpuid_ret_cid. }
    (* ---- the post-call register-map chain ---- *)
    set (N2 := <[Regidx a0_idx := regval_into_reg (ph_shl cid_word 13)]> mo).
    set (N3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N2).
    set (N4 := <[Regidx a5_idx := regval_into_reg (add_vec (rget N3 a5_idx) (rget N3 a0_idx))]> N3).
    (* ---- 0x0c: slliw a0,a0,13 ---- *)
    iApply (wp_slliw_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x0c)) a0_idx a0_idx
              (mword_of_int 13 : mword 5) (ph_shl cid_word 13) mo (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite Hmoa0; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.plic_claim + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (ph_shl cid_word 13)]> mo) with N2.
    (* ---- 0x10: lui a5,0xc201 ---- *)
    iApply (wp_lui_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x10)) a5_idx
              (mword_of_int 0xc201 : mword 20) (mword_of_int 0x0c201000 : mword 64) N2 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.plic_claim + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N2) with N3.
    (* ---- 0x14: c.add a5,a5,a0 ---- *)
    iApply (wp_cadd_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x14)) a5_idx a0_idx N3 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (rget N3 a5_idx) (rget N3 a0_idx))]> N3) with N4.
    assert (HN3a5 : rget N3 a5_idx = (mword_of_int 0x0c201000 : mword 64))
      by (rgne; unfold N3; apply upd_eq).
    assert (HN3a0 : rget N3 a0_idx = ph_shl cid_word 13).
    { rgne. unfold N3. rewrite upd_ne; [| vm_compute; discriminate]. unfold N2. apply upd_eq. }
    assert (HN4a5 : rget N4 a5_idx = ph_sthb cid_word).
    { rgne. unfold N4. rewrite upd_eq. unfold regval_into_reg, ph_sthb.
      rewrite HN3a5 HN3a0. reflexivity. }
    (* ---- 0x16: c.lw a0,4(a5) -- THE CLAIM ---- *)
    iApply (wp_lw_plic_dev_s_sconf (CID := CID) γd γv Φ (mword_of_int (KernelSyms.plic_claim + 0x16)) true false
              a0_idx a5_idx (mword_of_int 4 : mword 12) N4 (n - 2)%nat plic_claim_ret_ok false
              ltac:(rewrite HN4a5; exact (ph_geom_range _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_align _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_canon _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_vpn   _ (ph_sclaim_geom _ Hhart)))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HN4a5; intros pq Hpq;
                    destruct (plic_claim pq (Z.to_nat (bv_unsigned cid_word))) as [cv cp] eqn:Hc;
                    exists cv, cp; split; [ | split ];
                    [ rewrite (ph_sclaim_read _ pq Hhart); rewrite Hc; reflexivity
                    | pose proof (plic_ok_claim pq (Z.to_nat (bv_unsigned cid_word)) Hpq) as Hk;
                      rewrite Hc in Hk; exact Hk
                    | pose proof (plic_claim_ret pq (Z.to_nat (bv_unsigned cid_word)) Hpq) as Hk;
                      rewrite Hc in Hk; exact Hk ])
              with "Hcg Hpc Hi16 Hdinv [-]").
    iIntros (cv) "%Hcv".
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    set (cval := (extend_value false
                    (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) cv) : mword 64)).
    set (N5 := <[Regidx a0_idx := regval_into_reg cval]> N4).
    set (N6 := <[Regidx ra_idx := regval_into_reg ra0]> N5).
    set (N7 := <[Regidx s0_idx := regval_into_reg s00]> N6).
    set (N8 := <[Regidx csp_rs1 := regval_into_reg (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N7).
    change (<[Regidx a0_idx := regval_into_reg cval]> N4) with N5.
    (* ---- the epilogue ---- *)
    assert (HN5sp : N5 !!! Regidx csp_rs1 = sp').
    { unfold N5, N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmosp. }
    assert (Hpa1' : add_vec (N5 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HN5sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (N5 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HN5sp. rewrite -Hcsp1. exact Hpa2. }
    assert (Hra0v : rget R1 ra_idx = ra0)
      by (rgne; unfold R1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : rget R1 s0_idx = s00)
      by (rgne; unfold R1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    (* ---- 0x18: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x18)) (mword_of_int 1 : mword 6) ra_idx N5 (n - 2)%nat ra0 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 Hbra [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> N5) with N6.
    assert (HN6sp : N6 !!! Regidx csp_rs1 = N5 !!! Regidx csp_rs1)
      by (unfold N6; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -HN6sp) in "Hbs0".
    (* ---- 0x1a: c.ldsp s0,0(sp) ---- *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x1a)) (mword_of_int 0 : mword 6) s0_idx N6 (n - 2)%nat s00 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a Hbs0 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> N6) with N7.
    (* ---- 0x1c: c.addi sp,16 -- the frame pop ---- *)
    assert (HN7sp : N7 !!! Regidx csp_rs1 = sp').
    { unfold N7, N6. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact HN5sp. }
    assert (Hwv : add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite HN7sp. unfold sp', imm_dealloc, imm_entry, sp0. apply frame_cancel_16. }
    assert (Hpop : N7 !!! Regidx csp_rs1
                   = pa_stk (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv HN7sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite HN6sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x1c)) imm_dealloc N7
              (n - 2)%nat 2 false Hpop
              with "Hcg Hpc Hi1c Hframe [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.plic_claim + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.plic_claim + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N7) with N8.
    (* ---- 0x1e: c.ret ---- *)
    assert (HN8ra : N8 !!! Regidx ra_idx = ra0).
    { unfold N8, N7. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold N6. rewrite upd_eq. reflexivity. }
    assert (HN8a0 : N8 !!! Regidx a0_idx = cval).
    { unfold N8, N7, N6. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold N5. rewrite upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.plic_claim + 0x1e)) ra_idx N8 n false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (rget N8 ra_idx) = ret_tgt)
      by (rgne; rewrite HN8ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! N8 with "Hcg Hpc [%]").
    split; [ | split ].
    - (* sp and s0 are saved-then-restored ACROSS the call, so the fact does not
         factor through the callee's [callee_saved]; each conjunct on its own. *)
      unfold callee_saved.
      split.
      { unfold N8. rewrite upd_eq. unfold regval_into_reg. exact Hwv. }
      split.
      { unfold N8, N7, s0_idx, s00.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq. unfold regval_into_reg. reflexivity. }
      repeat split; cs_through Hmo_cs mo.
    - exact HN8ra.
    - rewrite HN8a0. unfold cval. apply pq_a0_of_claim. exact Hcv.
  Qed.

End ProofPlicClaim.

End PlicClaimProof.
