(* ProofPlicinithart.v: whole-function WP for xv6's plicinithart() in S-mode,
   over the SIE-agnostic sie_cap bundle.  plicinithart() @ 0x80005498 enables
   the UART + VIRTIO interrupts for THIS hart's S-mode PLIC context and drops
   that context's priority threshold to 0:

     0x80005498 <plicinithart>:
       +0x00  1141      c.addi   sp,sp,-16     frame alloc  (== cpuid/plicinit)
       +0x02  e406      c.sdsp   ra,8(sp)
       +0x04  e022      c.sdsp   s0,0(sp)
       +0x06  0800      c.addi4spn s0,sp,16
       +0x08  c30fc0ef  jal      ra,cpuid      a0 = hart id
       +0x0c  0085171b  slliw    a4,a0,0x8
       +0x10  0c0027b7  lui      a5,0xc002
       +0x14  97ba      c.add    a5,a5,a4      a5 = PLIC+0x2000 + hart*0x100
       +0x16  40200713  addi     a4,zero,1026
       +0x1a  08e7a023  sw       a4,128(a5)    *PLIC_SENABLE(hart)  = 1026
       +0x1e  00d5151b  slliw    a0,a0,0xd
       +0x22  0c2017b7  lui      a5,0xc201
       +0x26  97aa      c.add    a5,a5,a0      a5 = PLIC+0x201000 + hart*0x2000
       +0x28  0007a023  sw       zero,0(a5)    *PLIC_SPRIORITY(hart) = 0
       +0x2c  60a2      c.ldsp   ra,8(sp)      frame free   (== cpuid/plicinit)
       +0x2e  6402      c.ldsp   s0,0(sp)
       +0x30  0141      c.addi   sp,sp,16
       +0x32  8082      c.ret

   The 16-byte frame is byte-identical to cpuid/plicinit, so the prologue and
   epilogue reuse KernelRvcDecode's shared templates and the Proof{Mem,Ctl}
   frame leaves.  The two MMIO writes go through [wp_sw_plic_dev_s_sconf]
   (WpPlic.v), which opens the device invariant around each write: every hart
   runs this function concurrently, so none of them may own [plic_frag] across
   a step (see SpecPlicinithart.v).  Each write therefore has to preserve the
   kernel's PLIC plan [plic_ok] (PlicPlan.v) at EVERY state that plan admits.

   Unlike plicinit, both store addresses depend on the hart id, which is only
   bounded ([bv_unsigned tp < dev_ncpu]) rather than concrete.  Every fact that
   needs the address as a number is therefore proved by an eight-way case split
   on the hart id ([hart_cases]) followed by [vm_compute] -- see the geometry /
   write lemmas below, which are stated over an abstract [tp] so the main proof
   body stays single-copy and symbolic. *)
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
Require Import PlicPlan PlicHart DiskPtsto WpUart WpPlic SpecCpuid SpecPlicinithart.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodePlicinithart.
Import Defs.

(* The hart-id case split, the two context base addresses, their geometry and
   what an access at each does to the PLIC state all live in PlicHart.v -- they
   are keyed by a hart id and a PLIC address, nothing plicinithart-specific,
   and plic_claim / plic_complete reuse them. *)


(* ===================================================================== *)
(*  Decodes for the ten instructions not shared with the frame templates. *)
(* ===================================================================== *)







(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module PlicinithartProof (Cpuid : CPUID) : PLICINITHART.

Section ProofPlicinithart.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.




















  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plicinithart(), entry to return.  *)
  (*  Interrupts-off (see SpecPlicinithart.v's header): no [b] binder, no *)
  (*  [wp_next] wrapper, so the ambient hart never moves -- one           *)
  (*  [rewrite wp_next_off] per leaf, and the [jal cpuid] call needs no   *)
  (*  collapse at all since its own contract has no wrapper either. *)
  (* =================================================================== *)
  Lemma wp_plicinithart_sconf (γd : uart_names) (γv : disk_names) (m0 : regfile) (n : nat) (p : mword 64)
    : wp_plicinithart_sconf_body γd γv m0 n p.
  Proof.
    cbv beta delta [wp_plicinithart_sconf_body].
    intros ra_idx tp_idx pcE ra0 ret_tgt Hhart Hn.
    (* [tp] is pinned to the hart: [rget _ tp_idx] is [cid_word] at EVERY
       register map, and the ambient hart never moves in this proof (no
       [wp_next]), so this and the bound it carries are hoisted ONCE. *)
    assert (Htp : forall mm : regfile, rget mm tp_idx = cid_word)
      by (intros mm; exact (rget_tp mm)).
    rewrite (Htp m0) in Hhart.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (z_idx  := (mword_of_int 0 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    iIntros "Hcg #Htext Hpc #Hdinv Hcont".
    iPoseProof (phi_00 with "Htext") as "Hi00".
    iPoseProof (phi_02 with "Htext") as "Hi02".
    iPoseProof (phi_04 with "Htext") as "Hi04".
    iPoseProof (phi_06 with "Htext") as "Hi06".
    iPoseProof (phi_08 with "Htext") as "Hi08".
    iPoseProof (phi_0c with "Htext") as "Hi0c".
    iPoseProof (phi_10 with "Htext") as "Hi10".
    iPoseProof (phi_14 with "Htext") as "Hi14".
    iPoseProof (phi_16 with "Htext") as "Hi16".
    iPoseProof (phi_1a with "Htext") as "Hi1a".
    iPoseProof (phi_1e with "Htext") as "Hi1e".
    iPoseProof (phi_22 with "Htext") as "Hi22".
    iPoseProof (phi_26 with "Htext") as "Hi26".
    iPoseProof (phi_28 with "Htext") as "Hi28".
    iPoseProof (phi_2c with "Htext") as "Hi2c".
    iPoseProof (phi_2e with "Htext") as "Hi2e".
    iPoseProof (phi_30 with "Htext") as "Hi30".
    iPoseProof (phi_32 with "Htext") as "Hi32".
    assert (Hn2 : (2 <= n)%nat) by lia.
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE imm_entry m0 n 2 false Hn2 Hpush
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24 false
              with "Hcg Hpc Hi02 Hbra").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16 false
              with "Hcg Hpc Hi04 Hbs0").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    assert (Hm2sp : m2 !!! Regidx csp_rs1 = sp').
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp1. }
    (* ---- 0x08: jal ra,cpuid.  [Cpuid.wp_call_cpuid_sconf_cs] is itself
       [b = false]-only with no [wp_next] wrapper, matching plicinithart's
       own now-[b = false] contract, so the call's continuation is entered
       directly. ---- *)
    iApply (Cpuid.wp_call_cpuid_sconf_cs (mword_of_int (KernelSyms.plicinithart + 0x08))
              (mword_of_int 2081606 : mword 21) m2 (n - 2)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi08").
    iIntros (mo) "Hcg Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0c : ret_pc (add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x08) : mword 64) 4)
                       = (mword_of_int (KernelSyms.plicinithart + 0x0c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    iDestruct (sie_cap_gpr_x0 mo (n - 2)%nat false p z_idx ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
    assert (Hmosp : mo !!! Regidx csp_rs1 = sp')
      by (rewrite (proj1 Hmo_cs); exact Hm2sp).
    (* the hart id IS [cid_word] -- no detour through [m0]'s tp slot. *)
    assert (Hmoa0 : mo !!! Regidx a0_idx = cid_word).
    { rewrite Hmo_a0 (Htp m2). exact cpuid_ret_cid. }
    (* ---- the post-call register-map chain ---- *)
    set (N2 := <[Regidx a4_idx := regval_into_reg (ph_shl cid_word 8)]> mo).
    set (N3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c002000 : mword 64)]> N2).
    set (N4 := <[Regidx a5_idx := regval_into_reg (add_vec (rget N3 a5_idx) (rget N3 a4_idx))]> N3).
    set (N5 := <[Regidx a4_idx := regval_into_reg (add_vec (rget N4 z_idx) (sign_extend' 64 (mword_of_int 1026 : mword 12)))]> N4).
    set (N6 := <[Regidx a0_idx := regval_into_reg (ph_shl cid_word 13)]> N5).
    set (N7 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N6).
    set (N8 := <[Regidx a5_idx := regval_into_reg (add_vec (rget N7 a5_idx) (rget N7 a0_idx))]> N7).
    set (N9 := <[Regidx ra_idx := regval_into_reg ra0]> N8).
    set (N10 := <[Regidx s0_idx := regval_into_reg s00]> N9).
    set (N11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N10).
    (* ---- 0x0c: slliw a4,a0,8 ---- *)
    iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x0c)) a4_idx a0_idx
              (mword_of_int 8 : mword 5) (ph_shl cid_word 8) mo (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite Hmoa0; reflexivity)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (ph_shl cid_word 8)]> mo) with N2.
    (* ---- 0x10: lui a5,0xc002 ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x10)) a5_idx
              (mword_of_int 0xc002 : mword 20) (mword_of_int 0x0c002000 : mword 64) N2 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c002000 : mword 64)]> N2) with N3.
    (* ---- 0x14: c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x14)) a5_idx a4_idx N3 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (rget N3 a5_idx) (rget N3 a4_idx))]> N3) with N4.
    (* ---- 0x16: addi a4,zero,1026 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x16)) a4_idx z_idx
              (mword_of_int 1026 : mword 12) N4 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (add_vec (rget N4 z_idx) (sign_extend' 64 (mword_of_int 1026 : mword 12)))]> N4) with N5.
    (* the two operands of the first store *)
    assert (HN3a5 : rget N3 a5_idx = (mword_of_int 0x0c002000 : mword 64))
      by (rgne; unfold N3; apply upd_eq).
    assert (HN3a4 : rget N3 a4_idx = ph_shl cid_word 8).
    { rgne. unfold N3. rewrite upd_ne; [| vm_compute; discriminate]. unfold N2. apply upd_eq. }
    assert (HN4a5 : rget N4 a5_idx = ph_senb cid_word).
    { rgne. unfold N4. rewrite upd_eq. unfold regval_into_reg, ph_senb.
      rewrite HN3a5 HN3a4. reflexivity. }
    assert (HN5a5 : rget N5 a5_idx = ph_senb cid_word).
    { rgne. unfold N5. rewrite upd_ne; [| vm_compute; discriminate].
      unfold N4. rewrite upd_eq. unfold regval_into_reg, ph_senb.
      rewrite HN3a5 HN3a4. reflexivity. }
    assert (HN4z : rget N4 z_idx = zero_reg).
    { rgne. unfold N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hz0. }
    assert (HN5a4 : rget N5 a4_idx = (mword_of_int 1026 : mword 64)).
    { rgne. unfold N5. rewrite upd_eq. unfold regval_into_reg. rewrite HN4z.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HN5sw : (autocast (T := mword) (subrange_vec_dec (rget N5 a4_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = plic_senable_word).
    { rewrite HN5a4. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x1a: sw a4,128(a5) -- PLIC_SENABLE(hart) = 1026 ---- *)
    iApply (wp_sw_plic_dev_s_sconf (CID := CID) γd γv (mword_of_int (KernelSyms.plicinithart + 0x1a)) false a4_idx a5_idx
              (mword_of_int 128 : mword 12) N5 (n - 2)%nat
              ltac:(rewrite HN5a5; exact (ph_geom_range _ (ph_senable_geom _ Hhart)))
              ltac:(rewrite HN5a5; exact (ph_geom_align _ (ph_senable_geom _ Hhart)))
              ltac:(rewrite HN5a5; exact (ph_geom_canon _ (ph_senable_geom _ Hhart)))
              ltac:(rewrite HN5a5; exact (ph_geom_vpn   _ (ph_senable_geom _ Hhart)))
              ltac:(rewrite HN5sw HN5a5; intros pq Hpq;
                    eexists; split;
                    [ exact (ph_senable_write _ pq _ Hhart)
                    | apply plic_ok_hupd_enable;
                      [ exact Hpq | exact plic_senable_ok_mask ] ])
              with "Hcg Hpc Hi1a Hdinv").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* ---- 0x1e: slliw a0,a0,13 ---- *)
    assert (HN5a0 : rget N5 a0_idx = cid_word).
    { rgne. unfold N5, N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmoa0. }
    iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x1e)) a0_idx a0_idx
              (mword_of_int 13 : mword 5) (ph_shl cid_word 13) N5 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HN5a0; reflexivity)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (ph_shl cid_word 13)]> N5) with N6.
    (* ---- 0x22: lui a5,0xc201 ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x22)) a5_idx
              (mword_of_int 0xc201 : mword 20) (mword_of_int 0x0c201000 : mword 64) N6 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N6) with N7.
    (* ---- 0x26: c.add a5,a5,a0 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x26)) a5_idx a0_idx N7 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (rget N7 a5_idx) (rget N7 a0_idx))]> N7) with N8.
    (* the operands of the second store *)
    assert (HN7a5 : rget N7 a5_idx = (mword_of_int 0x0c201000 : mword 64))
      by (rgne; unfold N7; apply upd_eq).
    assert (HN7a0 : rget N7 a0_idx = ph_shl cid_word 13).
    { rgne. unfold N7. rewrite upd_ne; [| vm_compute; discriminate].
      unfold N6. apply upd_eq. }
    assert (HN8a5 : rget N8 a5_idx = ph_sthb cid_word).
    { rgne. unfold N8. rewrite upd_eq. unfold regval_into_reg, ph_sthb.
      rewrite HN7a5 HN7a0. reflexivity. }
    assert (HN8z : rget N8 z_idx = zero_reg).
    { rgne. unfold N8, N7, N6, N5, N4, N3, N2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hz0. }
    assert (HN8sw : (autocast (T := mword) (subrange_vec_dec (rget N8 z_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = Z_to_bv 32 0).
    { rewrite HN8z. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x28: sw zero,0(a5) -- PLIC_SPRIORITY(hart) = 0 ---- *)
    iApply (wp_sw_plic_dev_s_sconf (CID := CID) γd γv (mword_of_int (KernelSyms.plicinithart + 0x28)) false z_idx a5_idx
              (mword_of_int 0 : mword 12) N8 (n - 2)%nat
              ltac:(rewrite HN8a5; exact (ph_geom_range _ (ph_sthresh_geom _ Hhart)))
              ltac:(rewrite HN8a5; exact (ph_geom_align _ (ph_sthresh_geom _ Hhart)))
              ltac:(rewrite HN8a5; exact (ph_geom_canon _ (ph_sthresh_geom _ Hhart)))
              ltac:(rewrite HN8a5; exact (ph_geom_vpn   _ (ph_sthresh_geom _ Hhart)))
              ltac:(rewrite HN8sw HN8a5; intros pq Hpq;
                    eexists; split;
                    [ exact (ph_sthresh_write _ pq _ Hhart)
                    | apply plic_ok_hupd_thresh; exact Hpq ])
              with "Hcg Hpc Hi28 Hdinv").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.plicinithart + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- 0x2c: c.ldsp ra,8(sp) ---- *)
    assert (HN8sp : N8 !!! Regidx csp_rs1 = sp').
    { unfold N8, N7, N6, N5, N4, N3, N2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmosp. }
    assert (Hpa1' : add_vec (N8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HN8sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (N8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HN8sp. rewrite -Hcsp1. exact Hpa2. }
    assert (Hra0v : rget m1 ra_idx = ra0)
      by (rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : rget m1 s0_idx = s00)
      by (rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x2c)) (mword_of_int 1 : mword 6) ra_idx N8 (n - 2)%nat ra0 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c Hbra").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> N8) with N9.
    (* ---- 0x2e: c.ldsp s0,0(sp) ---- *)
    assert (HN9sp : N9 !!! Regidx csp_rs1 = N8 !!! Regidx csp_rs1)
      by (unfold N9; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -HN9sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x2e)) (mword_of_int 0 : mword 6) s0_idx N9 (n - 2)%nat s00 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e Hbs0").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> N9) with N10.
    (* ---- 0x30: c.addi sp,16 -- the frame pop ---- *)
    assert (HN10sp : N10 !!! Regidx csp_rs1 = sp').
    { unfold N10, N9. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact HN8sp. }
    assert (Hwv : add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite HN10sp. unfold sp', imm_dealloc, imm_entry, sp0. apply frame_cancel_16. }
    assert (Hpop : N10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv HN10sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite HN9sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x30)) imm_dealloc N10
              (n - 2)%nat 2 false Hpop
              with "Hcg Hpc Hi30 Hframe").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.plicinithart + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.plicinithart + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N10) with N11.
    (* ---- 0x32: c.ret ---- *)
    assert (HN11ra : N11 !!! Regidx ra_idx = ra0).
    { unfold N11, N10. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold N9. rewrite upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.plicinithart + 0x32)) ra_idx N11 n false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (rget N11 ra_idx) = ret_tgt)
      by (rgne; rewrite HN11ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! N11 with "Hcg Hpc [%]").
    split.
    - (* [callee_saved m0 N11].  The save/restore of sp and s0 SPANS the call
         (mid-call they hold the wrong values), so the fact does not factor
         through [callee_saved m0 m2] / [callee_saved mo N11] -- each conjunct
         is discharged on its own: sp and s0 by their epilogue restores, the
         other twelve by hopping cpuid's own [callee_saved]. *)
      unfold callee_saved.
      split.
      { unfold N11. rewrite upd_eq. unfold regval_into_reg. exact Hwv. }
      split.
      { unfold N11, N10, s0_idx, s00.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq. unfold regval_into_reg. reflexivity. }
      repeat split; cs_through Hmo_cs mo.
    - exact HN11ra.
  Qed.

End ProofPlicinithart.

End PlicinithartProof.
