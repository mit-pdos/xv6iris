(* ProofUserret.v -- THE USERRET WP over the ptree invariants, sealed
   behind [SpecUserret.USERRET]: all 38 instructions chained, from the
   kernel page table ([tlb_inv_pt]) through the pt2 satp-switch window,
   the 31 trapframe loads at TRAMPOLINE vas, and sret into USER mode,
   ending with the pc at the process's sepc, [utlb_inv_pt] established
   for user-phase execution, and the kernel table parked as [pt_frame]
   for the return trip.  (Formerly UserretAllPt.v; the statement now
   lives in SpecUserret.v as [wp_userret_pt_body].) *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpMmodeShiftiop.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptExecMap.
Require Import TrampPt UserretDefs UserretPt UserretEntryPt.
Require Import SpecUserret.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Local Notation idx2t := (subrange_vec_dec tramp_vpn 26 18).
Local Notation idx1t := (subrange_vec_dec tramp_vpn 17 9).
Local Notation idx0t := (subrange_vec_dec tramp_vpn 8 0).
Local Notation idx0f := (subrange_vec_dec tf_vpn 8 0).

Module UserretProof : USERRET.
Section UserretAllPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_userret_pt (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64))
      (m : regfile) (usatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0 : mword 64)
      (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
       vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
      (dqm : dfrac) :
    wp_userret_pt_body kroot uroot tfp um m usatp
      mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0
      vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
      vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f dqm.
  Proof.
    cbv beta delta [wp_userret_pt_body].
    (* [tf_pa] deliberately NOT unfolded here — see the twin note in
       ProofUservec.v: folded it is ~12 term nodes per trapframe cell instead
       of ~260, and the cells ride in the context for the whole proof.  Worth
       30 % of this file's proof term.  claude-notes/optimization.md. *)
    unfold userret_gpr.
    intros HSIE HMPRV HSXL HTVM HMXR Hmm Hpmm HPBMTE Hmenvval0 Hsenvval0 Hwf HTSR Hsup
      Ha0 HuMode Huasid Huppn.
    iIntros "#Hkt #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc
             #Hclaim Hktlb Hufr Hpc Hfile
             Htf_vra
             Htf_vsp
             Htf_vgp
             Htf_vtp
             Htf_vt0
             Htf_vt1
             Htf_vt2
             Htf_vs0
             Htf_vs1
             Htf_va1
             Htf_va2
             Htf_va3
             Htf_va4
             Htf_va5
             Htf_va6
             Htf_va7
             Htf_vs2
             Htf_vs3
             Htf_vs4
             Htf_vs5
             Htf_vs6
             Htf_vs7
             Htf_vs8
             Htf_vs9
             Htf_vs10
             Htf_vs11
             Htf_vt3
             Htf_vt4
             Htf_vt5
             Htf_vt6
             Htf_va0f
             Hcont".
    (* the 38 instruction resources, from the persistent kernel text *)
    iPoseProof (ui_fencei with "Hkt") as "Hi_fencei".
    iPoseProof (ui_sfence1 with "Hkt") as "Hi_sfence1".
    iPoseProof (ui_csrw with "Hkt") as "Hi_csrw".
    iPoseProof (ui_sfence2 with "Hkt") as "Hi_sfence2".
    (* ================= entry: the page-table switch ================= *)
    iApply (wp_userret_entry_pt kroot uroot tfp um m usatp
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwf Ha0 HuMode Huasid Huppn
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hclaim Hktlb Hufr
                    Hpc Hfile Hi_fencei Hi_sfence1 Hi_csrw Hi_sfence2").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hkfr Hpc Hfile".
    iClear "Hi_fencei".
    iClear "Hi_sfence1".
    iClear "Hi_csrw".
    iClear "Hi_sfence2".
    iPoseProof (ui_lui with "Hkt") as "Hi_lui".
    (* ---- lui @ 0xac ---- *)
    iApply (wp_ualu_pt uroot tfp um 0xac false ai_lui m
              usatp
              (mword_of_int 33554432 : mword 64)
              (fun _ : mstate => luival (mword_of_int 0x2000))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro s; exact (exec_execute_UTYPE_LUI_gpr (mword_of_int 10) (mword_of_int 0x2000) s))
              ltac:(intros s _; apply bv_eq; vm_compute; reflexivity)
              Ha0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_lui").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_lui".
    assert (Hpcx_0xac : add_vec_int (uva 0xac) (if false then 2 else 4) = uva 0xb0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xac) in "Hpc".
    assert (Ha0_addiw : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> m
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554432 : mword 64))
      by (apply upd_eq).
    iPoseProof (ui_addiw with "Hkt") as "Hi_addiw".
    (* ---- addiw @ 0xb0 ---- *)
    iApply (wp_ualu_pt uroot tfp um 0xb0 true ai_addiw (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> m)
              (regval_into_reg (mword_of_int 33554432 : mword 64))
              (mword_of_int 33554431 : mword 64)
              (gpr_addiw_val (mword_of_int 10) (sign_extend' 12 (mword_of_int 63 : mword 6)))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro s; exact (exec_execute_ADDIW_gpr (mword_of_int 10) (mword_of_int 10) (sign_extend' 12 (mword_of_int 63 : mword 6)) s))
              ltac:(intros s Hl; unfold gpr_addiw_val;
                    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false
                      by (vm_compute; reflexivity);
                    rewrite Hl; apply bv_eq; vm_compute; reflexivity)
              Ha0_addiw
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_addiw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_addiw".
    assert (Hpcx_0xb0 : add_vec_int (uva 0xb0) (if true then 2 else 4) = uva 0xb2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xb0) in "Hpc".
    assert (Ha0_slli : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> m)
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554431 : mword 64))
      by (apply upd_eq).
    iPoseProof (ui_slli with "Hkt") as "Hi_slli".
    (* ---- slli @ 0xb2 ---- *)
    iApply (wp_ualu_pt uroot tfp um 0xb2 true ai_slli (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> m))
              (regval_into_reg (mword_of_int 33554431 : mword 64))
              (mword_of_int TRAPFRAME : mword 64)
              (gpr_slli_val (mword_of_int 10) (mword_of_int 13))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro s; exact (exec_execute_SHIFTIOP_SLLI_gpr (mword_of_int 10) (mword_of_int 10) (mword_of_int 13) s))
              ltac:(intros s Hl; unfold gpr_slli_val, gpr_src;
                    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false
                      by (vm_compute; reflexivity);
                    rewrite Hl; apply bv_eq; vm_compute; reflexivity)
              Ha0_slli
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_slli").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile".
    iClear "Hi_slli".
    assert (Hpcx_0xb2 : add_vec_int (uva 0xb2) (if true then 2 else 4) = uva 0xb4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xb2) in "Hpc".
    (* collapse the three a0 writes: a0 = TRAPFRAME *)
    iEval (rewrite upd_upd) in "Hfile".
    iEval (rewrite upd_upd) in "Hfile".
    assert (Hrir : regval_into_reg (mword_of_int TRAPFRAME : mword 64) = (mword_of_int TRAPFRAME : mword 64))
      by reflexivity.
    iEval (rewrite Hrir) in "Hfile".
    set (M0 := <[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> m).
    assert (Ha0_0 : M0 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME)
      by (unfold M0; apply upd_eq).
    iPoseProof (ui_ld_ra with "Hkt") as "Hi_vra".
    (* ---- ld x1, 40(a0) @ 0xb4 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xb4 40 (mword_of_int 1) false M0 vra
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vra Htf_vra").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vra".
    iClear "Hi_vra".
    assert (Hpcx_0xb4 : add_vec_int (uva 0xb4) (if false then 2 else 4) = uva 0xb8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xb4) in "Hpc".
    set (M1 := <[Regidx (mword_of_int 1) := regval_into_reg vra]> M0).
    assert (Ha0_1 : M1 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M1. rewrite upd_ne; [exact Ha0_0 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_sp with "Hkt") as "Hi_vsp".
    (* ---- ld x2, 48(a0) @ 0xb8 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xb8 48 (mword_of_int 2) false M1 vsp
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_1
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vsp Htf_vsp").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vsp".
    iClear "Hi_vsp".
    assert (Hpcx_0xb8 : add_vec_int (uva 0xb8) (if false then 2 else 4) = uva 0xbc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xb8) in "Hpc".
    set (M2 := <[Regidx (mword_of_int 2) := regval_into_reg vsp]> M1).
    assert (Ha0_2 : M2 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M2. rewrite upd_ne; [exact Ha0_1 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_gp with "Hkt") as "Hi_vgp".
    (* ---- ld x3, 56(a0) @ 0xbc ---- *)
    iApply (wp_uld_pt uroot tfp um 0xbc 56 (mword_of_int 3) false M2 vgp
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vgp Htf_vgp").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vgp".
    iClear "Hi_vgp".
    assert (Hpcx_0xbc : add_vec_int (uva 0xbc) (if false then 2 else 4) = uva 0xc0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xbc) in "Hpc".
    set (M3 := <[Regidx (mword_of_int 3) := regval_into_reg vgp]> M2).
    assert (Ha0_3 : M3 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M3. rewrite upd_ne; [exact Ha0_2 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_tp with "Hkt") as "Hi_vtp".
    (* ---- ld x4, 64(a0) @ 0xc0 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xc0 64 (mword_of_int 4) false M3 vtp
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_3
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vtp Htf_vtp").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vtp".
    iClear "Hi_vtp".
    assert (Hpcx_0xc0 : add_vec_int (uva 0xc0) (if false then 2 else 4) = uva 0xc4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xc0) in "Hpc".
    set (M4 := <[Regidx (mword_of_int 4) := regval_into_reg vtp]> M3).
    assert (Ha0_4 : M4 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M4. rewrite upd_ne; [exact Ha0_3 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t0 with "Hkt") as "Hi_vt0".
    (* ---- ld x5, 72(a0) @ 0xc4 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xc4 72 (mword_of_int 5) false M4 vt0
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_4
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt0 Htf_vt0").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt0".
    iClear "Hi_vt0".
    assert (Hpcx_0xc4 : add_vec_int (uva 0xc4) (if false then 2 else 4) = uva 0xc8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xc4) in "Hpc".
    set (M5 := <[Regidx (mword_of_int 5) := regval_into_reg vt0]> M4).
    assert (Ha0_5 : M5 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M5. rewrite upd_ne; [exact Ha0_4 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t1 with "Hkt") as "Hi_vt1".
    (* ---- ld x6, 80(a0) @ 0xc8 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xc8 80 (mword_of_int 6) false M5 vt1
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_5
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt1 Htf_vt1").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt1".
    iClear "Hi_vt1".
    assert (Hpcx_0xc8 : add_vec_int (uva 0xc8) (if false then 2 else 4) = uva 0xcc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xc8) in "Hpc".
    set (M6 := <[Regidx (mword_of_int 6) := regval_into_reg vt1]> M5).
    assert (Ha0_6 : M6 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M6. rewrite upd_ne; [exact Ha0_5 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t2 with "Hkt") as "Hi_vt2".
    (* ---- ld x7, 88(a0) @ 0xcc ---- *)
    iApply (wp_uld_pt uroot tfp um 0xcc 88 (mword_of_int 7) false M6 vt2
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_6
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt2 Htf_vt2").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt2".
    iClear "Hi_vt2".
    assert (Hpcx_0xcc : add_vec_int (uva 0xcc) (if false then 2 else 4) = uva 0xd0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xcc) in "Hpc".
    set (M7 := <[Regidx (mword_of_int 7) := regval_into_reg vt2]> M6).
    assert (Ha0_7 : M7 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M7. rewrite upd_ne; [exact Ha0_6 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_s0 with "Hkt") as "Hi_vs0".
    (* ---- ld x8, 96(a0) @ 0xd0 ---- *)
    iEval (change (ai_cld_tgt 0 12) with (ai_ld 8 96)) in "Hi_vs0".
    iApply (wp_uld_pt uroot tfp um 0xd0 96 (mword_of_int 8) true M7 vs0
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_7
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs0 Htf_vs0").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs0".
    iClear "Hi_vs0".
    assert (Hpcx_0xd0 : add_vec_int (uva 0xd0) (if true then 2 else 4) = uva 0xd2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xd0) in "Hpc".
    set (M8 := <[Regidx (mword_of_int 8) := regval_into_reg vs0]> M7).
    assert (Ha0_8 : M8 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M8. rewrite upd_ne; [exact Ha0_7 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_s1 with "Hkt") as "Hi_vs1".
    (* ---- ld x9, 104(a0) @ 0xd2 ---- *)
    iEval (change (ai_cld_tgt 1 13) with (ai_ld 9 104)) in "Hi_vs1".
    iApply (wp_uld_pt uroot tfp um 0xd2 104 (mword_of_int 9) true M8 vs1
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_8
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs1 Htf_vs1").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs1".
    iClear "Hi_vs1".
    assert (Hpcx_0xd2 : add_vec_int (uva 0xd2) (if true then 2 else 4) = uva 0xd4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xd2) in "Hpc".
    set (M9 := <[Regidx (mword_of_int 9) := regval_into_reg vs1]> M8).
    assert (Ha0_9 : M9 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M9. rewrite upd_ne; [exact Ha0_8 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a1 with "Hkt") as "Hi_va1".
    (* ---- ld x11, 120(a0) @ 0xd4 ---- *)
    iEval (change (ai_cld_tgt 3 15) with (ai_ld 11 120)) in "Hi_va1".
    iApply (wp_uld_pt uroot tfp um 0xd4 120 (mword_of_int 11) true M9 va1
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_9
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va1 Htf_va1").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va1".
    iClear "Hi_va1".
    assert (Hpcx_0xd4 : add_vec_int (uva 0xd4) (if true then 2 else 4) = uva 0xd6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xd4) in "Hpc".
    set (M10 := <[Regidx (mword_of_int 11) := regval_into_reg va1]> M9).
    assert (Ha0_10 : M10 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M10. rewrite upd_ne; [exact Ha0_9 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a2 with "Hkt") as "Hi_va2".
    (* ---- ld x12, 128(a0) @ 0xd6 ---- *)
    iEval (change (ai_cld_tgt 4 16) with (ai_ld 12 128)) in "Hi_va2".
    iApply (wp_uld_pt uroot tfp um 0xd6 128 (mword_of_int 12) true M10 va2
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_10
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va2 Htf_va2").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va2".
    iClear "Hi_va2".
    assert (Hpcx_0xd6 : add_vec_int (uva 0xd6) (if true then 2 else 4) = uva 0xd8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xd6) in "Hpc".
    set (M11 := <[Regidx (mword_of_int 12) := regval_into_reg va2]> M10).
    assert (Ha0_11 : M11 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M11. rewrite upd_ne; [exact Ha0_10 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a3 with "Hkt") as "Hi_va3".
    (* ---- ld x13, 136(a0) @ 0xd8 ---- *)
    iEval (change (ai_cld_tgt 5 17) with (ai_ld 13 136)) in "Hi_va3".
    iApply (wp_uld_pt uroot tfp um 0xd8 136 (mword_of_int 13) true M11 va3
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_11
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va3 Htf_va3").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va3".
    iClear "Hi_va3".
    assert (Hpcx_0xd8 : add_vec_int (uva 0xd8) (if true then 2 else 4) = uva 0xda)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xd8) in "Hpc".
    set (M12 := <[Regidx (mword_of_int 13) := regval_into_reg va3]> M11).
    assert (Ha0_12 : M12 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M12. rewrite upd_ne; [exact Ha0_11 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a4 with "Hkt") as "Hi_va4".
    (* ---- ld x14, 144(a0) @ 0xda ---- *)
    iEval (change (ai_cld_tgt 6 18) with (ai_ld 14 144)) in "Hi_va4".
    iApply (wp_uld_pt uroot tfp um 0xda 144 (mword_of_int 14) true M12 va4
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_12
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va4 Htf_va4").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va4".
    iClear "Hi_va4".
    assert (Hpcx_0xda : add_vec_int (uva 0xda) (if true then 2 else 4) = uva 0xdc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xda) in "Hpc".
    set (M13 := <[Regidx (mword_of_int 14) := regval_into_reg va4]> M12).
    assert (Ha0_13 : M13 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M13. rewrite upd_ne; [exact Ha0_12 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a5 with "Hkt") as "Hi_va5".
    (* ---- ld x15, 152(a0) @ 0xdc ---- *)
    iEval (change (ai_cld_tgt 7 19) with (ai_ld 15 152)) in "Hi_va5".
    iApply (wp_uld_pt uroot tfp um 0xdc 152 (mword_of_int 15) true M13 va5
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_13
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va5 Htf_va5").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va5".
    iClear "Hi_va5".
    assert (Hpcx_0xdc : add_vec_int (uva 0xdc) (if true then 2 else 4) = uva 0xde)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xdc) in "Hpc".
    set (M14 := <[Regidx (mword_of_int 15) := regval_into_reg va5]> M13).
    assert (Ha0_14 : M14 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M14. rewrite upd_ne; [exact Ha0_13 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_a6 with "Hkt") as "Hi_va6".
    (* ---- ld x16, 160(a0) @ 0xde ---- *)
    iApply (wp_uld_pt uroot tfp um 0xde 160 (mword_of_int 16) false M14 va6
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_14
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va6 Htf_va6").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va6".
    iClear "Hi_va6".
    assert (Hpcx_0xde : add_vec_int (uva 0xde) (if false then 2 else 4) = uva 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xde) in "Hpc".
    set (M15 := <[Regidx (mword_of_int 16) := regval_into_reg va6]> M14).
    assert (Ha0_15 : M15 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M15. rewrite upd_ne; [exact Ha0_14 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_a7 with "Hkt") as "Hi_va7".
    (* ---- ld x17, 168(a0) @ 0xe2 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xe2 168 (mword_of_int 17) false M15 va7
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_15
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va7 Htf_va7").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va7".
    iClear "Hi_va7".
    assert (Hpcx_0xe2 : add_vec_int (uva 0xe2) (if false then 2 else 4) = uva 0xe6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xe2) in "Hpc".
    set (M16 := <[Regidx (mword_of_int 17) := regval_into_reg va7]> M15).
    assert (Ha0_16 : M16 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M16. rewrite upd_ne; [exact Ha0_15 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s2 with "Hkt") as "Hi_vs2".
    (* ---- ld x18, 176(a0) @ 0xe6 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xe6 176 (mword_of_int 18) false M16 vs2
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_16
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs2 Htf_vs2").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs2".
    iClear "Hi_vs2".
    assert (Hpcx_0xe6 : add_vec_int (uva 0xe6) (if false then 2 else 4) = uva 0xea)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xe6) in "Hpc".
    set (M17 := <[Regidx (mword_of_int 18) := regval_into_reg vs2]> M16).
    assert (Ha0_17 : M17 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M17. rewrite upd_ne; [exact Ha0_16 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s3 with "Hkt") as "Hi_vs3".
    (* ---- ld x19, 184(a0) @ 0xea ---- *)
    iApply (wp_uld_pt uroot tfp um 0xea 184 (mword_of_int 19) false M17 vs3
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_17
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs3 Htf_vs3").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs3".
    iClear "Hi_vs3".
    assert (Hpcx_0xea : add_vec_int (uva 0xea) (if false then 2 else 4) = uva 0xee)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xea) in "Hpc".
    set (M18 := <[Regidx (mword_of_int 19) := regval_into_reg vs3]> M17).
    assert (Ha0_18 : M18 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M18. rewrite upd_ne; [exact Ha0_17 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s4 with "Hkt") as "Hi_vs4".
    (* ---- ld x20, 192(a0) @ 0xee ---- *)
    iApply (wp_uld_pt uroot tfp um 0xee 192 (mword_of_int 20) false M18 vs4
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_18
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs4 Htf_vs4").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs4".
    iClear "Hi_vs4".
    assert (Hpcx_0xee : add_vec_int (uva 0xee) (if false then 2 else 4) = uva 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xee) in "Hpc".
    set (M19 := <[Regidx (mword_of_int 20) := regval_into_reg vs4]> M18).
    assert (Ha0_19 : M19 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M19. rewrite upd_ne; [exact Ha0_18 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s5 with "Hkt") as "Hi_vs5".
    (* ---- ld x21, 200(a0) @ 0xf2 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xf2 200 (mword_of_int 21) false M19 vs5
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_19
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs5 Htf_vs5").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs5".
    iClear "Hi_vs5".
    assert (Hpcx_0xf2 : add_vec_int (uva 0xf2) (if false then 2 else 4) = uva 0xf6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xf2) in "Hpc".
    set (M20 := <[Regidx (mword_of_int 21) := regval_into_reg vs5]> M19).
    assert (Ha0_20 : M20 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M20. rewrite upd_ne; [exact Ha0_19 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s6 with "Hkt") as "Hi_vs6".
    (* ---- ld x22, 208(a0) @ 0xf6 ---- *)
    iApply (wp_uld_pt uroot tfp um 0xf6 208 (mword_of_int 22) false M20 vs6
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_20
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs6 Htf_vs6").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs6".
    iClear "Hi_vs6".
    assert (Hpcx_0xf6 : add_vec_int (uva 0xf6) (if false then 2 else 4) = uva 0xfa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xf6) in "Hpc".
    set (M21 := <[Regidx (mword_of_int 22) := regval_into_reg vs6]> M20).
    assert (Ha0_21 : M21 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M21. rewrite upd_ne; [exact Ha0_20 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s7 with "Hkt") as "Hi_vs7".
    (* ---- ld x23, 216(a0) @ 0xfa ---- *)
    iApply (wp_uld_pt uroot tfp um 0xfa 216 (mword_of_int 23) false M21 vs7
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_21
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs7 Htf_vs7").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs7".
    iClear "Hi_vs7".
    assert (Hpcx_0xfa : add_vec_int (uva 0xfa) (if false then 2 else 4) = uva 0xfe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xfa) in "Hpc".
    set (M22 := <[Regidx (mword_of_int 23) := regval_into_reg vs7]> M21).
    assert (Ha0_22 : M22 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M22. rewrite upd_ne; [exact Ha0_21 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s8 with "Hkt") as "Hi_vs8".
    (* ---- ld x24, 224(a0) @ 0xfe ---- *)
    iApply (wp_uld_pt uroot tfp um 0xfe 224 (mword_of_int 24) false M22 vs8
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_22
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs8 Htf_vs8").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs8".
    iClear "Hi_vs8".
    assert (Hpcx_0xfe : add_vec_int (uva 0xfe) (if false then 2 else 4) = uva 0x102)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0xfe) in "Hpc".
    set (M23 := <[Regidx (mword_of_int 24) := regval_into_reg vs8]> M22).
    assert (Ha0_23 : M23 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M23. rewrite upd_ne; [exact Ha0_22 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s9 with "Hkt") as "Hi_vs9".
    (* ---- ld x25, 232(a0) @ 0x102 ---- *)
    iApply (wp_uld_pt uroot tfp um 0x102 232 (mword_of_int 25) false M23 vs9
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_23
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs9 Htf_vs9").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs9".
    iClear "Hi_vs9".
    assert (Hpcx_0x102 : add_vec_int (uva 0x102) (if false then 2 else 4) = uva 0x106)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x102) in "Hpc".
    set (M24 := <[Regidx (mword_of_int 25) := regval_into_reg vs9]> M23).
    assert (Ha0_24 : M24 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M24. rewrite upd_ne; [exact Ha0_23 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s10 with "Hkt") as "Hi_vs10".
    (* ---- ld x26, 240(a0) @ 0x106 ---- *)
    iApply (wp_uld_pt uroot tfp um 0x106 240 (mword_of_int 26) false M24 vs10
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_24
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs10 Htf_vs10").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs10".
    iClear "Hi_vs10".
    assert (Hpcx_0x106 : add_vec_int (uva 0x106) (if false then 2 else 4) = uva 0x10a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x106) in "Hpc".
    set (M25 := <[Regidx (mword_of_int 26) := regval_into_reg vs10]> M24).
    assert (Ha0_25 : M25 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M25. rewrite upd_ne; [exact Ha0_24 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_s11 with "Hkt") as "Hi_vs11".
    (* ---- ld x27, 248(a0) @ 0x10a ---- *)
    iApply (wp_uld_pt uroot tfp um 0x10a 248 (mword_of_int 27) false M25 vs11
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_25
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vs11 Htf_vs11").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vs11".
    iClear "Hi_vs11".
    assert (Hpcx_0x10a : add_vec_int (uva 0x10a) (if false then 2 else 4) = uva 0x10e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x10a) in "Hpc".
    set (M26 := <[Regidx (mword_of_int 27) := regval_into_reg vs11]> M25).
    assert (Ha0_26 : M26 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M26. rewrite upd_ne; [exact Ha0_25 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t3 with "Hkt") as "Hi_vt3".
    (* ---- ld x28, 256(a0) @ 0x10e ---- *)
    iApply (wp_uld_pt uroot tfp um 0x10e 256 (mword_of_int 28) false M26 vt3
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_26
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt3 Htf_vt3").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt3".
    iClear "Hi_vt3".
    assert (Hpcx_0x10e : add_vec_int (uva 0x10e) (if false then 2 else 4) = uva 0x112)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x10e) in "Hpc".
    set (M27 := <[Regidx (mword_of_int 28) := regval_into_reg vt3]> M26).
    assert (Ha0_27 : M27 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M27. rewrite upd_ne; [exact Ha0_26 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t4 with "Hkt") as "Hi_vt4".
    (* ---- ld x29, 264(a0) @ 0x112 ---- *)
    iApply (wp_uld_pt uroot tfp um 0x112 264 (mword_of_int 29) false M27 vt4
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_27
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt4 Htf_vt4").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt4".
    iClear "Hi_vt4".
    assert (Hpcx_0x112 : add_vec_int (uva 0x112) (if false then 2 else 4) = uva 0x116)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x112) in "Hpc".
    set (M28 := <[Regidx (mword_of_int 29) := regval_into_reg vt4]> M27).
    assert (Ha0_28 : M28 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M28. rewrite upd_ne; [exact Ha0_27 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t5 with "Hkt") as "Hi_vt5".
    (* ---- ld x30, 272(a0) @ 0x116 ---- *)
    iApply (wp_uld_pt uroot tfp um 0x116 272 (mword_of_int 30) false M28 vt5
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_28
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt5 Htf_vt5").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt5".
    iClear "Hi_vt5".
    assert (Hpcx_0x116 : add_vec_int (uva 0x116) (if false then 2 else 4) = uva 0x11a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x116) in "Hpc".
    set (M29 := <[Regidx (mword_of_int 30) := regval_into_reg vt5]> M28).
    assert (Ha0_29 : M29 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M29. rewrite upd_ne; [exact Ha0_28 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_ld_t6 with "Hkt") as "Hi_vt6".
    (* ---- ld x31, 280(a0) @ 0x11a ---- *)
    iApply (wp_uld_pt uroot tfp um 0x11a 280 (mword_of_int 31) false M29 vt6
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_29
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_vt6 Htf_vt6").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_vt6".
    iClear "Hi_vt6".
    assert (Hpcx_0x11a : add_vec_int (uva 0x11a) (if false then 2 else 4) = uva 0x11e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x11a) in "Hpc".
    set (M30 := <[Regidx (mword_of_int 31) := regval_into_reg vt6]> M29).
    assert (Ha0_30 : M30 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M30. rewrite upd_ne; [exact Ha0_29 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    iPoseProof (ui_cld_a0 with "Hkt") as "Hi_va0f".
    (* ---- ld x10, 112(a0) @ 0x11e ---- *)
    iEval (change (ai_cld_tgt 2 14) with (ai_ld 10 112)) in "Hi_va0f".
    iApply (wp_uld_pt uroot tfp um 0x11e 112 (mword_of_int 10) true M30 va0f
              mstatus0 mie_v mdv0 menvcfg0
              ltac:(vm_compute; lia)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              Ha0_30
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_va0f Htf_va0f").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf_va0f".
    iClear "Hi_va0f".
    assert (Hpcx_0x11e : add_vec_int (uva 0x11e) (if true then 2 else 4) = uva 0x120)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x11e) in "Hpc".
    set (M31 := <[Regidx (mword_of_int 10) := regval_into_reg va0f]> M30).
    iPoseProof (ui_sret with "Hkt") as "Hi_sret".
    (* ---- sret @ 0x120 ---- *)
    iApply (wp_usret_pt uroot tfp um M31
              mstatus0 mie_v mdv0 menvcfg0 senvcfg0 sepc0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsenvval0 HTSR Hsup
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hfile Hi_sret").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hfile".
    iClear "Hi_sret".
    subst M31 M30 M29 M28 M27 M26 M25 M24 M23 M22 M21 M20 M19 M18 M17 M16 M15 M14 M13 M12 M11 M10 M9 M8 M7 M6 M5 M4 M3 M2 M1 M0.
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hfile
Htf_vra Htf_vsp Htf_vgp Htf_vtp Htf_vt0 Htf_vt1 Htf_vt2 Htf_vs0 Htf_vs1 Htf_va1 Htf_va2 Htf_va3 Htf_va4 Htf_va5 Htf_va6 Htf_va7 Htf_vs2 Htf_vs3 Htf_vs4 Htf_vs5 Htf_vs6 Htf_vs7 Htf_vs8 Htf_vs9 Htf_vs10 Htf_vs11 Htf_vt3 Htf_vt4 Htf_vt5 Htf_vt6 Htf_va0f
             Hkfr").
  Qed.

End UserretAllPt.
End UserretProof.
