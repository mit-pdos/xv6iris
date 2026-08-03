(* ProofUservec.v -- THE USERVEC WP over the ptree invariants, sealed behind
   [SpecUservec.USERVEC]: all 44 trap-entry instructions of the trampoline
   page chained, from the trapped-out-of-user machine ([user_trap_frame],
   the USER table installed) through the [csrw sscratch] / [li a0,TRAPFRAME]
   prologue, the 31 register-save stores into the TRAPFRAME page, the four
   kernel-context loads, and the satp switch back to the KERNEL table,
   ending with the pc at [ret_pc vktr] (usertrap), [tlb_inv_pt kroot] live
   and the user table parked as [pt_frame]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import WpMmodeShiftiop.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import TrampPt UptTree.
Require Import UserretDefs UserretPt.
Require Import UservecDefs UservecPt UservecExitPt.
Require Import WpIntrCore.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import SpecUserret SpecUservec.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Module UservecProof : USERVEC.
Section UservecAllPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the user invariant already carries the map well-formedness the exit
     switch needs *)
  Lemma uv_utlb_map_wf (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
    utlb_inv_pt uroot tfp um -∗ ⌜upt_map_wf um⌝.
  Proof.
    iIntros "H". iDestruct "H" as (usatp tlbvec t)
      "(_ & _ & _ & _ & _ & _ & _ & %Hwf & _ & _ & _)".
    iPureIntro. exact Hwf.
  Qed.

  Lemma wp_uservec_pt (C : ucfg) (pt : uptd) (kroot : mword 44)
      (Φ : mval -> iProp Σ)
      (sscr0 : mword 64)
      (vksat vksp vktr vkhart : bv 64)
      (w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160
       w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264
       w272 w280 w112 : bv 64)
      (dqk : dfrac) :
    wp_uservec_pt_body C pt kroot Φ sscr0 vksat vksp vktr vkhart
      w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160
        w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264
        w272 w280 w112 dqk.
  Proof.
    cbv beta zeta delta [wp_uservec_pt_body].
    unfold tf_pa, uservec_gpr.
    intros Hstvec Hdqc HkMode Hkasid Hkppn.
    iIntros "#Hkt #Hhw #Hinv #Hclaim Hframe Hsscr Hkfr
             Hk0 Hk8 Hk16 Hk32
             Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264 Htf272 Htf280
             Htf112
             Hcont".
    (* ============ open the trapped machine ============ *)
    iDestruct (user_trap_frame_open C pt with "Hframe") as (ms_v sc_v stval_v sepc_v g)
      "(%Hok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpcc & Hnpc & Hfile &
        Hutlb & Hdata & %Hcov & %Hacc & Hstvec & Hmie & Hmdl & Hmedl & Hmip &
        Hmenv & Hsenv & Hmse & Hsse)".
    pose proof Hok as Hok2.
    destruct Hok2 as (HSXL & HMPRV & HMXR & HSPP & HSIE & HTVM & HTSR).
    pose proof (uc_mm C) as Hmm.
    assert (Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM MENVCFG_S) = PMM_Disabled)
      by (vm_compute; reflexivity).
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Hmenvval0 : (MENVCFG_S : mword 64) = MENVCFG_S) by reflexivity.
    (* the config cells are owned outright at this join *)
    iEval (rewrite Hdqc) in "Hstvec".
    iEval (rewrite Hdqc) in "Hmie".
    iEval (rewrite Hdqc) in "Hmdl".
    iEval (rewrite Hdqc) in "Hmedl".
    iEval (rewrite Hdqc) in "Hmip".
    iEval (rewrite Hdqc) in "Hmenv".
    iEval (rewrite Hdqc) in "Hsenv".
    iEval (rewrite Hdqc) in "Hmse".
    iEval (rewrite Hdqc) in "Hsse".
    (* the pc: stvec's direct base is the trampoline base *)
    assert (Hsb : stvec_base (uc_stvec C) = uva 0x00).
    { rewrite Hstvec. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hsb) in "Hpcc".
    iEval (rewrite Hsb) in "Hnpc".
    (* ============ the 44 instruction resources ============ *)
    iPoseProof (uvi_csrw_sscratch with "Hkt") as "Hi_csrw_ss".
    iPoseProof (uvi_lui with "Hkt") as "Hi_lui".
    iPoseProof (uvi_addiw with "Hkt") as "Hi_addiw".
    iPoseProof (uvi_slli with "Hkt") as "Hi_slli".
    iPoseProof (uvi_sd_ra with "Hkt") as "Hi_sd_ra".
    iPoseProof (uvi_sd_sp with "Hkt") as "Hi_sd_sp".
    iPoseProof (uvi_sd_gp with "Hkt") as "Hi_sd_gp".
    iPoseProof (uvi_sd_tp with "Hkt") as "Hi_sd_tp".
    iPoseProof (uvi_sd_t0 with "Hkt") as "Hi_sd_t0".
    iPoseProof (uvi_sd_t1 with "Hkt") as "Hi_sd_t1".
    iPoseProof (uvi_sd_t2 with "Hkt") as "Hi_sd_t2".
    iPoseProof (uvi_csd_s0 with "Hkt") as "Hi_csd_s0".
    iPoseProof (uvi_csd_s1 with "Hkt") as "Hi_csd_s1".
    iPoseProof (uvi_csd_a1 with "Hkt") as "Hi_csd_a1".
    iPoseProof (uvi_csd_a2 with "Hkt") as "Hi_csd_a2".
    iPoseProof (uvi_csd_a3 with "Hkt") as "Hi_csd_a3".
    iPoseProof (uvi_csd_a4 with "Hkt") as "Hi_csd_a4".
    iPoseProof (uvi_csd_a5 with "Hkt") as "Hi_csd_a5".
    iPoseProof (uvi_sd_a6 with "Hkt") as "Hi_sd_a6".
    iPoseProof (uvi_sd_a7 with "Hkt") as "Hi_sd_a7".
    iPoseProof (uvi_sd_s2 with "Hkt") as "Hi_sd_s2".
    iPoseProof (uvi_sd_s3 with "Hkt") as "Hi_sd_s3".
    iPoseProof (uvi_sd_s4 with "Hkt") as "Hi_sd_s4".
    iPoseProof (uvi_sd_s5 with "Hkt") as "Hi_sd_s5".
    iPoseProof (uvi_sd_s6 with "Hkt") as "Hi_sd_s6".
    iPoseProof (uvi_sd_s7 with "Hkt") as "Hi_sd_s7".
    iPoseProof (uvi_sd_s8 with "Hkt") as "Hi_sd_s8".
    iPoseProof (uvi_sd_s9 with "Hkt") as "Hi_sd_s9".
    iPoseProof (uvi_sd_s10 with "Hkt") as "Hi_sd_s10".
    iPoseProof (uvi_sd_s11 with "Hkt") as "Hi_sd_s11".
    iPoseProof (uvi_sd_t3 with "Hkt") as "Hi_sd_t3".
    iPoseProof (uvi_sd_t4 with "Hkt") as "Hi_sd_t4".
    iPoseProof (uvi_sd_t5 with "Hkt") as "Hi_sd_t5".
    iPoseProof (uvi_sd_t6 with "Hkt") as "Hi_sd_t6".
    iPoseProof (uvi_csrr_sscratch with "Hkt") as "Hi_csrr_ss".
    iPoseProof (uvi_sd_a0 with "Hkt") as "Hi_sd_a0".
    iPoseProof (uvi_ld_sp with "Hkt") as "Hi_ld_sp".
    iPoseProof (uvi_ld_tp with "Hkt") as "Hi_ld_tp".
    iPoseProof (uvi_ld_t0 with "Hkt") as "Hi_ld_t0".
    iPoseProof (uvi_ld_t1 with "Hkt") as "Hi_ld_t1".
    iPoseProof (uvi_sfence1 with "Hkt") as "Hi_sf1".
    iPoseProof (uvi_csrw_satp with "Hkt") as "Hi_csrw_satp".
    iPoseProof (uvi_sfence2 with "Hkt") as "Hi_sf2".
    iPoseProof (uvi_cjalr_t0 with "Hkt") as "Hi_cjalr".
    (* ---- csrw sscratch, a0 @ 0x00 ---- *)
    iApply (wp_ucsrw_sscratch_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x00 false (mword_of_int 10) g sscr0
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb [$Hpcc $Hnpc] Hfile Hi_csrw_ss").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile".
    assert (Hpcx_0x00 : add_vec_int (uva 0x00) (if false then 2 else 4) = uva 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x00) in "Hpc".
    (* ---- lui a0, 0x2000 @ 0x04 ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x04 false ai_lui g
              (g !!! Regidx (mword_of_int 10) : mword 64)
              (mword_of_int 33554432 : mword 64)
              (fun _ : mstate => luival (mword_of_int 0x2000))
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro s; exact (exec_execute_UTYPE_LUI_gpr (mword_of_int 10) (mword_of_int 0x2000) s))
              ltac:(intros s _; apply bv_eq; vm_compute; reflexivity)
              ltac:(reflexivity)
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
    assert (Hpcx_0x04 : add_vec_int (uva 0x04) (if false then 2 else 4) = uva 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x04) in "Hpc".
    assert (Ha0_addiw : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554432 : mword 64))
      by (apply upd_eq).
    (* ---- c.addiw a0, -1 @ 0x08 ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x08 true ai_addiw (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)
              (regval_into_reg (mword_of_int 33554432 : mword 64))
              (mword_of_int 33554431 : mword 64)
              (gpr_addiw_val (mword_of_int 10) (sign_extend' 12 (mword_of_int 63 : mword 6)))
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
    assert (Hpcx_0x08 : add_vec_int (uva 0x08) (if true then 2 else 4) = uva 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x08) in "Hpc".
    assert (Ha0_slli : <[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g)
                      !!! Regidx (mword_of_int 10)
                    = regval_into_reg (mword_of_int 33554431 : mword 64))
      by (apply upd_eq).
    (* ---- c.slli a0, 13 @ 0x0a ---- *)
    iApply (wp_ualu_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x0a true ai_slli (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554431 : mword 64)]> (<[Regidx (mword_of_int 10) := regval_into_reg (mword_of_int 33554432 : mword 64)]> g))
              (regval_into_reg (mword_of_int 33554431 : mword 64))
              (mword_of_int TRAPFRAME : mword 64)
              (gpr_slli_val (mword_of_int 10) (mword_of_int 13))
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
    assert (Hpcx_0x0a : add_vec_int (uva 0x0a) (if true then 2 else 4) = uva 0x0c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x0a) in "Hpc".
    (* collapse the three a0 writes: a0 = TRAPFRAME *)
    iEval (rewrite upd_upd) in "Hfile".
    iEval (rewrite upd_upd) in "Hfile".
    assert (Hrir : regval_into_reg (mword_of_int TRAPFRAME : mword 64) = (mword_of_int TRAPFRAME : mword 64))
      by reflexivity.
    iEval (rewrite Hrir) in "Hfile".
    set (M2 := <[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> g).
    assert (Ha0_2 : M2 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME)
      by (unfold M2; apply upd_eq).
    (* the 30 saved registers are untouched by the [li]: peel a0's insert *)
    assert (Hg1 : M2 !!! Regidx (mword_of_int 1) = (g !!! Regidx (mword_of_int 1) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg2 : M2 !!! Regidx (mword_of_int 2) = (g !!! Regidx (mword_of_int 2) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg3 : M2 !!! Regidx (mword_of_int 3) = (g !!! Regidx (mword_of_int 3) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg4 : M2 !!! Regidx (mword_of_int 4) = (g !!! Regidx (mword_of_int 4) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg5 : M2 !!! Regidx (mword_of_int 5) = (g !!! Regidx (mword_of_int 5) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg6 : M2 !!! Regidx (mword_of_int 6) = (g !!! Regidx (mword_of_int 6) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg7 : M2 !!! Regidx (mword_of_int 7) = (g !!! Regidx (mword_of_int 7) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg8 : M2 !!! Regidx (mword_of_int 8) = (g !!! Regidx (mword_of_int 8) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg9 : M2 !!! Regidx (mword_of_int 9) = (g !!! Regidx (mword_of_int 9) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg11 : M2 !!! Regidx (mword_of_int 11) = (g !!! Regidx (mword_of_int 11) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg12 : M2 !!! Regidx (mword_of_int 12) = (g !!! Regidx (mword_of_int 12) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg13 : M2 !!! Regidx (mword_of_int 13) = (g !!! Regidx (mword_of_int 13) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg14 : M2 !!! Regidx (mword_of_int 14) = (g !!! Regidx (mword_of_int 14) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg15 : M2 !!! Regidx (mword_of_int 15) = (g !!! Regidx (mword_of_int 15) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg16 : M2 !!! Regidx (mword_of_int 16) = (g !!! Regidx (mword_of_int 16) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg17 : M2 !!! Regidx (mword_of_int 17) = (g !!! Regidx (mword_of_int 17) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg18 : M2 !!! Regidx (mword_of_int 18) = (g !!! Regidx (mword_of_int 18) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg19 : M2 !!! Regidx (mword_of_int 19) = (g !!! Regidx (mword_of_int 19) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg20 : M2 !!! Regidx (mword_of_int 20) = (g !!! Regidx (mword_of_int 20) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg21 : M2 !!! Regidx (mword_of_int 21) = (g !!! Regidx (mword_of_int 21) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg22 : M2 !!! Regidx (mword_of_int 22) = (g !!! Regidx (mword_of_int 22) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg23 : M2 !!! Regidx (mword_of_int 23) = (g !!! Regidx (mword_of_int 23) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg24 : M2 !!! Regidx (mword_of_int 24) = (g !!! Regidx (mword_of_int 24) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg25 : M2 !!! Regidx (mword_of_int 25) = (g !!! Regidx (mword_of_int 25) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg26 : M2 !!! Regidx (mword_of_int 26) = (g !!! Regidx (mword_of_int 26) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg27 : M2 !!! Regidx (mword_of_int 27) = (g !!! Regidx (mword_of_int 27) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg28 : M2 !!! Regidx (mword_of_int 28) = (g !!! Regidx (mword_of_int 28) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg29 : M2 !!! Regidx (mword_of_int 29) = (g !!! Regidx (mword_of_int 29) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg30 : M2 !!! Regidx (mword_of_int 30) = (g !!! Regidx (mword_of_int 30) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg31 : M2 !!! Regidx (mword_of_int 31) = (g !!! Regidx (mword_of_int 31) : mword 64)).
    { unfold M2. rewrite upd_ne; [reflexivity |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    (* ---- sd x1, 40(a0) @ 0x0c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x0c 40 (mword_of_int 1) false M2 (w40 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_ra Htf40").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf40".
    iEval (rewrite Hg1) in "Htf40".
    assert (Hpcx_0x0c : add_vec_int (uva 0x0c) (if false then 2 else 4) = uva 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x0c) in "Hpc".
    (* ---- sd x2, 48(a0) @ 0x10 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x10 48 (mword_of_int 2) false M2 (w48 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_sp Htf48").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf48".
    iEval (rewrite Hg2) in "Htf48".
    assert (Hpcx_0x10 : add_vec_int (uva 0x10) (if false then 2 else 4) = uva 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x10) in "Hpc".
    (* ---- sd x3, 56(a0) @ 0x14 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x14 56 (mword_of_int 3) false M2 (w56 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_gp Htf56").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf56".
    iEval (rewrite Hg3) in "Htf56".
    assert (Hpcx_0x14 : add_vec_int (uva 0x14) (if false then 2 else 4) = uva 0x18)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x14) in "Hpc".
    (* ---- sd x4, 64(a0) @ 0x18 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x18 64 (mword_of_int 4) false M2 (w64 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_tp Htf64").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf64".
    iEval (rewrite Hg4) in "Htf64".
    assert (Hpcx_0x18 : add_vec_int (uva 0x18) (if false then 2 else 4) = uva 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x18) in "Hpc".
    (* ---- sd x5, 72(a0) @ 0x1c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x1c 72 (mword_of_int 5) false M2 (w72 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t0 Htf72").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf72".
    iEval (rewrite Hg5) in "Htf72".
    assert (Hpcx_0x1c : add_vec_int (uva 0x1c) (if false then 2 else 4) = uva 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x1c) in "Hpc".
    (* ---- sd x6, 80(a0) @ 0x20 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x20 80 (mword_of_int 6) false M2 (w80 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t1 Htf80").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf80".
    iEval (rewrite Hg6) in "Htf80".
    assert (Hpcx_0x20 : add_vec_int (uva 0x20) (if false then 2 else 4) = uva 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x20) in "Hpc".
    (* ---- sd x7, 88(a0) @ 0x24 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x24 88 (mword_of_int 7) false M2 (w88 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t2 Htf88").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf88".
    iEval (rewrite Hg7) in "Htf88".
    assert (Hpcx_0x24 : add_vec_int (uva 0x24) (if false then 2 else 4) = uva 0x28)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x24) in "Hpc".
    iEval (change (uvai_csd_tgt 0 12) with (uvai_sd 8 96)) in "Hi_csd_s0".
    (* ---- sd x8, 96(a0) @ 0x28 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x28 96 (mword_of_int 8) true M2 (w96 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_s0 Htf96").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf96".
    iEval (rewrite Hg8) in "Htf96".
    assert (Hpcx_0x28 : add_vec_int (uva 0x28) (if true then 2 else 4) = uva 0x2a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x28) in "Hpc".
    iEval (change (uvai_csd_tgt 1 13) with (uvai_sd 9 104)) in "Hi_csd_s1".
    (* ---- sd x9, 104(a0) @ 0x2a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x2a 104 (mword_of_int 9) true M2 (w104 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_s1 Htf104").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf104".
    iEval (rewrite Hg9) in "Htf104".
    assert (Hpcx_0x2a : add_vec_int (uva 0x2a) (if true then 2 else 4) = uva 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2a) in "Hpc".
    iEval (change (uvai_csd_tgt 3 15) with (uvai_sd 11 120)) in "Hi_csd_a1".
    (* ---- sd x11, 120(a0) @ 0x2c ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x2c 120 (mword_of_int 11) true M2 (w120 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a1 Htf120").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf120".
    iEval (rewrite Hg11) in "Htf120".
    assert (Hpcx_0x2c : add_vec_int (uva 0x2c) (if true then 2 else 4) = uva 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2c) in "Hpc".
    iEval (change (uvai_csd_tgt 4 16) with (uvai_sd 12 128)) in "Hi_csd_a2".
    (* ---- sd x12, 128(a0) @ 0x2e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x2e 128 (mword_of_int 12) true M2 (w128 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a2 Htf128").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf128".
    iEval (rewrite Hg12) in "Htf128".
    assert (Hpcx_0x2e : add_vec_int (uva 0x2e) (if true then 2 else 4) = uva 0x30)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x2e) in "Hpc".
    iEval (change (uvai_csd_tgt 5 17) with (uvai_sd 13 136)) in "Hi_csd_a3".
    (* ---- sd x13, 136(a0) @ 0x30 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x30 136 (mword_of_int 13) true M2 (w136 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a3 Htf136").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf136".
    iEval (rewrite Hg13) in "Htf136".
    assert (Hpcx_0x30 : add_vec_int (uva 0x30) (if true then 2 else 4) = uva 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x30) in "Hpc".
    iEval (change (uvai_csd_tgt 6 18) with (uvai_sd 14 144)) in "Hi_csd_a4".
    (* ---- sd x14, 144(a0) @ 0x32 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x32 144 (mword_of_int 14) true M2 (w144 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a4 Htf144").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf144".
    iEval (rewrite Hg14) in "Htf144".
    assert (Hpcx_0x32 : add_vec_int (uva 0x32) (if true then 2 else 4) = uva 0x34)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x32) in "Hpc".
    iEval (change (uvai_csd_tgt 7 19) with (uvai_sd 15 152)) in "Hi_csd_a5".
    (* ---- sd x15, 152(a0) @ 0x34 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x34 152 (mword_of_int 15) true M2 (w152 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_csd_a5 Htf152").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf152".
    iEval (rewrite Hg15) in "Htf152".
    assert (Hpcx_0x34 : add_vec_int (uva 0x34) (if true then 2 else 4) = uva 0x36)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x34) in "Hpc".
    (* ---- sd x16, 160(a0) @ 0x36 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x36 160 (mword_of_int 16) false M2 (w160 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a6 Htf160").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf160".
    iEval (rewrite Hg16) in "Htf160".
    assert (Hpcx_0x36 : add_vec_int (uva 0x36) (if false then 2 else 4) = uva 0x3a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x36) in "Hpc".
    (* ---- sd x17, 168(a0) @ 0x3a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x3a 168 (mword_of_int 17) false M2 (w168 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a7 Htf168").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf168".
    iEval (rewrite Hg17) in "Htf168".
    assert (Hpcx_0x3a : add_vec_int (uva 0x3a) (if false then 2 else 4) = uva 0x3e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x3a) in "Hpc".
    (* ---- sd x18, 176(a0) @ 0x3e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x3e 176 (mword_of_int 18) false M2 (w176 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s2 Htf176").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf176".
    iEval (rewrite Hg18) in "Htf176".
    assert (Hpcx_0x3e : add_vec_int (uva 0x3e) (if false then 2 else 4) = uva 0x42)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x3e) in "Hpc".
    (* ---- sd x19, 184(a0) @ 0x42 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x42 184 (mword_of_int 19) false M2 (w184 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s3 Htf184").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf184".
    iEval (rewrite Hg19) in "Htf184".
    assert (Hpcx_0x42 : add_vec_int (uva 0x42) (if false then 2 else 4) = uva 0x46)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x42) in "Hpc".
    (* ---- sd x20, 192(a0) @ 0x46 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x46 192 (mword_of_int 20) false M2 (w192 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s4 Htf192").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf192".
    iEval (rewrite Hg20) in "Htf192".
    assert (Hpcx_0x46 : add_vec_int (uva 0x46) (if false then 2 else 4) = uva 0x4a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x46) in "Hpc".
    (* ---- sd x21, 200(a0) @ 0x4a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x4a 200 (mword_of_int 21) false M2 (w200 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s5 Htf200").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf200".
    iEval (rewrite Hg21) in "Htf200".
    assert (Hpcx_0x4a : add_vec_int (uva 0x4a) (if false then 2 else 4) = uva 0x4e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x4a) in "Hpc".
    (* ---- sd x22, 208(a0) @ 0x4e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x4e 208 (mword_of_int 22) false M2 (w208 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s6 Htf208").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf208".
    iEval (rewrite Hg22) in "Htf208".
    assert (Hpcx_0x4e : add_vec_int (uva 0x4e) (if false then 2 else 4) = uva 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x4e) in "Hpc".
    (* ---- sd x23, 216(a0) @ 0x52 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x52 216 (mword_of_int 23) false M2 (w216 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s7 Htf216").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf216".
    iEval (rewrite Hg23) in "Htf216".
    assert (Hpcx_0x52 : add_vec_int (uva 0x52) (if false then 2 else 4) = uva 0x56)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x52) in "Hpc".
    (* ---- sd x24, 224(a0) @ 0x56 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x56 224 (mword_of_int 24) false M2 (w224 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s8 Htf224").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf224".
    iEval (rewrite Hg24) in "Htf224".
    assert (Hpcx_0x56 : add_vec_int (uva 0x56) (if false then 2 else 4) = uva 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x56) in "Hpc".
    (* ---- sd x25, 232(a0) @ 0x5a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x5a 232 (mword_of_int 25) false M2 (w232 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s9 Htf232").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf232".
    iEval (rewrite Hg25) in "Htf232".
    assert (Hpcx_0x5a : add_vec_int (uva 0x5a) (if false then 2 else 4) = uva 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x5a) in "Hpc".
    (* ---- sd x26, 240(a0) @ 0x5e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x5e 240 (mword_of_int 26) false M2 (w240 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s10 Htf240").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf240".
    iEval (rewrite Hg26) in "Htf240".
    assert (Hpcx_0x5e : add_vec_int (uva 0x5e) (if false then 2 else 4) = uva 0x62)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x5e) in "Hpc".
    (* ---- sd x27, 248(a0) @ 0x62 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x62 248 (mword_of_int 27) false M2 (w248 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_s11 Htf248").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf248".
    iEval (rewrite Hg27) in "Htf248".
    assert (Hpcx_0x62 : add_vec_int (uva 0x62) (if false then 2 else 4) = uva 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x62) in "Hpc".
    (* ---- sd x28, 256(a0) @ 0x66 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x66 256 (mword_of_int 28) false M2 (w256 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t3 Htf256").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf256".
    iEval (rewrite Hg28) in "Htf256".
    assert (Hpcx_0x66 : add_vec_int (uva 0x66) (if false then 2 else 4) = uva 0x6a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x66) in "Hpc".
    (* ---- sd x29, 264(a0) @ 0x6a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x6a 264 (mword_of_int 29) false M2 (w264 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t4 Htf264").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf264".
    iEval (rewrite Hg29) in "Htf264".
    assert (Hpcx_0x6a : add_vec_int (uva 0x6a) (if false then 2 else 4) = uva 0x6e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x6a) in "Hpc".
    (* ---- sd x30, 272(a0) @ 0x6e ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x6e 272 (mword_of_int 30) false M2 (w272 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t5 Htf272").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf272".
    iEval (rewrite Hg30) in "Htf272".
    assert (Hpcx_0x6e : add_vec_int (uva 0x6e) (if false then 2 else 4) = uva 0x72)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x6e) in "Hpc".
    (* ---- sd x31, 280(a0) @ 0x72 ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x72 280 (mword_of_int 31) false M2 (w280 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_t6 Htf280").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf280".
    iEval (rewrite Hg31) in "Htf280".
    assert (Hpcx_0x72 : add_vec_int (uva 0x72) (if false then 2 else 4) = uva 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x72) in "Hpc".
    (* ---- csrr t0, sscratch @ 0x76 ---- *)
    iApply (wp_ucsrr_sscratch_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x76 false (mword_of_int 5) M2
              (g !!! Regidx (mword_of_int 10) : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              ltac:(vm_compute; lia)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
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
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile Hi_csrr_ss").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsscr Hutlb Hpc Hfile".
    assert (Hpcx_0x76 : add_vec_int (uva 0x76) (if false then 2 else 4) = uva 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x76) in "Hpc".
    set (M3 := <[Regidx (mword_of_int 5) := regval_into_reg (g !!! Regidx (mword_of_int 10) : mword 64)]> M2).
    assert (Ha0_3 : M3 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M3. rewrite upd_ne; [exact Ha0_2 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    assert (Hg112 : M3 !!! Regidx (mword_of_int 5) = (g !!! Regidx (mword_of_int 10) : mword 64)).
    { unfold M3. rewrite upd_eq. reflexivity. }
    (* ---- sd t0, 112(a0) @ 0x7a ---- *)
    iApply (wp_usd_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x7a 112 (mword_of_int 5) false M3 (w112 : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_sd_a0 Htf112").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Htf112".
    iEval (rewrite Hg112) in "Htf112".
    assert (Hpcx_0x7a : add_vec_int (uva 0x7a) (if false then 2 else 4) = uva 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x7a) in "Hpc".
    (* ---- ld x2, 8(a0) @ 0x7e ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x7e 8 (mword_of_int 2) false M3 vksp
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_sp Hk8").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk8".
    assert (Hpcx_0x7e : add_vec_int (uva 0x7e) (if false then 2 else 4) = uva 0x82)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x7e) in "Hpc".
    set (M4 := <[Regidx (mword_of_int 2) := regval_into_reg vksp]> M3).
    assert (Ha0_4 : M4 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M4. rewrite upd_ne; [exact Ha0_3 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    (* ---- ld x4, 32(a0) @ 0x82 ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x82 32 (mword_of_int 4) false M4 vkhart
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_tp Hk32").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk32".
    assert (Hpcx_0x82 : add_vec_int (uva 0x82) (if false then 2 else 4) = uva 0x86)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x82) in "Hpc".
    set (M5 := <[Regidx (mword_of_int 4) := regval_into_reg vkhart]> M4).
    assert (Ha0_5 : M5 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M5. rewrite upd_ne; [exact Ha0_4 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    (* ---- ld x5, 16(a0) @ 0x86 ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x86 16 (mword_of_int 5) false M5 vktr
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_t0 Hk16").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk16".
    assert (Hpcx_0x86 : add_vec_int (uva 0x86) (if false then 2 else 4) = uva 0x8a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x86) in "Hpc".
    set (M6 := <[Regidx (mword_of_int 5) := regval_into_reg vktr]> M5).
    assert (Ha0_6 : M6 !!! Regidx (mword_of_int 10) = mword_of_int TRAPFRAME).
    { unfold M6. rewrite upd_ne; [exact Ha0_5 |].
      intro He. injection He as He2. vm_compute in He2. congruence. }
    (* ---- ld x6, 0(a0) @ 0x8a ---- *)
    iApply (wp_uld_pt (ud_root pt) (ud_tfp pt) (ud_um pt) Φ 0x8a 0 (mword_of_int 6) false M6 vksat
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
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
              ltac:(intro Hf; vm_compute in Hf; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hi_ld_t1 Hk0").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfile Hk0".
    assert (Hpcx_0x8a : add_vec_int (uva 0x8a) (if false then 2 else 4) = uva 0x8e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcx_0x8a) in "Hpc".
    set (M7 := <[Regidx (mword_of_int 6) := regval_into_reg vksat]> M6).
    (* ---- the exit switch: sfence / csrw satp,t1 / sfence / c.jalr t0 ---- *)
    assert (Ht1v : M7 !!! Regidx (mword_of_int 6) = (vksat : mword 64)).
    { unfold M7. rewrite upd_eq. reflexivity. }
    assert (Ht0v : M7 !!! Regidx (mword_of_int 5) = (vktr : mword 64)).
    { unfold M7. rewrite upd_ne.
      - unfold M6. rewrite upd_eq. reflexivity.
      - intro He. injection He as He2. vm_compute in He2. congruence. }
    iDestruct (uv_utlb_map_wf with "Hutlb") as %Hwfu.
    iApply (wp_uservec_exit_pt kroot (ud_root pt) (ud_tfp pt) (ud_um pt) Φ M7
              (vksat : mword 64)
              ms_v (uc_mie C) (uc_mideleg C) MENVCFG_S
              HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwfu Ht1v HkMode Hkasid Hkppn
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hclaim Hutlb Hkfr Hpc Hfile
                    Hi_sf1 Hi_csrw_satp Hi_sf2 Hi_cjalr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hufr Hpc Hfile".
    iEval (rewrite Ht0v) in "Hpc".
    (* rebuild the config bundle *)
    iAssert (user_cfg C) with "[Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse]" as "Hcfg".
    { unfold user_cfg. rewrite Hdqc.
      iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse". }
    subst M7 M6 M5 M4 M3 M2.
    iSpecialize ("Hcont" $! g ms_v sc_v stval_v sepc_v with "[%]"); [ exact Hok |].
    iApply ("Hcont" with "Hhs Hpriv Hms Hsc Hstval Hsepc Hsscr Hktlb Hufr Hdata Hcfg Hpc Hfile
             Hk0 Hk8 Hk16 Hk32
             Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264 Htf272 Htf280
             Htf112").
  Qed.

End UservecAllPt.
End UservecProof.
