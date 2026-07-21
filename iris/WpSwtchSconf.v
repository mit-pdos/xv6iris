(* WpSwtchSconf.v -- the proof of swtch()'s sconf-tier context-switch spec
   (SpecSwtch.v), as a sealed module.

   Plan (mirrors the retired smode-config wp_swtch proof that lived in
   WpSwtchVc.v, over the same decode facts / VCgen run, with three changes):

   - CONFIG: the caller hands the [swconf] bundle; the proof unbundles
     [sconf γ] into the raw CSR resources and runs the plain (non-sp-
     tracking) engine [wp_vc_block_s_den_r (kpt_regime root_ppn)] -- swtch
     loads sp from memory, which the sp-tracking sconf VCgen cannot model.
     The SIE=0 pin comes from [intr_count 1]'s ghost eighth agreeing with
     [sconf]'s tied half; MPRV/SXL/MXR from [sconf_ms_facts]; menvcfg is
     pinned MENVCFG_S by the bundle.  [sie_arm]/[intr_count]/[hart_state]/
     [tlb_inv_pt] ride through untouched and are re-bundled at both exits.

   - ▷ TARGET: the [valid_context newc] premise is ▷-guarded.  At entry,
     [fupd_wp] + [later_exist_except_0] + timelessness strip the two pure
     facts and the (timeless) [ctx_cells]; the non-timeless resume wand
     stays under ▷ until the final c.ret, discharged with the later-handing
     leaf [wp_cret_s_zca_r_later] (WpSmodePtCtl.v) -- the [iNext] there
     strips it.

   - PAYLOAD: P is three-place (resumed ctx, resumer ctx, resumer tp); the
     proof supplies [P newc oldc (m0 !!! x4)] and must show x4 threads
     through the block unchanged (x4 is not among swtch_regs1's keys), and
     hands the resumed party [ctx_cells newc new_vs] back through the wand
     (the block only reads new's cells; [swtch_heap1] returns them intact). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecode KernelText RegFile WpGpr.
Require Import WpMmodeLeafBase WpRvcBridge SRegime.
Require Import SmodeCore KernelRvcDecode.
Require Import VcGen VcGenS.
Require Import KptTree.
Require Import IntrDefs.
Require Import WpSmodePtCtl.
Require Import SwtchCtx.
Require Import WpSwtchVc.
Require Import SpecSwtch.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Module SwtchProof : SWTCH.
Section WpSwtchSconf.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_swtch_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
      (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64)) :
    wp_swtch_sconf_body γ root_ppn Φ P oldc newc m0 old_vs.
  Proof.
    cbv beta delta [wp_swtch_sconf_body].
    iIntros (Hlen_old Holdc Hnewc Hal_old)
      "#Ht Hswconf Hpc Hfile Holdcells Hvalidnew HP Hwold".
    (* ---- unbundle swconf / sconf into the raw CSR resources ---- *)
    iEval (rewrite /swconf) in "Hswconf".
    iDestruct "Hswconf" as "(Hsc & Hhs & Htlbinv & Hsiearm & Hintr)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmiex" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    (* ---- SIE = 0 from the intr_count-1 eighth agreeing with sconf's tied half ---- *)
    iDestruct (intr_count_pos_off γ root_ppn 0 with "Hintr") as "[Hq0 Hrestore]".
    iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
      by (rewrite Hb0; vm_compute; reflexivity).
    (* re-pack [intr_count 1] NOW (folded): a folded [intr_count] has no leading
       ▷, so it rides through the c.ret's [iNext] untouched -- whereas the raw
       [intr_restore] carries an internal ▷ that [iNext] would strip. *)
    iDestruct (intr_count_pack_S γ root_ppn 0 with "Hq0 Hrestore") as "Hintr".
    (* ---- strip the ▷ off the target VC: keep the resume wand ▷'d ---- *)
    iApply fupd_wp.
    iEval (rewrite (valid_context_unfold (swconf γ root_ppn) Φ P newc)
                   /valid_context_pre bi.later_exist) in "Hvalidnew".
    iDestruct "Hvalidnew" as (new_vs) "Hvalidnew".
    iDestruct "Hvalidnew" as "(>%Hlen_new & >%Hal_new & >Hnewcells & Hnewwand)".
    iModIntro.
    (* ---- the symbolic environment: 0..31 = m0; 32..45 = new's saved; 46..59 = old's ---- *)
    iDestruct (VcGenS.gpr_file_dom with "Hfile") as "[%Hdom Hfile]".
    iDestruct (gpr_file_x0 m0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0 Hfile]".
    set (rho := fun k : nat =>
           if (k <? 32)%nat
           then m0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if (k <? 46)%nat then nth (k - 32) new_vs (mword_of_int 0)
           else nth (k - 46) old_vs (mword_of_int 0)).
    assert (Hden : vregs_den rho vregs_init = m0).
    { apply (vregs_den_init_agree _ _ Hx0). intros k Hk.
      unfold rho. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (Hrho10 : rho 10%nat = oldc) by (unfold rho; exact Holdc).
    assert (Hrho11 : rho 11%nat = newc) by (unfold rho; exact Hnewc).
    assert (Hmapold : map (fun w => rho w)
              [46;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat = old_vs).
    { unfold rho; cbn.
      apply (list14_nth old_vs (mword_of_int 0) Hlen_old). }
    assert (Hmapnew : map (fun w => rho w)
              [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat = new_vs).
    { unfold rho; cbn.
      apply (list14_nth new_vs (mword_of_int 0) Hlen_new). }
    iDestruct (swtch_code with "Ht") as "Hcode".
    iEval (rewrite -Hden) in "Hfile".
    (* ---- run the 28-instruction straight-line block (plain kpt_regime engine) ---- *)
    iApply (wp_vc_block_s_den root_ppn swtch_prog Φ
              (VSt KernelSyms.swtch vregs_init swtch_heap0 [])
              (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 [])
              rho ms mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 swtch_run
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hcode [Holdcells Hnewcells] []").
    { rewrite /vheap_own /swtch_heap0 big_sepL_app.
      rewrite (seg_cells_ctx rho 10 oldc 0 _ Hrho10).
      rewrite (seg_cells_ctx rho 11 newc 0 _ Hrho11).
      rewrite Hmapold Hmapnew.
      rewrite -/(ctx_cells oldc old_vs) -/(ctx_cells newc new_vs).
      iFrame "Holdcells Hnewcells". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    (* ---- split the post-block heap into old's (now current callee regs) and new's ---- *)
    iEval (rewrite /vheap_own /swtch_heap1 big_sepL_app
                   (seg_cells_ctx rho 10 oldc 0 ctx_regs_nat Hrho10)
                   (seg_cells_ctx rho 11 newc 0
                      [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat Hrho11))
      in "Hheap".
    assert (Hmapcallee : map (fun w => rho w) ctx_regs_nat = callee_img m0).
    { unfold callee_img, ctx_regs, ctx_regs_nat, rho; cbn. reflexivity. }
    iEval (rewrite Hmapcallee Hmapnew) in "Hheap".
    iDestruct "Hheap" as "[Holdpart Hnewpart]".
    (* ---- build [valid_context P oldc] from old's restored cells + the caller cont ---- *)
    iAssert (valid_context (swconf γ root_ppn) Φ P oldc)
      with "[Holdpart Hwold]" as "Hvoldc".
    { rewrite (valid_context_unfold (swconf γ root_ppn) Φ P oldc) /valid_context_pre.
      iExists (callee_img m0).
      iSplit.
      { iPureIntro. unfold callee_img, ctx_regs; cbn. reflexivity. }
      iSplit.
      { iPureIntro.
        assert (Hn0 : nth 0 (callee_img m0) (mword_of_int 0)
                      = m0 !!! Regidx (mword_of_int 1 : mword 5))
          by (unfold callee_img, ctx_regs; cbn; reflexivity).
        rewrite Hn0. exact Hal_old. }
      rewrite -/(ctx_cells oldc (callee_img m0)).
      iFrame "Holdpart". iExact "Hwold". }
    (* ---- the trailing c.ret returns to new's saved return address ---- *)
    assert (Hm1 : vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 1 : mword 5)
                = nth 0 new_vs (mword_of_int 0)).
    { rewrite (vregs_den_lookup rho swtch_regs1 (Regidx (mword_of_int 1 : mword 5))
                 (SX 32 0) ltac:(vm_compute; reflexivity)).
      rewrite sval_den_SX0. unfold rho. cbn. reflexivity. }
    assert (Hm4 : vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 4 : mword 5)
                = m0 !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite (vregs_den_lookup rho swtch_regs1 (Regidx (mword_of_int 4 : mword 5))
                 (SX 4 0) ltac:(vm_compute; reflexivity)).
      rewrite sval_den_SX0. unfold rho. cbn. reflexivity. }
    assert (Hlow : eq_vec (access_vec_dec
               (update_vec_dec (add_vec
                  (vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 1 : mword 5))
                  (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true).
    { rewrite Hm1. exact Hal_new. }
    assert (Hcallee_new :
              callee_img (vregs_den rho swtch_regs1) = new_vs).
    { rewrite <- Hmapnew. unfold callee_img, ctx_regs; cbn [map nth].
      repeat f_equal;
        (erewrite vregs_den_lookup by (vm_compute; reflexivity);
         apply sval_den_SX0). }
    iDestruct (swi_ret with "Ht") as "Hret".
    iApply (wp_cret_s_zca_r_later (kpt_regime root_ppn) Φ
              (mword_of_int (KernelSyms.swtch + 0x68) : mword 64)
              (mword_of_int 1 : mword 5) (vregs_den rho swtch_regs1)
              ms mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro Hc0; vm_compute in Hc0; discriminate) Hlpe Hlow
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hret
                    [Hnewwand Hvoldc Hnewpart HP Hhalf Hsiearm Hintr]").
    (* ---- the ▷ continuation: iNext strips it AND the resume wand's later ---- *)
    iNext.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    (* ---- rebuild sconf, then swconf, and hand control to new's saved WP ---- *)
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmie Hmdl Hmenv]" as "Hsc".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf".
      { iExists ms. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    (* the c.ret's [iNext] stripped [intr_count]'s internal ▷ (on the handler
       spec); re-introduce it via [intr_restore_intro] and re-pack. *)
    iDestruct "Hintr" as "(Hq0 & (%h & #Hinv_h & #Hspec_h) & Hsepc & Hscause & Hstval)".
    iDestruct (intr_restore_intro γ root_ppn h
                 with "Hinv_h Hspec_h Hsepc Hscause Hstval") as "Hrestore".
    iDestruct (intr_count_pack_S γ root_ppn 0 with "Hq0 Hrestore") as "Hintr".
    iAssert (swconf γ root_ppn)
      with "[Hsc Hhs Htlbinv Hsiearm Hintr]" as "Hswconf".
    { rewrite /swconf. iFrame "Hsc Hhs Htlbinv Hsiearm Hintr". }
    iApply ("Hnewwand" $! (vregs_den rho swtch_regs1)
              with "[] Hswconf Hpc Hfile Hnewpart [Hvoldc HP]").
    { iPureIntro. exact Hcallee_new. }
    iExists oldc. iSplitL "Hvoldc".
    { iNext. iExact "Hvoldc". }
    { rewrite Hm4. iExact "HP". }
  Qed.

End WpSwtchSconf.
End SwtchProof.
