(* ProofSwtch.v -- the proof of swtch()'s sconf-tier context-switch spec
   (SpecSwtch.v), as a sealed module.  swtch calls nothing, so SwtchProof takes
   no functor arguments.

   Plan (mirrors the retired smode-config wp_swtch proof that lived in
   WpSwtchVc.v, over the same decode facts / VCgen run, with three changes):

   - CONFIG: the caller hands the [swconf] bundle; the proof unbundles
     [sconf γ] into the raw CSR resources and runs the plain (non-sp-
     tracking) engine [wp_vc_block_s_den_r strans_regime] -- swtch
     loads sp from memory, which the sp-tracking sconf VCgen cannot model.
     The translation slot rides FOLDED through the regime-blind engines
     (no skolem root is ever opened), so swtch is provable at either regime.
     The SIE=0 pin comes from [swconf]'s interrupts-off eighth [intr_off_tok]
     agreeing with [sconf]'s tied half (the crossing is always interrupts-off;
     the counting token itself rides in the chain payload); MPRV/SXL/MXR from
     [sconf_ms_facts]; menvcfg is pinned MENVCFG_S by the bundle.  The eighth /
     [hart_state] / [strans_inv] ride through untouched and are re-bundled at
     both exits.

   - ▷ TARGET: the [valid_context newc] premise is ▷-guarded.  At entry,
     [fupd_wp] + [later_exist_except_0] + timelessness strip the two pure
     facts and the (timeless) [ctx_cells]; the non-timeless resume wand
     stays under ▷ until the final c.ret, discharged with the later-handing
     leaf [wp_cret_s_zca_r_later] (WpSmodePtCtl.v) -- the [iNext] there
     strips it.

   - PAYLOAD: P is seven-place (resuming hart + its SIE ghost, the resumer
     record's admissibility index, resumed ctx, resumer ctx, resumer tp, the
     record's own c->proc index); the proof supplies
     [P cpu_id γ Ao newc oldc (m0 !!! x4) p] and must show x4 threads
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
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import VcGen VcGenS.
Require Import IntrDefs.
Require Import WpSmodePtCtl.
Require Import StackOwn.
Require Import CpuOwn.
Require Import SwtchCtx.
Require Import WpSwtchVc.
Require Import SpecSwtch.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Module SwtchProof : SWTCH.
Section ProofSwtch.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Local Instance stack_own_timeless_local (sp : mword 64) (n : nat) :
    Timeless (stack_own sp n).
  Proof.
    rewrite /stack_own. apply bi.exist_timeless. intros ws.
    apply bi.sep_timeless; [ apply _ | ].
    apply big_sepL_timeless. intros ? ?.
    rewrite /word_pointsto /mem_pointsto. apply _.
  Qed.

  Lemma wp_swtch_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (P : CPU -d> gname -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> iPropO Σ)
      (An Ao : ctx_adm)
      (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64))
      (av : nat) (eb : bool) (p : mword 64) :
    wp_swtch_sconf_body γ Φ P An Ao oldc newc m0 old_vs av eb p.
  Proof.
    cbv beta delta [wp_swtch_sconf_body].
    iIntros (Hlen_old Holdc Hnewc Hadm)
      "#Ht Hcg Hcpuown Hpc Holdcells Hvalidnew HP Hwold".
    (* The record no longer parks [eb] or an avail copy: its resume wand is
       [∀ m eb'], so the resumer supplies cpu_own at ITS OWN [eb']; the
       same-eb contract is realized one level up (sched's intena epilogue). *)
    (* ---- unbundle sie_cap_gpr into hart_state / sconf / sie_cap / gpr_file;
       sie_cap into stack + strans_inv + arm ---- *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iEval (rewrite /sie_cap) in "Hcap".
    iDestruct "Hcap" as "(Hstk & Htr & Hsiearm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmiex" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    (* ---- refute sie_arm '1' against cpu_own's level-1 count eighth; keep the
       off-eighth [Hq0] for the SIE=0 pin, refold cpu_own ---- *)
    iEval (rewrite /cpu_own) in "Hcpuown".
    iDestruct "Hcpuown" as "(%Hcpb & Hcnoff & Hcint & Hccnt & Hcproc & _)".
    iDestruct (intr_count_pos_off γ 0 with "Hccnt") as "[Hq0cnt Hres]".
    iAssert (intr_off_tok γ ∗ intr_count γ 1 eb)%I with "[Hsiearm Hq0cnt Hres]" as "(Hq0 & Hccnt)".
    { iDestruct "Hsiearm" as "[Hq0arm | (Hq1arm & _)]".
      - iFrame "Hq0arm". rewrite /intr_count. iFrame "Hq0cnt Hres".
      - iDestruct (ghost_var_agree with "Hq0cnt Hq1arm") as %Hbad.
        exfalso. apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate. }
    iAssert (cpu_own γ 1 eb p emp) with "[Hcnoff Hcint Hccnt Hcproc]" as "Hcpuown".
    { rewrite /cpu_own. iFrame "Hcnoff Hcint Hccnt Hcproc". iPureIntro; exact Hcpb. }
    iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
      by (rewrite Hb0; vm_compute; reflexivity).
    (* ---- strip the ▷ off the target VC record.  [valid_context γ Φ P newc p]
       is indexed by the caller's OWN [p]; its existentials are just (vs, av),
       and its resume wand demands cpu_own at that SAME index p -- so the
       cpu_own we already hold fits with no retune, no equation. ---- *)
    iApply fupd_wp.
    iEval (rewrite (valid_context_unfold Φ P An newc p)
                   /valid_context_pre !bi.later_exist) in "Hvalidnew".
    iDestruct "Hvalidnew" as (new_vs av_t) "Hvalidnew".
    iDestruct "Hvalidnew" as "(>%Hlen_new & >%Hal_new & >Hnewcells & >Hstk_t & Hnewwand)".
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
    (* ---- run the 28-instruction straight-line block (regime-blind engine) ---- *)
    iApply (wp_vc_block_s_den_r strans_regime swtch_prog Φ
              (VSt KernelSyms.swtch vregs_init swtch_heap0 [])
              (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 [])
              rho ms mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 swtch_run
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htr
                    Hpc Hfile Hcode [Holdcells Hnewcells] []").
    { rewrite /vheap_own /swtch_heap0 big_sepL_app.
      rewrite (seg_cells_ctx rho 10 oldc 0 _ Hrho10).
      rewrite (seg_cells_ctx rho 11 newc 0 _ Hrho11).
      rewrite Hmapold Hmapnew.
      rewrite -/(ctx_cells oldc old_vs) -/(ctx_cells newc new_vs).
      iFrame "Holdcells Hnewcells". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htr Hpc Hfile Hheap _".
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
    (* ---- build the OLD context's record: (callee_img m0, av, p), the caller's
       stack (keyed by saved sp), and the caller continuation as the resume
       wand.  Pack p := the spec's [p] param; the caller continuation [Hwold]
       is already [∀ m eb', … cpu_own γ 1 eb' p emp …], matching the record's
       [∀ m eb'] wand at that same p. ---- *)
    iAssert (valid_context Φ P Ao oldc p)
      with "[Holdpart Hstk Hwold]" as "Hvoldc".
    { rewrite (valid_context_unfold Φ P Ao oldc p) /valid_context_pre.
      iExists (callee_img m0), av.
      iSplit.
      { iPureIntro. unfold callee_img, ctx_regs; cbn. reflexivity. }
      iSplit.
      { iPureIntro. apply ret_pc_aligned. }
      rewrite -/(ctx_cells oldc (callee_img m0)).
      iFrame "Holdpart".
      iSplitL "Hstk".
      { assert (Hn1 : nth 1 (callee_img m0) (mword_of_int 0) = m0 !!! Regidx csp_rs1)
          by (unfold callee_img, ctx_regs, csp_rs1; cbn; reflexivity).
        rewrite Hn1. iExact "Hstk". }
      iExact "Hwold". }
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
    assert (Hcallee_new :
              callee_img (vregs_den rho swtch_regs1) = new_vs).
    { rewrite <- Hmapnew. unfold callee_img, ctx_regs; cbn [map nth].
      repeat f_equal;
        (erewrite vregs_den_lookup by (vm_compute; reflexivity);
         apply sval_den_SX0). }
    (* the resumed file's sp (= new's saved sp = nth 1 new_vs) keys its stack. *)
    assert (Hcsp_t : vregs_den rho swtch_regs1 !!! Regidx csp_rs1
                     = nth 1 new_vs (mword_of_int 0)).
    { rewrite <- Hcallee_new. unfold callee_img, ctx_regs, csp_rs1. cbn. reflexivity. }
    iDestruct (swi_ret with "Ht") as "Hret".
    iApply (wp_cret_s_zca_r_later strans_regime Φ
              (mword_of_int (KernelSyms.swtch + 0x68) : mword 64)
              (mword_of_int 1 : mword 5) (vregs_den rho swtch_regs1)
              ms mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro Hc0; vm_compute in Hc0; discriminate) Hlpe
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htr
                    Hpc Hfile Hret
                    [Hnewwand Hvoldc Hnewpart HP Hhalf Hq0 Hcpuown Hstk_t]").
    (* ---- the ▷ continuation: iNext strips it AND the record's ▷'d pieces ---- *)
    iNext.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htr Hpc Hfile".
    (* ---- rebuild sconf ---- *)
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmie Hmdl Hmenv]" as "Hsc".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf".
      { iExists ms. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    (* ---- the target record's resume wand is [∀ m eb'] and demands cpu_own at
       the record's INDEX p (= our own p); supply our bundle at our own [eb]
       (eb' := eb) -- no retune, no equation. ---- *)
    iAssert (sie_cap γ (vregs_den rho swtch_regs1) av_t) with "[Hstk_t Htr Hq0]" as "Hcap_t".
    { rewrite /sie_cap Hcsp_t. iFrame "Hstk_t Htr". iLeft. iExact "Hq0". }
    iDestruct (sie_cap_gpr_join γ (vregs_den rho swtch_regs1) av_t
                 with "Hhs Hsc Hcap_t Hfile") as "Hcg_t".
    (* the record's wand is [∀ h g m eb']; swtch resumes it HERE, so it is
       applied at this hart and this hart's ghost, and the spec's [adm An
       cpu_id γ] premise is exactly its admissibility obligation.  The
       hand-off names the OLD record's own index [Ao]. *)
    iApply ("Hnewwand" $! cpu_id γ (vregs_den rho swtch_regs1) eb
              with "[] [] Hcg_t Hcpuown Hpc Hnewpart [Hvoldc HP]").
    { iPureIntro. exact Hadm. }
    { iPureIntro. exact Hcallee_new. }
    iExists Ao, oldc. iSplitL "Hvoldc".
    { iNext. iExact "Hvoldc". }
    { rewrite Hm4. iExact "HP". }
  Qed.

End ProofSwtch.
End SwtchProof.
