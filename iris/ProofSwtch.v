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
Require Import RiscvLang RiscvPtsto RiscvFetchExec.   (* MIE_S: the pinned cause set *)
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import VcGen VcGenS.
Require Import IntrDefs HartTp.
Require Import WpSmodePtCtl.
Require Import StackOwn.
Require Import CpuOwn.
Require Import SwtchCtx.
Require Import WpSwtchVc.
Require Import SpecSwtch.
From Kernel Require KernelSyms.
Require Import CodeSwtch.
Local Open Scope Z_scope.
Import Defs.

Module SwtchProof : SWTCH.
Section ProofSwtch.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Instance stack_own_timeless_local (sp : mword 64) (n : nat) :
    Timeless (stack_own sp n).
  Proof.
    rewrite /stack_own. apply bi.exist_timeless. intros ws.
    apply bi.sep_timeless; [ apply _ | ].
    apply big_sepL_timeless. intros ? ?.
    rewrite /word_pointsto /mem_pointsto. apply _.
  Qed.

  (* Field 1 of a context record is the saved sp.  Proved ONCE over an
     ABSTRACT [m], with [cbn] RESTRICTED to the list combinators: at a
     concrete register file (the [vregs_den rho swtch_regs1] this proof
     reaches at the c.ret) a bare [cbn] normalises the whole VC denotation
     instead, and the resulting proof term is re-checked at [Qed].  Measured
     2026-08-03: inline, that one [assert] was 18.4 s of [cbn] + 23.4 s of
     [reflexivity] and most of the file's 39.1 s [Qed] (98 s file); as this
     lemma the file is 39 s. *)
  Local Lemma callee_img_nth1 (m : regfile) (d : mword 64) :
    nth 1 (callee_img m) d = m !!! Regidx csp_rs1.
  Proof. unfold callee_img, ctx_regs, csp_rs1. cbn [map nth]. reflexivity. Qed.

  Lemma wp_swtch_sconf
      (P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> iPropO Σ)
      (An Ao : ctx_adm)
      (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64))
      (av : nat) (eb : bool) (p : mword 64) :
    wp_swtch_sconf_body P An Ao oldc newc m0 old_vs av eb p.
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
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    (* [mie] is PINNED at [MIE_S] by [sconf] (only [mideleg] is existential),
       so the block/ret leaves below are instantiated at that literal and
       [Hmm] is already the no-M-destined-pending fact at [MIE_S]. *)
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    (* ---- [Hcg]'s [sie_cap_gpr] is pinned at the literal [b = false] (both
       swtch's own entry and exit index, per SpecSwtch.v's header), so
       [Hsiearm : sie_arm false p] IS [intr_off_tok] by conversion -- no
       disjunction to destruct any more (that was the pre-index [sie_arm]
       shape), so the old ghost_var_agree contradiction arm is simply GONE:
       there is no other case to refute. ---- *)
    iEval (rewrite /cpu_own /cpu_hart /cpu_priv /cpu_cells) in "Hcpuown".
    iDestruct "Hcpuown" as "((((%Hcpb & Hcnoff & Hcint & Hcproc) & Hclks) & Hccnt) & _)".
    iDestruct (intr_count_pos_off 0 eb with "Hccnt") as "[Hq0cnt Hres]".
    iAssert (intr_off_tok ∗ intr_count 1 eb)%I with "[Hsiearm Hq0cnt Hres]" as "(Hq0 & Hccnt)".
    { iFrame "Hsiearm". rewrite /intr_count. iFrame "Hq0cnt Hres". }
    iAssert (cpu_own 1 eb p emp false) with "[Hcnoff Hcint Hclks Hccnt Hcproc]" as "Hcpuown".
    { rewrite /cpu_own /cpu_hart /cpu_priv /cpu_cells.
      iFrame "Hcnoff Hcint Hcproc Hclks Hccnt". iPureIntro; exact Hcpb. }
    iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
      by (rewrite Hb0; vm_compute; reflexivity).
    (* ---- strip the ▷ off the target VC record.  [valid_context γ Φ P newc p]
       is indexed by the caller's OWN [p]; its existentials are just (vs, av),
       and its resume wand demands cpu_own at that SAME index p -- so the
       cpu_own we already hold fits with no retune, no equation. ---- *)
    iApply fupd_wp.
    iEval (rewrite (valid_context_unfold P An newc p)
                   /valid_context_pre !bi.later_exist) in "Hvalidnew".
    iDestruct "Hvalidnew" as (new_vs av_t) "Hvalidnew".
    iDestruct "Hvalidnew" as "(>%Hlen_new & >%Hal_new & >Hnewcells & >Hstk_t & Hnewwand)".
    iModIntro.
    (* ---- the symbolic environment: 0..31 = [gpr_file]'s ACTUAL map
       [tp_pin m0] (its tp slot, index 4, is [cid_word_of cpu_id] by
       construction, not whatever [m0]'s raw slot 4 happens to hold);
       32..45 = new's saved; 46..59 = old's.  Every OTHER index agrees with
       raw [m0] via [rget_ne] (tp_pin only ever touches index 4). ---- *)
    (* fold [tp_pin m0] into an opaque local name FIRST: [rho] and every
       [vm_compute]-driven side condition below is far cheaper against one
       flat map than against a live [<[Regidx Rtp := ...]> m0] insert
       re-exposed at every one of [rho]'s 32 low branches. *)
    set (M0 := tp_pin m0).
    iDestruct (VcGenS.gpr_file_dom with "Hfile") as "[%Hdom Hfile]".
    iDestruct (gpr_file_x0 M0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0 Hfile]".
    set (rho := fun k : nat =>
           if (k <? 32)%nat
           then M0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if (k <? 46)%nat then nth (k - 32) new_vs (mword_of_int 0)
           else nth (k - 46) old_vs (mword_of_int 0)).
    assert (Hden : vregs_den rho vregs_init = M0).
    { apply (vregs_den_init_agree _ _ Hx0). intros k Hk.
      unfold rho. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (Hrho10 : rho 10%nat = oldc).
    { unfold rho; cbn. unfold M0, tp_pin. rewrite upd_ne; [exact Holdc | vm_compute; discriminate]. }
    assert (Hrho11 : rho 11%nat = newc).
    { unfold rho; cbn. unfold M0, tp_pin. rewrite upd_ne; [exact Hnewc | vm_compute; discriminate]. }
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
    iApply (wp_vc_block_s_den_r strans_regime swtch_prog
              (VSt KernelSyms.swtch vregs_init swtch_heap0 [])
              (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 [])
              rho ms MIE_S mdv0 menvcfg0 (dq:=DfracOwn 1)
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
    iAssert (valid_context P Ao oldc p)
      with "[Holdpart Hstk Hwold]" as "Hvoldc".
    { rewrite (valid_context_unfold P Ao oldc p) /valid_context_pre.
      iExists (callee_img m0), av.
      iSplit.
      { iPureIntro. unfold callee_img, ctx_regs; cbn. reflexivity. }
      iSplit.
      { iPureIntro. apply ret_pc_aligned. }
      rewrite -/(ctx_cells oldc (callee_img m0)).
      iFrame "Holdpart".
      iSplitL "Hstk".
      { rewrite (callee_img_nth1 m0 (mword_of_int 0)). iExact "Hstk". }
      iExact "Hwold". }
    (* ---- the trailing c.ret returns to new's saved return address ---- *)
    assert (Hm1 : vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 1 : mword 5)
                = nth 0 new_vs (mword_of_int 0)).
    { rewrite (vregs_den_lookup rho swtch_regs1 (Regidx (mword_of_int 1 : mword 5))
                 (SX 32 0) ltac:(vm_compute; reflexivity)).
      rewrite sval_den_SX0. unfold rho. cbn. reflexivity. }
    (* x4 (tp) is not among [swtch_regs1]'s keys (it threads through the
       block unchanged), so it denotes its GENERATION-0 (initial) value --
       which, since [rho]'s environment IS [tp_pin m0], is [cid_word_of
       cpu_id] by [tp_pin]'s own definition, with no dependence on raw
       [m0] at all. *)
    assert (Hm4_raw : vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 4 : mword 5)
                = cid_word_of cpu_id).
    { rewrite (vregs_den_lookup rho swtch_regs1 (Regidx (mword_of_int 4 : mword 5))
                 (SX 4 0) ltac:(vm_compute; reflexivity)).
      rewrite sval_den_SX0. unfold rho. cbn. unfold M0, tp_pin. rewrite upd_eq. reflexivity. }
    (* tp is never carried by the raw map any more -- both sides are this
       SAME hart's [rget ... Rtp] (swtch's own proof never migrates; only
       the payload it hands off is later resumed elsewhere), so the two
       [rget]s agree unconditionally via [rget_tp_agree] with no map lookup
       at all. *)
    pose proof (rget_tp_agree (vregs_den rho swtch_regs1) m0) as Hm4.
    assert (Hcallee_new :
              callee_img (vregs_den rho swtch_regs1) = new_vs).
    { rewrite <- Hmapnew. unfold callee_img, ctx_regs; cbn [map nth].
      repeat f_equal;
        (erewrite vregs_den_lookup; [apply sval_den_SX0 | vm_compute; reflexivity]). }
    (* the resumed file's sp (= new's saved sp = nth 1 new_vs) keys its stack. *)
    assert (Hcsp_t : vregs_den rho swtch_regs1 !!! Regidx csp_rs1
                     = nth 1 new_vs (mword_of_int 0)).
    { rewrite <- Hcallee_new. exact (eq_sym (callee_img_nth1 _ (mword_of_int 0))). }
    iDestruct (swi_68 with "Ht") as "Hret".
    iApply (wp_cret_s_zca_r_later strans_regime
              (mword_of_int (KernelSyms.swtch + 0x68) : mword 64)
              (mword_of_int 1 : mword 5) (vregs_den rho swtch_regs1)
              ms MIE_S mdv0 menvcfg0 (dq:=DfracOwn 1)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(intro Hc0; vm_compute in Hc0; discriminate) Hlpe
              with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htr
                    Hpc Hfile Hret
                    [Hnewwand Hvoldc Hnewpart HP Hhalf Hspp Hq0 Hcpuown Hstk_t]").
    (* ---- the ▷ continuation: iNext strips it AND the record's ▷'d pieces ---- *)
    iNext.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htr Hpc Hfile".
    (* ---- rebuild sconf ---- *)
    iAssert sconf with "[Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv]" as "Hsc".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    (* ---- the target record's resume wand is [∀ h g m eb'] and demands
       cpu_own at the record's INDEX p (= our own p); supply our bundle at
       our own [eb] (eb' := eb) -- no retune, no equation.  [sie_arm false p]
       is [intr_off_tok] by conversion now (an INDEX, not a disjunction), so
       building [sie_cap] at [false] needs no [iLeft]. ---- *)
    iAssert (sie_cap (vregs_den rho swtch_regs1) av_t false p) with "[Hstk_t Htr Hq0]" as "Hcap_t".
    { rewrite /sie_cap Hcsp_t. iFrame "Hstk_t Htr". iExact "Hq0". }
    (* [Hfile] comes back from the block as the bare [gpr_file (vregs_den
       rho swtch_regs1)] (it went in the same way, via [Hden]); re-fold it
       under [tp_pin] -- a no-op, since that map's own tp slot is ALREADY
       [cid_word_of cpu_id] ([Hm4_raw]) -- to match [sie_cap_gpr]'s shape. *)
    iEval (rewrite -(tp_pin_id (vregs_den rho swtch_regs1) Hm4_raw)) in "Hfile".
    iDestruct (sie_cap_gpr_join (vregs_den rho swtch_regs1) av_t false p
                 with "Hhs Hsc Hcap_t Hfile") as "Hcg_t".
    (* the record's wand is [∀ h m eb']; swtch resumes it HERE, so it is
       applied at this hart -- whose SIE ghost is [sie_gname] by
       construction -- and the spec's [adm An cpu_id] premise is
       exactly its admissibility obligation.  The hand-off names the OLD
       record's own index [Ao]. *)
    iApply ("Hnewwand" $! cpu_id (vregs_den rho swtch_regs1) eb
              with "[] [] Hcg_t Hcpuown Hpc Hnewpart [Hvoldc HP]").
    { iPureIntro. exact Hadm. }
    { iPureIntro. exact Hcallee_new. }
    iExists Ao, oldc. iSplitL "Hvoldc".
    { iApply bi.later_intro. iExact "Hvoldc". }
    { rewrite Hm4. iExact "HP". }
  Qed.

End ProofSwtch.
End SwtchProof.
