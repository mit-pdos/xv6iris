(* UptWalkTramp.v -- THE TRAMPOLINE FETCH on the USER table: the
   [TrampStepPt.tramp_tr_obl] instances at [Res := upt_res_pt uroot tfp um]
   and the whole-instruction forms built on them ([wp_instr_u_pt] /
   [wp_instr_u_pt_user]).  Split out of UptWalkPt.v.

   DELIBERATELY RED (the §0.37′ successor): [UptWalkPt.swp_translate_upt]
   takes [own_context] (the walk's A/D write-back is a ledger append), and
   [tramp_tr_obl] is a □-obligation whose ∀ cannot capture the linear
   token -- the measured fix (tso-machine-flip.md A6.61, recorded in
   TrampStepPt.v beside the obligation) threads the token as a parameter
   of the obligation through six files, its own tranche against a green
   tree.  Until that tranche lands, this file does not compile; its
   consumers are the (equally red) trampoline-proof files
   [Pt2WalkPt]/[UservecPt]/[UservecExitPt]/[UserretPt]/[UserretEntryPt]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import KptTree UptTree.
Require Import KptExecMap.
Require Import PtAdBits SRegime.
Require Import HartSwp HartLift HartSFrame.
Require Import WpDecodeBridge.
Require Import SmodeCorePt TrampStepPt.
Require Import UptWalkPt.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 5. THE TRAMPOLINE FETCH, on the USER table.                            *)
(*                                                                        *)
(* [TrampStepPt.tramp_tr_obl] at [Res := upt_res_pt uroot tfp um].  The    *)
(* claim side is the trampoline CLAUSE of [upt_tree_spec] -- the user      *)
(* table maps [tramp_vpn] to [pte_tramp] on every A/D variant -- so the    *)
(* obligation's own geometry premises are all it takes; nothing outside    *)
(* the invariant is consulted.                                            *)
(* ===================================================================== *)

(* the trampoline leaf's fetch check, certified (the [goodb] twin of
   [KptTree.tramp_variant_check_fetch], same proof) *)
Lemma tramp_variant_goodb_check_fetch (a d : mword 1) (mxr do_sum : bool)
    (Db : register -> bool) (s : mstate) :
  goodb Db (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad pte_tramp a d) 7 0))
              (ext_bits_of_PTE (pte_set_ad pte_tramp a d)) tt) s = true.
Proof.
  unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Section UptTramp.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac tlbpeel :=
    rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma utramp_tr_obl (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (Df : register -> dfrac)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) :
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    gen_cert -∗
    tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
      (upt_res_pt uroot tfp um).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma.
    iIntros "#Hcert". rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag Htok HRes Hrw Hro".
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pax).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hident.
      rewrite pte_set_ad_ppn in Hident. exact Hident. }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_translate_upt (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  uroot tfp um va pax satp0 pte_tramp mst0 tv pcfg paddr pmar0 rr
                  s_disj upt_Dr_in_s upt_Dw_in_s (or_introl eq_refl)
                  ltac:(rewrite s_rs_misa; exact Hmisa)
                  ltac:(rewrite s_rs_menv; exact Hmenv)
                  ltac:(apply s_rs_htif) ltac:(apply s_rs_priv)
                  ltac:(apply s_rs_mst) HSXL HMPRV
                  ltac:(apply s_rs_satp) ltac:(apply s_rs_tlb)
                  ltac:(apply s_rs_pcfg) ltac:(apply s_rs_paddr)
                  ltac:(apply s_rs_pma)
                  Hsatpok Hpmpok Hpma
                  (or_introl (conj Hvpn eq_refl))
                  (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
                  (fun a d mxr do_sum Db s0 =>
                     tramp_variant_goodb_check_fetch a d mxr do_sum Db s0)
                  Hcanon Hout
                  with "Hcert Hfrag Htok HRes Hrw Hro"). }
    iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & HRes & Htok & Hany)".
    iSplitR; [done |].
    destruct Hshape as [-> | (tvx & ->)].
    - iExists tv. rewrite s_rs_tlb. iFrame "Htok Hany Hrw Hro HRes".
    - assert (Ltlbv : register_lookup tlb
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = tvx)
        by apply register_lookup_set.
      assert (Hag : reg_agree_on (s_Drw ∪ s_Dro)
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx)).
      { apply (s_rs_agree pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx);
          [ tlbpeel; apply s_rs_PC
          | tlbpeel; apply s_rs_nPC
          | tlbpeel; apply s_rs_ms
          | tlbpeel; apply s_rs_mi
          | tlbpeel; apply s_rs_cy
          | tlbpeel; apply s_rs_ti
          | tlbpeel; apply s_rs_ip
          | exact Ltlbv
          | tlbpeel; apply s_rs_priv
          | tlbpeel; apply s_rs_mst
          | tlbpeel; apply s_rs_hart
          | tlbpeel; apply s_rs_pcfg
          | tlbpeel; apply s_rs_paddr
          | tlbpeel; apply s_rs_mc
          | tlbpeel; apply s_rs_micfg
          | tlbpeel; apply s_rs_misa
          | tlbpeel; apply s_rs_sec
          | tlbpeel; apply s_rs_pma
          | tlbpeel; apply s_rs_htif
          | tlbpeel; apply s_rs_elp
          | tlbpeel; apply s_rs_senv
          | tlbpeel; apply s_rs_satp
          | tlbpeel; apply s_rs_mie
          | tlbpeel; apply s_rs_mdl
          | tlbpeel; apply s_rs_menv ]. }
      iDestruct (s_rw_ext _ _ Hag with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen Df _ _ Hag with "Hro") as "Hro".
      iExists tvx. rewrite Ltlbv. iFrame "Htok Hany Hrw Hro HRes".
  Qed.

  (* the whole-tower form the engine takes.  [tramp_fetch_tr] ∀-quantifies
     misa and pma_regions, which [utramp_tr_obl] wants as literals, so -- as
     in [WpSmodePtFetch.spt_fetch_tr_of_regime] -- the producer applies only
     from INSIDE the box, where the frame's own discarded cells and
     [hw_config]'s pins turn the two ∀-bound components into those literals. *)
  Lemma utramp_fetch_tr (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (dq : dfrac) (pc mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (upt_res_pt uroot tfp um) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok.
    iIntros "#Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /tramp_fetch_tr.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag Htok HRes Hrw Hro".
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (utramp_tr_obl uroot tfp um (s_Df_mix dq) pc ms bmi cy ti ip mst0
                 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0 satp0
                 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma
                 with "Hcert") as "#Hobl".
    iApply ("Hobl" $! va pax tv rr with "[%] [%] [%] Hfrag Htok HRes Hrw Hro");
      [ exact Hcanon | exact Hvpn | exact Hident ].
  Qed.

  (* ==================================================================== *)
  (* THE USER-TABLE STEP ENGINE.                                           *)
  (*                                                                      *)
  (* [TrampStepPt.wp_instr_tramp_pt] at [Res := upt_res_pt uroot tfp um],   *)
  (* on the bundle [UptTree.utlb_inv_pt] -- i.e. the shape                 *)
  (* [SmodeCorePt.wp_instr_s_config_tlbinv_pt] has on [tlb_res_pt], with   *)
  (* [upt_swp_open]/[upt_swp_close] as the bundle face and the trampoline   *)
  (* fetch underneath.  The user table is NOT an [s_regime] and cannot be   *)
  (* one ([sr_swp_translate] is keyed on a [kmap_at] claim, and the user    *)
  (* table's mapping facts come from [um]), so this is the bespoke twin of  *)
  (* [TrampStepPt.wp_instr_ktramp_pt_share] rather than an instance.        *)
  (*                                                                      *)
  (* The fetch obligation costs the caller NOTHING beyond [hw_config]: the  *)
  (* trampoline claim is the trampoline CLAUSE of [upt_tree_spec], i.e. it  *)
  (* is already inside the bundle.                                          *)
  (* ==================================================================== *)
  Lemma wp_instr_u_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    neq_vec (bits_of_virtaddr (Virtaddr pc))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub 39 1) 0)) = false ->
    svpn_of pc = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int pc 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr pc) 4 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    own_context XI -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ upt_satp_ok_pt uroot satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ upt_res_pt uroot tfp um tv' -∗
       own_context XI -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ upt_res_pt uroot tfp um tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   own_context XI ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         utlb_inv_pt uroot tfp um -∗
         own_context XI -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Htok Hpc
             Hinstr Hex Hcont".
    iDestruct (upt_swp_open uroot tfp um with "Hinv")
      as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt (upt_res_pt uroot tfp um)
              (upt_res_pt uroot tfp um) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr Supervisor Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Htok Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (utramp_fetch_tr uroot tfp um dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                with "Hhw").
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Htok Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Htok Hpc HRl").
      iApply (upt_swp_close uroot tfp um satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

  (* ==================================================================== *)
  (* THE USER-LANDING TWIN.                                                *)
  (*                                                                      *)
  (* Every trampoline instruction RUNS at Supervisor -- the trap raised    *)
  (* the privilege before the pc reached the trampoline page -- and all    *)
  (* but one of them LANDS there too.  The exception is userret's [sret],  *)
  (* which lands in User; this is [wp_instr_u_pt] with that one cell's     *)
  (* post value spelled out.  Stated CONCRETELY rather than as a           *)
  (* privilege-parametric wrapper, so that a leaf's [iApply] against the   *)
  (* cycle's WP goal has nothing extra to unify.                           *)
  (* ==================================================================== *)
  Lemma wp_instr_u_pt_user (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    neq_vec (bits_of_virtaddr (Virtaddr pc))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub 39 1) 0)) = false ->
    svpn_of pc = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int pc 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr pc) 4 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    own_context XI -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ upt_satp_ok_pt uroot satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ upt_res_pt uroot tfp um tv' -∗
       own_context XI -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } User ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ upt_res_pt uroot tfp um tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   own_context XI ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } User -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         utlb_inv_pt uroot tfp um -∗
         own_context XI -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Htok Hpc
             Hinstr Hex Hcont".
    iDestruct (upt_swp_open uroot tfp um with "Hinv")
      as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt (upt_res_pt uroot tfp um)
              (upt_res_pt uroot tfp um) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr User Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Htok Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (utramp_fetch_tr uroot tfp um dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                with "Hhw").
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Htok Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Htok Hpc HRl").
      iApply (upt_swp_close uroot tfp um satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

End UptTramp.
