(* WpInstrRun.v -- THE FETCH-SHAPE DISPATCH, ONCE.

   [swp_run_hart_active_instr] is the fifth member of HartMRun's
   [swp_run_hart_active_*] family, and the only one a wrapper calls: where
   those four each take a CONCRETE fetch shape (a 32-bit word, two
   halfwords, a compressed halfword in a word, a bare compressed halfword)
   plus that shape's alignment and decode facts, this one takes the [instr]
   resource and DISPATCHES -- on the fetch result hidden inside it and on
   [pc]'s 4-alignment, four cases in all.

   It exists because that dispatch is the same for every M-mode wrapper.
   [WpInstr.wp_instr] (config read-only, fraction-parameterised bundle) and
   [WpInstrConfig.wp_instr_config] (config WRITTEN, raw cells) differ in
   their bundles and in which cells they hand the caller -- not in how the
   instruction is fetched.  Keeping the four arms here means adding a
   wrapper costs its own bundle bookkeeping and nothing else.

   Abstract in [Drw] / [Dro] / [Df] / the pre- and post-files, exactly like
   the four rules it wraps: the M-mode-specific part is the caller's
   footprint, not this rule. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import HartSwp HartLift HartLift2 HartSpan HartSpanChar
        HartRegNode HartMCycle HartMRun HartMFrame RegFile WpGpr.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep
        RiscvFetchExec.
Require Import KptPt KMap.
Require Import InstrBytes.
Local Open Scope Z_scope.

Section WpInstrRun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [decode_ok] survives a nextPC write: the compressed expansion runs AFTER
     the fetch has committed nextPC, so it needs the same regime pins at the
     updated file. *)
  Lemma decode_ok_set_nPC (D : gset register) (rs : regstate) (v : mword 64) :
    decode_ok D rs -> decode_ok D (register_set (R_bitvector_64 nextPC) v rs).
  Proof.
    rewrite /decode_ok.
    rewrite (irrelevant_register_set cur_privilege (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set misa (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set mseccfg (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set menvcfg (R_bitvector_64 nextPC)
               _ _ eq_refl).
    exact (fun H => H).
  Qed.

  (* the 4-byte text window, resplit as the two halfwords the 2-mod-4 base
     fetch reads.  The bytes are persistent, so this is a duplication, not a
     transfer. *)
  Lemma text_split_halves (pc : mword 64) (w : mword 32) :
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₓ□ nth_byte w j) -∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add pc j) ↦ₓ□ nth_byte (subrange_vec_dec w 15 0 : mword 16) j) ∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add (add_vec_int pc 2) j) ↦ₓ□
         nth_byte (subrange_vec_dec w 31 16 : mword 16) j).
  Proof.
    assert (Hoff : forall j : nat,
              pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
    { intros j. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
    iIntros "#Hb".
    iAssert (∀ k : nat, ⌜(k < 4)%nat⌝ -∗
               (pa_add pc k) ↦ₓ□ nth_byte w k)%I as "#Hbk".
    { iIntros (k) "%Hk". iApply (big_sepL_lookup _ _ k k with "Hb").
      rewrite lookup_seq_lt; [reflexivity | lia]. }
    iSplit; iApply big_sepL_intro; iIntros "!>" (k j) "%Hk";
      apply lookup_seq in Hk as [-> Hj].
    - rewrite (nth_byte_subrange_lo w (0 + k)%nat ltac:(lia)).
      iApply "Hbk". iPureIntro. lia.
    - rewrite (nth_byte_subrange_hi w (0 + k)%nat ltac:(lia))
              (Hoff (0 + k)%nat).
      iApply "Hbk". iPureIntro. lia.
  Qed.

  (* ==================================================================== *)
  (* swp_run_hart_active_instr.                                            *)
  (*                                                                      *)
  (* The obligation the caller sees is UNIFORM across the four shapes,     *)
  (* because [decode_hval]'s RVC arm carries the [ExecuteAs] expansion:    *)
  (* the caller supplies [execute i] and never sees [execute i0].  The     *)
  (* only trace of the shape is the nextPC the fetch committed             *)
  (* ([pc + 2] or [pc + 4]), which is what [is_rvc] is for.                *)
  (*                                                                      *)
  (* The fetched word stays EXISTENTIAL in the conclusion: each arm knows  *)
  (* its own word, no caller does, and the cycle rule does not care.       *)
  (* ==================================================================== *)
  Lemma swp_run_hart_active_instr (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs2 : regstate)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs)) ('b"1") = true ->
    eq_vec (_get_Misa_C (register_lookup misa rs)) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs)) ('b"1") = false ->
    pmp_allows_all pcfg ->
    pma_allows_all pmar0 ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    decode_ok (Drw ∪ Dro) rs ->
    hfrun 8 (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt)
      = Some (false, rs) ->
    gen_cert -∗
    kmap_static_claims -∗
    instr pc is_rvc i -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc (if is_rvc then 2 else 4)) rs) Drw -∗
     hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                   (add_vec_int pc (if is_rvc then 2 else 4)) rs) Dro -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R)) -∗
    swp (run_hart_active 0)
      (fun st => ∃ w : mword 32,
                 ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                 hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HWnpc HDpma HDcfg HDhtif
      Lpriv Lpc Lpma Lpcfg Lhtif HmS HmC HmIE Hpmp Hpmaall Hstat Hdok Hlp.
    iIntros "#Hcert #Hkm Hinstr Hrw Hro Hex".
    iDestruct "Hinstr" as "(%Hlpi & Hib)".
    iDestruct "Hib" as (r) "(%Hrvc & Hbytes & %Hdec)".
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx]; [ done | | | done ];
      cbn [fetch_is_rvc decode_fetch] in Hrvc, Hdec; subst is_rvc.

    - (* ============================ F_Base w ======================== *)
      iDestruct "Hbytes" as "[%HnotRVC #Hb]".
      iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
      { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                     with "Hkm Hb0") as "Hb0'".
        iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* ---- 4-aligned: one 4-byte read ---- *)
        destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
        iApply swp_step_ex.
        iApply (swp_run_hart_active_base Drw Dro Df rs rs2 pc w i pmar0 pcfg
                  8 R Hdisj HDpriv HDmisa HDmst HDpc HWnpc HDpma HDcfg HDhtif
                  Lpriv Lpc Lpma Lpcfg Lhtif HmS HmIE
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Hal
                  HnotRVC (Hdec _ _ _ Hdok) Hlp
                  with "Hcert Hrw Hro [] Hex").
        iApply (text_fetch_obl pc 4 w with "Hb").
      + (* ---- 2 mod 4: two halfword reads ---- *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
        pose proof (align2_plus2 pc H2al) as Halignh.
        rewrite fetch_pa_id in Halignl. rewrite fetch_pa_id in Halignh.
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hb") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 2%nat ltac:(lia))
                       with "Hkm Hb2") as "Hb2'".
          iDestruct (phys_ram with "Hb2'") as %Hr2. iPureIntro.
          unfold pa_add in Hr2. exact Hr2. }
        iDestruct (text_split_halves pc w with "Hb") as "[#Hbl #Hbh]".
        iApply swp_step_ex.
        iApply (swp_run_hart_active_base2 Drw Dro Df rs rs2 pc
                  (subrange_vec_dec w 15 0) (subrange_vec_dec w 31 16) i
                  pmar0 pcfg 8 R
                  Hdisj HDpriv HDmisa HDmst HDpc HWnpc HDpma HDcfg HDhtif
                  Lpriv Lpc Lpma Lpcfg Lhtif HmS HmIE
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Halignl
                  Hramh Halignh HmC HnotRVC
                  ltac:(rewrite concat_subranges_id; exact (Hdec _ _ _ Hdok))
                  Hlp
                  with "Hcert Hrw Hro [] [] Hex").
        { iApply (text_fetch_obl pc 2 (subrange_vec_dec w 15 0) with "Hbl"). }
        { iApply (text_fetch_obl (add_vec_int pc 2) 2
                    (subrange_vec_dec w 31 16) with "Hbh"). }

    - (* ============================ F_RVC h ========================= *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct Hdec as (i0 & Hlp0 & Hdec2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* ---- 4-aligned: the compressed halfword sits in a 4-byte word -- *)
        iDestruct "Hbytes" as (w) "[%Hsub #Hb]".
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                       with "Hkm Hb0") as "Hb0'".
          iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
        iApply swp_step_ex.
        iApply (swp_run_hart_active_rvc Drw Dro Df rs rs2 pc w i0 i pmar0
                  pcfg 8 R
                  Hdisj HDpriv HDmisa HDmst HDpc HWnpc HDpma HDcfg HDhtif
                  Lpriv Lpc Lpma Lpcfg Lhtif HmS HmIE HmC
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Hal
                  ltac:(rewrite Hsub; exact HisRVC)
                  ltac:(rewrite Hsub; exact (proj1 (Hdec2 _ _ _ Hdok)))
                  Hlp
                  with "Hcert Hrw Hro [] [] Hex").
        { iApply (text_fetch_obl pc 4 w with "Hb"). }
        { iIntros "Hrw Hro".
          iApply (swp_span Drw Dro Df _ _ _ _ Hdisj
                    (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _ Hdok)))
                    with "Hcert Hrw Hro"). }
      + (* ---- 2 mod 4: a bare halfword read ---- *)
        iDestruct "Hbytes" as "#Hb".
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                       with "Hkm Hb0") as "Hb0'".
          iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        destruct (align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl.
        iApply swp_step_ex.
        iApply (swp_run_hart_active_rvc2 Drw Dro Df rs rs2 pc h i0 i pmar0
                  pcfg 8 R
                  Hdisj HDpriv HDmisa HDmst HDpc HWnpc HDpma HDcfg HDhtif
                  Lpriv Lpc Lpma Lpcfg Lhtif HmS HmIE HmC
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Halignl
                  HisRVC (proj1 (Hdec2 _ _ _ Hdok)) Hlp
                  with "Hcert Hrw Hro [] [] Hex").
        { iApply (text_fetch_obl pc 2 h with "Hb"). }
        { iIntros "Hrw Hro".
          iApply (swp_span Drw Dro Df _ _ _ _ Hdisj
                    (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _ Hdok)))
                    with "Hcert Hrw Hro"). }
  Qed.

End WpInstrRun.
