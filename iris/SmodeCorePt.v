(* SmodeCorePt.v -- the S-mode instruction-step ENGINE over the
   generalized page-table-tree invariant [tlb_inv_pt] (KptTree.v).

   The successor of [wp_instr_s_tlbinv]/[wp_instr_s_tlbinv_ad]
   (SmodeCore.v): the fetch's per-chunk translation goes through the
   invariant-ABSORPTION theorem [tlb_inv_pt_translateAddr_fetch] instead
   of the pure [kpt_mem]-based walk, so

     - there is NO A-bit premise (the `_ad` engines' ∀-over-RAM
       [fst (adf (svpn_of a)) = true] residue is gone): a fetch touching
       a clear-A page takes the Svadu write-back instead of faulting,
       and the invariant absorbs the page-table write;
     - the fetch may CHANGE MEMORY (the written leaf slot); instruction
       bytes are re-derived per chunk from the persistent [↦ₘ□] window
       against the post-chunk heap interpretation -- ownership
       separation guarantees the PT write missed the text, no pure
       memory relation is needed.

   Layers:
     - [pt_regs_preserved]: the absorption theorem's sregs-shape
       disjunct gives every non-tlb register lookup unchanged;
     - [tlb_inv_pt_fetch]: the unified S-mode fetch as a [==∗]: for any
       geometry (4-aligned Base / 2-aligned 2+2 Base / RVC at either
       alignment), [exec (fetch tt) σ = Some (r, σf)] with the state
       interpretation and [tlb_inv_pt] re-established at [σf], reusing
       SmodeCore's state-generic fetch drivers [exec_fetch_*_S_gen];
     - [wp_instr_s_tlbinv_pt]: the step engine, same interface as
       [wp_instr_s_tlbinv] with [tlb_inv_pt] threaded in place of
       [tlb_inv].                                                        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodeCore.
Require Import KptTree.
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* every non-tlb register survives a translation step (the absorption
   theorem's sregs shape: unchanged, or exactly one tlb register_set) *)
Lemma pt_regs_preserved (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs)%type ->
  forall rr, register_beq rr tlb = false ->
    register_lookup rr rs' = register_lookup rr rs.
Proof.
  intros [-> | (tv & ->)] rr Hrr; [reflexivity |].
  apply (irrelevant_register_set rr tlb rs tv Hrr).
Qed.

Section SmodeCorePt.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* The unified S-mode fetch over [tlb_inv_pt], as a bupd.  Pure         *)
  (* premises are the σ-level config lookups (the engine extracts them    *)
  (* from [smode_config]/[hw_config]'s cells); everything the walk needs  *)
  (* rides inside [tlb_inv_pt].                                           *)
  (* =================================================================== *)
  Lemma s_regime_fetch (R : s_regime) (σ : mstate)
      (pc : mword 64) (r : FetchResult) :
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    mstate_interp σ -∗
    sr_inv R -∗
    instr_bytes pc r ==∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      sr_inv R.
  Proof.
    intros Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma.
    iIntros "[Hreg [Hmem Hdev]] Hinv Hbytes".
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC #Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: one chunk, one 4-byte read *)
        iAssert (⌜addr_is_text pc⌝)%I as %Htext.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        pose proof (addr_is_text_ram pc Htext) as Hram.
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iMod (sr_absorb_region R (InstructionFetch tt) pc σ
                (or_introl eq_refl) Htext Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpma with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   s1.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s1)).
        { apply (exec_fetch_F_Base_4_S_gen pc w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp pc (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)).
            exact Hmatch0.
          - exact Hal.
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned: TWO chunks (low at pc, high at pc+2) *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        pose proof (align2_plus2 pc H2al) as Halignh0.
        rewrite fetch_pa_id in Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
        { intros j _. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜addr_is_text pc⌝)%I as %Htextl.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        pose proof (addr_is_text_ram pc Htextl) as Hraml.
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hraml1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iAssert (⌜addr_is_text (add_vec_int pc 2)⌝)%I as %Htexth.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb2") as %Hr2. iPureIntro.
          unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        pose proof (addr_is_text_ram (add_vec_int pc 2) Htexth) as Hramh.
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pc 2) 1)).
        { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3. }
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl.
        pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch.
        pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (Lpma pc 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Lpma (add_vec_int pc 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        (* --- low chunk: σ -> s1 --- *)
        iMod (sr_absorb_region R (InstructionFetch tt) pc σ
                (or_introl eq_refl) Htextl Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpma with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        (* config lookups at s1 *)
        assert (L1pc : register_lookup PC s1.(sregs) = pc)
          by (rewrite (Hpres1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1misa : register_lookup misa s1.(sregs) = MISA_C)
          by (rewrite (Hpres1 misa ltac:(vm_compute; reflexivity)); exact Lmisa).
        assert (L1menv : register_lookup menvcfg s1.(sregs) = MENVCFG_S)
          by (rewrite (Hpres1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (L1SXL : _get_Mstatus_SXL (register_lookup mstatus s1.(sregs)) = 'b"10")
          by (rewrite (Hpres1 mstatus ltac:(vm_compute; reflexivity)); exact LSXL).
        assert (L1pma : pma_allows_all (register_lookup pma_regions s1.(sregs)))
          by (rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        (* low-halfword byte facts at s1 *)
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   s1.(mem) !! (pa_add pc j)
                   = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)⌝)%I as %HblS1.
        { iIntros (j Hj). rewrite nth_byte_subrange_lo; [| exact Hj].
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        (* --- high chunk: s1 -> s2 --- *)
        iMod (sr_absorb_region R (InstructionFetch tt) (add_vec_int pc 2) s1
                (or_introl eq_refl) Htexth L1misa L1menv L1htif L1priv L1SXL
                (exec_effectivePrivilege_fetch _ _ s1)
                (exec_is_shadow_stack_fetch s1)
                L1pma with "Hreg Hmem Hinv")
          as (s2) "(%Htr2 & %Hmdev2 & %Hsh2 & %Hgr2 & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh2) as Hpres2.
        assert (Hpres12 : forall rr, register_beq rr tlb = false ->
                  register_lookup rr s2.(sregs) = register_lookup rr σ.(sregs)).
        { intros rr Hrr. rewrite (Hpres2 rr Hrr). exact (Hpres1 rr Hrr). }
        (* high-halfword byte facts at s2 *)
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   s2.(mem) !! (pa_add (add_vec_int pc 2) j)
                   = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)⌝)%I as %HbhS2.
        { iIntros (j Hj). rewrite nth_byte_subrange_hi; [| exact Hj].
          rewrite (Haddr j Hj).
          iDestruct (big_sepL_lookup _ _ (2 + j)%nat (2 + j)%nat with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        (* the s1/s2 PMP facts for the two instruction reads *)
        destruct Hgr1 as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
        destruct Hgr2 as (HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s2)).
        { apply (exec_fetch_F_Base_2_S_gen pc w σ s1 s2 regl regh
                   Lpc L1pc HmisaC Hbit0 Hbit1 Hal Htr1 Htr2).
          - exact HA1.
          - exact Hord1.
          - exact (ram_fetch_pmp pc (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hraml Hraml1 Hcov1).
          - exact HX1.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hml0.
          - exact Halignl0.
          - exact Hxl.
          - apply within_clint_false; [exact Hncl | lia].
          - apply within_sig_false; [exact Hnsl | lia].
          - apply within_htif_false. exact L1htif.
          - apply addr_is_ram_not_dev. exact Hraml.
          - exact HblS1.
          - exact L1priv.
          - exact HA2.
          - exact Hord2.
          - exact (ram_fetch_pmp (add_vec_int pc 2) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hramh Hramh1 Hcov2).
          - exact HX2.
          - rewrite (Hpres12 pma_regions ltac:(vm_compute; reflexivity)). exact Hmh0.
          - exact Halignh0.
          - exact Hxh.
          - apply within_clint_false; [exact Hnch | lia].
          - apply within_sig_false; [exact Hnsh | lia].
          - apply within_htif_false.
            rewrite (Hpres12 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hramh.
          - exact HbhS2.
          - rewrite (Hpres12 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC.
          - exact (concat_subranges_id w). }
        iModIntro. iExists s2.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; rewrite Hmdev2; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres12 |].
        rewrite /mstate_interp. rewrite Hmdev2 Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window: one chunk, one 4-byte read *)
        iDestruct "Hbytes" as (w) "[%Hsub #Hbytes]".
        iAssert (⌜addr_is_text pc⌝)%I as %Htext.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        pose proof (addr_is_text_ram pc Htext) as Hram.
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iMod (sr_absorb_region R (InstructionFetch tt) pc σ
                (or_introl eq_refl) Htext Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpma with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   s1.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { rewrite <- Hsub.
          apply (exec_fetch_RVC_4_S_gen pc w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp pc (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact Hal.
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - rewrite Hsub. exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned: one chunk, one 2-byte read *)
        iDestruct "Hbytes" as "#Hbytes".
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        iAssert (⌜addr_is_text pc⌝)%I as %Htext.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        pose proof (addr_is_text_ram pc Htext) as Hram.
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hram1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iMod (sr_absorb_region R (InstructionFetch tt) pc σ
                (or_introl eq_refl) Htext Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpma with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   s1.(mem) !! (pa_add pc j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pc 2) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { apply (exec_fetch_RVC_2_S_gen pc h σ s1 region Lpc HmisaC
                   Hbit0 Hbit1 Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp pc (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram1 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact Halignl0.
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_Ext_Error *) done.
  Qed.

  (* =================================================================== *)
  (* THE STEP ENGINE over [tlb_inv_pt]: same interface as                 *)
  (* [wp_instr_s_tlbinv] with the tree invariant threaded, and NO A/D     *)
  (* premise -- the Svadu write-back is absorbed inside the fetch.        *)
  (* =================================================================== *)
  Lemma wp_instr_s_regime (R : s_regime) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    smode_config γ dq -∗
    sr_inv R -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          sr_inv R -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hsm Htlbinv Hpc Hinstr H".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    (* interrupt dispatch decision at σ (before the fetch moves the state) *)
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    (* σ-level config lookups for the fetch *)
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpc")     as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmstatus") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenvc")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")   as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")    as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    (* the unified fetch through the tree invariant (may write A/D back) *)
    iMod (s_regime_fetch R σ pc r
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)".
    (* decode agreement + its side conditions, at σf *)
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc Htlbinv]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] Htlbinv Hpc'").
      iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc"). }
    iDestruct "Hexec" as %Hexec.
    (* the dispatch fact is at σ; the machinery wants it at σ (pre-fetch) *)
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
  Qed.

  (* =================================================================== *)
  (* THE RAW-CELL DATA ENGINE over [tlb_inv_pt]: the [wp_instr_s_config_  *)
  (* tlbinv] mirror.  The caller's fupd receives the WHOLE [tlb_inv_pt]   *)
  (* (not opened pieces): a data-access leaf runs its own data-side       *)
  (* translation through [tlb_inv_pt_translateAddr_load/store] (a [==∗]   *)
  (* inside the fupd) and stashes the returned invariant in its           *)
  (* continuation.  No A/D premise anywhere.                              *)
  (* =================================================================== *)
  Lemma wp_instr_s_config_regime (R : s_regime) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       sr_inv R -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpc")     as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmstatus") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenvc")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")   as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")    as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    iMod (s_regime_fetch R σ pc r
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)".
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    iMod ("H" $! σf Lpc_σf
            with "Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
  Qed.


  (* =================================================================== *)
  (* Sv39-kernel instances under the ORIGINAL names/signatures: nothing   *)
  (* downstream moves.  [sr_inv (kpt_regime root_ppn)] is definitionally  *)
  (* [tlb_inv_pt root_ppn], so [exact] closes each restatement.           *)
  (* =================================================================== *)
  Lemma tlb_inv_pt_fetch (root_ppn : mword 44) (σ : mstate)
      (pc : mword 64) (r : FetchResult) :
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    mstate_interp σ -∗
    tlb_inv_pt root_ppn -∗
    instr_bytes pc r ==∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      tlb_inv_pt root_ppn.
  Proof. exact (s_regime_fetch (kpt_regime root_ppn) σ pc r). Qed.

  Lemma wp_instr_s_config_tlbinv_pt (root_ppn : mword 44) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       tlb_inv_pt root_ppn -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_instr_s_config_regime (kpt_regime root_ppn) Φ pc is_rvc i
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

End SmodeCorePt.
