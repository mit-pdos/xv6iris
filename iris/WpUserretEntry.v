(* WpUserretEntry.v -- the userret ENTRY (phase A/B): sfence.vma;
   csrw satp,a0; sfence.vma.  Executes at the TRAMPOLINE va while satp
   still points at the KERNEL table (whose kroot[255]->kl1[511]->kl0[511]
   path also maps the trampoline page), switches satp to the USER table,
   and ends with an empty TLB under the user satp -- establishing
   [utlb_inv] for the user-phase steps (WpUserret's wp_instr_u engine). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpDecodeBridge WpRvcBridge WpLeafCommon.
Require Import WpGpr WpGprLui WpGprAddi WpMmodeShiftiop WpGprRvc WpGprRvcTor WpGprLoad WpLoad.
Require Import WpGprCsrwCommon WpGprCsrwB WpGprMretNew WpRelease.
Require Import WpEntryNew SmodeCore WpSmodeGpr WpSmodeSret WpKallocDecode.
Require Import TrampPt TrampTlb WpUserret.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Local Notation idx2t := (subrange_vec_dec tramp_vpn 26 18).
Local Notation idx1t := (subrange_vec_dec tramp_vpn 17 9).
Local Notation idx0t := (subrange_vec_dec tramp_vpn 8 0).
Local Notation idx0f := (subrange_vec_dec tf_vpn 8 0).

(* ===================================================================== *)
(* 1. Pure helpers: PMP read permission for an arbitrary in-RAM PTE       *)
(* address (from the components of any existing [pmp_tor0_pte_read] +     *)
(* the RAM coverage bound), and the kernel TLB's slot-63 disjunction.     *)
(* ===================================================================== *)

Lemma pmp_pte_read_of_bounds (cfg : type_of_register pmpcfg_n)
    (addrs : type_of_register pmpaddr_n) (aref a : mword 64) :
  pmp_tor0_pte_read cfg addrs aref ->
  ram_base <= uint a ->
  uint a + 8 <= ram_base + ram_size ->
  ram_base + ram_size <= uint (vec_access_dec addrs 0) * 4 ->
  pmp_tor0_pte_read cfg addrs a.
Proof.
  intros (HA & Hord & _ & HR) Hlo Hfit Hcov.
  exact (conj HA (conj Hord (conj (ram_pmp_match a _ Hlo Hfit Hcov) HR))).
Qed.

(* the kernel table's TLB contents never MATCH the trampoline vpn: every
   consistent slot is empty or the kernel-text superpage entry, whose
   masked vpn differs from [tramp_vpn]. *)
Lemma pw_tlb_entry_tramp_nonmatch (rp : mword 44) :
  match_TLB_Entry (pw_tlb_entry rp (mword_of_int 0)) (mword_of_int 0)
    (sign_extend' (57 - 12) tramp_vpn) = false.
Proof.
  unfold match_TLB_Entry, pw_tlb_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  vm_compute; reflexivity.
Qed.

Lemma ktramp_slot63 (kroot : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_pt_consistent kroot tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = None \/
  (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = Some ent /\
               match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
  (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn
                          (mk_pte tramp_ppn PTE_TRAMP) ptea)).
Proof.
  intros Hc.
  rewrite tramp_hash.
  destruct (Hc 63 ltac:(vm_compute; split; congruence)) as [Hn | He].
  - left. exact Hn.
  - right; left. exists (pw_tlb_entry kroot (mword_of_int 0)).
    split; [exact He | apply pw_tlb_entry_tramp_nonmatch].
Qed.

(* an all-None vector satisfies the slot disjunction trivially. *)
Lemma empty_slot63 (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall i, 0 <= i < 64 -> vec_access_dec tlbvec i = None) ->
  vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = None \/
  (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = Some ent /\
               match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
  (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn
                          (mk_pte tramp_ppn PTE_TRAMP) ptea)).
Proof.
  intros Hn. left. rewrite tramp_hash. apply Hn. lia.
Qed.

Section UserretEntry.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* RAM bounds of an owned 8-byte PTE (bytes 0 and 7 are RAM cells). *)
  Lemma pte8_ram_bounds (a v : mword 64) (dq : dfrac) :
    pte8 a v dq -∗
    ⌜ ram_base <= uint a /\ uint a + 8 <= ram_base + ram_size ⌝.
  Proof.
    iIntros "Hp".
    iAssert (⌜addr_is_ram a⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hp") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hp") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    iPureIntro.
    destruct Hr0 as [Hlo Hhi0].
    assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z)
      by (unfold ram_base, ram_size in Hhi0; change (Z.of_nat 7) with 7; lia).
    destruct Hr7 as [_ Hhi7].
    rewrite (uint_pa_add a 7 Hnw) in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    split; [exact Hlo | unfold ram_base, ram_size in *; lia].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 2. The entry-phase fetch: a 4-ALIGNED trampoline-page va fetched      *)
  (* through an EXPLICIT walk path (p2,p1,p0) -- kernel tables in phase    *)
  (* A/B, user tables at the third instruction -- with an EXPLICIT slot-63 *)
  (* disjunction and an EXPLICIT tlb outcome (hit: unchanged / walk: fill).*)
  (* ------------------------------------------------------------------- *)
  Lemma fetch_from_instr_bytes_tramp (p2 p1 p0 : mword 44)
      (σ : mstate) (va pa : mword 64) (w : mword 32)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (rgA rgB rgC : PMA_Region) (pmar0 : list PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqm dqe dqa dqh dqA dqB dqC : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = p2 ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    (* slot 63 (the trampoline hash slot): empty, non-matching, or the hit *)
    (vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = Some ent /\
                  match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                   = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn
                             (mk_pte tramp_ppn PTE_TRAMP) ptea))) ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p2 idx2t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p1 idx1t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p0 idx0t) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at p2 idx2t)) 8 = Some rgA /\
     (override_PMA (PMA_Region_attributes rgA) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at p1 idx1t)) 8 = Some rgB /\
     (override_PMA (PMA_Region_attributes rgB) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at p0 idx0t)) 8 = Some rgC /\
     (override_PMA (PMA_Region_attributes rgC) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (* --- va/pa geometry ([vm_compute] at the concrete entry vas) --- *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 3) ->
    mstate_interp σ -∗
    PC ↦ᵣ va -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    pte8 (pte_addr_at p2 idx2t) (pte_ptr p1) dqA -∗
    pte8 (pte_addr_at p1 idx1t) (pte_ptr p0) dqB -∗
    pte8 (pte_addr_at p0 idx0t) pte_tramp dqC -∗
    instr_bytes pa (F_Base w) -∗
    ⌜ exists tv2,
        exec (fetch tt) σ = Some (F_Base w, set_reg σ tlb tv2)
        /\ (tv2 = tlbvec \/
            tv2 = vec_update_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                    (Some (tramp_ent p0))) ⌝.
  Proof.
    iIntros (Hpma0 HmisaS HSXL Hmode Hppn Hasid Hslot HPBMTE HX Hcov
             HpA HpB HpC HrA HrB HrC
             Hcanon Hvpn Hident Hal4 Hpa4 Hram0 Hram3b)
      "Hsi Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa HpbA HpbB HpbC Hbytes".
    (* register lookups at σ *)
    iDestruct (state_interp_reg_dq σ cur_privilege _ _ with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ mstatus _ _ with "Hsi Hms") as %Lms.
    iDestruct (state_interp_reg_dq σ misa _ _ with "Hsi Hmisa") as %Lmisa.
    iDestruct (state_interp_reg_dq σ menvcfg _ _ with "Hsi Hmenv") as %Lmenv.
    iDestruct (state_interp_reg_dq σ pma_regions _ _ with "Hsi Hpma") as %Lpma.
    iDestruct (state_interp_reg_dq σ htif_tohost_base _ _ with "Hsi Hhtif") as %Lhtif.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb") as %Ltlb.
    iDestruct (reg_valid with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpa") as %Lpmpa.
    iAssert (mstate_interp σ) with "[Hreg Hmem]" as "Hsi". { iFrame. }
    (* the three walk PTE mem facts *)
    iDestruct (pte8_facts σ _ _ _ with "Hsi HpbA") as %[HbA HramA].
    iDestruct (pte8_facts σ _ _ _ with "Hsi HpbB") as %[HbB HramB].
    iDestruct (pte8_facts σ _ _ _ with "Hsi HpbC") as %[HbC HramC].
    iDestruct "Hsi" as "[Hreg Hmem]".
    destruct HpA as (HAx & Hordx & HrgAx & HRx).
    pose proof (addr_is_ram_not_in_clint _ HramA) as HncA.
    pose proof (addr_is_ram_not_in_sig _ HramA) as HnsA.
    pose proof (addr_is_ram_not_in_clint _ HramB) as HncB.
    pose proof (addr_is_ram_not_in_sig _ HramB) as HnsB.
    pose proof (addr_is_ram_not_in_clint _ HramC) as HncC.
    pose proof (addr_is_ram_not_in_sig _ HramC) as HnsC.
    destruct HrA as [HmA HprA]. destruct HrB as [HmB HprB]. destruct HrC as [HmC HprC].
    (* the translation at σ *)
    destruct (exec_translateAddr_tramp
                (InstructionFetch tt) tramp_vpn p2 p1 p0 tramp_ppn PTE_TRAMP
                rgA rgB rgC menvcfg0 σ
                ltac:(unfold PTE_TRAMP; lia)
                tramp_inv_red
                ltac:(vm_compute; reflexivity)
                tramp_chk_fetch
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Lmisa; exact HmisaS)
                ltac:(rewrite Lpmpc; exact HAx)
                ltac:(rewrite Lpmpa; exact Hordx)
                ltac:(rewrite Lpmpc; exact HRx)
                Lmenv HPBMTE
                ltac:(rewrite Lpmpa; exact HrgAx)
                ltac:(rewrite Lpma; exact HmA)
                HprA
                (within_clint_false _ 8 σ HncA ltac:(lia))
                (within_sig_false _ 8 σ HnsA ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                HbA
                ltac:(rewrite Lpmpa; destruct HpB as (_&_&HH&_); exact HH)
                ltac:(rewrite Lpma; exact HmB)
                HprB
                (within_clint_false _ 8 σ HncB ltac:(lia))
                (within_sig_false _ 8 σ HnsB ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                HbB
                ltac:(rewrite Lpmpa; destruct HpC as (_&_&HH&_); exact HH)
                ltac:(rewrite Lpma; exact HmC)
                HprC
                (within_clint_false _ 8 σ HncC ltac:(lia))
                (within_sig_false _ 8 σ HnsC ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                HbC
                ltac:(unfold PTE_TRAMP; vm_compute; reflexivity)
                satp0 pa va
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpriv
                ltac:(rewrite Lms; exact HSXL)
                Lsatp Hmode Hppn Hasid Hcanon Hvpn Hident
                tlbvec Ltlb Hslot)
      as (s' & Htr & Hcase).
    (* register facts survive a tlb write *)
    assert (Hreg1 : forall (tv2 : vec (option TLB_Entry) (2 ^ 6)) (rr : register),
              register_beq rr tlb = false ->
              register_lookup rr (set_reg σ tlb tv2).(sregs) = register_lookup rr σ.(sregs)).
    { intros tv2 rr Hne. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [reflexivity | exact Hne]. }
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    (* instruction bytes *)
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2alp Hbytes]".
    iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iPureIntro.
    destruct (Hpma0 pa 4) as (rgi & Hmi & Hxi & _ & _).
    (* normalize the translate's outcome state to a [set_reg .. tlb ..] *)
    assert (Hcase2 : exists tv2,
              s' = set_reg σ tlb tv2 /\
              (tv2 = tlbvec \/
               tv2 = vec_update_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                       (Some (tramp_ent p0)))).
    { destruct Hcase as [-> | ->].
      - exists tlbvec. split; [| left; reflexivity].
        rewrite <- Ltlb. symmetry. apply set_reg_tlb_id.
      - eexists. split; [reflexivity |]. right.
        change (tramp_tlb_ent tramp_vpn p0 tramp_ppn PTE_TRAMP) with (tramp_ent p0).
        reflexivity. }
    destruct Hcase2 as (tv2 & -> & Hout).
    exists tv2. split; [| exact Hout].
    apply (exec_fetch_F_Base_4_pa va pa w σ (set_reg σ tlb tv2) rgi Lpc Hal4 Htr).
    - rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
    - rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
    - rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram0 Hram3b Hcov).
    - rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
    - rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hmi.
    - exact Hpa4.
    - exact Hxi.
    - exact (within_clint_false pa 4 (set_reg σ tlb tv2) Hnc ltac:(lia)).
    - exact (within_sig_false pa 4 (set_reg σ tlb tv2) Hns ltac:(lia)).
    - apply within_htif_false.
      rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
    - intros j Hj. unfold set_reg; cbn [mem]. exact (Hbf j Hj).
    - rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
    - exact HnotRVC.
  Qed.

End UserretEntry.

(* ===================================================================== *)
(* 3. wp_step_tramp -- ONE entry-phase step: a 4-aligned trampoline-page  *)
(* instruction fetched through the EXPLICIT walk path, with the satp and  *)
(* tlb cells EXPLICIT (no invariant yet -- the entry tracks them by hand).*)
(* ===================================================================== *)

Section WpStepTramp.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_step_tramp (p2 p1 p0 : mword 44) E Φ
      (va pa : mword 64) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (rgA rgB rgC : PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dq dqA dqB dqC : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = p2 ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = Some ent /\
                  match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                   = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn
                             (mk_pte tramp_ppn PTE_TRAMP) ptea))) ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p2 idx2t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p1 idx1t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at p0 idx0t) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at p2 idx2t)) 8 = Some rgA /\
       (override_PMA (PMA_Region_attributes rgA) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at p1 idx1t)) 8 = Some rgB /\
       (override_PMA (PMA_Region_attributes rgB) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at p0 idx0t)) 8 = Some rgC /\
       (override_PMA (PMA_Region_attributes rgC) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (* --- va/pa geometry ([vm_compute] at the concrete entry vas) --- *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 3) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pte8 (pte_addr_at p2 idx2t) (pte_ptr p1) dqA -∗
    pte8 (pte_addr_at p1 idx1t) (pte_ptr p0) dqB -∗
    pte8 (pte_addr_at p0 idx0t) pte_tramp dqC -∗
    PC ↦ᵣ va -∗
    instr pa false i -∗
    (∀ σf (Hpceq : register_lookup PC σf.(sregs) = va)
       (tv2 : vec (option TLB_Entry) (2 ^ 6))
       (Hout : tv2 = tlbvec \/
               tv2 = vec_update_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                       (Some (tramp_ent p0))),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗
       tlb ↦ᵣ tv2 -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       pmpaddr_n ↦ᵣ pmpaddr00 -∗
       pte8 (pte_addr_at p2 idx2t) (pte_ptr p1) dqA -∗
       pte8 (pte_addr_at p1 idx1t) (pte_ptr p0) dqB -∗
       pte8 (pte_addr_at p0 idx0t) pte_tramp dqC -∗
       mstate_interp σf ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HSXL Hmm HPBMTE Hmenvval0 Hmode Hppn Hasid Hslot HX Hcov
             HpA HpB HpC HrA HrB HrC
             Hcanon Hvpn Hident Hal4 Hpa4 Hram0 Hram3b)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Htlb Hpmpc Hpmpa
       HpbA HpbB HpbC Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (HrA pmar0 Hpma_all) as HrA0.
    pose proof (HrB pmar0 Hpma_all) as HrB0.
    pose proof (HrC pmar0 Hpma_all) as HrC0.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w: the only possible geometry at a 4-aligned non-RVC va *)
      iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
      iIntros (σ) "Hsi".
      iDestruct (fetch_from_instr_bytes_tramp p2 p1 p0 σ va pa w
                   satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 rgA rgB rgC pmar0 tlbvec
                   Hpma_all HmisaS HSXL Hmode Hppn Hasid Hslot HPBMTE HX Hcov
                   HpA HpB HpC HrA0 HrB0 HrC0
                   Hcanon Hvpn Hident Hal4 Hpa4 Hram0 Hram3b
                   with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa HpbA HpbB HpbC Hbytes")
        as %Hfetch.
      destruct Hfetch as (tv2 & Hfetcheq & Hout).
      iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                   HmisaS Hmm HSIE
                   with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
      iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
      iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
      iMod (reg_update _ tlb _ tv2 with "Hreg Htlb") as "[Hreg Htlb]".
      set (σf := set_reg σ tlb tv2 : mstate).
      iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
      { unfold σf, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
      iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
      iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
      iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
      iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
      specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                        ltac:(rewrite Hmisa_σf; exact HmisaC)
                        ltac:(rewrite Hmisa_σf; exact HmisaA)
                        ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                        ltac:(unfold cfg_ok; right; split;
                              [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
      assert (Lpc_σf : register_lookup PC σf.(sregs) = va).
      { unfold σf, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
      iMod ("H" $! σf Lpc_σf tv2 Hout
              with "Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Htlb Hpmpc Hpmpa
                    HpbA HpbB HpbC [$Hreg $Hmem]")
        as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      iDestruct "Hexec" as %Hexec.
      cbn [fetch_is_rvc] in Hrvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - cbn [fetch_is_rvc] in Hrvc. discriminate Hrvc.
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

End WpStepTramp.

(* ===================================================================== *)
(* 4. wp_userret_entry -- the page-table switch: sfence.vma; csrw satp,a0;*)
(* sfence.vma.  Consumes the kernel [tlb_inv] (satp leaves it and the PMP *)
(* cells migrate into the user bundle) and establishes [utlb_inv].        *)
(* ===================================================================== *)

Section WpUserretEntryTop.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_userret_entry (kroot kl1 kl0 uroot ul1 ul0 tfp : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (usatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (rg2 rg1 rg0t rg0f rgk2 rgk1 rgk0 : PMA_Region) {dq dqk : dfrac} :
    ↑minstretN ⊆ E ->
    (* S-mode config *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* a0 holds the USER satp value *)
    m !! Regidx (mword_of_int 10) = Some usatp ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    (* PMA pte-read regions: the user path (4, they seed [upmp_config])
       and the kernel trampoline path (3, they drive the phase-A/B walks) *)
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at uroot idx2t)) 8 = Some rg2 /\
       (override_PMA (PMA_Region_attributes rg2) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul1 idx1t)) 8 = Some rg1 /\
       (override_PMA (PMA_Region_attributes rg1) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0t)) 8 = Some rg0t /\
       (override_PMA (PMA_Region_attributes rg0t) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0f)) 8 = Some rg0f /\
       (override_PMA (PMA_Region_attributes rg0f) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at kroot idx2t)) 8 = Some rgk2 /\
       (override_PMA (PMA_Region_attributes rgk2) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at kl1 idx1t)) 8 = Some rgk1 /\
       (override_PMA (PMA_Region_attributes rgk1) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at kl0 idx0t)) 8 = Some rgk0 /\
       (override_PMA (PMA_Region_attributes rgk0) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv kroot -∗
    ktramp_pte_bytes kroot kl1 kl0 dqk -∗
    upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) -∗
    pc_is (uva 0x9c) -∗
    gpr_file m -∗
    instr (upa 0x9c) false ai_sfence -∗
    instr (upa 0xa0) false ai_csrw -∗
    instr (upa 0xa4) false ai_sfence -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv uroot ul1 ul0 tfp -∗
      pc_is (uva 0xa8) -∗
      gpr_file m -∗
      ktramp_pte_bytes kroot kl1 kl0 dqk -∗
      pte_super_bytes kroot (DfracOwn 1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HSXL HTVM Hmm HPBMTE Hmenvval0 Ha0 HuMode Huasid Huppn
      HrU2 HrU1 HrU0t HrU0f HrK2 HrK1 HrK0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hktramp Hupte
             [Hpc Hnpc] [%Hdom Hfmap] Hi1 Hi2 Hi3 Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    (* open the kernel invariant: satp value, tlb value + consistency,
       the super PTE, and the PMP cells + ambient facts *)
    iDestruct (tlb_inv_open with "Hktlb") as (ksatp0 tlbvec0)
      "(Hsatp & %HkMode & %Hkasid & %Hkppn & Htlb & %Hconsk & Hsuper & Hkpmp)".
    iDestruct "Hkpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpk & %Hpkreg & %HX & %HW & %HR & %Hcov)".
    iDestruct "Hktramp" as "(HkbA & HkbB & HkbC)".
    iDestruct "Hupte" as "(HubA & HubB & HubC & HubD)".
    (* PMP read permission for all seven walk PTE addresses, from RAM
       coverage + the owned cells' RAM bounds *)
    iDestruct (pte8_ram_bounds with "HkbA") as %[HloKA HfitKA].
    iDestruct (pte8_ram_bounds with "HkbB") as %[HloKB HfitKB].
    iDestruct (pte8_ram_bounds with "HkbC") as %[HloKC HfitKC].
    iDestruct (pte8_ram_bounds with "HubA") as %[HloUA HfitUA].
    iDestruct (pte8_ram_bounds with "HubB") as %[HloUB HfitUB].
    iDestruct (pte8_ram_bounds with "HubC") as %[HloUC HfitUC].
    iDestruct (pte8_ram_bounds with "HubD") as %[HloUD HfitUD].
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloKA HfitKA Hcov) as HpKA.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloKB HfitKB Hcov) as HpKB.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloKC HfitKC Hcov) as HpKC.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloUA HfitUA Hcov) as HpUA.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloUB HfitUB Hcov) as HpUB.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloUC HfitUC Hcov) as HpUC.
    pose proof (pmp_pte_read_of_bounds _ _ _ _ Hpk HloUD HfitUD Hcov) as HpUD.
    (* the concrete next-pc equalities *)
    assert (Hva01 : add_vec_int (uva 0x9c) 4 = uva 0xa0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva02 : add_vec_int (uva 0xa0) 4 = uva 0xa4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva03 : add_vec_int (uva 0xa4) 4 = uva 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ================= STEP 1: sfence.vma (kernel PT) ================= *)
    iApply (wp_step_tramp kroot kl1 kl0 E Φ (uva 0x9c) (upa 0x9c) ai_sfence
              ksatp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 rgk2 rgk1 rgk0 tlbvec0
              HN HSIE HSXL Hmm HPBMTE Hmenvval0 HkMode Hkppn Hkasid
              (ktramp_slot63 kroot tlbvec0 Hconsk)
              HX Hcov HpKA HpKB HpKC HrK2 HrK1 HrK0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa
                    HkbA HkbB HkbC Hpc Hi1").
    iIntros (σf1 Hpceq1 tv1 Hout1)
      "Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa HkbA HkbB HkbC Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv1.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms1.
    iMod (reg_update _ nextPC _ (uva 0xa0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc1 := set_reg σf1 nextPC (uva 0xa0)).
    assert (Lpriv1p : register_lookup cur_privilege s_pc1.(sregs) = Supervisor)
      by (unfold s_pc1; tmig; exact Lpriv1).
    assert (Lms1p : register_lookup mstatus s_pc1.(sregs) = mstatus0)
      by (unfold s_pc1; tmig; exact Lms1).
    destruct (exec_execute_SFENCE_VMA_S s_pc1 Lpriv1p
                ltac:(rewrite Lms1p; exact HTVM)) as (tlbz1 & Hex1 & Hnone1).
    iMod (reg_update _ tlb _ tlbz1 with "Hreg Htlb") as "[Hreg Htlb]".
    iModIntro.
    iExists (set_reg s_pc1 tlb tlbz1).
    iSplitR.
    { iPureIntro. rewrite Hpceq1. rewrite Hva01. fold s_pc1.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex1. }
    iSplitL "Hreg Hmem".
    { unfold s_pc1, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc1 : register_lookup nextPC (set_reg s_pc1 tlb tlbz1).(sregs) = uva 0xa0).
    { unfold s_pc1; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc1) in "Hpc".
    iNext.
    (* ================= STEP 2: csrw satp, a0 (kernel PT) ================= *)
    iApply (wp_step_tramp kroot kl1 kl0 E Φ (uva 0xa0) (upa 0xa0) ai_csrw
              ksatp0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 rgk2 rgk1 rgk0 tlbz1
              HN HSIE HSXL Hmm HPBMTE Hmenvval0 HkMode Hkppn Hkasid
              (empty_slot63 tlbz1 Hnone1)
              HX Hcov HpKA HpKB HpKC HrK2 HrK1 HrK0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa
                    HkbA HkbB HkbC Hpc Hi2").
    iIntros (σf2 Hpceq2 tv2 Hout2)
      "Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa HkbA HkbB HkbC Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv2.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms2.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa2.
    iMod (reg_update _ nextPC _ (uva 0xa4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc2 := set_reg σf2 nextPC (uva 0xa4)).
    assert (Lpriv2p : register_lookup cur_privilege s_pc2.(sregs) = Supervisor)
      by (unfold s_pc2; tmig; exact Lpriv2).
    assert (Lms2p : register_lookup mstatus s_pc2.(sregs) = mstatus0)
      by (unfold s_pc2; tmig; exact Lms2).
    assert (Lmisa2p : register_lookup misa s_pc2.(sregs) = misa0)
      by (unfold s_pc2; tmig; exact Lmisa2).
    (* a0's value at the executing state *)
    assert (Hmsp : m !! Regidx (mword_of_int 10 : mword 5)
                   = Some (m !!! Regidx (mword_of_int 10 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value (mword_of_int 10) (m !!! Regidx (mword_of_int 10 : mword 5)) s_pc2
                 with "Hreg Hspc") as %Lva2.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Hma0v : m !!! Regidx (mword_of_int 10 : mword 5) = usatp)
      by (apply lookup_total_correct; exact Ha0).
    replace (Z.eqb (uint (mword_of_int 10 : mword 5)) 0) with false in Lva2
      by (vm_compute; reflexivity).
    rewrite Hma0v in Lva2.
    pose proof (exec_execute_csrw_satp_S (mword_of_int 10) s_pc2
                  ltac:(vm_compute; lia) Lpriv2p
                  ltac:(rewrite Lms2p; exact HTVM)
                  ltac:(rewrite Lmisa2p; exact HmisaS)
                  ltac:(rewrite Lms2p; exact HSXL)) as Hex2.
    rewrite Lva2 in Hex2.
    rewrite (satp_legalized_sv39 (register_lookup satp s_pc2.(sregs)) usatp HuMode) in Hex2.
    iMod (reg_update _ satp _ usatp with "Hreg Hsatp") as "[Hreg Hsatp]".
    iModIntro.
    iExists (set_reg s_pc2 satp usatp).
    iSplitR.
    { iPureIntro. rewrite Hpceq2. rewrite Hva02. fold s_pc2.
      change ai_csrw with (CSRReg (csr_satp, Regidx (mword_of_int 10 : mword 5), zreg, CSRRW)).
      exact Hex2. }
    iSplitL "Hreg Hmem".
    { unfold s_pc2, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc2 : register_lookup nextPC (set_reg s_pc2 satp usatp).(sregs) = uva 0xa4).
    { unfold s_pc2; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc2) in "Hpc".
    iNext.
    (* ================= STEP 3: sfence.vma (USER PT) ================= *)
    assert (Hslot3 : vec_access_dec tv2 (tlb_hash (__id 39) tramp_vpn) = None \/
      (exists ent, vec_access_dec tv2 (tlb_hash (__id 39) tramp_vpn) = Some ent /\
                   match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
      (exists ptea, vec_access_dec tv2 (tlb_hash (__id 39) tramp_vpn)
                    = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn
                              (mk_pte tramp_ppn PTE_TRAMP) ptea))).
    { destruct Hout2 as [-> | ->].
      - apply empty_slot63. exact Hnone1.
      - right; right. exists (pte_addr_at kl0 idx0t).
        rewrite tramp_hash.
        rewrite (vec64_access_update tlbz1 63 63 _ ltac:(lia)).
        replace (Z.eqb 63 63) with true by reflexivity.
        unfold tramp_ent, pte_tramp. reflexivity. }
    iApply (wp_step_tramp uroot ul1 ul0 E Φ (uva 0xa4) (upa 0xa4) ai_sfence
              usatp mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 rg2 rg1 rg0t tv2
              HN HSIE HSXL Hmm HPBMTE Hmenvval0 HuMode Huppn Huasid
              Hslot3
              HX Hcov HpUA HpUB HpUC HrU2 HrU1 HrU0t
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; split; congruence)
              ltac:(vm_compute; split; congruence)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa
                    HubA HubB HubC Hpc Hi3").
    iIntros (σf3 Hpceq3 tv3 Hout3)
      "Hpriv Hms Hmie Hmdl Hmenv Hsatp Htlb Hpmpc Hpmpa HubA HubB HubC Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv3.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms3.
    iMod (reg_update _ nextPC _ (uva 0xa8) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc3 := set_reg σf3 nextPC (uva 0xa8)).
    assert (Lpriv3p : register_lookup cur_privilege s_pc3.(sregs) = Supervisor)
      by (unfold s_pc3; tmig; exact Lpriv3).
    assert (Lms3p : register_lookup mstatus s_pc3.(sregs) = mstatus0)
      by (unfold s_pc3; tmig; exact Lms3).
    destruct (exec_execute_SFENCE_VMA_S s_pc3 Lpriv3p
                ltac:(rewrite Lms3p; exact HTVM)) as (tlbz3 & Hex3 & Hnone3).
    iMod (reg_update _ tlb _ tlbz3 with "Hreg Htlb") as "[Hreg Htlb]".
    iModIntro.
    iExists (set_reg s_pc3 tlb tlbz3).
    iSplitR.
    { iPureIntro. rewrite Hpceq3. rewrite Hva03. fold s_pc3.
      change ai_sfence with (SFENCE_VMA (zreg, zreg)). exact Hex3. }
    iSplitL "Hreg Hmem".
    { unfold s_pc3, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc".
    assert (Lnpc3 : register_lookup nextPC (set_reg s_pc3 tlb tlbz3).(sregs) = uva 0xa8).
    { unfold s_pc3; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc3) in "Hpc".
    iNext.
    (* ================= close: seal [utlb_inv] ================= *)
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv
                          [Hsatp Htlb HubA HubB HubC HubD Hpmpc Hpmpa]
                          [$Hpc $Hnpc] [Hfmap] [$HkbA $HkbB $HkbC] Hsuper").
    { iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbz3 HuMode Huasid Huppn
                (utlb_consistent_empty ul0 tfp tlbz3 Hnone3)
                with "Hsatp Htlb [$HubA $HubB $HubC $HubD] [Hpmpc Hpmpa]").
      iExists pmpcfg0, pmpaddr00, rg2, rg1, rg0t, rg0f.
      iFrame "Hpmpc Hpmpa". iPureIntro.
      exact (conj HpUA (conj HpUB (conj HpUC (conj HpUD (conj
              (fun pmar Hall => conj (HrU2 pmar Hall)
                 (conj (HrU1 pmar Hall) (conj (HrU0t pmar Hall) (HrU0f pmar Hall))))
              (conj HX (conj HW (conj HR Hcov)))))))). }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

End WpUserretEntryTop.
