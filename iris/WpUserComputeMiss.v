(* WpUserComputeMiss.v -- the TLB-MISS twins of the retiring compute USTEP
   arms.  Where the hit arms (WpUserCompute.v) ride [wp_instr_u_hit] on a
   TLB that already caches [va]'s page, these ride [wp_instr_u_miss]: the
   model walks the page table inline, fills the TLB with [upt_entry vpn ie],
   decodes, executes, and retires -- all in the one fetch step.  The frame
   re-establishes with the FILLED TLB, whose [upt_tlb_ok] follows from
   [upt_tlb_ok_fill].  These are the arms the TOTAL classification needs for
   an arbitrary (possibly empty) TLB.                                       *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import CommonWalk.
Require Import UptInv Pt4kWalk SmodePte.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserComputeMiss.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation wp_instr_u_miss := (WpUserBase.wp_instr_u_miss U).
  Local Notation wp_instr_u_hit := (WpUserBase.wp_instr_u_hit U).
  Local Notation wp_instr_u_hit_data := (WpUserBase.wp_instr_u_hit_data U).
  Local Notation wp_instr_u_miss_data := (WpUserBase.wp_instr_u_miss_data U).


  (* ------------------------------------------------------------------ *)
  (* PA bridge: a FILLED entry translates exactly like the WALK that      *)
  (* filled it.  [u_pa (upt_entry vpn ie) va vpn] (the hit-form address,  *)
  (* read off the stored TLB entry) coincides with [u_walk_pa (uw_pte0    *)
  (* ie) va] (the miss-form address, computed directly from the leaf      *)
  (* PTE).  tlb_get_ppn on a level-0 entry drops the (zero) levelMask and *)
  (* returns the leaf ppn.  This is the consistency fact that lets a      *)
  (* single classification serve both the hit and the miss branch.        *)
  (* ------------------------------------------------------------------ *)
  Lemma u_pa_upt_entry_walk (vpn : mword 27) (ie : uwalk_info) (va : mword 64) :
    u_pa (upt_entry vpn ie) va vpn = u_walk_pa (uw_pte0 ie) va.
  Proof.
    unfold u_pa, u_walk_pa. f_equal. f_equal.
    unfold upt_entry, u_walk_entry, tlb_get_ppn.
    cbn [TLB_Entry_levelMask TLB_Entry_ppn].
    match goal with |- context[and_vec ?a (zero_extend' 64 ?b)] =>
      replace (and_vec a (zero_extend' 64 b)) with (zeros' 64 : mword 64);
      [| symmetry; apply and64_zero_r; vm_compute; reflexivity] end.
    rewrite or64_zeros_r.
    rewrite trunc44_zext.
    apply zext44_and_ones. vm_compute. reflexivity.
  Qed.


  (* Updating a 64-slot TLB vector at a slot to the value it ALREADY holds
     is the identity.  This is what collapses the miss-engine's FILLED TLB
     back to the original one on the HIT branch of the combined engine, so
     both branches can hand back one uniform (filled) frame.               *)
  Lemma vec64_update_same {T} `{Inhabited T} (v : vec T (2 ^ 6)) (m : Z) (t : T) :
    0 <= m < 64 -> vec_access_dec v m = t -> vec_update_dec v m t = v.
  Proof.
    intros Hm Hacc. destruct v as [xs Hlen].
    assert (Hl : length xs = 64%nat) by (rewrite Hlen; reflexivity).
    unfold vec_update_dec.
    destruct (sumbool_of_bool (0 <=? m <? 2 ^ 6)) as [He|He].
    2:{ exfalso.
        assert (Ht : ((0 <=? m) && (m <? 2 ^ 6))%bool = true)
          by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite Ht in He. discriminate He. }
    apply eq_sigT_hprop; [ intros ? ? ?; apply UIP_nat | ].
    cbn [projT1].
    unfold update_list_dec, update_list_inc, length_list. rewrite Hl.
    change (Z.of_nat 64 - 1) with 63.
    set (k := Z.to_nat (63 - m)).
    assert (Hk : (k < length xs)%nat) by (unfold k; rewrite Hl; lia).
    rewrite (tlb_list_update_insert xs k t Hk).
    apply list_insert_id.
    unfold vec_access_dec, access_list_dec, access_list_inc, length_list in Hacc.
    cbn [projT1] in Hacc. rewrite Hl in Hacc.
    change (Z.of_nat 64 - 1) with 63 in Hacc.
    destruct (63 - m <? 0) eqn:Hlt.
    { apply Z.ltb_lt in Hlt. lia. }
    fold k in Hacc.
    destruct (lookup_lt_is_Some_2 xs k Hk) as [y Hy].
    rewrite Hy. f_equal.
    rewrite (nth_lookup_Some xs k dummy_value y Hy) in Hacc. exact Hacc.
  Qed.


  (* ================================================================== *)
  (* THE COMBINED FETCH ENGINE.  Given only [spec!!vpn = Some ie] and a  *)
  (* [upt_tlb_ok] TLB (which the EMPTY TLB satisfies), it dispatches:     *)
  (*   - a matching cached entry  -> the HIT engine (and the stored entry *)
  (*     is forced to be [upt_entry vpn ie], so the filled TLB collapses  *)
  (*     back to the original via [vec64_update_same]);                   *)
  (*   - an empty or colliding slot -> the MISS engine (walk + fill),     *)
  (*     converting the hit-form code address to the walk form via the PA *)
  (*     bridge.                                                          *)
  (* Both branches hand back ONE uniform continuation: the FILLED TLB and *)
  (* [upt_inv].  Arms riding this need NO TLB-state hypothesis at all --  *)
  (* exactly what makes the TOTAL step classification provable against an *)
  (* arbitrary (cold) TLB.                                                *)
  (* ================================================================== *)
  Lemma wp_instr_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (upt_entry vpn ie))) -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          upt_inv root slots spec -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    (* the code / align facts, transported onto the WALK address for the
       two miss branches *)
    assert (Hcw' : forall j : nat, (j < 4)%nat ->
              code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)).
    { intros j Hj. rewrite <- (u_pa_upt_entry_walk vpn ie va). exact (Hcw j Hj). }
    assert (Hpaal' : is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true).
    { rewrite <- (u_pa_upt_entry_walk vpn ie va). exact Hpaal. }
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - (* the slot is occupied *)
      destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + (* HIT: the stored entry is forced to be [upt_entry vpn ie] *)
        destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (upt_entry vpn ie)) = tlbvec).
        { apply vec64_update_same; [ pose proof (tlb_hash_range vpn); lia | exact Hvacc ]. }
        iApply (wp_instr_u_hit va vpn ie w ii ms_v tlbvec E Φ HN Hvacc Hchk0 HupdN
                  Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hcfg").
        iIntros (σ Hpceq Hag Hpins) "Hσ".
        iMod ("H" $! σ Hpceq Hag with "Hσ") as (s_exec) "(%Hexe & Hσ' & Hcont)".
        iModIntro. iExists s_exec. iFrame "Hσ'". iSplitR; [iPureIntro; exact Hexe |].
        iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
        iApply ("Hcont" with "Hhs' Hpriv' Hms' [Htlbc'] Hpc' Hupt Hcfg'").
        rewrite Hfill_id. iExact "Htlbc'".
      + (* colliding miss: the walk fills a fresh entry *)
        iApply (wp_instr_u_miss va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                  (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
    - (* empty miss: the walk fills the slot *)
      iApply (wp_instr_u_miss va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                (or_introl Hvacc)
                Hchk0 HupdN Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
  Qed.

  (* ================================================================= *)
  (* Combined (hit + miss) fetch engine WITH the data callback.          *)
  (* Dispatches the FETCH from only [upt_tlb_ok] + [spec!!vpn], and       *)
  (* hands the (fetch-filled) tlb + upt_inv to the execute callback so a  *)
  (* memory arm can additionally walk+fill the DATA EA.  Both branches    *)
  (* present ONE uniform callback (tlb = the fetch-filled vector).        *)
  (* ================================================================= *)
  Lemma wp_instr_u_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = vec_update_dec tlbvec
                                                  (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    assert (Hcw' : forall j : nat, (j < 4)%nat ->
              code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)).
    { intros j Hj. rewrite <- (u_pa_upt_entry_walk vpn ie va). exact (Hcw j Hj). }
    assert (Hpaal' : is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true).
    { rewrite <- (u_pa_upt_entry_walk vpn ie va). exact Hpaal. }
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + (* HIT: stored entry is forced to be [upt_entry vpn ie] *)
        destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (upt_entry vpn ie)) = tlbvec).
        { apply vec64_update_same; [ pose proof (tlb_hash_range vpn); lia | exact Hvacc ]. }
        iApply (wp_instr_u_hit_data va vpn ie w ii ms_v tlbvec E Φ HN Hvacc Hchk0 HupdN
                  Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg").
        iIntros (σ Hpceq Hag Hpins) "Htlbc Hupt Hσ".
        rewrite <- Hfill_id in Hpins.
        iMod ("H" $! σ Hpceq Hag Hpins
                with "[Htlbc] Hupt Hσ") as (s_exec) "(%Hexe & Hσ' & Hcont)".
        { rewrite Hfill_id. iExact "Htlbc". }
        iModIntro. iExists s_exec. iFrame "Hσ'". iSplitR; [iPureIntro; exact Hexe |].
        iIntros "Hhs' Hpriv' Hms' Hpc' Hcfg'".
        iApply ("Hcont" with "Hhs' Hpriv' Hms' Hpc' Hcfg'").
      + (* colliding miss *)
        iApply (wp_instr_u_miss_data va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                  (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
    - (* empty miss *)
      iApply (wp_instr_u_miss_data va vpn ie w ii ms_v tlbvec E Φ HN Hsome
                (or_introl Hvacc)
                Hchk0 HupdN Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpc Hcode Hupt Hcfg H").
  Qed.



  (* ---- combined (hit+miss) arm: ustep_itype_u ---- *)
  Lemma ustep_itype_u (op : iop) (f : mword 64 -> mword 12 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact *)
    (forall (rs1' rd' : mword 5) (imm' : mword 12) s,
       exec (execute (ITYPE (imm', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            imm')))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this ITYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (ITYPE (imm, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u va vpn ie w (ITYPE (imm, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) imm))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) imm))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) imm))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) imm)]> g), (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_rtype_u ---- *)
  Lemma ustep_rtype_u (op : rop) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u va vpn ie w (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_utype_u ---- *)
  Lemma ustep_utype_u (op : uop) (V : mword 20 -> mstate -> mword 64) (v : mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 20) (rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rd' : mword 5) (imm' : mword 20) s,
       exec (execute (UTYPE (imm', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg (V imm' s)))) ->
    (forall s', register_lookup PC s'.(sregs) = va -> V imm s' = v) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op HV Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (UTYPE (imm, Regidx rd, op)) = false)
      by reflexivity.
    iApply (wp_instr_u va vpn ie w (UTYPE (imm, Regidx rd, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* PC is untouched by the nextPC tick, so [V] evaluates to [v] *)
    assert (HpcX : register_lookup PC
              (set_reg σ nextPC (add_vec_int va 4)).(sregs) = va).
    { unfold set_reg; cbn [sregs]. tmig. exact Hpceq. }
    pose proof (HV (set_reg σ nextPC (add_vec_int va 4)) HpcX) as Hv.
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hv in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg v]> g), (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_shiftiop_u ---- *)
  Lemma ustep_shiftiop_u (op : sop) (f : mword 64 -> mword 6 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (shamt : mword 6) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rs1' rd' : mword 5) (shamt' : mword 6) s,
       exec (execute (SHIFTIOP (shamt', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            shamt')))) ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
                       = false) by reflexivity.
    iApply (wp_instr_u va vpn ie w (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) shamt))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) shamt))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) shamt))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd shamt (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) shamt))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) shamt)]> g), (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- combined (hit+miss) arm: ustep_nop_u ---- *)
  Lemma ustep_nop_u (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_nop Hnlpad Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_u va vpn ie w ii
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    iModIntro.
    iExists s1.
    iSplitR; [iPureIntro; exact (Hexec_nop s1) |].
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4), g, (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hgpr Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iFrame "Hpc' Hnpc".
  Qed.


  (* ---- combined (hit+miss) generic two-source arm: ustep_rtype2_u ---- *)
  Lemma ustep_rtype2_u (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (mk2 rs2' rs1' rd')) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    is_lpad_instruction (mk2 rs2 rs1 rd) = false ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (mk2 rs2 rs1 rd, s0)) ->
    uint rd <> 0 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hnlpad Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    iApply (wp_instr_u va vpn ie w (mk2 rs2 rs1 rd)
              ms_v tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hupt Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hupt' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt' Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact (upt_tlb_ok_fill spec tlbvec vpn ie Hsome Hok) |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpUserComputeMiss.
