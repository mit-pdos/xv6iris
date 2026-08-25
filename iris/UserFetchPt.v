(* UserFetchPt.v -- the U-mode instruction-fetch composer over the ptree
   user table (UserPtTree.v): the successor of UserFetch §6's
   [upt_fetch_instr].

   At a user-mapped, fetch-permitted, 4-aligned canonical pc the fetch
   succeeds with SOME word sourced from the owned data pages
   ([udata_own]), and the state moves in one of the ABSORBED ways
   (unchanged TLB hit / TLB fill / Svadu A-D write-back into the owned
   tree) -- the composer hands back the moved state's interpretations
   with the bundle re-established, so the caller never sees hit-vs-miss
   or the write-back.  (Under ADUE the old "A/D preset,
   update_PTE_Bits = None" premises are GONE.)

   Layout: §1 pure-fact extraction helpers over the bundle; §2 the word
   and mem_read facts from the data pages; §3 the composer.             *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import CommonWalk.
Require Import SmodeCore.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import UserMem.
Require Import UserFetch.
Require Import UserMemPt.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* (the PMP-fact extraction helper [utlb_inv_pt_pmp_facts] lives in
   UserPtTree.v §4b -- shared with the data-memory layer)                 *)

(* ===================================================================== *)
(* §2 Sourcing the fetched word from the owned data pages.                 *)
(* ===================================================================== *)

Section UserFetchPtWord.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the 4 bytes at the translated pc exist in the data pages (with SOME
     values -- contents are existential) and the window is RAM.  Borrowed
     at the POST-translation state: an A/D write-back only touches
     tree-owned slots, disjoint from the data pages by separation. *)
  Lemma udata_fetch_word (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists iw : mword 32,
       (forall j : nat, (N.of_nat j < 4)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte iw j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) 3)⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < 4)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window _ _ _ Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (H0 : is_Some (dm !! pa_add pa 0)) by (apply elem_of_dom, Hin; lia).
    assert (H1 : is_Some (dm !! pa_add pa 1)) by (apply elem_of_dom, Hin; lia).
    assert (H2 : is_Some (dm !! pa_add pa 2)) by (apply elem_of_dom, Hin; lia).
    assert (H3 : is_Some (dm !! pa_add pa 3)) by (apply elem_of_dom, Hin; lia).
    destruct H0 as [b0 Hb0]. destruct H1 as [b1 Hb1].
    destruct H2 as [b2 Hb2]. destruct H3 as [b3 Hb3].
    set (iw := Z_to_bv 32 (assemble_bytes [b0; b1; b2; b3]) : mword 32).
    assert (Hw : forall j : nat, (j < 4)%nat ->
              nth_byte iw j = [b0; b1; b2; b3] !!! j).
    { intros j Hj. apply nth_byte_assemble4; [reflexivity | exact Hj]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb0 with "Hbytes") as "[Hb0' Hrest]".
    iDestruct (phys_valid with "Hmem Hb0'") as %Hp0.
    iDestruct (phys_ram with "Hb0'") as %Hram0.
    iDestruct ("Hrest" with "Hb0'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb1 with "Hbytes") as "[Hb1' Hrest]".
    iDestruct (phys_valid with "Hmem Hb1'") as %Hp1.
    iDestruct ("Hrest" with "Hb1'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb2 with "Hbytes") as "[Hb2' Hrest]".
    iDestruct (phys_valid with "Hmem Hb2'") as %Hp2.
    iDestruct ("Hrest" with "Hb2'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb3 with "Hbytes") as "[Hb3' Hrest]".
    iDestruct (phys_valid with "Hmem Hb3'") as %Hp3.
    iDestruct (phys_ram with "Hb3'") as %Hram3.
    iDestruct ("Hrest" with "Hb3'") as "Hbytes".
    iPureIntro.
    exists iw.
    split; [ | split; [ rewrite <- (pa_add_0 pa); exact Hram0 | exact Hram3 ] ].
    intros j HjN.
    assert (Hj : (j < 4)%nat) by lia.
    rewrite Hw; [ | exact Hj ].
    destruct j as [ | [ | [ | [ | ] ] ] ]; try lia; cbn [lookup_total list_lookup_total];
      [ exact Hp0 | exact Hp1 | exact Hp2 | exact Hp3 ].
  Qed.

  (* the COMPLETE physical fetch read at the (possibly moved) state *)
  Lemma udata_fetch_mem_read (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ->
    register_lookup cur_privilege σ'.(sregs) = User ->
    register_lookup htif_tohost_base σ'.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions σ'.(sregs)) ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists iw : mword 32,
       exec (mem_read (InstructionFetch tt) PBMT_PMA
               (Physaddr (u_walk_pa w va)) 4 false false false) σ'
         = Some (Ok iw, σ')⌝.
  Proof.
    iIntros (Hl Hcov Hal HA Hord HX Hcovp Lpriv Lhtif Hall) "Hmem Hdata".
    iDestruct (udata_fetch_word um data w va σ' Hl Hcov Hal with "Hmem Hdata")
      as %(iw & Hbytes & Hram0 & Hram3).
    iPureIntro.
    set (pa := u_walk_pa w va) in *.
    destruct (pma_all_ram Hall pa 4
               (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hpmam & Hexec & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { exact (ram_fetch_pmp pa _ 4 3 ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram0 Hram3 Hcovp). }
    assert (Halp : is_aligned_paddr (Physaddr pa) 4 = true).
    { exact (pa4_aligned _ va Hal). }
    exists iw.
    exact (exec_mem_read_fetch_4_U PBMT_PMA pa region iw σ'
             HA Hord Hrange HX Hpmam Halp Hexec
             (within_clint_false pa 4 σ' Hnc ltac:(lia))
             (within_sig_false pa 4 σ' Hns ltac:(lia))
             (within_htif_false pa 4 σ' Lhtif)
             (addr_is_ram_not_dev _ Hram0)
             Hbytes Lpriv).
  Qed.

End UserFetchPtWord.

(* ===================================================================== *)
(* §3 THE FETCH-SUCCESS COMPOSER over the bundle.                          *)
(* ===================================================================== *)

Section UserFetchPtOk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma user_pt_fetch_instr (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (InstructionFetch tt) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    register_lookup PC σ.(sregs) = va ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (iw : mword 32) (σ' : mstate),
      ⌜exec (fetch tt) σ
        = Some ((if isRVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                 then F_RVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                 else F_Base (autocast (T := mword) iw)), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Lpc Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_fetch_mem_read um data w va σ' Hl Hcov Hal
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp))
                 (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
                 (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
                 with "Hgh Hdata") as %(iw & Hmr).
    iModIntro.
    iExists iw, σ'.
    iSplit; [ iPureIntro;
              exact (exec_fetch_ok_4 σ σ' va (u_walk_pa w va) iw Lpc Hal Htr Hmr) | ].
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserFetchPtOk.

(* ===================================================================== *)
(* §4 THE FETCH-FAULT COMPOSER: at a 4-aligned pc whose translation        *)
(*    faults (non-canonical / unmapped / fetch-denied), the fetch raises  *)
(*    E_Fetch_Page_Fault with the state UNCHANGED, the bundle merely      *)
(*    borrowed.  (The odd-pc E_Fetch_Addr_Align case never translates --  *)
(*    [exec_fetch_align_fault], UserFetch §2, is PT-free.)                *)
(* ===================================================================== *)

(* the fetch instance of the access-generic fault flavor (UserPtTree §5b) *)
Definition u_fetch_fault_flavor (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  u_fault_flavor (InstructionFetch tt) tfp um va.

Section UserFetchPtFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma user_pt_fetch_fault (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (σ : mstate) :
    u_fetch_fault_flavor tfp um va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    register_lookup PC σ.(sregs) = va ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (fetch tt) σ = Some (F_Error (E_Fetch_Page_Fault tt, va), σ)⌝.
  Proof.
    intros Hflavor Hal Lpc Hhtif Hcp HSXL Hall.
    iIntros "Hri Hgh Hinv".
    iAssert (⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
              = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr.
    { iApply (utlb_inv_pt_translateAddr_u_fault (InstructionFetch tt)
                uroot tfp um va (E_Fetch_Page_Fault tt) σ
                Hflavor Hhtif Hcp HSXL
                (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
                (exec_is_shadow_stack_fetch σ) Hall
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                with "Hri Hgh Hinv"). }
    iPureIntro.
    exact (exec_fetch_fault_4 σ va Lpc (E_Fetch_Page_Fault tt) Hal Htr).
  Qed.

End UserFetchPtFault.

(* ===================================================================== *)
(* §5 The 2-ALIGNED (split) fetch composer: at a 2-aligned-not-4-aligned  *)
(*    pc, the low halfword comes off the pc's page; if it is not RVC the  *)
(*    high halfword translates INDEPENDENTLY at pc+2 -- possibly another  *)
(*    page (the straddle) -- through the same absorption.  The conclusion *)
(*    has the SAME if-isRVC shape as the 4-aligned composer, so the       *)
(*    classification treats both alignments uniformly; the sregs shape    *)
(*    after up to two absorbed moves is reported as the lookup-transport  *)
(*    property (all non-tlb registers unchanged).                         *)
(* ===================================================================== *)

Section UserFetchPtSplit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma user_pt_fetch_instr_2 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w wh va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (InstructionFetch tt) w ->
    um !! svpn_of (add_vec_int va 2) = Some wh ->
    uleaf_ok (InstructionFetch tt) wh ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    register_lookup PC σ.(sregs) = va ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (iw : mword 32) (σ' : mstate),
      ⌜exec (fetch tt) σ
        = Some ((if isRVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                 then F_RVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
                 else F_Base (autocast (T := mword) iw)), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hlh Hchkh Hcov Hal2 Hal2h Hbit0 Hbit1 Hnal4 Lpc Hcanon Hcanonh
           Hmisa Hmenv Hhtif Hcp HSXL Hall.
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    (* first halfword: translate at va (absorbed) *)
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ1) "(%Htr1 & %Hmdev1 & %Hsregs1 & Hri & Hgh & Hinv)".
    assert (Tr1 : forall r : register, register_beq r tlb = false ->
              register_lookup r σ1.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs1 as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    (* the low halfword out of the data pages, read at σ1 *)
    iDestruct (udata_read_word_g 2 ltac:(lia) ltac:(exists 2048; reflexivity)
                 um data w va σ1 Hl Hcov Hal2 with "Hgh Hdata")
      as %(ilo & Hbytes1 & Hram1a & Hram1b).
    assert (Hmr1 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w va)) 2 false false false) σ1
                   = Some (Ok ilo, σ1)).
    { set (pa := u_walk_pa w va) in *.
      destruct (pma_all_ram (ltac:(rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ1.(sregs))) pa 2
                (pma_access_ram _ _ _ Hram1a Hram1b (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
        as (region & Hpmam & Hexec & _).
      pose proof (addr_is_ram_not_in_clint _ Hram1a) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram1a) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ1.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 2 1 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram1a Hram1b Hcovp). }
      exact (exec_mem_read_fetch_2_U PBMT_PMA pa region ilo σ1
               (ltac:(rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX))
               Hpmam
               (pa_aligned_div _ va 2 ltac:(lia) ltac:(exists 2048; reflexivity) Hal2)
               Hexec
               (within_clint_false pa 2 σ1 Hnc ltac:(lia))
               (within_sig_false pa 2 σ1 Hns ltac:(lia))
               (within_htif_false pa 2 σ1
                  (ltac:(rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram1a)
               Hbytes1
               (ltac:(rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    destruct (isRVC ilo) eqn:Hrvc.
    - (* RVC: done at σ1 *)
      iModIntro.
      iExists (zero_extend' 32 ilo), σ1.
      assert (Hsub : subrange_vec_dec (autocast (T := mword)
                       (zero_extend' 32 ilo) : mword 32) 15 0 = ilo).
      { rewrite autocast_mword_id. apply subrange16_zext32. }
      iSplit; [ iPureIntro | ].
      { rewrite Hsub. rewrite Hrvc.
        exact (exec_fetch_rvc_2 σ σ1 va (u_walk_pa w va)
                 Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1 Hrvc). }
      iSplit; [ iPureIntro; exact Hmdev1 | ].
      iSplit; [ iPureIntro; exact Tr1 | ].
      iFrame "Hri Hgh Hinv Hdata".
    - (* not RVC: the high halfword at va+2, through a SECOND absorption *)
      iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt) uroot tfp um wh
              (add_vec_int va 2) (u_walk_pa wh (add_vec_int va 2)) σ1 Hlh Hchkh Hcanonh eq_refl
              (ltac:(rewrite (Tr1 misa ltac:(vm_compute; reflexivity)); exact Hmisa))
              (ltac:(rewrite (Tr1 menvcfg ltac:(vm_compute; reflexivity)); exact Hmenv))
              (ltac:(rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
              (ltac:(rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
              (ltac:(rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact HSXL))
              (exec_effectivePrivilege_fetch (register_lookup mstatus σ1.(sregs)) User σ1)
              (exec_is_shadow_stack_fetch σ1)
              (ltac:(rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
              with "Hri Hgh Hinv")
        as (σ2) "(%Htr2 & %Hmdev2 & %Hsregs2 & Hri & Hgh & Hinv)".
      assert (Tr2 : forall r : register, register_beq r tlb = false ->
                register_lookup r σ2.(sregs) = register_lookup r σ1.(sregs)).
      { intros r Hne.
        destruct Hsregs2 as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iDestruct (udata_read_word_g 2 ltac:(lia) ltac:(exists 2048; reflexivity)
                   um data wh (add_vec_int va 2) σ2 Hlh Hcov Hal2h with "Hgh Hdata")
        as %(ihi & Hbytes2 & Hram2a & Hram2b).
      assert (Hmr2 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                       (Physaddr (u_walk_pa wh (add_vec_int va 2))) 2 false false false) σ2
                     = Some (Ok ihi, σ2)).
      { set (pah := u_walk_pa wh (add_vec_int va 2)) in *.
        destruct (pma_all_ram (ltac:(rewrite (Tr2 pma_regions ltac:(vm_compute; reflexivity))
                                 (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ2.(sregs))) pah 2
                  (pma_access_ram _ _ _ Hram2a Hram2b (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hpmam & Hexec & _).
        pose proof (addr_is_ram_not_in_clint _ Hram2a) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram2a) as Hns.
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ2.(sregs)) 0)) 4)
                  (uint pah) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite (Tr2 pmpaddr_n ltac:(vm_compute; reflexivity))
                  (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pah _ 2 1 ltac:(lia) ltac:(lia)
                   ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hram2a Hram2b Hcovp). }
        exact (exec_mem_read_fetch_2_U PBMT_PMA pah region ihi σ2
                 (ltac:(rewrite (Tr2 pmpcfg_n ltac:(vm_compute; reflexivity))
                                (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr2 pmpaddr_n ltac:(vm_compute; reflexivity))
                                (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr2 pmpcfg_n ltac:(vm_compute; reflexivity))
                                (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX))
                 Hpmam
                 (pa_aligned_div _ (add_vec_int va 2) 2 ltac:(lia)
                    ltac:(exists 2048; reflexivity) Hal2h)
                 Hexec
                 (within_clint_false pah 2 σ2 Hnc ltac:(lia))
                 (within_sig_false pah 2 σ2 Hns ltac:(lia))
                 (within_htif_false pah 2 σ2
                    (ltac:(rewrite (Tr2 htif_tohost_base ltac:(vm_compute; reflexivity))
                                   (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
                 (addr_is_ram_not_dev _ Hram2a)
                 Hbytes2
                 (ltac:(rewrite (Tr2 cur_privilege ltac:(vm_compute; reflexivity))
                                (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
      iModIntro.
      iExists (concat_vec ihi ilo), σ2.
      assert (Hsub : subrange_vec_dec (autocast (T := mword)
                       (concat_vec ihi ilo) : mword 32) 15 0 = ilo).
      { rewrite autocast_mword_id. apply subrange16_concat16. }
      iSplit; [ iPureIntro | ].
      { rewrite Hsub. rewrite Hrvc. rewrite autocast_mword_id.
        exact (exec_fetch_base_2 σ σ1 va (u_walk_pa w va)
                 Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1 σ2
                 (u_walk_pa wh (add_vec_int va 2))
                 (eq_trans (Tr1 PC ltac:(vm_compute; reflexivity)) Lpc)
                 Hrvc ihi Htr2 Hmr2). }
      iSplit; [ iPureIntro; rewrite Hmdev2; exact Hmdev1 | ].
      iSplit; [ iPureIntro;
                intros r Hne; rewrite (Tr2 r Hne); exact (Tr1 r Hne) | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserFetchPtSplit.

(* ===================================================================== *)
(* §6 The 2-ALIGNED fetch-FAULT composers.  The FIRST halfword's fault    *)
(*    (flavored at pc) leaves the state untouched, the bundle borrowed.   *)
(*    The SECOND halfword's fault (flavored at pc+2) can only fire after  *)
(*    the low halfword was fetched and found non-compressed -- since the  *)
(*    low halfword's bits are EXISTENTIAL, the conclusion is inherently   *)
(*    the RVC-success / page-fault disjunction, after ONE absorbed move.  *)
(* ===================================================================== *)

Section UserFetchPtSplitFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma user_pt_fetch_fault_2_first (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (σ : mstate) :
    u_fetch_fault_flavor tfp um va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    register_lookup PC σ.(sregs) = va ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (fetch tt) σ = Some (F_Error (E_Fetch_Page_Fault tt, va), σ)⌝.
  Proof.
    intros Hflavor Hbit0 Hbit1 Hnal4 Lpc Hmisa Hhtif Hcp HSXL Hall.
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "Hri Hgh Hinv".
    iAssert (⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
              = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr.
    { iApply (utlb_inv_pt_translateAddr_u_fault (InstructionFetch tt)
                uroot tfp um va (E_Fetch_Page_Fault tt) σ
                Hflavor Hhtif Hcp HSXL
                (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
                (exec_is_shadow_stack_fetch σ) Hall
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                with "Hri Hgh Hinv"). }
    iPureIntro.
    exact (exec_fetch_fault_2_first σ va Lpc HmisaC Hbit0 Hbit1 Hnal4
             (E_Fetch_Page_Fault tt) Htr).
  Qed.

  Lemma user_pt_fetch_fault_2_second (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (InstructionFetch tt) w ->
    u_fetch_fault_flavor tfp um (add_vec_int va 2) ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    register_lookup PC σ.(sregs) = va ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ' : mstate,
      ⌜(exists h : mword 16, isRVC h = true /\
          exec (fetch tt) σ = Some (F_RVC h, σ'))
       \/ exec (fetch tt) σ
          = Some (F_Error (E_Fetch_Page_Fault tt, add_vec_int va 2), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hflavor Hcov Hal2 Hbit0 Hbit1 Hnal4 Lpc Hcanon
           Hmisa Hmenv Hhtif Hcp HSXL Hall.
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ1) "(%Htr1 & %Hmdev1 & %Hsregs1 & Hri & Hgh & Hinv)".
    assert (Tr1 : forall r : register, register_beq r tlb = false ->
              register_lookup r σ1.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs1 as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 2 ltac:(lia) ltac:(exists 2048; reflexivity)
                 um data w va σ1 Hl Hcov Hal2 with "Hgh Hdata")
      as %(ilo & Hbytes1 & Hram1a & Hram1b).
    assert (Hmr1 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w va)) 2 false false false) σ1
                   = Some (Ok ilo, σ1)).
    { set (pa := u_walk_pa w va) in *.
      destruct (pma_all_ram (ltac:(rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ1.(sregs))) pa 2
                (pma_access_ram _ _ _ Hram1a Hram1b (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
        as (region & Hpmam & Hexec & _).
      pose proof (addr_is_ram_not_in_clint _ Hram1a) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram1a) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ1.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 2 1 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram1a Hram1b Hcovp). }
      exact (exec_mem_read_fetch_2_U PBMT_PMA pa region ilo σ1
               (ltac:(rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX))
               Hpmam
               (pa_aligned_div _ va 2 ltac:(lia) ltac:(exists 2048; reflexivity) Hal2)
               Hexec
               (within_clint_false pa 2 σ1 Hnc ltac:(lia))
               (within_sig_false pa 2 σ1 Hns ltac:(lia))
               (within_htif_false pa 2 σ1
                  (ltac:(rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram1a)
               Hbytes1
               (ltac:(rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    destruct (isRVC ilo) eqn:Hrvc.
    - (* the low halfword happens to be compressed: RVC success *)
      iModIntro. iExists σ1.
      iSplit; [ iPureIntro; left; exists ilo; split; [ exact Hrvc | ] | ].
      { exact (exec_fetch_rvc_2 σ σ1 va (u_walk_pa w va)
                 Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1 Hrvc). }
      iSplit; [ iPureIntro; exact Hmdev1 | ].
      iSplit; [ iPureIntro; exact Tr1 | ].
      iFrame "Hri Hgh Hinv Hdata".
    - (* not compressed: the second halfword's translation faults at σ1 *)
      iAssert (⌜exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) σ1
                = Some (Err (E_Fetch_Page_Fault tt, tt), σ1)⌝)%I as %Htr2.
      { iApply (utlb_inv_pt_translateAddr_u_fault (InstructionFetch tt)
                  uroot tfp um (add_vec_int va 2) (E_Fetch_Page_Fault tt) σ1
                  Hflavor
                  (ltac:(rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
                  (ltac:(rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                  (ltac:(rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact HSXL))
                  (exec_effectivePrivilege_fetch (register_lookup mstatus σ1.(sregs)) User σ1)
                  (exec_is_shadow_stack_fetch σ1)
                  (ltac:(rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
                  ltac:(unfold translationException; cbn match; apply exec_returnm)
                  ltac:(unfold translationException; cbn match; apply exec_returnm)
                  ltac:(unfold translationException; cbn match; apply exec_returnm)
                  with "Hri Hgh Hinv"). }
      iModIntro. iExists σ1.
      iSplit; [ iPureIntro; right | ].
      { exact (exec_fetch_fault_2_second σ σ1 va (u_walk_pa w va)
                 Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1
                 (eq_trans (Tr1 PC ltac:(vm_compute; reflexivity)) Lpc)
                 Hrvc (E_Fetch_Page_Fault tt) Htr2). }
      iSplit; [ iPureIntro; exact Hmdev1 | ].
      iSplit; [ iPureIntro; exact Tr1 | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserFetchPtSplitFault.
