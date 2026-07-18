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
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import TrampPt.
Require Import SmodeCore.
Require Import KptTree.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import UserMem.
Require Import UserFetch.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Pure-fact extraction: the PMP entry-0 facts, borrowed from the       *)
(*    bundle (used both before the translation move and, transported,     *)
(*    after it).                                                           *)
(* ===================================================================== *)

Section UserFetchPtFacts.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma utlb_inv_pt_pmp_facts (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (σ : mstate) :
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜(pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
      zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)%type⌝.
  Proof.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro.
    rewrite Hpcv Hpav. auto 8.
  Qed.

End UserFetchPtFacts.

(* ===================================================================== *)
(* §2 Sourcing the fetched word from the owned data pages.                 *)
(* ===================================================================== *)

Section UserFetchPtWord.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

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
    iDestruct (mem_valid with "Hmem Hb0'") as %Hp0.
    iDestruct (mem_ram with "Hb0'") as %Hram0.
    iDestruct ("Hrest" with "Hb0'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb1 with "Hbytes") as "[Hb1' Hrest]".
    iDestruct (mem_valid with "Hmem Hb1'") as %Hp1.
    iDestruct ("Hrest" with "Hb1'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb2 with "Hbytes") as "[Hb2' Hrest]".
    iDestruct (mem_valid with "Hmem Hb2'") as %Hp2.
    iDestruct ("Hrest" with "Hb2'") as "Hbytes".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hb3 with "Hbytes") as "[Hb3' Hrest]".
    iDestruct (mem_valid with "Hmem Hb3'") as %Hp3.
    iDestruct (mem_ram with "Hb3'") as %Hram3.
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
    destruct (Hall pa 4) as (region & Hpmam & Hexec & _).
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
  Context `{CID : CpuId}.

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
