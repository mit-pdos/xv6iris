(* TrampStepPt.v -- the S-mode TRAMPOLINE-page fetch and step engine over
   an ABSTRACT translation invariant.  Both page tables map the trampoline
   va to the kernel-text trampoline page ([pte_tramp]); the kernel
   [tlb_inv_pt] and the user [utlb_inv_pt] instantiate [INV]/[Habs] below,
   giving the two phases of the userret/uservec paths one shared fetch. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt TrampPt.
Require Import SmodeCore SmodeCorePt KptTree UptTree PtFetchGen.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section TrampFetchPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.
  Variable INV : iProp Σ.
  Variable Habs : forall (va pa : mword 64) (σ : mstate),
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ INV ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      ⌜ pmpAddrMatchType_encdec_backwards
          (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ⌝ ∗
      ⌜ zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ⌝ ∗
      ⌜ (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ INV.

  Lemma tramp_fetch_pt (σ : mstate) (pc pa : mword 64) (r : FetchResult) :
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    (* va/pa geometry ([vm_compute] at each concrete trampoline pc) *)
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
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr pc) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    mstate_interp σ -∗
    INV -∗
    instr_bytes pa r ==∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      INV.
  Proof.
    intros Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
           Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al.
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
        iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iMod (Habs pc pa σ Hcanon Hvpn Hident Lmisa Lmenv Lhtif Lpriv LSXL Lpma
                with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %H1A & %H1ord & %H1X & %H1cov & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pa 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s1)).
        { apply (exec_fetch_F_Base_4_S_gen_pa pc pa w σ s1 region Lpc Hal Htr1).
          - exact H1A.
          - exact H1ord.
          - exact (ram_fetch_pmp pa (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram3 H1cov).
          - exact H1X.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)).
            exact Hmatch0.
          - apply Hpa4al. reflexivity.
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
        destruct (align2_not4_facts pc Hva2 Hal) as (_ & Hbit0 & Hbit1).
        pose proof Hpa2al as Halignl0.
        pose proof Hpa2al2 as Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pa 2) j = pa_add pa (2 + j)).
        { intros j _. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜addr_is_ram pa⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hraml1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iAssert (⌜addr_is_ram (add_vec_int pa 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb2") as %Hr2. iPureIntro.
          unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pa 2) 1)).
        { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3. }
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl.
        pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch.
        pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (Lpma pa 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Lpma (add_vec_int pa 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        (* --- low chunk: σ -> s1 --- *)
        iMod (Habs pc pa σ Hcanon Hvpn Hident Lmisa Lmenv Lhtif Lpriv LSXL Lpma
                with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %H1A & %H1ord & %H1X & %H1cov & Hreg & Hmem & Hinv)".
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
                   s1.(mem) !! (pa_add pa j)
                   = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)⌝)%I as %HblS1.
        { iIntros (j Hj). rewrite nth_byte_subrange_lo; [| exact Hj].
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        (* --- high chunk: s1 -> s2 --- *)
        iMod (Habs (add_vec_int pc 2) (add_vec_int pa 2) s1 Hcanon2 Hvpn2 Hident2
                L1misa L1menv L1htif L1priv L1SXL L1pma
                with "Hreg Hmem Hinv")
          as (s2) "(%Htr2 & %Hmdev2 & %Hsh2 & %H2A & %H2ord & %H2X & %H2cov & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh2) as Hpres2.
        assert (Hpres12 : forall rr, register_beq rr tlb = false ->
                  register_lookup rr s2.(sregs) = register_lookup rr σ.(sregs)).
        { intros rr Hrr. rewrite (Hpres2 rr Hrr). exact (Hpres1 rr Hrr). }
        (* high-halfword byte facts at s2 *)
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   s2.(mem) !! (pa_add (add_vec_int pa 2) j)
                   = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)⌝)%I as %HbhS2.
        { iIntros (j Hj). rewrite nth_byte_subrange_hi; [| exact Hj].
          rewrite (Haddr j Hj).
          iDestruct (big_sepL_lookup _ _ (2 + j)%nat (2 + j)%nat with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        (* the s1/s2 PMP facts for the two instruction reads *)
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s2)).
        { apply (exec_fetch_F_Base_2_S_gen_pa pc pa w σ s1 s2 regl regh
                   Lpc L1pc HmisaC Hbit0 Hbit1 Hal Htr1 Htr2).
          - exact H1A.
          - exact H1ord.
          - exact (ram_fetch_pmp pa (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hraml Hraml1 H1cov).
          - exact H1X.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hml0.
          - exact Halignl0.
          - exact Hxl.
          - apply within_clint_false; [exact Hncl | lia].
          - apply within_sig_false; [exact Hnsl | lia].
          - apply within_htif_false. exact L1htif.
          - apply addr_is_ram_not_dev. exact Hraml.
          - exact HblS1.
          - exact L1priv.
          - exact H2A.
          - exact H2ord.
          - exact (ram_fetch_pmp (add_vec_int pa 2) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hramh Hramh1 H2cov).
          - exact H2X.
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
        iEval (rewrite Hpa4va4) in "Hbytes".
        iDestruct "Hbytes" as (w) "[%Hsub #Hbytes]".
        iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iMod (Habs pc pa σ Hcanon Hvpn Hident Lmisa Lmenv Lhtif Lpriv LSXL Lpma
                with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %H1A & %H1ord & %H1X & %H1cov & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pa 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { rewrite <- Hsub.
          apply (exec_fetch_RVC_4_S_gen_pa pc pa w σ s1 region Lpc Hal Htr1).
          - exact H1A.
          - exact H1ord.
          - exact (ram_fetch_pmp pa (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram3 H1cov).
          - exact H1X.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - apply Hpa4al. reflexivity.
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
        iEval (rewrite Hpa4va4) in "Hbytes".
        iDestruct "Hbytes" as "#Hbytes".
        destruct (align2_not4_facts pc Hva2 Hal) as (_ & Hbit0 & Hbit1).
        pose proof Hpa2al as Halignl0.
        iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iMod (Habs pc pa σ Hcanon Hvpn Hident Lmisa Lmenv Lhtif Lpriv LSXL Lpma
                with "Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %H1A & %H1ord & %H1X & %H1cov & Hreg & Hmem & Hinv)".
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   s1.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Lpma pa 2) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { apply (exec_fetch_RVC_2_S_gen_pa pc pa h σ s1 region Lpc HmisaC
                   Hbit0 Hbit1 Hal Htr1).
          - exact H1A.
          - exact H1ord.
          - exact (ram_fetch_pmp pa (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram Hram1 H1cov).
          - exact H1X.
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


  (* the trampoline-page STEP ENGINE over [INV]: one S-mode instruction at
     virtual [pc] whose bytes live at physical [pa] on the trampoline page.
     The invariant is threaded WHOLE into the σ-callback. *)
  Lemma wp_instr_tramp_pt Φ
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
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
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr pc) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    INV -∗
    PC ↦ᵣ pc -∗
    instr pa is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       INV -∗
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
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
             Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
             Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
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
    iMod (tramp_fetch_pt σ pc pa r
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
            Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al
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

End TrampFetchPt.

Section TrampFetchInst.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the KERNEL instance: [tlb_inv_pt kroot] absorbs the trampoline fetch
     (the kernel table maps the trampoline too). *)
  Lemma ktramp_fetch_habs (root_ppn : mword 44) :
    forall (va pa : mword 64) (σ : mstate),
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      ⌜ pmpAddrMatchType_encdec_backwards
          (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ⌝ ∗
      ⌜ zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ⌝ ∗
      ⌜ (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros va pa σ Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "Hri Hgh Hinv".
    iMod (tlb_inv_pt_translateAddr_tramp_fetch root_ppn va pa σ
            Hvpn Hcanon Hid Lmisa Lmenv Lhtif Lpriv LSXL
            (exec_effectivePrivilege_fetch _ _ σ)
            (exec_is_shadow_stack_fetch σ)
            Lpma with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct "Hinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc0") as %Lc.
    iDestruct (reg_valid_dq with "Hri Hpa0") as %La.
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htr |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsh |].
    iSplit; [iPureIntro; rewrite Lc; exact HA |].
    iSplit; [iPureIntro; rewrite La; exact Hord |].
    iSplit; [iPureIntro; rewrite Lc; exact HX |].
    iSplit; [iPureIntro; rewrite La; exact Hcov |].
    iFrame "Hri Hgh".
    iApply (tlb_inv_pt_intro root_ppn satp1 tlbvec1 t1
              Hmode Hasid Hppn Htlbok Hspec Hpmawimpl with "Hsatp Htlb Ht").
    iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
              HA Hord Hpmarimpl HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

  (* the USER instance: [utlb_inv_pt uroot tfp um] absorbs the same fetch. *)
  Lemma utramp_fetch_habs (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
    forall (va pa : mword 64) (σ : mstate),
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    svpn_of va = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      ⌜ pmpAddrMatchType_encdec_backwards
          (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ⌝ ∗
      ⌜ zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ⌝ ∗
      ⌜ (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros va pa σ Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "Hri Hgh Hinv".
    iMod (utlb_inv_pt_translateAddr_tramp_fetch uroot tfp um va pa σ
            Hvpn Hcanon Hid Lmisa Lmenv Lhtif Lpriv LSXL
            (exec_effectivePrivilege_fetch _ _ σ)
            (exec_is_shadow_stack_fetch σ)
            Lpma with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct "Hinv" as (usatp tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc0") as %Lc.
    iDestruct (reg_valid_dq with "Hri Hpa0") as %La.
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htr |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsh |].
    iSplit; [iPureIntro; rewrite Lc; exact HA |].
    iSplit; [iPureIntro; rewrite La; exact Hord |].
    iSplit; [iPureIntro; rewrite Lc; exact HX |].
    iSplit; [iPureIntro; rewrite La; exact Hcov |].
    iFrame "Hri Hgh".
    iApply (utlb_inv_pt_intro uroot tfp um usatp tlbvec1 t1
              Hmode Hasid Hppn Htlbok Hspec Hwf Hpmawimpl with "Hsatp Htlb Ht").
    iApply (pmp_config_intro uroot pmpcfg0 pmpaddr00
              HA Hord Hpmarimpl HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

  (* the two instantiated trampoline fetches *)
  Definition ktramp_fetch_pt (root_ppn : mword 44) :=
    tramp_fetch_pt (tlb_inv_pt root_ppn) (ktramp_fetch_habs root_ppn).
  Definition utramp_fetch_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :=
    tramp_fetch_pt (utlb_inv_pt uroot tfp um) (utramp_fetch_habs uroot tfp um).

  (* ... and the two instantiated step engines: the KERNEL-phase trampoline
     step (userret's first two instructions) and the USER-phase step (the
     rest of userret / uservec). *)
  Definition wp_instr_ktramp_pt (root_ppn : mword 44) :=
    wp_instr_tramp_pt (tlb_inv_pt root_ppn) (ktramp_fetch_habs root_ppn).
  Definition wp_instr_u_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :=
    wp_instr_tramp_pt (utlb_inv_pt uroot tfp um) (utramp_fetch_habs uroot tfp um).

End TrampFetchInst.
