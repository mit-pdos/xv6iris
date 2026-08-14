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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import KMap.
Require Import KptExecMap.
Require Import SmodeCore SmodeCorePt KptTree UptTree PtFetchGen.
Require Import PtTree PtAdBits PtTreeAdue KptGhost KptShare.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section TrampFetchPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
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
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ INV ={⊤ ∖ ↑minstretN}=∗
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
    (* PHYSICAL-storage premise (NOT about the fetched va): the trampoline
       page IS kernel text (ppn 0x80006 < etext), so each byte's PHYSICAL
       location [pa_add pa j] is a text vpn.  Dischargeable by [vm_compute]
       at the concrete-[pa] call sites; the va's non-identity translation
       stays entirely inside [Habs]. *)
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pa j)) KP_rx) ->
    mstate_interp σ -∗
    INV -∗
    kmap_static_claims -∗
    instr_bytes pa r ={⊤ ∖ ↑minstretN}=∗
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
           Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al Hstat.
    iIntros "[Hreg [Hmem Hdev]] Hinv #Hbundle Hbytes".
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
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia)) with "Hbundle Hb0") as "Hp0".
          iDestruct (phys_ram with "Hp0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 3%nat ltac:(lia)) with "Hbundle Hb3") as "Hp3".
          iDestruct (phys_ram with "Hp3") as %Hr3. iPureIntro.
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
          iDestruct (text_ident_phys _ _ _ (Hstat j ltac:(lia)) with "Hbundle Hbj") as "Hpj".
          iDestruct (phys_valid with "Hmem Hpj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (pma_all_ram Lpma pa 4
                   (pma_access_ram _ _ _ Hram Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
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
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia)) with "Hbundle Hb0") as "Hp0".
          iDestruct (phys_ram with "Hp0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hraml1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 1%nat ltac:(lia)) with "Hbundle Hb1") as "Hp1".
          iDestruct (phys_ram with "Hp1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iAssert (⌜addr_is_ram (add_vec_int pa 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 2%nat ltac:(lia)) with "Hbundle Hb2") as "Hp2".
          iDestruct (phys_ram with "Hp2") as %Hr2. iPureIntro.
          unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 3%nat ltac:(lia)) with "Hbundle Hb3") as "Hp3".
          iDestruct (phys_ram with "Hp3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pa 2) 1)).
        { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3. }
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl.
        pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch.
        pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (pma_all_ram Lpma pa 2
                   (pma_access_ram _ _ _ Hraml Hraml1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (regl & Hml0 & Hxl & _ & _).
        destruct (pma_all_ram Lpma (add_vec_int pa 2) 2
                   (pma_access_ram _ _ _ Hramh Hramh1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (regh & Hmh0 & Hxh & _ & _).
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
          iDestruct (text_ident_phys _ _ _ (Hstat j ltac:(lia)) with "Hbundle Hbj") as "Hpj".
          iDestruct (phys_valid with "Hmem Hpj") as %Hmj. iPureIntro. exact Hmj. }
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
          iDestruct (text_ident_phys _ _ _ (Hstat (2 + j)%nat ltac:(lia)) with "Hbundle Hbj") as "Hpj".
          iDestruct (phys_valid with "Hmem Hpj") as %Hmj. iPureIntro. exact Hmj. }
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
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia)) with "Hbundle Hb0") as "Hp0".
          iDestruct (phys_ram with "Hp0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 3%nat ltac:(lia)) with "Hbundle Hb3") as "Hp3".
          iDestruct (phys_ram with "Hp3") as %Hr3. iPureIntro.
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
          iDestruct (text_ident_phys _ _ _ (Hstat j ltac:(lia)) with "Hbundle Hbj") as "Hpj".
          iDestruct (phys_valid with "Hmem Hpj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (pma_all_ram Lpma pa 4
                   (pma_access_ram _ _ _ Hram Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
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
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia)) with "Hbundle Hb0") as "Hp0".
          iDestruct (phys_ram with "Hp0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 1%nat ltac:(lia)) with "Hbundle Hb1") as "Hp1".
          iDestruct (phys_ram with "Hp1") as %Hr1. iPureIntro.
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
          iDestruct (text_ident_phys _ _ _ (Hstat j ltac:(lia)) with "Hbundle Hbj") as "Hpj".
          iDestruct (phys_valid with "Hmem Hpj") as %Hmj. iPureIntro. exact Hmj. }
        pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (pma_all_ram Lpma pa 2
                   (pma_access_ram _ _ _ Hram Hram1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
          as (region & Hmatch0 & Hexec0 & _ & _).
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
  Lemma wp_instr_tramp_pt
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
          ▷ WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
             Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
             Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor with "Hinv Hhs").
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
            (tramp_window_static pc pa Hident Hident2 Hpa2al)
            with "[$Hreg $Hmem] Htlbinv Hkmapb Hbytes")
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
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the KERNEL instance (stage C): the trampoline is an ordinary M entry
     [tramp_vpn ↦ (tramp_ppn, KP_rx)], so the fetch is absorbed by the
     GENERAL [tlb_inv_pt_translateAddr_at] fed the trampoline claim
     [kmap_at tramp_vpn tramp_ppn KP_rx].  The claim is persistent and rides
     inside [INV] (it is threaded up from the post-switch caller, which holds
     it after the kvminithart switch mints it). *)
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
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt root_ppn) ={⊤ ∖ ↑minstretN}=∗
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
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt root_ppn).
  Proof.
    intros va pa σ Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "Hri Hgh [#Hclaim Hinv]".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hclaimva".
    { rewrite Hvpn. iApply "Hclaim". }
    iMod (tlb_inv_pt_translateAddr_at (InstructionFetch tt) root_ppn va pa tramp_ppn KP_rx σ
            (fun a d mxr do_sum => kperm_variant_check_fetch tramp_ppn a d mxr do_sum)
            Hcanon Hid Lmisa Lmenv Lhtif Lpriv LSXL
            (exec_effectivePrivilege_fetch _ _ σ)
            (exec_is_shadow_stack_fetch σ)
            Lpma with "Hclaimva Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct "Hinv" as (satp1 tlbvec1 t1 M)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & HM & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
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
    iFrame "Hri Hgh Hclaim".
    iApply (tlb_inv_pt_intro root_ppn satp1 tlbvec1 t1 M
              Hmode Hasid Hppn Htlbok Hspec with "Hsatp Htlb HM Ht").
    iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
              HA Hord HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

  (* the SHARED-KERNEL instance: the mirror of [ktramp_fetch_habs] over the
     shared residue [KptShare.tlb_res_pt] instead of the exclusive
     [tlb_inv_pt] -- for kernel-side trampoline steps taken OUTSIDE the
     satp-switch window, once the window's own exit no longer reseals the
     exclusive invariant (TransPt.v's [tlb_inv_pt2_kcur]/[_kprev]).  Opening
     [kpt_inv] happens ENTIRELY inside this one call (mask [⊤], since
     nothing else is ever held open around a trampoline step), so [Habs]'s
     fixed [==∗] shape needs no change. *)
  Lemma ktramp_fetch_habs_share (root_ppn : mword 44) :
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
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_res_pt root_ppn) ={⊤ ∖ ↑minstretN}=∗
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
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_res_pt root_ppn).
  Proof.
    intros va pa σ Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "Hri Hgh [#Hclaim Hres]".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hclaimva".
    { rewrite Hvpn. iApply "Hclaim". }
    iDestruct (tlb_res_pt_open with "Hres") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & Hsnap & Hpmp & #Hkinv)".
    iDestruct "Hsnap" as (t0) "(%Htlbok0 & #Hlb0)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof (pma_allows_all_pte_write _ Lpma) as Hpmaw.
    pose proof (pma_allows_all_pte_read _ Lpma) as Hpmar.
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (HW' : eq_vec (_get_Pmpcfg_ent_W
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HW).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    assert (Htm : exec (translationMode Supervisor) σ = Some (Sv39, σ))
      by exact (exec_translationMode_S_sv39 satp0 σ LSXL Hsatpv Hmode).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    (* ---- open the shared table for THIS instruction only ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hclaimva") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan0.
    assert (Htlbok : tlb_ok_pt (mword_of_int 0) t tlbvec)
      by exact (tlb_ok_pt_canon (mword_of_int 0) t0 t tlbvec Hcan0 Htlbok0).
    pose proof Hspec as (Hbase & Hmapspec).
    pose proof (Hmapspec (svpn_of va)) as Hmapv. rewrite HMlk in Hmapv.
    destruct Hmapv as (p2 & p1 & a0 & d0 & Hmaps).
    assert (Hlf : pte_set_ad (kpt_leaf_pte_of (svpn_of va) (tramp_ppn, KP_rx)) a0 d0
                = pte_set_ad pte_tramp a0 d0)
      by (unfold kpt_leaf_pte_of; cbn [fst snd]; apply kperm_rx_tramp_variant).
    rewrite Hlf in Hmaps.
    iMod (ptree_translateAddr_own (InstructionFetch tt) Supervisor root_ppn t
            pte_tramp va pa satp0 tlbvec p2 p1 a0 d0 σ
            (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
            tramp_variant Hcanon Hout Hbase Hmaps Htlbok
            Lmisa Lmenv Lhtif Lpriv Htm
            (exec_effectivePrivilege_fetch _ _ σ)
            (exec_is_shadow_stack_fetch σ)
            Hsatpv Hppn Hasid Htlbv
            HA' Hord' HR' HW' Hcov' Hpmar Hpmaw
            with "Hri Hgh Htlb Ht")
      as (σ' t' tlbvec') "(%Htrans & %Hmdev & %Hsregs & %Htsh & %Htlbok' & Hri & Hgh & Htlb & Ht)".
    assert (Hcan' : ptree_canon t = ptree_canon t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [reflexivity |].
      rewrite <- (pte_set_ad_absorb pte_tramp a0 d0 a1 d1).
      symmetry.
      exact (ptree_canon_set_leaf t (svpn_of va) p2 p1
               (pte_set_ad pte_tramp a0 d0) a1 d1 Hmaps). }
    iDestruct (kpt_lb_canon t t' Hcan' with "Hlbt") as "#Hlb'".
    assert (Hspec' : kpt_tree_spec_gen root_ppn M t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [exact Hspec |].
      rewrite <- (pte_set_ad_absorb pte_tramp a0 d0 a1 d1).
      apply (kpt_tree_spec_gen_set_leaf root_ppn M t (svpn_of va) (tramp_ppn, KP_rx) p2 p1
               (pte_set_ad pte_tramp a0 d0) a1 d1 Hspec Hmaps HMlk).
      exists a0, d0. symmetry. exact Hlf. }
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists t', M. iFrame "Ht HM Hlb'". iPureIntro. exact Hspec'. }
    iAssert (pmp_config root_ppn) with "[Hpc Hpa]" as "Hpmp".
    { iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                HA Hord HX HW HR Hcov with "Hpc Hpa"). }
    iAssert (tlb_res_pt root_ppn) with "[Hsatp Htlb Hpmp]" as "Hres'".
    { iApply (tlb_res_pt_intro root_ppn satp0 tlbvec' t' Hmode Hasid Hppn Htlbok'
                with "Hsatp Htlb Hlb' Hpmp Hkinv"). }
    iDestruct (tlb_res_pt_grant_facts root_ppn σ' with "Hri Hres'") as %(HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htrans |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsregs |].
    iSplit; [iPureIntro; exact HA2 |].
    iSplit; [iPureIntro; exact Hord2 |].
    iSplit; [iPureIntro; exact HX2 |].
    iSplit; [iPureIntro; exact Hcov2 |].
    iFrame "Hri Hgh Hclaim Hres'".
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
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ={⊤ ∖ ↑minstretN}=∗
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
      "(Hpc0 & Hpa0 & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
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
              HA Hord HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

  (* the two instantiated trampoline fetches *)

  (* ... and the two instantiated step engines: the KERNEL-phase trampoline
     step (userret's first two instructions) and the USER-phase step (the
     rest of userret / uservec). *)
  Definition wp_instr_ktramp_pt (root_ppn : mword 44) :=
    wp_instr_tramp_pt (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt root_ppn)
      (ktramp_fetch_habs root_ppn).
  (* the SHARED-invariant mirror, for kernel trampoline steps taken with the
     kernel table already folded back into [kpt_inv] (post-window). *)
  Definition wp_instr_ktramp_pt_share (root_ppn : mword 44) :=
    wp_instr_tramp_pt (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_res_pt root_ppn)
      (ktramp_fetch_habs_share root_ppn).
  Definition wp_instr_u_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :=
    wp_instr_tramp_pt (utlb_inv_pt uroot tfp um) (utramp_fetch_habs uroot tfp um).

End TrampFetchInst.
