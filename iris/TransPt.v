(* TransPt.v -- the satp-SWITCH WINDOW: translation between two page
   tables.  Between a [csrw satp] and the following [sfence.vma] the TLB
   holds entries of MIXED provenance: some cached from the previous
   table, some from the newly installed one -- and provenance matters
   beyond the leaf word, because a Svadu hit write-back goes to the
   pteAddr recorded by the INSTALLING walk (i.e. into the provenance
   tree's L0 slot).  [tlb_inv_pt2] owns BOTH trees, each constrained by
   an abstract spec, with the two-table consistency [tlb_ok_pt2]
   (PtTree.v §7b); [tlb_inv_pt2_translateAddr] absorbs a translation of
   any va that BOTH specs map to A/D-variants of the same canonical
   leaf; [tlb_inv_pt2_enter]/[tlb_inv_pt2_exit] convert at the window
   boundaries against [pt_frame] (a parked, spec-constrained table).
   The trampoline instantiation ([pt2_tramp_fetch_habs] +
   [wp_instr_pt2_tramp]) drives the switch-window instruction of the
   userret/uservec paths through the shared engine [wp_instr_tramp_pt]. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import PtAdBits CommonWalk PtTree PtTreeAdue.
Require Import KptExecMap.
Require Import KptTree UptTree.
Require Import KptPt.
Require Import Pt4kWalk.
Require Import RiscvExtras.
Require Import SmodePte.
Require Import KMap MinstretInv KptGhost KptShare.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The PURE two-table translation case analysis.  Both trees map       *)
(*    [va]'s vpn to A/D variants of the SAME canonical leaf [w]; the TLB  *)
(*    is two-table consistent.  Translation always succeeds at [pa], and  *)
(*    the state moves in one of four invariant-absorbable ways:           *)
(*      O1     unchanged (hit with sufficient A/D, either provenance)     *)
(*      O2     TLB fill from the CURRENT tree's walk                      *)
(*      O3cur  walk / cur-hit A/D write-back into the CURRENT tree's L0   *)
(*             slot + fill/refresh                                        *)
(*      O3prev hit on a PREVIOUS-provenance entry lacking A/D: write-back *)
(*             through the cached pteAddr into the PREVIOUS tree's L0     *)
(*             slot + refresh                                             *)
(* ===================================================================== *)

Section Pt2Translate.
  Context (acc : MemoryAccessType mem_payload).

  Lemma ptree2_translateAddr_cases (rc : mword 44) (va w pa satp0 : mword 64)
        (tp tc : ptree) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (pp2 pp1 pc2 pc1 : mword 64) (ap dp ac dc : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0p := pte_set_ad w ap dp in
    let p0c := pte_set_ad w ac dc in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    pt_base tc = rc ->
    ptree_maps tp vpn pp2 pp1 p0p ->
    ptree_maps tc vpn pc2 pc1 p0c ->
    tlb_ok_pt2 (mword_of_int 0) tp tc tlbvec ->
    pt_slot_mem σ (pt_addr2 tc vpn) pc2 ->
    pt_slot_mem σ (pt_addr1 pc2 vpn) pc1 ->
    pt_slot_mem σ (pt_addr0 pc1 vpn) p0c ->
    pt_slot_mem σ (pt_addr0 pp1 vpn) p0p ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions σ.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions σ.(sregs)) ->
    exists σ',
      exec (translateAddr (Virtaddr va) acc) σ
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')
      /\ ( σ' = σ
         \/ σ' = set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                  (Some (u_walk_entry vpn pc2 pc1 p0c (mword_of_int 0))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8
                                 (pte_set_ad p0c a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn pc2 pc1 (pte_set_ad p0c a1 d1) (mword_of_int 0)))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 pp1 vpn) 8
                                 (pte_set_ad p0p a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn pp2 pp1 (pte_set_ad p0p a1 d1) (mword_of_int 0)))))
         (* the fork's atomic update re-reads MEMORY: if the previous tree's
            leaf ALREADY has the bits the cached copy lacks, nothing is
            written and the entry is merely refreshed *)
         \/ σ' = set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                  (Some (u_walk_entry vpn pp2 pp1 p0p (mword_of_int 0))))).
  Proof.
    intros vpn p0p p0c Hchk Hcanon Hout Hvarp Hbase Hmaps_p Hmaps_c Htlbok
           Hsm2 Hsm1 Hsm0 Hsm0p
           Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hsatp Hmode Hppn Hasid Htlb
           HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps_c as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                           Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    (* the current tree's three PTE reads, at the walk's canonical slot
       spellings *)
    assert (Hsm2' : pt_slot_mem σ (u_pte_addr rc (subrange_vec_dec vpn 26 18)) pc2).
    { assert (Ha2 : pt_addr2 tc vpn = u_pte_addr rc (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hsm1' : pt_slot_mem σ (u_pte_addr (u_next_base pc2) (subrange_vec_dec vpn 17 9)) pc1)
      by exact Hsm1.
    assert (Hsm0' : pt_slot_mem σ (u_pte_addr (u_next_base pc1) (subrange_vec_dec vpn 8 0)) p0c)
      by exact Hsm0.
    destruct (Hpmar (u_pte_addr rc (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2'))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (u_pte_addr (u_next_base pc2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1'))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (u_pte_addr (u_next_base pc1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0'))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot σ _ pc2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot σ _ pc1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot σ _ p0c region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    pose proof (pt_read_pte_exclusive_slot σ _ p0c region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    (* the PREVIOUS tree's leaf: the fork's re-read on a hit reads THIS slot *)
    pose proof Hmaps_p as (cp1 & cp0 & _ & _ & _ & _ & _ & _ & _ &
                           Hv2p & Hn2p & Hv1p & Hn1p & Hv0p & Hl0p & Hnapp & Hpb0p).
    assert (Hsm0p' : pt_slot_mem σ (u_pte_addr (u_next_base pp1) (subrange_vec_dec vpn 8 0)) p0p)
      by exact Hsm0p.
    destruct (Hpmar (u_pte_addr (u_next_base pp1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0p')) as (region0p & Hm0p & Hs0p).
    pose proof (pt_read_pte_exclusive_slot σ _ p0p region0p Hsm0p' HA Hord HR Hcov Hm0p Hs0p Hhtif)
      as Hrdxp.
    assert (Htm : exec (translationMode Supervisor) σ = Some (Sv39, σ))
      by exact (exec_translationMode_S_sv39 satp0 σ HSXL Hsatp Hmode).
    (* output geometry for the current tree's leaf *)
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0c : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0c. rewrite pte_set_ad_ppn. exact Hout. }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    (* shared continuation: the miss path (empty or non-matching slot)
       walks the CURRENT tree *)
    assert (Hmiss : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ) ->
      exists σ',
        exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')
        /\ ( σ' = set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                   (Some (u_walk_entry vpn pc2 pc1 p0c (mword_of_int 0))))
           \/ (exists (a1 d1 : mword 1),
                σ' = set_reg (MState σ.(sregs)
                                (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8
                                   (pte_set_ad p0c a1 d1))
                                σ.(mdev))
                       tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                              (Some (u_walk_entry vpn pc2 pc1 (pte_set_ad p0c a1 d1) (mword_of_int 0))))))).
    { intros Hlk.
      destruct (ptree_translate_miss_core acc Supervisor rc va w tlbvec pc2 pc1 ac dc σ Hchk
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlb Hlk
                  HA Hord HW Hcov Hpmaw)
        as (σ' & Htr & Hshape).
      exists σ'. split.
      { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0c : mword 64))) : mword 44))
                 satp0 va pa σ σ'
                 Heff Hss Hcp Htm Hsatp Hppn Hasid
                 Hcanon eq_refl Htr Hid). }
      exact Hshape. }
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - (* resident entry: split by provenance *)
      destruct (Htlbok vpn ent Hslot) as [Hcache | Hcache];
        destruct Hcache as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & ->);
        (destruct (decide (vpn0 = vpn)) as [-> | Hne];
         [ | (* foreign entry: rejected by the tag, so the walk runs *)
           destruct Hmiss as (σ' & Htr & Hshape);
           [ exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlb Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                         (mword_of_int 0) Hne))
           | exists σ'; split;
             [ exact Htr
             | destruct Hshape as [Ho2 | Ho3];
               [right; left; exact Ho2 | right; right; left; exact Ho3] ] ] ]).
      + (* HIT on this vpn's entry, PREVIOUS provenance *)
        destruct (ptree_maps_det tp vpn q2 q1 qp0 pp2 pp1 p0p Hm0 Hmaps_p) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc Supervisor mxr do_sum (pte_set_ad p0p a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0p a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w ap dp a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0p a' d')).
        { assert (Habs : pte_set_ad p0p a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w ap dp a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0p a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. unfold p0p. rewrite pte_set_ad_ppn. exact Hout. }
        assert (Hvarm : exists a2 d2 : mword 1, p0p = pte_set_ad (pte_set_ad p0p a' d') a2 d2).
        { exists ap, dp. rewrite pte_set_ad_absorb.
          unfold p0p. rewrite pte_set_ad_absorb. reflexivity. }
        destruct (update_PTE_Bits (pte_set_ad p0p a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * destruct (update_PTE_Bits (p0p : mword 64) acc) as [p0p'|] eqn:Hupm.
          -- (* hit + write-back through the cached pteAddr: the PREVIOUS
                tree's L0 slot (O3prev) *)
             destruct Hsm0p as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 pp1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec (write_pte_conditional
                        (Physaddr (u_pte_addr (u_next_base pp1) (subrange_vec_dec vpn 8 0))) 8
                        (p0p' : mword 64)) σ
                      = Some (Ok true, MState σ.(sregs)
                                 (write_bytes σ.(mem) (pt_addr0 pp1 vpn) 8 p0p') σ.(mdev)))
               by exact (exec_write_pte_conditional_ram (pt_addr0 pp1 vpn) p0p' regionw σ
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             eexists. split.
             { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0p a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn pp2 pp1 (pte_set_ad p0p a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_upd acc Supervisor mxr do_sum
                        vpn pp2 pp1 (pte_set_ad p0p a' d') q0' p0p p0p' MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdxp Hv0p Hl0p Hnapp (Hchk ap dp mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm Hwr eq_refl). }
             right. right. right. left. exists a1, d1.
             rewrite <- Hq. rewrite Htlb. reflexivity.
          -- (* memory already has them: TLB-only refresh *)
             eexists. split.
             { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0p a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn pp2 pp1 (pte_set_ad p0p a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_refresh acc Supervisor mxr do_sum
                        vpn pp2 pp1 (pte_set_ad p0p a' d') q0' p0p MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdxp Hv0p Hl0p Hnapp (Hchk ap dp mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm). }
             right. right. right. right. rewrite Htlb. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0p a' d') : mword 64) acc = None)
            by exact Hupq.
          eexists. split.
          { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0p a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn pp2 pp1 (pte_set_ad p0p a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc Supervisor mxr do_sum
                     vpn pp2 pp1 (pte_set_ad p0p a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
      + (* HIT on this vpn's entry, CURRENT provenance *)
        destruct (ptree_maps_det tc vpn q2 q1 qp0 pc2 pc1 p0c Hm0 Hmaps_c) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc Supervisor mxr do_sum (pte_set_ad p0c a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0c a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w ac dc a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0c a' d')).
        { assert (Habs : pte_set_ad p0c a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w ac dc a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0c a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. exact Hid. }
        assert (Hvarmc : exists a2 d2 : mword 1, p0c = pte_set_ad (pte_set_ad p0c a' d') a2 d2).
        { exists ac, dc. rewrite pte_set_ad_absorb.
          unfold p0c. rewrite pte_set_ad_absorb. reflexivity. }
        destruct (update_PTE_Bits (pte_set_ad p0c a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * destruct (update_PTE_Bits (p0c : mword 64) acc) as [p0c'|] eqn:Hupm.
          -- (* hit + write-back into the CURRENT tree's L0 slot (O3cur) *)
             destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 pc1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec (write_pte_conditional
                        (Physaddr (u_pte_addr (u_next_base pc1) (subrange_vec_dec vpn 8 0))) 8
                        (p0c' : mword 64)) σ
                      = Some (Ok true, MState σ.(sregs)
                                 (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8 p0c') σ.(mdev)))
               by exact (exec_write_pte_conditional_ram (pt_addr0 pc1 vpn) p0c' regionw σ
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             eexists. split.
             { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0c a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn pc2 pc1 (pte_set_ad p0c a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_upd acc Supervisor mxr do_sum
                        vpn pc2 pc1 (pte_set_ad p0c a' d') q0' p0c p0c' MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk ac dc mxr do_sum) Hmisa HPBMTE
                        Hvarmc Hupm Hwr eq_refl). }
             right. right. left. exists a1, d1.
             rewrite <- Hq. rewrite Htlb. reflexivity.
          -- (* memory already has them: TLB-only refresh, which is exactly the
                clean fill from the current tree (O2) *)
             eexists. split.
             { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0c a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn pc2 pc1 (pte_set_ad p0c a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_refresh acc Supervisor mxr do_sum
                        vpn pc2 pc1 (pte_set_ad p0c a' d') q0' p0c MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk ac dc mxr do_sum) Hmisa HPBMTE
                        Hvarmc Hupm). }
             right. left. rewrite Htlb. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0c a' d') : mword 64) acc = None)
            by exact Hupq.
          eexists. split.
          { apply (exec_translateAddr_pt_front acc Supervisor vpn rc
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0c a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn pc2 pc1 (pte_set_ad p0c a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc Supervisor mxr do_sum
                     vpn pc2 pc1 (pte_set_ad p0c a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
    - (* empty slot: the walk runs on the current tree *)
      destruct Hmiss as (σ' & Htr & Hshape).
      { exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlb Hslot). }
      exists σ'. split; [exact Htr |].
      destruct Hshape as [Ho2 | Ho3];
        [right; left; exact Ho2 | right; right; left; exact Ho3].
  Qed.

End Pt2Translate.

(* ===================================================================== *)
(* §2 THE TWO-TABLE TRANSLATION INVARIANT.  satp points at the CURRENT    *)
(*    root [rc]; both trees are owned, each constrained only by its       *)
(*    abstract spec; the TLB is two-table consistent.                     *)
(* ===================================================================== *)

Section Pt2Inv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* [pmp_config]'s content is root-independent (the root is a phantom
     index); re-index it across the switch by conversion *)
  Lemma pmp_config_reindex (r1 r2 : mword 44) :
    pmp_config r1 -∗ pmp_config r2.
  Proof. iIntros "H". iExact "H". Qed.

  Definition tlb_inv_pt2 (rc : mword 44) (Sp Sc : ptree -> Prop) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc : ptree),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp tc tlbvec ⌝ ∗
       ⌜ Sp tp ⌝ ∗ ⌜ Sc tc ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) tp ∗ ptree_own 2 (DfracOwn 1) tc ∗
       pmp_config rc)%I.

  Lemma tlb_inv_pt2_intro (rc : mword 44) (Sp Sc : ptree -> Prop)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    tlb_ok_pt2 (mword_of_int 0) tp tc tlbvec ->
    Sp tp -> Sc tc ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗
    ptree_own 2 (DfracOwn 1) tp -∗ ptree_own 2 (DfracOwn 1) tc -∗
    pmp_config rc -∗
    tlb_inv_pt2 rc Sp Sc.
  Proof.
    intros Hmode Hasid Hppn Hok HSp HSc Hpmaw. iIntros "Hsatp Htlb Htp Htc Hpmp".
    iExists satp0, tlbvec, tp, tc. iFrame "Hsatp Htlb Htp Htc Hpmp".
    iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_pt2_open (rc : mword 44) (Sp Sc : ptree -> Prop) :
    tlb_inv_pt2 rc Sp Sc -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp tc tlbvec ⌝ ∗
      ⌜ Sp tp ⌝ ∗ ⌜ Sc tc ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) tp ∗ ptree_own 2 (DfracOwn 1) tc ∗
      pmp_config rc.
  Proof. iIntros "H". iExact "H". Qed.

  (* ---- the WINDOW BOUNDARY conversions ------------------------------ *)

  (* ENTER: right after the [csrw satp] installing the new root [rc].
     The satp cell has just been written to [satp0] (pointing at [rc]);
     every resident TLB entry was cached under the PREVIOUS table [tp]
     (single-table consistency); the new table arrives PARKED as
     [pt_frame Sc]. *)
  Lemma tlb_inv_pt2_enter (rc : mword 44) (Sp Sc : ptree -> Prop)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    tlb_ok_pt (mword_of_int 0) tp tlbvec ->
    Sp tp ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) tp -∗
    pt_frame Sc -∗ pmp_config rc -∗
    tlb_inv_pt2 rc Sp Sc.
  Proof.
    intros Hmode Hasid Hppn Hok HSp Hpmaw.
    iIntros "Hsatp Htlb Htp Hfr Hpmp".
    iDestruct "Hfr" as (tc) "[%HSc Htc]".
    iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tlbvec tp tc
              Hmode Hasid Hppn (tlb_ok_pt2_prev _ _ _ _ Hok) HSp HSc Hpmaw
              with "Hsatp Htlb Htp Htc Hpmp").
  Qed.

  (* EXIT: at the closing [sfence.vma].  The previous table leaves parked
     as [pt_frame Sp]; the caller zeroes the TLB with the sfence and
     re-establishes the current table's single-table invariant from the
     returned pieces ([tlb_ok_pt_empty]). *)
  Lemma tlb_inv_pt2_exit (rc : mword 44) (Sp Sc : ptree -> Prop) :
    tlb_inv_pt2 rc Sp Sc -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tc : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ Sc tc ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) tc ∗ pmp_config rc ∗
      pt_frame Sp.
  Proof.
    iIntros "Hinv".
    iDestruct (tlb_inv_pt2_open with "Hinv") as (satp0 tlbvec tp tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok & %HSp & %HSc & %Hpmaw & Htp & Htc & Hpmp)".
    iExists satp0, tlbvec, tc.
    iFrame "Hsatp Htlb Htc Hpmp".
    iSplit; [iPureIntro; exact Hmode |].
    iSplit; [iPureIntro; exact Hasid |].
    iSplit; [iPureIntro; exact Hppn |].
    iSplit; [iPureIntro; exact HSc |].
    iSplit; [iPureIntro; exact Hpmaw |].
    iExists tp. iFrame "Htp". iPureIntro. exact HSp.
  Qed.

End Pt2Inv.

(* ===================================================================== *)
(* §2b THE SHARED-KERNEL WINDOW INVARIANT.  The mirror of [tlb_inv_pt2]     *)
(*    with the CURRENT root's tree folded into [KptShare.kpt_inv] instead   *)
(*    of exclusively owned -- uservec's role, where the switch installs    *)
(*    the KERNEL table as [rc].  [_kprev] below is userret's mirror image  *)
(*    (kernel plays the PREVIOUS slot).  Both exist because an Iris        *)
(*    invariant can only be opened for the span of ONE atomic step, so the *)
(*    shared side cannot be "checked out" once for the whole window the    *)
(*    way the exclusive tree was -- it has to be re-opened at each         *)
(*    absorption call that touches it (here: the window's one fetch).      *)
(* ===================================================================== *)

Section Pt2InvKcur.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Definition tlb_inv_pt2_kcur (rc : mword 44) (Sp : ptree -> Prop) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc0 : ptree),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp tc0 tlbvec ⌝ ∗
       ⌜ Sp tp ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) tp ∗
       pmp_config rc ∗
       kpt_lb tc0 ∗ kpt_inv rc)%I.

  Lemma tlb_inv_pt2_kcur_intro (rc : mword 44) (Sp : ptree -> Prop)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc0 : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    tlb_ok_pt2 (mword_of_int 0) tp tc0 tlbvec ->
    Sp tp -> (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗
    ptree_own 2 (DfracOwn 1) tp -∗ pmp_config rc -∗ kpt_lb tc0 -∗ kpt_inv rc -∗
    tlb_inv_pt2_kcur rc Sp.
  Proof.
    intros Hmode Hasid Hppn Hok HSp Hpmaw.
    iIntros "Hsatp Htlb Htp Hpmp Hlb0 Hkinv".
    iExists satp0, tlbvec, tp, tc0. iFrame "Hsatp Htlb Htp Hpmp Hlb0 Hkinv".
    iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_pt2_kcur_open (rc : mword 44) (Sp : ptree -> Prop) :
    tlb_inv_pt2_kcur rc Sp -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp tc0 : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp tc0 tlbvec ⌝ ∗
      ⌜ Sp tp ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) tp ∗
      pmp_config rc ∗ kpt_lb tc0 ∗ kpt_inv rc.
  Proof. iIntros "H". iExact "H". Qed.

  (* ENTER: right after [csrw satp] installs [rc].  The previous table
     [Sp] arrives PARKED as [pt_frame Sp] (a per-process user table
     genuinely is exclusive); the shared kernel side needs only a fresh
     SNAPSHOT off [kpt_inv], never ownership -- one [iMod], no later. *)
  Lemma tlb_inv_pt2_kcur_enter (rc : mword 44) (Sp : ptree -> Prop) (E : coPset)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp : ptree) :
    ↑kptN ⊆ E ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    tlb_ok_pt (mword_of_int 0) tp tlbvec ->
    Sp tp -> (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) tp -∗
    pmp_config rc -∗ kpt_inv rc
    ={E}=∗
    tlb_inv_pt2_kcur rc Sp.
  Proof.
    intros HE Hmode Hasid Hppn Hok HSp Hpmaw.
    iIntros "Hsatp Htlb Htp Hpmp #Hkinv".
    iMod (kpt_inv_snapshot E rc HE with "Hkinv") as (tc0) "#Hlb0".
    iModIntro.
    iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tlbvec tp tc0
              Hmode Hasid Hppn (tlb_ok_pt2_prev _ _ _ _ Hok) HSp Hpmaw
              with "Hsatp Htlb Htp Hpmp Hlb0 Hkinv").
  Qed.

  (* EXIT: at the closing [sfence.vma].  [Sp]'s table leaves parked as
     [pt_frame Sp]; the shared side hands back nothing but the persistent
     snapshot -- [kpt_inv] never needed returning, and [tlb_ok_pt_empty]
     re-seals at ANY tree once the sfence has emptied the TLB, so the
     snapshot the caller already has is exactly what it needs. *)
  Lemma tlb_inv_pt2_kcur_exit (rc : mword 44) (Sp : ptree -> Prop) :
    tlb_inv_pt2_kcur rc Sp -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tc0 : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗
      pmp_config rc ∗ kpt_lb tc0 ∗ kpt_inv rc ∗
      pt_frame Sp.
  Proof.
    iIntros "Hinv".
    iDestruct (tlb_inv_pt2_kcur_open with "Hinv") as (satp0 tlbvec tp tc0)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok & %HSp & %Hpmaw & Htp & Hpmp & Hlb0 & Hkinv)".
    iExists satp0, tlbvec, tc0.
    iFrame "Hsatp Htlb Hpmp Hlb0 Hkinv".
    iSplit; [iPureIntro; exact Hmode |].
    iSplit; [iPureIntro; exact Hasid |].
    iSplit; [iPureIntro; exact Hppn |].
    iExists tp. iFrame "Htp". iPureIntro. exact HSp.
  Qed.

End Pt2InvKcur.

(* ===================================================================== *)
(* §2c THE SHARED-KERNEL WINDOW INVARIANT, userret's mirror image: the     *)
(*    switch installs the USER root as CURRENT, so the kernel table plays  *)
(*    the PREVIOUS slot.  [kroot] is carried as its own parameter (unlike  *)
(*    [_kcur], [rc] here is the USER root, not the kernel one).            *)
(* ===================================================================== *)

Section Pt2InvKprev.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Definition tlb_inv_pt2_kprev (rc kroot : mword 44) (Sc : ptree -> Prop) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp0 tc : ptree),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp0 tc tlbvec ⌝ ∗
       ⌜ Sc tc ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) tc ∗
       pmp_config rc ∗
       kpt_lb tp0 ∗ kpt_inv kroot)%I.

  Lemma tlb_inv_pt2_kprev_intro (rc kroot : mword 44) (Sc : ptree -> Prop)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp0 tc : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    tlb_ok_pt2 (mword_of_int 0) tp0 tc tlbvec ->
    Sc tc -> (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗
    ptree_own 2 (DfracOwn 1) tc -∗ pmp_config rc -∗ kpt_lb tp0 -∗ kpt_inv kroot -∗
    tlb_inv_pt2_kprev rc kroot Sc.
  Proof.
    intros Hmode Hasid Hppn Hok HSc Hpmaw.
    iIntros "Hsatp Htlb Htc Hpmp Hlb0 Hkinv".
    iExists satp0, tlbvec, tp0, tc. iFrame "Hsatp Htlb Htc Hpmp Hlb0 Hkinv".
    iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_pt2_kprev_open (rc kroot : mword 44) (Sc : ptree -> Prop) :
    tlb_inv_pt2_kprev rc kroot Sc -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tp0 tc : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt2 (mword_of_int 0) tp0 tc tlbvec ⌝ ∗
      ⌜ Sc tc ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) tc ∗
      pmp_config rc ∗ kpt_lb tp0 ∗ kpt_inv kroot.
  Proof. iIntros "H". iExact "H". Qed.

  (* ENTER: right after [csrw satp] installs [rc] (the USER root).  The
     caller already holds a fresh kernel-side snapshot from whatever left
     it (e.g. [KptShare.tlb_res_pt]'s own [tlb_snap_ok] -- the TLB has not
     moved since, so it is still valid); [Sc]'s table arrives PARKED as
     [pt_frame Sc].  No fupd needed: unlike [_kcur_enter], nothing is
     freshly minted here. *)
  Lemma tlb_inv_pt2_kprev_enter (rc kroot : mword 44) (Sc : ptree -> Prop)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ tlb_snap_ok tlbvec -∗
    pt_frame Sc -∗ pmp_config rc -∗ kpt_inv kroot -∗
    tlb_inv_pt2_kprev rc kroot Sc.
  Proof.
    intros Hmode Hasid Hppn Hpmaw.
    iIntros "Hsatp Htlb Hsnap Hfr Hpmp #Hkinv".
    iDestruct "Hsnap" as (tp0) "[%Htlbok0 #Hlb0]".
    iDestruct "Hfr" as (tc) "[%HSc Htc]".
    iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tlbvec tp0 tc
              Hmode Hasid Hppn (tlb_ok_pt2_prev _ _ _ _ Htlbok0) HSc Hpmaw
              with "Hsatp Htlb Htc Hpmp Hlb0 Hkinv").
  Qed.

  (* EXIT: at the closing [sfence.vma].  [Sc]'s table stays live (it is
     about to become the running invariant); the shared kernel side hands
     back nothing -- [kpt_inv] never needed returning. *)
  Lemma tlb_inv_pt2_kprev_exit (rc kroot : mword 44) (Sc : ptree -> Prop) :
    tlb_inv_pt2_kprev rc kroot Sc -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (tc : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = rc ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ Sc tc ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) tc ∗ pmp_config rc.
  Proof.
    iIntros "Hinv".
    iDestruct (tlb_inv_pt2_kprev_open with "Hinv") as (satp0 tlbvec tp0 tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok & %HSc & %Hpmaw & Htc & Hpmp & _ & _)".
    iExists satp0, tlbvec, tc.
    iFrame "Hsatp Htlb Htc Hpmp".
    repeat (iSplit; [done |]). done.
  Qed.

End Pt2InvKprev.

(* ===================================================================== *)
(* §3 THE TWO-TABLE INVARIANT ABSORBS TRANSLATION.  Premises: BOTH specs  *)
(*    force a mapping of [va]'s vpn to an A/D variant of the same         *)
(*    canonical leaf [w], and both specs survive an A/D write-back to     *)
(*    that vpn.  Whatever the machine does -- nothing, a fill from the    *)
(*    current walk, or a Svadu write-back into EITHER tree -- the         *)
(*    invariant re-establishes.                                           *)
(* ===================================================================== *)

Section Pt2TranslateIris.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma tlb_inv_pt2_translateAddr (rc : mword 44) (Sp Sc : ptree -> Prop)
      (w va pa : mword 64) (σ : mstate)
      (S : TsoMemPa.bytemap -> iProp Σ) :
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum (pte_set_ad w a d)) ->
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall t, Sp t -> exists p2 p1 (a d : mword 1),
       ptree_maps t (svpn_of va) p2 p1 (pte_set_ad w a d)) ->
    (forall t, Sc t -> exists p2 p1 (a d : mword 1),
       ptree_maps t (svpn_of va) p2 p1 (pte_set_ad w a d)) ->
    (forall t, Sc t -> pt_base t = rc) ->
    (forall t (a1 d1 : mword 1), Sp t ->
       Sp (ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1))) ->
    (forall t (a1 d1 : mword 1), Sc t ->
       Sc (ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1))) ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    (* A6.24's payer, at the memory-indexed (chainable) currency and
       PERSISTENT -- [UptTree.utlb_inv_pt_translateAddr]'s shape.  This
       walker's A/D write-back is a real store to a LEDGER slot, so it owes
       the era log's append and cannot be paid by [phys_word_pointsto_write]
       (a gen_heap-only gate); the caller discharges it with
       [TsoCtx.ctx_store_win_ok] and its own [own_context]. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wnew) -∗
    S σ.(mem) -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt2 rc Sp Sc ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      S σ'.(mem) ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt2 rc Sp Sc.
  Proof.
    intros Hchk Hvar Hcanon Hout Hsel_p Hsel_c Hbase_c Hpres_p Hpres_c
           Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "#Hpay Hsto Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0 tlbvec tp tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSp & %HSc & %Hpmawimpl & Htp & Htc & Hpmp)".
    pose proof (Hpmawimpl _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    set (vpn := svpn_of va) in *.
    destruct (Hsel_p tp HSp) as (pp2 & pp1 & ap & dp & Hmaps_p).
    destruct (Hsel_c tc HSc) as (pc2 & pc1 & ac & dc & Hmaps_c).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) tp vpn pp2 pp1 _ Hmaps_p with "Hgh Htp")
      as %(Hsm2p & Hsm1p & Hsm0p).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) tc vpn pc2 pc1 _ Hmaps_c with "Hgh Htc")
      as %(Hsm2c & Hsm1c & Hsm0c).
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
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Hvarp : forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d))
      by (intros a d; exact (proj2 (proj2 (proj2 (Hvar a d))))).
    destruct (ptree2_translateAddr_cases acc rc va w pa satp0 tp tc tlbvec
                pp2 pp1 pc2 pc1 ap dp ac dc σ
                Hchk Hcanon Hout Hvarp (Hbase_c tc HSc) Hmaps_p Hmaps_c Hok2
                Hsm2c Hsm1c Hsm0c Hsm0p
                Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hsatpv Hmode Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (σ' & Htrans & Hshape).
    (* the PMP cells re-seal in every arm *)
    iAssert (pmp_config rc) with "[Hpc Hpa]" as "Hpmp".
    { iApply (pmp_config_intro rc pmpcfg0 pmpaddr00
                HA Hord HX HW HR Hcov with "Hpc Hpa"). }
    destruct Hshape as [-> | [-> | [ (a1 & d1 & ->) | [ (a1 & d1 & ->) | -> ] ]]].
    - (* O1: nothing moved *)
      iModIntro. iExists σ.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iFrame "Hsto Hri Hgh".
      iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tlbvec tp tc
                Hmode Hasid Hppn Hok2 HSp HSc Hpmawimpl
                with "Hsatp Htlb Htp Htc Hpmp").
    - (* O2: TLB fill from the current tree's walk *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pc2 pc1 (pte_set_ad w ac dc) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hsto Hri Hgh".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp tc tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp tc tlbvec vpn pc2 pc1
                 (pte_set_ad w ac dc) (pte_set_ad w ac dc) Hmaps_c
                 (pte_set_ad_refl _) Hok2). }
      iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tv' tp tc
                Hmode Hasid Hppn Hok' HSp HSc Hpmawimpl
                with "Hsatp Htlb Htp Htc Hpmp").
    - (* O3cur: the Svadu write-back into the CURRENT tree, absorbed *)
      set (p0c := pte_set_ad w ac dc) in *.
      set (w' := pte_set_ad p0c a1 d1) in *.
      assert (Habs : w' = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w ac dc a1 d1).
      assert (Hv' : pte_valid w') by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hl' : pte_leaf w') by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot w')
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 w')
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      iDestruct (ptree_own_path_upd (DfracOwn 1) tc vpn pc2 pc1 p0c Hmaps_c with "Htc")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpay" $! σ.(mem) (pt_addr0 pc1 vpn) p0c w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Htc".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pc2 pc1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hsto Hri Hgh".
      assert (HSc' : Sc (ptree_set_leaf tc vpn w')).
      { rewrite Habs. exact (Hpres_c tc a1 d1 HSc). }
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp (ptree_set_leaf tc vpn w') tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp (ptree_set_leaf tc vpn w')
                 tlbvec vpn pc2 pc1 w' w'
                 (ptree_set_leaf_maps_self tc vpn pc2 pc1 p0c w' Hmaps_c Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_cur (mword_of_int 0) tp tc tlbvec vpn pc2 pc1 p0c a1 d1
                    Hmaps_c Hv' Hl' Hn' Hp' Hok2)). }
      iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tv' tp (ptree_set_leaf tc vpn w')
                Hmode Hasid Hppn Hok' HSp HSc' Hpmawimpl
                with "Hsatp Htlb Htp Htc Hpmp").
    - (* O3prev: the Svadu write-back through the cached pteAddr into the
         PREVIOUS tree, absorbed *)
      set (p0p := pte_set_ad w ap dp) in *.
      set (w' := pte_set_ad p0p a1 d1) in *.
      assert (Habs : w' = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w ap dp a1 d1).
      assert (Hv' : pte_valid w') by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hl' : pte_leaf w') by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot w')
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 w')
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      iDestruct (ptree_own_path_upd (DfracOwn 1) tp vpn pp2 pp1 p0p Hmaps_p with "Htp")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpay" $! σ.(mem) (pt_addr0 pp1 vpn) p0p w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Htp".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pp2 pp1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 pp1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hsto Hri Hgh".
      assert (HSp' : Sp (ptree_set_leaf tp vpn w')).
      { rewrite Habs. exact (Hpres_p tp a1 d1 HSp). }
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) (ptree_set_leaf tp vpn w') tc tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) (ptree_set_leaf tp vpn w') tc
                 tlbvec vpn pp2 pp1 w' w'
                 (ptree_set_leaf_maps_self tp vpn pp2 pp1 p0p w' Hmaps_p Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_prev (mword_of_int 0) tp tc tlbvec vpn pp2 pp1 p0p a1 d1
                    Hmaps_p Hv' Hl' Hn' Hp' Hok2)). }
      iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tv' (ptree_set_leaf tp vpn w') tc
                Hmode Hasid Hppn Hok' HSp' HSc Hpmawimpl
                with "Hsatp Htlb Htp Htc Hpmp").
    - (* O2prev: the fork's re-read found the previous tree's leaf ALREADY
         carrying the bits the cached copy lacked, so memory is untouched and
         only the TLB entry is refreshed *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pp2 pp1 (pte_set_ad w ap dp) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hsto Hri Hgh".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp tc tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) tp tc tlbvec vpn pp2 pp1
                 (pte_set_ad w ap dp) (pte_set_ad w ap dp) Hmaps_p
                 (pte_set_ad_refl _) Hok2). }
      iApply (tlb_inv_pt2_intro rc Sp Sc satp0 tv' tp tc
                Hmode Hasid Hppn Hok' HSp HSc Hpmawimpl
                with "Hsatp Htlb Htp Htc Hpmp").
  Qed.

End Pt2TranslateIris.

(* ===================================================================== *)
(* §4 THE TRAMPOLINE INSTANTIATION: the switch-window instruction fetch.  *)
(*    Both specs carry a trampoline clause (variants of [pte_tramp] at    *)
(*    [tramp_vpn]), which discharges the agreement premises; the engine   *)
(*    instantiation gives the switch-window step for free.                *)
(* ===================================================================== *)

Section Pt2TrampInst.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the spec-side premises the trampoline instantiation needs: a
     trampoline clause + an A/D write-back closure, per side *)
  Definition pt2_tramp_spec (S : ptree -> Prop) : Prop :=
    (forall t, S t -> exists p2 p1 (a d : mword 1),
       ptree_maps t tramp_vpn p2 p1 (pte_set_ad pte_tramp a d)) /\
    (forall t (a1 d1 : mword 1), S t ->
       S (ptree_set_leaf t tramp_vpn (pte_set_ad pte_tramp a1 d1))).

  Lemma pt2_tramp_fetch_habs (rc : mword 44) (Sp Sc : ptree -> Prop) :
    pt2_tramp_spec Sp -> pt2_tramp_spec Sc ->
    (forall t, Sc t -> pt_base t = rc) ->
    forall (va pa : mword 64) (σ : mstate) (S : TsoMemPa.bytemap -> iProp Σ),
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
    (* A6.24's payer, threaded through the wrapper unchanged. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wnew) -∗
    S σ.(mem) -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt2 rc Sp Sc ={⊤ ∖ ↑minstretN}=∗
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
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt2 rc Sp Sc.
  Proof.
    intros (Hsel_p & Hpres_p) (Hsel_c & Hpres_c) Hbase_c
           va pa σ S Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "#Hpay Hsto Hri Hgh Hinv".
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    iMod (tlb_inv_pt2_translateAddr (InstructionFetch tt) rc Sp Sc pte_tramp va pa σ S
            (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
            tramp_variant Hcanon Hout
            (fun t HS => match Hsel_p t HS with
                         | ex_intro _ p2 (ex_intro _ p1 (ex_intro _ a (ex_intro _ d Hm))) =>
                             ex_intro _ p2 (ex_intro _ p1 (ex_intro _ a (ex_intro _ d
                               (eq_rect_r (fun v => ptree_maps t v p2 p1 _) Hm Hvpn))))
                         end)
            (fun t HS => match Hsel_c t HS with
                         | ex_intro _ p2 (ex_intro _ p1 (ex_intro _ a (ex_intro _ d Hm))) =>
                             ex_intro _ p2 (ex_intro _ p1 (ex_intro _ a (ex_intro _ d
                               (eq_rect_r (fun v => ptree_maps t v p2 p1 _) Hm Hvpn))))
                         end)
            Hbase_c
            (fun t a1 d1 HS =>
               eq_rect_r (fun v => Sp (ptree_set_leaf t v _)) (Hpres_p t a1 d1 HS) Hvpn)
            (fun t a1 d1 HS =>
               eq_rect_r (fun v => Sc (ptree_set_leaf t v _)) (Hpres_c t a1 d1 HS) Hvpn)
            Lmisa Lmenv Lhtif Lpriv LSXL
            (exec_effectivePrivilege_fetch _ _ σ)
            (exec_is_shadow_stack_fetch σ)
            Lpma with "Hpay Hsto Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hsto & Hri & Hgh & Hinv)".
    iDestruct (tlb_inv_pt2_open with "Hinv") as (satp1 tlbvec1 tp1 tc1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %HSp1 & %HSc1 & %Hpmawimpl & Htp & Htc & Hpmp)".
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
    iApply (tlb_inv_pt2_intro rc Sp Sc satp1 tlbvec1 tp1 tc1
              Hmode Hasid Hppn Htlbok HSp1 HSc1 Hpmawimpl
              with "Hsatp Htlb Htp Htc").
    iApply (pmp_config_intro rc pmpcfg0 pmpaddr00
              HA Hord HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

End Pt2TrampInst.

(* the SHARED-KERNEL mirror of [pt2_tramp_fetch_habs]: [Sp]'s side is
   exactly as before (a parked, exclusively-owned table genuinely needs
   its own [pt2_tramp_spec] clause); the kernel side opens [kpt_inv]
   for the span of this ONE fetch instead of drawing on an ambient [Sc].
   The trampoline claim travels as an explicit resource (mirroring
   [TrampStepPt.ktramp_fetch_habs_share]) since nothing else supplies it
   once [Sc] is gone. *)
Section Pt2TrampInstKcur.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma pt2_tramp_fetch_habs_kcur (rc : mword 44) (Sp : ptree -> Prop) :
    pt2_tramp_spec Sp ->
    forall (va pa : mword 64) (σ : mstate) (S : TsoMemPa.bytemap -> iProp Σ),
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
    (* A6.24's payer, threaded through the wrapper unchanged. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wnew) -∗
    (* ...AND A SECOND PAYER, AT THE KERNEL TIER.  These two wrappers walk
       BOTH trees: the previous/current user tree at the [Some ξ] tier and
       the SHARED KERNEL tree at the [None] tier ([kptree_own]).  The
       kernel tree's A/D write-back is a context-FREE ledger store (A6.20 --
       its owner is a bare [inv], so it can name no context), so it needs its
       own currency: [TsoCtx.ledger_store_win_ok] rather than
       [ctx_store_win_ok].  Two payers, one per tier, is the honest shape. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.phys_ledger_word a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.phys_ledger_word a (DfracOwn 1) wnew) -∗
    S σ.(mem) -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt2_kcur rc Sp) ={⊤ ∖ ↑minstretN}=∗
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
      S σ'.(mem) ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt2_kcur rc Sp).
  Proof.
    intros (Hsel_p & Hpres_p) va pa σ S Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "#Hpay #Hpayk Hsto Hri Hgh [#Hclaim Hinv]".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hclaimva".
    { rewrite Hvpn. iApply "Hclaim". }
    iDestruct (tlb_inv_pt2_kcur_open with "Hinv") as (satp0 tlbvec tp tc0)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSp & %Hpmawimpl & Htp & Hpmp & #Hlb0 & #Hkinv)".
    pose proof (Hpmawimpl _ Lpma) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    destruct (Hsel_p tp HSp) as (pp2 & pp1 & ap & dp & Hmaps_p0).
    assert (Hmaps_p : ptree_maps tp (svpn_of va) pp2 pp1 (pte_set_ad pte_tramp ap dp))
      by (rewrite Hvpn; exact Hmaps_p0).
    assert (Hpres_p' : forall t' (a1 d1 : mword 1), Sp t' ->
              Sp (ptree_set_leaf t' (svpn_of va) (pte_set_ad pte_tramp a1 d1))).
    { intros t' a1 d1 HSpt'. rewrite Hvpn. exact (Hpres_p t' a1 d1 HSpt'). }
    set (vpn := svpn_of va) in *.
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
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HX).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Lpma) as Hpmar.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    assert (Hvarp : forall a d : mword 1, pte_pbmt0 (pte_set_ad pte_tramp a d))
      by (intros a d; exact (proj2 (proj2 (proj2 (tramp_variant a d))))).
    (* ---- open the shared table for THIS instruction only ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hclaimva") as %HMlk.
    iDestruct (kpt_lb_agree tc0 t with "Hlb0 Hlbt") as %Hcan0.
    assert (Hok2' : tlb_ok_pt2 (mword_of_int 0) tp t tlbvec)
      by exact (tlb_ok_pt2_canon_cur (mword_of_int 0) tp tc0 t tlbvec Hcan0 Hok2).
    pose proof Hspec as (Hbase & Hmapspec).
    pose proof (Hmapspec vpn) as Hmapv. rewrite HMlk in Hmapv.
    destruct Hmapv as (pc2 & pc1 & ac & dc & Hmaps_c0).
    assert (Hlf : pte_set_ad (kpt_leaf_pte_of vpn (tramp_ppn, KP_rx)) ac dc
                = pte_set_ad pte_tramp ac dc)
      by (unfold kpt_leaf_pte_of; cbn [fst snd]; apply kperm_rx_tramp_variant).
    rewrite Hlf in Hmaps_c0.
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) tp vpn pp2 pp1 _ Hmaps_p with "Hgh Htp")
      as %(Hsm2p & Hsm1p & Hsm0p).
    (* the CURRENT tree here is the KERNEL one ([kptree_own] = the [None]
       tier), so the memory projection is taken at that tier explicitly. *)
    iDestruct (ptree_own_path_mem_at None σ (DfracOwn 1) t vpn pc2 pc1 _ Hmaps_c0
                 with "Hgh Ht") as %(Hsm2c & Hsm1c & Hsm0c).
    assert (Hbase_c : pt_base t = rc) by (rewrite Hbase; reflexivity).
    destruct (ptree2_translateAddr_cases (InstructionFetch tt) rc va pte_tramp pa satp0 tp t tlbvec
                pp2 pp1 pc2 pc1 ap dp ac dc σ
                (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
                Hcanon Hout Hvarp Hbase_c Hmaps_p Hmaps_c0 Hok2'
                Hsm2c Hsm1c Hsm0c Hsm0p
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Hsatpv Hmode Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (σ' & Htrans & Hshape).
    iAssert (pmp_config rc) with "[Hpc Hpa]" as "Hpmp".
    { iApply (pmp_config_intro rc pmpcfg0 pmpaddr00
                HA Hord HX HW HR Hcov with "Hpc Hpa"). }
    destruct Hshape as [-> | [-> | [ (a1 & d1 & ->) | [ (a1 & d1 & ->) | -> ] ]]].
    - (* O1: nothing moved *)
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists σ.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iSplit; [iPureIntro; exact HA' |].
      iSplit; [iPureIntro; exact Hord' |].
      iSplit; [iPureIntro; exact HX' |].
      iSplit; [iPureIntro; exact Hcov' |].
      iFrame "Hsto Hri Hgh Hclaim".
      iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tlbvec tp tc0
                Hmode Hasid Hppn Hok2 HSp Hpmawimpl
                with "Hsatp Htlb Htp Hpmp Hlb0 Hkinv").
    - (* O2: TLB fill from the current (shared) tree's walk -- [t] unchanged *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pc2 pc1 (pte_set_ad pte_tramp ac dc) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp t tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp t tlbvec vpn pc2 pc1
                 (pte_set_ad pte_tramp ac dc) (pte_set_ad pte_tramp ac dc) Hmaps_c0
                 (pte_set_ad_refl _) Hok2'). }
      iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tv' tp tc0
                Hmode Hasid Hppn (tlb_ok_pt2_canon_cur (mword_of_int 0) tp t tc0 tv'
                  (eq_sym Hcan0) Hok') HSp Hpmawimpl
                with "Hsatp Htlb Htp Hpmp Hlb0 Hkinv").
    - (* O3cur: the Svadu write-back into the CURRENT (shared) tree *)
      set (p0c := pte_set_ad pte_tramp ac dc) in *.
      set (w' := pte_set_ad p0c a1 d1) in *.
      assert (Habs : w' = pte_set_ad pte_tramp a1 d1)
        by exact (pte_set_ad_absorb pte_tramp ac dc a1 d1).
      pose proof (tramp_variant a1 d1) as (Hv' & Hl' & Hn' & Hp').
      rewrite <- Habs in Hv', Hl', Hn', Hp'.
      iDestruct (ptree_own_path_upd_at None (DfracOwn 1) t vpn pc2 pc1 p0c Hmaps_c0
                   with "Ht") as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpayk" $! σ.(mem) (pt_addr0 pc1 vpn) p0c w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Ht".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pc2 pc1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      assert (Hcan' : ptree_canon t = ptree_canon (ptree_set_leaf t vpn w')).
      { symmetry. exact (ptree_canon_set_leaf t vpn pc2 pc1 p0c a1 d1 Hmaps_c0). }
      iDestruct (kpt_lb_canon t (ptree_set_leaf t vpn w') Hcan' with "Hlbt") as "#Hlb'".
      assert (Hspec' : kpt_tree_spec_gen rc M (ptree_set_leaf t vpn w')).
      { apply (kpt_tree_spec_gen_set_leaf rc M t vpn (tramp_ppn, KP_rx) pc2 pc1
                 p0c a1 d1 Hspec Hmaps_c0 HMlk).
        exists ac, dc. symmetry. exact Hlf. }
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists (ptree_set_leaf t vpn w'), M. iFrame "Ht HM Hlb'".
        iPureIntro. exact Hspec'. }
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp (ptree_set_leaf t vpn w') tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp (ptree_set_leaf t vpn w')
                 tlbvec vpn pc2 pc1 w' w'
                 (ptree_set_leaf_maps_self t vpn pc2 pc1 p0c w' Hmaps_c0 Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_cur (mword_of_int 0) tp t tlbvec vpn pc2 pc1 p0c a1 d1
                    Hmaps_c0 Hv' Hl' Hn' Hp' Hok2')). }
      iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tv' tp (ptree_set_leaf t vpn w')
                Hmode Hasid Hppn Hok' HSp Hpmawimpl
                with "Hsatp Htlb Htp Hpmp Hlb' Hkinv").
    - (* O3prev: the Svadu write-back into the PREVIOUS (still exclusive) tree *)
      set (p0p := pte_set_ad pte_tramp ap dp) in *.
      set (w' := pte_set_ad p0p a1 d1) in *.
      assert (Habs : w' = pte_set_ad pte_tramp a1 d1)
        by exact (pte_set_ad_absorb pte_tramp ap dp a1 d1).
      pose proof (tramp_variant a1 d1) as (Hv' & Hl' & Hn' & Hp').
      rewrite <- Habs in Hv', Hl', Hn', Hp'.
      iDestruct (ptree_own_path_upd (DfracOwn 1) tp vpn pp2 pp1 p0p Hmaps_p with "Htp")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpay" $! σ.(mem) (pt_addr0 pp1 vpn) p0p w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Htp".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pp2 pp1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 pp1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (HSp' : Sp (ptree_set_leaf tp vpn w')).
      { rewrite Habs. exact (Hpres_p' tp a1 d1 HSp). }
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) (ptree_set_leaf tp vpn w') t tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) (ptree_set_leaf tp vpn w') t
                 tlbvec vpn pp2 pp1 w' w'
                 (ptree_set_leaf_maps_self tp vpn pp2 pp1 p0p w' Hmaps_p Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_prev (mword_of_int 0) tp t tlbvec vpn pp2 pp1 p0p a1 d1
                    Hmaps_p Hv' Hl' Hn' Hp' Hok2')). }
      iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tv' (ptree_set_leaf tp vpn w') tc0
                Hmode Hasid Hppn (tlb_ok_pt2_canon_cur (mword_of_int 0)
                  (ptree_set_leaf tp vpn w') t tc0 tv'
                  (eq_sym Hcan0) Hok') HSp' Hpmawimpl
                with "Hsatp Htlb Htp Hpmp Hlb0 Hkinv").
    - (* O2prev: the previous tree already carried the bits -- memory untouched *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn pp2 pp1 (pte_set_ad pte_tramp ap dp) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) tp t tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) tp t tlbvec vpn pp2 pp1
                 (pte_set_ad pte_tramp ap dp) (pte_set_ad pte_tramp ap dp) Hmaps_p
                 (pte_set_ad_refl _) Hok2'). }
      iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tv' tp tc0
                Hmode Hasid Hppn (tlb_ok_pt2_canon_cur (mword_of_int 0) tp t tc0 tv'
                  (eq_sym Hcan0) Hok') HSp Hpmawimpl
                with "Hsatp Htlb Htp Hpmp Hlb0 Hkinv").
  Qed.

End Pt2TrampInstKcur.

(* userret's mirror: [Sc] (the USER table) is exclusive and abstract, exactly
   as [Sp] was in [pt2_tramp_fetch_habs_kcur]; the KERNEL table now plays the
   PREVIOUS slot and is opened from [kpt_inv] for the span of this one call.
   [rc] is the CURRENT (user) root; [kroot] is the shared kernel root -- two
   independent quantities, unlike [_kcur] where both coincided. *)
Section Pt2TrampInstKprev.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma pt2_tramp_fetch_habs_kprev (rc kroot : mword 44) (Sc : ptree -> Prop) :
    pt2_tramp_spec Sc ->
    (forall t, Sc t -> pt_base t = rc) ->
    forall (va pa : mword 64) (σ : mstate) (S : TsoMemPa.bytemap -> iProp Σ),
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
    (* A6.24's payer, threaded through the wrapper unchanged. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wnew) -∗
    (* ...AND A SECOND PAYER, AT THE KERNEL TIER.  These two wrappers walk
       BOTH trees: the previous/current user tree at the [Some ξ] tier and
       the SHARED KERNEL tree at the [None] tier ([kptree_own]).  The
       kernel tree's A/D write-back is a context-FREE ledger store (A6.20 --
       its owner is a bare [inv], so it can name no context), so it needs its
       own currency: [TsoCtx.ledger_store_win_ok] rather than
       [ctx_store_win_ok].  Two payers, one per tier, is the honest shape. *)
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.phys_ledger_word a (DfracOwn 1) wold ==∗
         gen_heap_interp (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         S (RiscvModelBytes.write_bytes m a 8 wnew) ∗
         TsoCtx.phys_ledger_word a (DfracOwn 1) wnew) -∗
    S σ.(mem) -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt2_kprev rc kroot Sc) ={⊤ ∖ ↑minstretN}=∗
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
      S σ'.(mem) ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      (kmap_at tramp_vpn tramp_ppn KP_rx ∗ tlb_inv_pt2_kprev rc kroot Sc).
  Proof.
    intros (Hsel_c & Hpres_c) Hbc va pa σ S Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "#Hpay #Hpayk Hsto Hri Hgh [#Hclaim Hinv]".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hclaimva".
    { rewrite Hvpn. iApply "Hclaim". }
    iDestruct (tlb_inv_pt2_kprev_open with "Hinv") as (satp0 tlbvec tp0 tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSc & %Hpmawimpl & Htc & Hpmp & #Hlb0 & #Hkinv)".
    pose proof (Hpmawimpl _ Lpma) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    destruct (Hsel_c tc HSc) as (uc2 & uc1 & ua & ud & Hmaps_c0).
    assert (Hmaps_c : ptree_maps tc (svpn_of va) uc2 uc1 (pte_set_ad pte_tramp ua ud))
      by (rewrite Hvpn; exact Hmaps_c0).
    assert (Hpres_c' : forall t' (a1 d1 : mword 1), Sc t' ->
              Sc (ptree_set_leaf t' (svpn_of va) (pte_set_ad pte_tramp a1 d1))).
    { intros t' a1 d1 HSct'. rewrite Hvpn. exact (Hpres_c t' a1 d1 HSct'). }
    assert (Hbase_c : pt_base tc = rc) by exact (Hbc tc HSc).
    set (vpn := svpn_of va) in *.
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
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HX).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Lpma) as Hpmar.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    assert (Hvarp : forall a d : mword 1, pte_pbmt0 (pte_set_ad pte_tramp a d))
      by (intros a d; exact (proj2 (proj2 (proj2 (tramp_variant a d))))).
    (* ---- open the shared KERNEL table (the PREVIOUS slot) for THIS
       instruction only ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hclaimva") as %HMlk.
    iDestruct (kpt_lb_agree tp0 t with "Hlb0 Hlbt") as %Hcan0.
    assert (Hok2' : tlb_ok_pt2 (mword_of_int 0) t tc tlbvec)
      by exact (tlb_ok_pt2_canon_prev (mword_of_int 0) tp0 t tc tlbvec Hcan0 Hok2).
    pose proof Hspec as (Hbase & Hmapspec).
    pose proof (Hmapspec vpn) as Hmapv. rewrite HMlk in Hmapv.
    destruct Hmapv as (kp2 & kp1 & ka & kd & Hmaps_p0).
    assert (Hlf : pte_set_ad (kpt_leaf_pte_of vpn (tramp_ppn, KP_rx)) ka kd
                = pte_set_ad pte_tramp ka kd)
      by (unfold kpt_leaf_pte_of; cbn [fst snd]; apply kperm_rx_tramp_variant).
    rewrite Hlf in Hmaps_p0.
    (* the PREVIOUS tree here is the KERNEL one ([None] tier) *)
    iDestruct (ptree_own_path_mem_at None σ (DfracOwn 1) t vpn kp2 kp1 _ Hmaps_p0
                 with "Hgh Ht") as %(_ & _ & Hsm0k).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) tc vpn uc2 uc1 _ Hmaps_c with "Hgh Htc")
      as %(Hsm2u & Hsm1u & Hsm0u).
    destruct (ptree2_translateAddr_cases (InstructionFetch tt) rc va pte_tramp pa satp0 t tc tlbvec
                kp2 kp1 uc2 uc1 ka kd ua ud σ
                (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
                Hcanon Hout Hvarp Hbase_c Hmaps_p0 Hmaps_c Hok2'
                Hsm2u Hsm1u Hsm0u Hsm0k
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Hsatpv Hmode Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (σ' & Htrans & Hshape).
    iAssert (pmp_config rc) with "[Hpc Hpa]" as "Hpmp".
    { iApply (pmp_config_intro rc pmpcfg0 pmpaddr00
                HA Hord HX HW HR Hcov with "Hpc Hpa"). }
    destruct Hshape as [-> | [-> | [ (a1 & d1 & ->) | [ (a1 & d1 & ->) | -> ] ]]].
    - (* O1: nothing moved *)
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists σ.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iSplit; [iPureIntro; exact HA' |].
      iSplit; [iPureIntro; exact Hord' |].
      iSplit; [iPureIntro; exact HX' |].
      iSplit; [iPureIntro; exact Hcov' |].
      iFrame "Hsto Hri Hgh Hclaim".
      iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tlbvec tp0 tc
                Hmode Hasid Hppn Hok2 HSc Hpmawimpl
                with "Hsatp Htlb Htc Hpmp Hlb0 Hkinv").
    - (* O2: TLB fill from the current (EXCLUSIVE, user) tree's walk --
         [t] untouched, so [kpt_inv] recloses unchanged *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn uc2 uc1 (pte_set_ad pte_tramp ua ud) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) t tc tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) t tc tlbvec vpn uc2 uc1
                 (pte_set_ad pte_tramp ua ud) (pte_set_ad pte_tramp ua ud) Hmaps_c
                 (pte_set_ad_refl _) Hok2'). }
      iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tv' tp0 tc
                Hmode Hasid Hppn (tlb_ok_pt2_canon_prev (mword_of_int 0) t tp0 tc tv'
                  (eq_sym Hcan0) Hok') HSc Hpmawimpl
                with "Hsatp Htlb Htc Hpmp Hlb0 Hkinv").
    - (* O3cur: the Svadu write-back into the CURRENT (EXCLUSIVE, user) tree
         -- an ordinary write against [Htc]; [t]/[kpt_inv] untouched *)
      set (p0u := pte_set_ad pte_tramp ua ud) in *.
      set (w' := pte_set_ad p0u a1 d1) in *.
      assert (Habs : w' = pte_set_ad pte_tramp a1 d1)
        by exact (pte_set_ad_absorb pte_tramp ua ud a1 d1).
      pose proof (tramp_variant a1 d1) as (Hv' & Hl' & Hn' & Hp').
      rewrite <- Habs in Hv', Hl', Hn', Hp'.
      iDestruct (ptree_own_path_upd (DfracOwn 1) tc vpn uc2 uc1 p0u Hmaps_c with "Htc")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpay" $! σ.(mem) (pt_addr0 uc1 vpn) p0u w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Htc".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn uc2 uc1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 uc1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (HSc' : Sc (ptree_set_leaf tc vpn w')).
      { rewrite Habs. exact (Hpres_c' tc a1 d1 HSc). }
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) t (ptree_set_leaf tc vpn w') tv').
      { apply (tlb_ok_pt2_fill_cur (mword_of_int 0) t (ptree_set_leaf tc vpn w')
                 tlbvec vpn uc2 uc1 w' w'
                 (ptree_set_leaf_maps_self tc vpn uc2 uc1 p0u w' Hmaps_c Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_cur (mword_of_int 0) t tc tlbvec vpn uc2 uc1 p0u a1 d1
                    Hmaps_c Hv' Hl' Hn' Hp' Hok2')). }
      iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tv' tp0 (ptree_set_leaf tc vpn w')
                Hmode Hasid Hppn (tlb_ok_pt2_canon_prev (mword_of_int 0) t tp0 _ tv'
                  (eq_sym Hcan0) Hok') HSc' Hpmawimpl
                with "Hsatp Htlb Htc Hpmp Hlb0 Hkinv").
    - (* O3prev: the Svadu write-back into the PREVIOUS (SHARED, kernel)
         tree -- opened from [kpt_inv], reclosed with the updated tree and
         the SAME snapshot (a write-back never moves the canonical form) *)
      set (p0k := pte_set_ad pte_tramp ka kd) in *.
      set (w' := pte_set_ad p0k a1 d1) in *.
      assert (Habs : w' = pte_set_ad pte_tramp a1 d1)
        by exact (pte_set_ad_absorb pte_tramp ka kd a1 d1).
      pose proof (tramp_variant a1 d1) as (Hv' & Hl' & Hn' & Hp').
      rewrite <- Habs in Hv', Hl', Hn', Hp'.
      iDestruct (ptree_own_path_upd_at None (DfracOwn 1) t vpn kp2 kp1 p0k Hmaps_p0 with "Ht")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod ("Hpayk" $! σ.(mem) (pt_addr0 kp1 vpn) p0k w' with "Hgh Hsto Hs0")
        as "(Hgh & Hsto & Hs0)".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Ht".
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn kp2 kp1 w' (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      assert (Hcan' : ptree_canon t = ptree_canon (ptree_set_leaf t vpn w')).
      { symmetry. exact (ptree_canon_set_leaf t vpn kp2 kp1 p0k a1 d1 Hmaps_p0). }
      iDestruct (kpt_lb_canon t (ptree_set_leaf t vpn w') Hcan' with "Hlbt") as "#Hlb'".
      assert (Hspec' : kpt_tree_spec_gen kroot M (ptree_set_leaf t vpn w')).
      { apply (kpt_tree_spec_gen_set_leaf kroot M t vpn (tramp_ppn, KP_rx) kp2 kp1
                 p0k a1 d1 Hspec Hmaps_p0 HMlk).
        exists ka, kd. symmetry. exact Hlf. }
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists (ptree_set_leaf t vpn w'), M. iFrame "Ht HM Hlb'".
        iPureIntro. exact Hspec'. }
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 kp1 vpn) 8 w') σ.(mdev))
                 tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) (ptree_set_leaf t vpn w') tc tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) (ptree_set_leaf t vpn w') tc
                 tlbvec vpn kp2 kp1 w' w'
                 (ptree_set_leaf_maps_self t vpn kp2 kp1 p0k w' Hmaps_p0 Hv' Hl' Hn' Hp')
                 (pte_set_ad_refl _)
                 (tlb_ok_pt2_set_leaf_prev (mword_of_int 0) t tc tlbvec vpn kp2 kp1 p0k a1 d1
                    Hmaps_p0 Hv' Hl' Hn' Hp' Hok2')). }
      iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tv' (ptree_set_leaf t vpn w') tc
                Hmode Hasid Hppn Hok' HSc Hpmawimpl
                with "Hsatp Htlb Htc Hpmp Hlb' Hkinv").
    - (* O2prev: the previous (kernel) tree already carried the bits --
         memory untouched, only the TLB entry refreshes *)
      set (tv' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (u_walk_entry vpn kp2 kp1 (pte_set_ad pte_tramp ka kd) (mword_of_int 0)))).
      iMod (reg_update σ.(sregs) tlb tlbvec tv' with "Hri Htlb") as "[Hri Htlb]".
      iMod ("Hclose" with "[Ht HM]") as "_".
      { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
      iModIntro. iExists (set_reg σ tlb tv').
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HA' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hord' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact HX' | vm_compute; reflexivity] |].
      iSplit; [iPureIntro; rewrite irrelevant_register_set; [exact Hcov' | vm_compute; reflexivity] |].
      iFrame "Hsto Hri Hgh Hclaim".
      assert (Hok' : tlb_ok_pt2 (mword_of_int 0) t tc tv').
      { apply (tlb_ok_pt2_fill_prev (mword_of_int 0) t tc tlbvec vpn kp2 kp1
                 (pte_set_ad pte_tramp ka kd) (pte_set_ad pte_tramp ka kd) Hmaps_p0
                 (pte_set_ad_refl _) Hok2'). }
      iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tv' tp0 tc
                Hmode Hasid Hppn (tlb_ok_pt2_canon_prev (mword_of_int 0) t tp0 tc tv'
                  (eq_sym Hcan0) Hok') HSc Hpmawimpl
                with "Hsatp Htlb Htc Hpmp Hlb0 Hkinv").
  Qed.

End Pt2TrampInstKprev.

(* ---- the two concrete spec instances: both page-table specs carry a
   trampoline clause and survive the trampoline A/D write-back ---------- *)


(* the M-indexed analogue (rwx-kmap §5f, stage C): the trampoline is now an
   ordinary M entry [(tramp_ppn, KP_rx)], so the generalized spec's own
   maps-clause at [tramp_vpn] gives the [pt2_tramp_spec] premises -- the
   class-KP_rx leaf [mk_pte tramp_ppn 0xCB] is [pte_tramp] modulo A/D
   ([kperm_rx_tramp_variant]).  Its [M !! tramp_vpn = Some (tramp_ppn, KP_rx)]
   premise is supplied by [kmap_at_lookup] against the window's auth from the
   caller's trampoline claim. *)
Lemma kpt_pt2_tramp_spec_gen (kroot : mword 44)
    (M : gmap (mword 27) (mword 44 * kperm)) :
  M !! tramp_vpn = Some (tramp_ppn, KP_rx) ->
  pt2_tramp_spec (kpt_tree_spec_gen kroot M).
Proof.
  intro Htr. split.
  - intros t (Hbase & Hall). pose proof (Hall tramp_vpn) as Hm. rewrite Htr in Hm.
    destruct Hm as (p2 & p1 & a0 & d0 & Hmaps).
    exists p2, p1, a0, d0.
    rewrite <- kperm_rx_tramp_variant. exact Hmaps.
  - intros t a1 d1 Hspec.
    pose proof Hspec as (Hbase & Hall). pose proof (Hall tramp_vpn) as Hm.
    rewrite Htr in Hm. destruct Hm as (p2 & p1 & a0 & d0 & Hmaps).
    assert (Heq : pte_set_ad pte_tramp a1 d1
                = pte_set_ad (kpt_leaf_pte_of tramp_vpn (tramp_ppn, KP_rx)) a1 d1).
    { unfold kpt_leaf_pte_of; cbn [fst snd]. symmetry. apply kperm_rx_tramp_variant. }
    rewrite Heq.
    rewrite <- (pte_set_ad_absorb (kpt_leaf_pte_of tramp_vpn (tramp_ppn, KP_rx)) a0 d0 a1 d1).
    apply (kpt_tree_spec_gen_set_leaf kroot M t tramp_vpn (tramp_ppn, KP_rx)
             p2 p1 _ a1 d1 Hspec Hmaps Htr).
    exists a0, d0. reflexivity.
Qed.

(* the parked kernel table + its mapping auth, threaded across the pt2
   window as one token (rwx-kmap §5f: "auth rides in pt_frame"). *)
Section KptFrame.
  Context `{!riscvGS Σ}.
  (* the KERNEL table is the CONTEXT-FREE tier (A6.20/A6.21): its owner is a
     bare [inv] shared by every S-mode thread, so the frame is [None]-tiered
     and this section needs no [CurCtx]. *)
  Definition kpt_frame (kroot : mword 44) : iProp Σ :=
    (∃ M, pt_frame_at None (kpt_tree_spec_gen kroot M) ∗ kmap_auth M)%I.
End KptFrame.

Lemma upt_pt2_tramp_spec (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  upt_map_wf um -> pt2_tramp_spec (upt_tree_spec uroot tfp um).
Proof.
  intros Hwf. split.
  - intros t Hspec. exact (proj1 (proj2 Hspec)).
  - intros t a1 d1 Hspec.
    destruct (proj1 (proj2 Hspec)) as (p2 & p1 & a0 & d0 & Hmaps).
    exact (upt_tree_spec_set_leaf uroot tfp um t tramp_vpn pte_tramp p2 p1 a0 d0 a1 d1
             Hwf Hspec (or_introl (conj eq_refl eq_refl)) Hmaps).
Qed.

Lemma upt_pt2_base (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  forall t, upt_tree_spec uroot tfp um t -> pt_base t = uroot.
Proof. intros t Hspec. exact (proj1 Hspec). Qed.

(* THE PER-NODE SWITCH-WINDOW STEP ENGINES LIVE IN [Pt2WalkPt.v].

   [wp_instr_pt2_tramp_kcur] / [_kprev] there are
   [TrampStepPt.wp_instr_tramp_pt] at [Res :=] the window's residue
   ([Pt2WalkPt.pt2_res_kcur] / [_kprev] -- these invariants with the satp /
   tlb / pmpcfg_n / pmpaddr_n cells taken out into the engine's frame, since
   the walk reads and writes them), with the fetch obligation
   [TrampStepPt.tramp_fetch_tr] in place of the whole-cycle [Habs] a
   [translateAddr] fupd over a whole sigma used to be (per-node stepping
   makes that unsound: other harts run between the walk's nodes).

   The exec-level [pt2_tramp_fetch_habs_kcur] / [_kprev] above are what the
   per-node walk had to reproduce, and their geometry plumbing carried over
   verbatim; only the interpreter changed.  What did NOT carry is the
   INTERPRETER's uniformity: these two invariants hold one OWNED table and
   one SHARED one, so neither of the two existing routes serves the whole
   walk -- see [Pt2WalkPt.v]'s header for how the arms split. *)
