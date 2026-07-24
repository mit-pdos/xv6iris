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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import KptExecMap.
Require Import Pt4kWalk.
Require Import SmodeCore KptTree UptTree TrampStepPt.
Require Import KMap.
Require Import Riscv.rv64d_types Riscv.rv64d.
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
                            (Some (u_walk_entry vpn pp2 pp1 (pte_set_ad p0p a1 d1) (mword_of_int 0)))))).
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
    destruct (Hpmar (u_pte_addr rc (subrange_vec_dec vpn 26 18)))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (u_pte_addr (u_next_base pc2) (subrange_vec_dec vpn 17 9)))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (u_pte_addr (u_next_base pc1) (subrange_vec_dec vpn 8 0)))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot σ _ pc2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot σ _ pc1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot σ _ p0c region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
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
                  Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
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
        destruct (update_PTE_Bits (pte_set_ad p0p a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* hit + write-back through the cached pteAddr: the PREVIOUS
             tree's L0 slot (O3prev) *)
          destruct Hsm0p as (Hbytes0 & Hram0 & Hram0' & Hal0).
          destruct (Hpmaw (pt_addr0 pp1 vpn)) as (regionw & Hmw & Hww).
          assert (Hwr : exec (write_pte
                     (Physaddr (u_pte_addr (u_next_base pp1) (subrange_vec_dec vpn 8 0))) 8
                     (q0' : mword 64)) σ
                   = Some (Ok true, MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 pp1 vpn) 8 q0') σ.(mdev)))
            by exact (exec_write_pte_ram (pt_addr0 pp1 vpn) q0' regionw σ
                        Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
          destruct (update_PTE_Bits_set_ad _ _ _ Hupq) as (a1 & d1 & Hq).
          assert (Hq' : q0' = pte_set_ad p0p a1 d1)
            by exact (eq_trans Hq (pte_set_ad_absorb p0p a' d' a1 d1)).
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
                     vpn pp2 pp1 (pte_set_ad p0p a' d') q0' MENVCFG_S (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) _ σ
                     (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE Hwr eq_refl). }
          right. right. right. exists a1, d1.
          rewrite <- Hq'. rewrite Htlb. reflexivity.
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
        destruct (update_PTE_Bits (pte_set_ad p0c a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* hit + write-back into the CURRENT tree's L0 slot (O3cur) *)
          destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
          destruct (Hpmaw (pt_addr0 pc1 vpn)) as (regionw & Hmw & Hww).
          assert (Hwr : exec (write_pte
                     (Physaddr (u_pte_addr (u_next_base pc1) (subrange_vec_dec vpn 8 0))) 8
                     (q0' : mword 64)) σ
                   = Some (Ok true, MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 pc1 vpn) 8 q0') σ.(mdev)))
            by exact (exec_write_pte_ram (pt_addr0 pc1 vpn) q0' regionw σ
                        Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
          destruct (update_PTE_Bits_set_ad _ _ _ Hupq) as (a1 & d1 & Hq).
          assert (Hq' : q0' = pte_set_ad p0c a1 d1)
            by exact (eq_trans Hq (pte_set_ad_absorb p0c a' d' a1 d1)).
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
                     vpn pc2 pc1 (pte_set_ad p0c a' d') q0' MENVCFG_S (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) _ σ
                     (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE Hwr eq_refl). }
          right. right. left. exists a1, d1.
          rewrite <- Hq'. rewrite Htlb. reflexivity.
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
  Context `{CID : CpuId}.

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
(* §3 THE TWO-TABLE INVARIANT ABSORBS TRANSLATION.  Premises: BOTH specs  *)
(*    force a mapping of [va]'s vpn to an A/D variant of the same         *)
(*    canonical leaf [w], and both specs survive an A/D write-back to     *)
(*    that vpn.  Whatever the machine does -- nothing, a fill from the    *)
(*    current walk, or a Svadu write-back into EITHER tree -- the         *)
(*    invariant re-establishes.                                           *)
(* ===================================================================== *)

Section Pt2TranslateIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma tlb_inv_pt2_translateAddr (rc : mword 44) (Sp Sc : ptree -> Prop)
      (w va pa : mword 64) (σ : mstate) :
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
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt2 rc Sp Sc ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt2 rc Sp Sc.
  Proof.
    intros Hchk Hvar Hcanon Hout Hsel_p Hsel_c Hbase_c Hpres_p Hpres_c
           Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0 tlbvec tp tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSp & %HSc & %Hpmawimpl & Htp & Htc & Hpmp)".
    pose proof (Hpmawimpl _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
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
    pose proof (Hpmarimpl _ Hall) as Hpmar.
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
                HA Hord Hpmarimpl HX HW HR Hcov with "Hpc Hpa"). }
    destruct Hshape as [-> | [-> | [ (a1 & d1 & ->) | (a1 & d1 & ->) ]]].
    - (* O1: nothing moved *)
      iModIntro. iExists σ.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iFrame "Hri Hgh".
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
      iFrame "Hri Hgh".
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
      iMod (phys_word_pointsto_write σ.(mem) (pt_addr0 pc1 vpn) p0c w' with "Hgh Hs0")
        as "[Hgh Hs0]".
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
      iFrame "Hri Hgh".
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
      iMod (phys_word_pointsto_write σ.(mem) (pt_addr0 pp1 vpn) p0p w' with "Hgh Hs0")
        as "[Hgh Hs0]".
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
      iFrame "Hri Hgh".
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
  Context `{CID : CpuId}.

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
    ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt2 rc Sp Sc ==∗
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
           va pa σ Hcanon Hvpn Hid Lmisa Lmenv Lhtif Lpriv LSXL Lpma.
    iIntros "Hri Hgh Hinv".
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    iMod (tlb_inv_pt2_translateAddr (InstructionFetch tt) rc Sp Sc pte_tramp va pa σ
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
            Lpma with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct (tlb_inv_pt2_open with "Hinv") as (satp1 tlbvec1 tp1 tc1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %HSp1 & %HSc1 & %Hpmawimpl & Htp & Htc & Hpmp)".
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
    iApply (tlb_inv_pt2_intro rc Sp Sc satp1 tlbvec1 tp1 tc1
              Hmode Hasid Hppn Htlbok HSp1 HSc1 Hpmawimpl
              with "Hsatp Htlb Htp Htc").
    iApply (pmp_config_intro rc pmpcfg0 pmpaddr00
              HA Hord Hpmarimpl HX HW HR Hcov with "Hpc0 Hpa0").
  Qed.

End Pt2TrampInst.

(* ---- the two concrete spec instances: both page-table specs carry a
   trampoline clause and survive the trampoline A/D write-back ---------- *)


(* the M-indexed analogue (rwx-kmap §5f): the generalized spec survives the
   trampoline A/D write-back; its [M !! tramp_vpn = None] premise is supplied
   from [kmap_auth]'s wf conjunct at the use site. *)
Lemma kpt_pt2_tramp_spec_gen (kroot : mword 44)
    (M : gmap (mword 27) (mword 44 * kperm)) :
  M !! tramp_vpn = None -> pt2_tramp_spec (kpt_tree_spec_gen kroot M).
Proof.
  intro Htn. split.
  - intros t Hspec. exact (proj1 (proj2 (proj2 Hspec))).
  - intros t a1 d1 Hspec.
    destruct (proj1 (proj2 (proj2 Hspec))) as (p2 & p1 & a0 & d0 & Hmaps).
    rewrite <- (pte_set_ad_absorb pte_tramp a0 d0 a1 d1).
    exact (kpt_tree_spec_gen_set_leaf_tramp kroot M t p2 p1 _ a1 d1 Hspec Hmaps Htn
             (ex_intro _ a0 (ex_intro _ d0 eq_refl))).
Qed.

(* the parked kernel table + its mapping auth, threaded across the pt2
   window as one token (rwx-kmap §5f: "auth rides in pt_frame"). *)
Section KptFrame.
  Context `{!riscvGS Σ}.
  Definition kpt_frame (kroot : mword 44) : iProp Σ :=
    (∃ M, pt_frame (kpt_tree_spec_gen kroot M) ∗ kmap_auth M)%I.
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

(* the instantiated switch-window trampoline fetch + step engine *)
Section Pt2TrampEngines.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.


  Definition wp_instr_pt2_tramp (rc : mword 44) (Sp Sc : ptree -> Prop)
      (HSp : pt2_tramp_spec Sp) (HSc : pt2_tramp_spec Sc)
      (Hbc : forall t, Sc t -> pt_base t = rc) :=
    wp_instr_tramp_pt (tlb_inv_pt2 rc Sp Sc) (pt2_tramp_fetch_habs rc Sp Sc HSp HSc Hbc).

End Pt2TrampEngines.
