(* Pt2Walk.v -- THE SLOT-LEVEL TLB PREMISE, and the walk lemmas restated
   over it.

   [KptTree.ptree_translateAddr_cases] and
   [PtWalkCert.goodmb_ptree_translateAddr] both take
   [tlb_ok_pt asid t tlbvec] -- "every resident entry was cached from [t]".
   That is TRUE for a single-table regime and FALSE inside the satp-switch
   window, where the TLB holds entries of MIXED provenance
   ([PtTree.tlb_ok_pt2]).  But neither proof uses more than the ONE slot the
   walked vpn hashes to: the whole of [tlb_ok_pt] is consumed by a single
   [Htlbok vpn ent Hslot].

   So both are restated here over [tlb_slot_pt] -- "the slot this vpn hashes
   to either fails the tag test outright, or holds THIS vpn's own entry off
   [t]" -- which is what a two-table window can supply for whichever tree the
   walk actually consults.  [tlb_slot_pt_of_ok] recovers the single-table
   instance; [tlb_slot_pt_of_cache] is the entry-level converter the window
   uses after splitting [tlb_ok_pt2]'s disjunction.

   NOTHING ELSE MOVES: the two proofs below are the originals with that one
   premise use rerouted, so they stay in step with them. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge HartMemRun HartMemAsm PtBytes.
Require Import MemAccessGen WpLoad WpMmodeLeafBase SmodePte CommonWalk PtAdBits
        Pt4kWalk PtreeType KptPt PtTree PtTreeAdue KptTree PtWalkCert.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. THE SLOT-LEVEL PREMISE.                                             *)
(* ===================================================================== *)

Definition tlb_slot_pt (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) : Prop :=
  forall ent : TLB_Entry,
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    (exists (q2 q1 q0 : mword 64) (a d : mword 1),
       ptree_maps t vpn q2 q1 q0 /\
       ent = u_walk_entry vpn q2 q1 (pte_set_ad q0 a d) asid) \/
    match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = false.

(* one entry's worth of [tlb_ok_pt]: an entry cached off [t] under a
   possibly-DIFFERENT vpn is rejected by the tag ([uwe_match_other]). *)
Lemma tlb_slot_pt_of_cache (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
  (forall ent : TLB_Entry,
     vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
     tlb_cache_of (mword_of_int 0) t vpn ent) ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof.
  intros Hc ent Hget.
  destruct (Hc ent Hget) as (vpn0 & q2 & q1 & q0 & a & d & Hmaps & _ & ->).
  destruct (decide (vpn0 = vpn)) as [-> | Hne].
  - left. exists q2, q1, q0, a, d. split; [exact Hmaps | reflexivity].
  - right. exact (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a d)
                    (mword_of_int 0) Hne).
Qed.

Lemma tlb_slot_pt_of_ok (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
  tlb_ok_pt (mword_of_int 0) t tlbvec ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof. intros Hok. exact (tlb_slot_pt_of_cache t tlbvec vpn (Hok vpn)). Qed.

(* the FOREIGN-TAG half on its own: whatever the slot holds, it does not
   serve this vpn.  This is the shape the switch window hands the walked
   tree for an entry cached off the OTHER table. *)
Lemma tlb_slot_pt_nomatch (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
  (forall ent : TLB_Entry,
     vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
     match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false) ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof. intros H ent Hget. right. exact (H ent Hget). Qed.

(* the slot holds THIS vpn's own entry off [t] *)
Lemma tlb_slot_pt_hit (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27)
    (q2 q1 q0 : mword 64) (a d : mword 1) :
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
    = Some (u_walk_entry vpn q2 q1 (pte_set_ad q0 a d) (mword_of_int 0)) ->
  ptree_maps t vpn q2 q1 q0 ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof.
  intros Hslot Hmaps ent Hget. rewrite Hslot in Hget. injection Hget as <-.
  left. exists q2, q1, q0, a, d. split; [exact Hmaps | reflexivity].
Qed.


(* the slot's status, at ONE entry: the three shapes a two-table window
   splits [tlb_ok_pt2] into. *)
Lemma tlb_slot_pt_none (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) :
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof. intros H e He. rewrite H in He. discriminate. Qed.

Lemma tlb_slot_pt_one (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) (ent : TLB_Entry) :
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  tlb_cache_of (mword_of_int 0) t vpn ent ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof.
  intros Hs Hc. apply tlb_slot_pt_of_cache.
  intros e He. rewrite Hs in He. injection He as <-. exact Hc.
Qed.

Lemma tlb_slot_pt_one_nomatch (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) (ent : TLB_Entry) :
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false ->
  tlb_slot_pt (mword_of_int 0) t tlbvec vpn.
Proof.
  intros Hs Hm e He. rewrite Hs in He. injection He as <-. right. exact Hm.
Qed.

(* the slot POSITIVELY holds this vpn's own entry off [t] -- the premise of
   the hit-only walk lemmas, where [t] is not the tree the walk starts from *)
Definition tlb_slot_hit_pt (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27) : Prop :=
  exists (q2 q1 q0 : mword 64) (a d : mword 1),
    ptree_maps t vpn q2 q1 q0 /\
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn q2 q1 (pte_set_ad q0 a d) asid).

(* ===================================================================== *)
(* 2. THE EXEC-LEVEL CASE ANALYSIS, over the slot premise.                *)
(*    [KptTree.ptree_translateAddr_cases] verbatim, with [tlb_ok_pt]      *)
(*    weakened to [tlb_slot_pt].                                          *)
(* ===================================================================== *)

Section Pt2ExecSlot.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma ptree_translateAddr_cases_slot (root_ppn : mword 44) (va w pa satp0 : mword 64)
        (t : ptree) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_slot_pt (mword_of_int 0) t tlbvec vpn ->
    pt_slot_mem σ (pt_addr2 t vpn) p2 ->
    pt_slot_mem σ (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem σ (pt_addr0 p1 vpn) p0 ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    exec (translationMode p) σ = Some (Sv39, σ) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
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
                                  (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8
                                 (pte_set_ad p0 a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0)))))).
  Proof.
    intros vpn p0 Hchk Hcanon Hout Hvarp Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
           Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatp Hppn Hasid Htlb
           HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    (* the three PTE reads, at the walk's canonical slot spellings *)
    assert (Hsm2' : pt_slot_mem σ (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hsm1' : pt_slot_mem σ (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) p1)
      by exact Hsm1.
    assert (Hsm0' : pt_slot_mem σ (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) p0)
      by exact Hsm0.
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2'))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1'))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0'))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot σ _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot σ _ p1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot σ _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    pose proof (pt_read_pte_exclusive_slot σ _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    (* identity geometry *)
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - (* resident entry *)
      destruct (Htlbok ent Hslot)
        as [(q2 & q1 & qp0 & a' & d' & Hm0 & ->) | Hnm].
      + (* HIT on this vpn's own (A/D-variant) entry *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc p mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d')).
        { assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. exact Hid. }
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* the CACHED word wants A/D bits.  Under the fork the write-back is
             an atomic read-check-write, so what is recomputed and written is
             derived from the word in MEMORY ([p0]), not from the cached copy
             -- and memory may already have the bits the cache lacks.  Split. *)
          assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
          { exists a0, d0. rewrite pte_set_ad_absorb.
            unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
          destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back (O3) *)
             destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 p1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec (write_pte_conditional
                        (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                        (p0' : mword 64)) σ
                      = Some (Ok true, MState σ.(sregs)
                                 (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8 p0') σ.(mdev)))
               by exact (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw σ
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             eexists. split.
             { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_upd acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm Hwr eq_refl). }
             right. right. exists a1, d1.
             rewrite <- Hq. rewrite Htlb. reflexivity.
          -- (* memory ALREADY has them: nothing is written, the stale entry is
                merely refreshed with the memory word (O2) *)
             eexists. split.
             { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_refresh acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm). }
             right. left. rewrite Htlb. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          eexists. split.
          { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc p mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlb Hslot
                      Hnm).
        destruct (ptree_translate_miss_core acc p root_ppn va w tlbvec p2 p1 a0 d0 σ Hchk
                    Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                    Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlb Hlk
                    HA Hord HW Hcov Hpmaw)
          as (σ' & Htr & Hshape).
        exists σ'. split.
        { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (p0 : mword 64))) : mword 44))
                   satp0 va pa σ σ'
                   Heff Hss Hcp Htm Hsatp Hppn Hasid
                   Hcanon eq_refl Htr Hid). }
        destruct Hshape as [Ho2 | Ho3]; [right; left; exact Ho2 | right; right; exact Ho3].
    - (* empty slot: the walk runs *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlb Hslot).
      destruct (ptree_translate_miss_core acc p root_ppn va w tlbvec p2 p1 a0 d0 σ Hchk
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlb Hlk
                  HA Hord HW Hcov Hpmaw)
        as (σ' & Htr & Hshape).
      exists σ'. split.
      { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va pa σ σ'
                 Heff Hss Hcp Htm Hsatp Hppn Hasid
                 Hcanon eq_refl Htr Hid). }
      destruct Hshape as [Ho2 | Ho3]; [right; left; exact Ho2 | right; right; exact Ho3].
  Qed.


  (* THE HIT ARM ON ITS OWN.  When the slot already holds THIS vpn's entry off
     [t], the walk never runs: the only memory touched is [t]'s own leaf slot,
     reached through the entry's cached pteAddr.  So [t] need NOT be the tree
     [satp] points at -- which is what the switch window's PREVIOUS table is:
     owned, mapped, and not the root of the walk. *)
  Lemma ptree_translateAddr_hit_slot (root_ppn : mword 44) (va w pa satp0 : mword 64)
        (t : ptree) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 a' d' : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    ptree_maps t vpn p2 p1 p0 ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)) ->
    pt_slot_mem σ (pt_addr0 p1 vpn) p0 ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    exec (translationMode p) σ = Some (Sv39, σ) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
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
                                    (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8
                                 (pte_set_ad p0 a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0)))))).
  Proof.
    intros vpn p0 Hchk Hcanon Hout Hvarp Hmaps Hslot Hsm0
           Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatp Hppn Hasid Htlb
           HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    assert (Hsm0' : pt_slot_mem σ (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) p0)
      by exact Hsm0.
    destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0'))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_exclusive_slot σ _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc p mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d')).
        { assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. exact Hid. }
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* the CACHED word wants A/D bits.  Under the fork the write-back is
             an atomic read-check-write, so what is recomputed and written is
             derived from the word in MEMORY ([p0]), not from the cached copy
             -- and memory may already have the bits the cache lacks.  Split. *)
          assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
          { exists a0, d0. rewrite pte_set_ad_absorb.
            unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
          destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back (O3) *)
             destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 p1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec (write_pte_conditional
                        (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                        (p0' : mword 64)) σ
                      = Some (Ok true, MState σ.(sregs)
                                 (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8 p0') σ.(mdev)))
               by exact (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw σ
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             eexists. split.
             { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_upd acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm Hwr eq_refl). }
             right. right. exists a1, d1.
             rewrite <- Hq. rewrite Htlb. reflexivity.
          -- (* memory ALREADY has them: nothing is written, the stale entry is
                merely refreshed with the memory word (O2) *)
             eexists. split.
             { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa σ _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               unfold translate.
               rewrite (exec_bind_Some _ _ _ _ _
                          (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               cbn match.
               apply (exec_translate_TLB_hit_pt_refresh acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) σ
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                        Hvarm Hupm). }
             right. left. rewrite Htlb. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          eexists. split.
          { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc p mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
  Qed.

End Pt2ExecSlot.

(* =====================================================================  *)
(* 3. THE GOODMB CERTIFICATE, over the slot premise.                       *)
(*    [PtWalkCert.goodmb_ptree_translateAddr] verbatim, with [tlb_ok_pt]   *)
(*    weakened to [tlb_slot_pt].                                           *)
(* =====================================================================  *)

Section Pt2CertSlot.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege).
  Hypothesis HDmi : Dr misa = true.
  Hypothesis HDme : Dr menvcfg = true.
  Hypothesis HDms : Dr mstatus = true.
  Hypothesis HDcp : Dr cur_privilege = true.
  Hypothesis HDsatp : Dr satp = true.
  Hypothesis HDt : Dr tlb = true.
  Hypothesis HWt : Dw tlb = true.
  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.

  (* THE WHOLE OF [translateAddr] OVER AN OWNED PTREE, certified.  Same
     five-way split as [KptTree.ptree_translateAddr_cases]. *)
  (* the shared miss path, certified (PtWalkCert's own, re-proved here so
     the slot-level statement below can call it inside this section) *)
  Lemma gm_pt2_miss_core (root_ppn : mword 44) (va w : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (p2 p1 : mword 64)
      (a0 d0 : mword 1) (mxr do_sum : bool) (sg : mstate) (mm : pamap) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr0 do_sum0 : bool),
       pte_check_ok acc pv mxr0 do_sum0 (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr0 do_sum0 : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr0 do_sum0
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 -> pte_no_napot p0 ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                   (ext_bits_of_PTE p2)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                   (ext_bits_of_PTE p1)) s0 = true) ->
    (forall (a d : mword 1) (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true) ->
    pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    bytes_owned mm (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8 = true ->
    bytes_owned mm (pt_addr1 p2 vpn) 8 = true ->
    bytes_owned mm (pt_addr0 p1 vpn) 8 = true ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    goodmb Dr Dw (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc pv mxr do_sum tt)
      sg mm = true.
  Proof.
    intros vpn p0 Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
           Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
           Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    (* the three slot reads, exec side and certificate side *)
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) (pt_slot_ram_access _ _ _ Hsm2))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (pt_addr1 p2 vpn) (pt_slot_ram_access _ _ _ Hsm1))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot sg _ p2 region2 Hsm2 HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    pose proof (pt_read_pte_exclusive_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p2 region2
                  Hsm2 Hown2 HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2g.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p1 region1
                  Hsm1 Hown1 HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1g.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0g.
    pose proof (goodmb_read_pte_exclusive_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrdxg.
    unfold translate.
    gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlk.
    cbn match. try rewrite <- Htlb.
    destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hup.
    - (* the walk writes the A/D-updated leaf back *)
      destruct (Hpmaw (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
        as (regionw & Hmw & Hww).
      pose proof (goodmb_write_pte_conditional_slot Dr Dw HDc HDa HDp HDh sg mm
                    _ p0 p0' regionw Hsm0 Hown0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwrg.
      destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
      pose proof (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                    Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwr.
      exact (goodmb_translate_TLB_miss_pt_upd Dr Dw acc pv mxr do_sum HDt HWt HDme
               vpn root_ppn p2 p1 p0 p0' MENVCFG_S (mword_of_int 0) _ sg mm
               HDmi Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
               Hg2 Hg1 (Hg0 a0 d0) (Hgchk a0 d0 mxr do_sum) Hup
               Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hrdx Hrdxg
               Hmisa Hmenv HPBMTE HADUE Hwr Hwrg eq_refl).
    - (* clean fill *)
      assert (Hupd : update_PTE_Bits (autocast (T := mword) p0 : mword 64) acc = None)
        by exact Hup.
      exact (goodmb_translate_TLB_miss_user vpn root_ppn p2 p1 p0 acc pv mxr do_sum
               Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap
               Hg1 Hg2 (Hg0 a0 d0) (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
               (mword_of_int 0) MENVCFG_S sg mm HDt HWt Hmisa Hupd
               Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE).
  Qed.


  Lemma goodmb_ptree_translateAddr_slot (root_ppn : mword 44) (t : ptree)
      (va w pa satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (p2 p1 : mword 64) (a0 d0 : mword 1) (sg : mstate) (mm : pamap) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc pv mxr do_sum (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_slot_pt (mword_of_int 0) t tlbvec vpn ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                   (ext_bits_of_PTE p2)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                   (ext_bits_of_PTE p1)) s0 = true) ->
    (forall (a d : mword 1) (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true) ->
    pt_slot_mem sg (pt_addr2 t vpn) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    bytes_owned mm (pt_addr2 t vpn) 8 = true ->
    bytes_owned mm (pt_addr1 p2 vpn) 8 = true ->
    bytes_owned mm (pt_addr0 p1 vpn) 8 = true ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = pv ->
    exec (translationMode pv) sg = Some (Sv39, sg) ->
    goodb Dr (translationMode pv) sg = true ->
    exec (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg
      = Some (pv, sg) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg = true ->
    exec (is_shadow_stack_access acc) sg = Some (false, sg) ->
    goodb Dr (is_shadow_stack_access acc) sg = true ->
    register_lookup satp sg.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) sg mm = true.
  Proof.
    intros vpn p0 Hchk Hgchk Hcanon Hout Hvarp Hbase Hmaps Htlbok Hg2 Hg1 Hg0
           Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
           Hmisa Hmenv Hhtif Hcp Htm Htmg Heff Heffg Hss Hssg
           Hsatp Hppn Hasid Htlb HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    assert (Hsm2' : pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hown2' : bytes_owned mm (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8 = true).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hown2. exact Hown2. }
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
                (pt_slot_ram_access _ _ _ Hsm2')) as (region2 & Hm2 & Hs2).
    destruct (Hpmar (pt_addr1 p2 vpn) (pt_slot_ram_access _ _ _ Hsm1))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_exclusive_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    pose proof (goodmb_read_pte_exclusive_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrdxg.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Htlbok ent Hslot)
        as [(q2 & q1 & qp0 & a' & d' & Hm0 & ->) | Hnm].
      + (* HIT on this vpn's own entry *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
          by exact (pte_set_ad_absorb w a0 d0 a' d').
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc pv mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum. rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hchkcg : forall (mxr do_sum : bool) (Db : register -> bool) s0,
                  goodb Db (check_PTE_permission acc pv mxr do_sum
                              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad p0 a' d') 7 0))
                              (ext_bits_of_PTE (pte_set_ad p0 a' d')) tt) s0 = true).
        { intros mxr do_sum Db s0. rewrite Habs. exact (Hgchk a' d' mxr do_sum Db s0). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d'))
          by (rewrite Habs; apply Hvarp).
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
        assert (Hlkh : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg
                       = Some (Some (tlb_hash (__id 39) vpn,
                                     u_walk_entry vpn p2 p1 (pte_set_ad p0 a' d')
                                       (mword_of_int 0)), sg))
          by exact (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlb Hslot
                      (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d'))).
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             destruct (Hpmaw (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
               as (regionw & Hmw & Hww).
             pose proof (goodmb_write_pte_conditional_slot Dr Dw HDc HDa HDp HDh sg mm
                           _ p0 p0' regionw Hsm0 Hown0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwrg.
             pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             pose proof (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwr.
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_upd acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm Hwr eq_refl).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_upd Dr Dw acc pv mxr do_sum HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm Hwr Hwrg eq_refl).
          -- (* memory ALREADY has them: no write, the entry is refreshed *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_refresh acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_refresh Dr Dw acc pv mxr do_sum
                         HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm).
        * (* hit, A/D already sufficient *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                   vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                   satp0 va sg mm
                   Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
          -- exists sg. intros mxr do_sum. unfold translate.
             rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
             apply (exec_translate_TLB_hit_pt acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg (Hchkc mxr do_sum) Hupq' Hpbc).
          -- intros mxr do_sum. unfold translate.
             gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
             cbn match.
             apply (goodmb_translate_TLB_hit_pt Dr Dw acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg mm (Hchkc mxr do_sum)
                      (fun s0 => Hchkcg mxr do_sum Dr s0) Hupq' Hpbc).
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec sg Htlb Hslot
                      Hnm).
        destruct (ptree_translate_miss_core acc pv root_ppn va w tlbvec p2 p1 a0 d0 sg Hchk
                    Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                    (pt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif)
                    (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif)
                    (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
                    Hrdx Hmisa Hmenv Hhtif Htlb Hlk HA Hord HW Hcov Hpmaw)
          as (sg' & Htr & _).
        apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                 vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va sg mm
                 Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
                 (ex_intro _ sg' Htr)).
        intros mxr do_sum.
        exact (gm_pt2_miss_core root_ppn va w tlbvec p2 p1 a0 d0
                 mxr do_sum sg mm Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
                 Hsm2' Hsm1 Hsm0 Hown2' Hown1 Hown0
                 Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw).
    - (* empty slot: the walk runs *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec sg Htlb Hslot).
      destruct (ptree_translate_miss_core acc pv root_ppn va w tlbvec p2 p1 a0 d0 sg Hchk
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  (pt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif)
                  (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif)
                  (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
                  Hrdx Hmisa Hmenv Hhtif Htlb Hlk HA Hord HW Hcov Hpmaw)
        as (sg' & Htr & _).
      apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
               vpn root_ppn
               (autocast (T := mword) ((autocast (T := mword)
                  (PPN_of_PTE (p0 : mword 64))) : mword 44))
               satp0 va sg mm
               Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
               (ex_intro _ sg' Htr)).
      intros mxr do_sum.
      exact (gm_pt2_miss_core root_ppn va w tlbvec p2 p1 a0 d0
               mxr do_sum sg mm Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
               Hsm2' Hsm1 Hsm0 Hown2' Hown1 Hown0
               Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw).
  Qed.


  (* the HIT arm's certificate, over the same reduced premises *)
  Lemma goodmb_ptree_translateAddr_hit_slot (root_ppn : mword 44) (t : ptree)
      (va w pa satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (p2 p1 : mword 64) (a0 d0 a' d' : mword 1) (sg : mstate) (mm : pamap) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc pv mxr do_sum (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    ptree_maps t vpn p2 p1 p0 ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)) ->
    (forall (a d : mword 1) (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true) ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    bytes_owned mm (pt_addr0 p1 vpn) 8 = true ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = pv ->
    exec (translationMode pv) sg = Some (Sv39, sg) ->
    goodb Dr (translationMode pv) sg = true ->
    exec (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg
      = Some (pv, sg) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg = true ->
    exec (is_shadow_stack_access acc) sg = Some (false, sg) ->
    goodb Dr (is_shadow_stack_access acc) sg = true ->
    register_lookup satp sg.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) sg mm = true.
  Proof.
    intros vpn p0 Hchk Hgchk Hcanon Hout Hvarp Hmaps Hslot Hg0 Hsm0 Hown0
           Hmisa Hmenv Hhtif Hcp Htm Htmg Heff Heffg Hss Hssg
           Hsatp Hppn Hasid Htlb HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    destruct (Hpmar (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_exclusive_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    pose proof (goodmb_read_pte_exclusive_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrdxg.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
        assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
          by exact (pte_set_ad_absorb w a0 d0 a' d').
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc pv mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum. rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hchkcg : forall (mxr do_sum : bool) (Db : register -> bool) s0,
                  goodb Db (check_PTE_permission acc pv mxr do_sum
                              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad p0 a' d') 7 0))
                              (ext_bits_of_PTE (pte_set_ad p0 a' d')) tt) s0 = true).
        { intros mxr do_sum Db s0. rewrite Habs. exact (Hgchk a' d' mxr do_sum Db s0). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d'))
          by (rewrite Habs; apply Hvarp).
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
        assert (Hlkh : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg
                       = Some (Some (tlb_hash (__id 39) vpn,
                                     u_walk_entry vpn p2 p1 (pte_set_ad p0 a' d')
                                       (mword_of_int 0)), sg))
          by exact (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlb Hslot
                      (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d'))).
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             destruct (Hpmaw (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
               as (regionw & Hmw & Hww).
             pose proof (goodmb_write_pte_conditional_slot Dr Dw HDc HDa HDp HDh sg mm
                           _ p0 p0' regionw Hsm0 Hown0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwrg.
             pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             pose proof (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwr.
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_upd acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm Hwr eq_refl).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_upd Dr Dw acc pv mxr do_sum HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm Hwr Hwrg eq_refl).
          -- (* memory ALREADY has them: no write, the entry is refreshed *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_refresh acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_refresh Dr Dw acc pv mxr do_sum
                         HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm).
        * (* hit, A/D already sufficient *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                   vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                   satp0 va sg mm
                   Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
          -- exists sg. intros mxr do_sum. unfold translate.
             rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
             apply (exec_translate_TLB_hit_pt acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg (Hchkc mxr do_sum) Hupq' Hpbc).
          -- intros mxr do_sum. unfold translate.
             gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
             cbn match.
             apply (goodmb_translate_TLB_hit_pt Dr Dw acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg mm (Hchkc mxr do_sum)
                      (fun s0 => Hchkcg mxr do_sum Dr s0) Hupq' Hpbc).
  Qed.

End Pt2CertSlot.
