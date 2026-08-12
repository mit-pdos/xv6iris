(** * WeakKptStale.v — the RACY absorption theorem: the TLB-miss walk
    certified at the stale mirror  (walk-bridge §8.3 item 5)

    [WeakKpt.wtlb_res_pt_translateAddr_at]'s twin over
    [WeakWalkStale.exec_stale_translateAddr_pt_miss_cases]: the same
    invariant opening, the same collapse conjuncts, but the translation
    stated at [WeakStale.exec_stale la 8 pv] — the mirror in which the
    walk's PLAIN leaf read returns the racy variant [pv] while the CAS's
    exclusive re-read returns the coherence-latest word — for EVERY
    admissible variant at once (the peel producer's family), plus the SIXTH
    outcome disjunct (gate fires on the racy word, the fresh one needs
    nothing: four reads, NO write).

    THREE deltas against the [exec_eff] original, and nothing else moves:

      - the headline [exec] fact becomes a FAMILY — ∀ (av dv) with
        [pte_ad_le (pte_set_ad w0 av dv) lw], a run of the translation at
        [exec_stale la 8 (pte_set_ad w0 av dv)].  The ghost arm (log
        unchanged vs appended) is family-UNIFORM: the write-back event is
        decided by the LATEST word alone
        ([WeakVariant.update_PTE_Bits_fires_mono] — a variant admissibly
        below a latest word that needs bits also needs them), which is what
        lets one fupd commit one ghost outcome for the whole family;
      - the read-only arm's trace enumeration grows by ONE disjunct — the
        sixth outcome [walk ++ CAS-read];
      - the registers come back as a WAND keyed on the actual family
        member: [exec_stale] is a function, so the caller's equation for
        the member that actually ran pins [sg'] against the stored family
        analysis, and the wand advances [reg_interp] to [sregs sg'] and
        re-establishes the residue ([PtTree.tlb_ok_pt_fill] holds for an
        entry carrying ANY A/D variant of the mapped leaf).

    Design: claude-notes/design/weak-memory-walk-bridge.md §8. *)
From Stdlib Require Import ZArith Bool Lia Wf_nat.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakFetchEff WeakLeafEffCommon WeakLeafEff8.
Require Import WeakStore WeakRacy WeakWord8.
Require Import WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree UserPtTree PtTreeAdue.
Require Import KptPt KMap SmodeCore KptTree KptGhost KptShare.
Require Import WeakWalkEff WeakUpdEff.
Require Import WeakVariant.
Require Import WeakKpt.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. Slot geometry: two slots holding a POINTER and a LEAF are
    disjoint

    The transports ([WeakWalkStale.pt_slot_mem_mpatch_disj]) want the two
    pointer slots [racc_disj] from the leaf window.  That is derivable, not
    a new premise: slots are 8-aligned, so two slots either coincide or are
    disjoint — and coincidence forces the two slot WORDS equal (a word is
    its eight bytes), which [pte_ptr] vs [pte_leaf] refutes. *)

Lemma pt_slot_mem_acc_wf (sg : mstate) (a : Arch.pa) (v : mword 64) :
  pt_slot_mem sg a v -> acc_wf a 8.
Proof.
  intros (_ & Hram & Hram7 & Hal).
  exact (wslot_geom_acc_wf a (conj Hram (conj Hram7 Hal))).
Qed.

Lemma pt_slot_mem_det (sg : mstate) (a : Arch.pa) (v v' : mword 64) :
  pt_slot_mem sg a v -> pt_slot_mem sg a v' -> v = v'.
Proof.
  intros (Hb & _) (Hb' & _).
  apply (bv_eq_of_bytes (n := 8%N)).
  intros j Hj. specialize (Hb j Hj). specialize (Hb' j Hj).
  rewrite Hb in Hb'. injection Hb' as Hb'. apply bv_eq. exact Hb'.
Qed.

Lemma pt_slot_racc_disj (sg : mstate) (la a : Arch.pa) (lv v : mword 64) :
  pt_slot_mem sg la lv -> pt_slot_mem sg a v ->
  pte_leaf lv -> pte_ptr v ->
  racc_disj la 8 a 8.
Proof.
  intros Hla Ha Hleaf Hptr.
  pose proof (pa_z_range la) as Hrla. pose proof (pa_z_range a) as Hra.
  rewrite /pa_z in Hrla, Hra.
  pose proof Hla as (_ & _ & _ & Hall).
  pose proof Ha as (_ & _ & _ & Hala).
  (* extract the two mod-8 facts *)
  unfold is_aligned_paddr in Hall, Hala.
  apply Z.eqb_eq in Hall. apply Z.eqb_eq in Hala.
  rewrite (Z.rem_mod_nonneg (uint la) 8 ltac:(lia) ltac:(lia)) in Hall.
  rewrite (Z.rem_mod_nonneg (uint a) 8 ltac:(lia) ltac:(lia)) in Hala.
  destruct (decide (pa_z la = pa_z a)) as [Heqz|Hne].
  - exfalso.
    assert (Heq : la = a)
      by (apply bv_eq; rewrite -!uint_unsigned; exact Heqz).
    subst a.
    pose proof (pt_slot_mem_det sg la lv v Hla Ha) as ->.
    unfold pte_leaf in Hleaf. unfold pte_ptr in Hptr. congruence.
  - unfold racc_disj.
    apply Z.mod_divide in Hall; [|lia]. apply Z.mod_divide in Hala; [|lia].
    destruct Hall as [k1 Hk1]. destruct Hala as [k2 Hk2].
    rewrite /pa_z in Hne |- *.
    assert (k1 <> k2) by (intros ->; apply Hne; lia).
    lia.
Qed.

(* ====================================================================== *)
(** ** 2. The pure dispatch at the stale mirror

    [WeakKpt.wptree_translateAddr_eff_cases]' twin: same premises, and the
    conclusion is the per-variant FAMILY, split by whether a write-back
    happens — which is family-uniform (see the header).  The hit arms
    transfer the [exec_eff] runs unchanged ([WeakStale.exec_stale_of_exec_eff]
    applies: no unpinned read touches anything); the miss arm is
    [WeakWalkStale.exec_stale_translateAddr_pt_miss_cases], fed the walk's
    three reads AT THE PATCHED STATE through the §7 transports (the two
    pointer slots are [racc_disj] from the window by §1) and the CAS's at
    the real one. *)

Section WeakKptStaleDispatch.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma wptree_translateAddr_stale_cases (root_ppn : mword 44)
        (va w pa satp0 : mword 64) (t : ptree)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (sg : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    let a2w := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
    let a1w := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    (forall a d : mword 1, wpte_valid (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    wpte_valid p2 -> wpte_valid p1 ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    pt_slot_mem sg (pt_addr2 t vpn) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = p ->
    exec_eff (translationMode p) sg = Some (Sv39, sg, []) ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) p) sg
      = Some (p, sg, []) ->
    exec_eff (is_shadow_stack_access acc) sg = Some (false, sg, []) ->
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
    ( (* READ-ONLY: no family member writes *)
      (forall av dv : mword 1,
         pte_ad_le (pte_set_ad w av dv) p0 ->
         exists (sg' : mstate) (es : list weff),
           exec_stale la 8 (pte_set_ad w av dv)
             (translateAddr (Virtaddr va) acc) sg
           = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)
           /\ mem sg' = sg.(mem) /\ mdev sg' = sg.(mdev)
           /\ (sregs sg' = sg.(sregs) \/
               (exists ae de : mword 1,
                  sregs sg' = register_set tlb
                    (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn p2 p1 (pte_set_ad w ae de)
                                (mword_of_int 0))))
                    sg.(sregs)))
           /\ (es = [] \/
               es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                     WEread wak_plain la 8] \/
               es = [WEread (AkInfo false true false) la 8] \/
               es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                     WEread wak_plain la 8;
                     WEread (AkInfo false true false) la 8]))
      \/
      (* WRITE-BACK: every family member writes the SAME word, computed
         from the resident (latest) leaf *)
      (exists a1 d1 : mword 1,
         update_PTE_Bits (p0 : mword 64) acc = Some (pte_set_ad p0 a1 d1)
         /\ forall av dv : mword 1,
              pte_ad_le (pte_set_ad w av dv) p0 ->
              exists (sg' : mstate) (es : list weff),
                exec_stale la 8 (pte_set_ad w av dv)
                  (translateAddr (Virtaddr va) acc) sg
                = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)
                /\ mem sg' = write_bytes sg.(mem) la 8 (pte_set_ad p0 a1 d1)
                /\ mdev sg' = sg.(mdev)
                /\ (exists ae de : mword 1,
                      sregs sg' = register_set tlb
                        (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                           (Some (u_walk_entry vpn p2 p1 (pte_set_ad w ae de)
                                    (mword_of_int 0))))
                        sg.(sregs))
                /\ (es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                          WEread wak_plain la 8;
                          WEread (AkInfo false true false) la 8;
                          WEwrite (AkInfo false true false) la 8
                            (pte_set_ad p0 a1 d1 : mword 64)] \/
                    es = [WEread (AkInfo false true false) la 8;
                          WEwrite (AkInfo false true false) la 8
                            (pte_set_ad p0 a1 d1 : mword 64)])) ).
  Proof.
    intros vpn p0 a2w a1w la Hchk Hval Hcanon Hout Hvarp Hwv2 Hwv1 Hbase Hmaps
           Htlbok Hsm2 Hsm1 Hsm0 Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatp Hppn
           Hasid Htlbv HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    (* the three slot facts at the walk's canonical spellings *)
    assert (Hsm2' : pt_slot_mem sg a2w p2).
    { assert (Ha2 : pt_addr2 t vpn = a2w).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hsm1' : pt_slot_mem sg a1w p1) by exact Hsm1.
    assert (Hsm0' : pt_slot_mem sg la p0) by exact Hsm0.
    (* §1: the window's geometry, and its disjointness from the two
       pointer slots *)
    pose proof (pt_slot_mem_acc_wf sg _ _ Hsm2') as Hwf2.
    pose proof (pt_slot_mem_acc_wf sg _ _ Hsm1') as Hwf1.
    pose proof (pt_slot_mem_acc_wf sg _ _ Hsm0') as Hwf0.
    pose proof (pt_slot_racc_disj sg _ _ _ _ Hsm0' Hsm2' Hl0 Hn2) as Hd2.
    pose proof (pt_slot_racc_disj sg _ _ _ _ Hsm0' Hsm1' Hl0 Hn1) as Hd1.
    (* the reads at the REAL state *)
    destruct (Hpmar a2w (pt_slot_ram_access _ _ _ Hsm2')) as (region2 & Hm2 & Hs2).
    destruct (Hpmar a1w (pt_slot_ram_access _ _ _ Hsm1')) as (region1 & Hm1 & Hs1).
    destruct (Hpmar la (pt_slot_ram_access _ _ _ Hsm0')) as (region0 & Hm0r & Hs0).
    pose proof (wpt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif)
      as Hrd2.
    pose proof (wpt_read_pte_slot sg _ p1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif)
      as Hrd1.
    pose proof (wpt_read_pte_slot sg _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrd0.
    pose proof (wpt_read_pte_exclusive_slot sg _ p0 region0 Hsm0' HA Hord HR Hcov
                  Hm0r Hs0 Hhtif) as Hrdx.
    (* identity geometry *)
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    (* the CAS's write half, available whenever the fresh word needs bits *)
    assert (Hwrite : forall q : mword 64,
              update_PTE_Bits (p0 : mword 64) acc = Some q ->
              exec_eff (write_pte_conditional (Physaddr la) 8 (q : mword 64)) sg
              = Some (Ok true,
                      MState sg.(sregs) (write_bytes sg.(mem) la 8 (q : mword 64)) sg.(mdev),
                      [WEwrite wak_excl la 8 (q : mword 64)])).
    { intros q _.
      pose proof Hsm0' as (Hbytes0 & Hram0 & Hram0' & Hal0).
      destruct (Hpmaw la
            (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
               eq_refl eq_refl)) as (regionw & Hmw & Hww).
      exact (exec_eff_write_pte_conditional_ram la q regionw sg
               Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif). }
    (* ---------------------------------------------------------------- *)
    (* THE MISS PATH, once, as a hypothesis keyed on the [lookup_TLB]
       fact — both the foreign-entry and the empty-slot branch use it. *)
    match goal with |- ?G =>
      assert (Hmiss : exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg
                      = Some (None, sg, []) -> G)
    end.
    { intros Hlk.
      (* the per-member run, uniform in the family: [exec_stale] at [pv] *)
      assert (Hfam : forall av dv : mword 1,
        exists (sg' : mstate) (es : list weff),
          exec_stale la 8 (pte_set_ad w av dv)
            (translateAddr (Virtaddr va) acc) sg
          = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)
          /\ mdev sg' = sg.(mdev)
          /\ (exists ae de : mword 1,
                sregs sg' = register_set tlb
                  (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                     (Some (u_walk_entry vpn p2 p1 (pte_set_ad w ae de)
                              (mword_of_int 0))))
                  sg.(sregs))
          /\ ( (mem sg' = sg.(mem)
                /\ ((update_PTE_Bits (pte_set_ad w av dv : mword 64) acc = None
                     /\ es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                              WEread wak_plain la 8])
                    \/ (update_PTE_Bits (p0 : mword 64) acc = None
                        /\ es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                                 WEread wak_plain la 8; WEread wak_excl la 8])))
             \/ (exists q : mword 64,
                   update_PTE_Bits (p0 : mword 64) acc = Some q
                   /\ mem sg' = write_bytes sg.(mem) la 8 (q : mword 64)
                   /\ es = [WEread wak_plain a2w 8; WEread wak_plain a1w 8;
                            WEread wak_plain la 8; WEread wak_excl la 8;
                            WEwrite wak_excl la 8 (q : mword 64)]) )).
      { intros av dv.
        assert (Hleafv : pte_is_non_leaf
                  (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w av dv) 7 0)) = false).
        { apply (proj2 (pte_set_ad_leaf w av dv)).
          exact (proj1 (pte_set_ad_leaf w a0 d0) Hl0). }
        assert (Hnapv : eq_vec (_get_PTE_Ext_N
                  (ext_bits_of_PTE (pte_set_ad w av dv))) ('b"1") = false).
        { apply (proj2 (pte_set_ad_no_napot w av dv)).
          exact (proj1 (pte_set_ad_no_napot w a0 d0) Hnap). }
        assert (Hidv : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                     (PPN_of_PTE (pte_set_ad w av dv : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. exact Hout. }
        assert (Habs : p0 = pte_set_ad (pte_set_ad w av dv) a0 d0)
          by (symmetry; exact (pte_set_ad_absorb w av dv a0 d0)).
        (* the three walk reads, at the PATCHED state *)
        pose proof (pt_slot_mem_mpatch_disj la 8 (pte_set_ad w av dv) sg a2w p2
                      Hwf0 Hwf2 Hd2 Hsm2') as Hsm2p.
        pose proof (pt_slot_mem_mpatch_disj la 8 (pte_set_ad w av dv) sg a1w p1
                      Hwf0 Hwf1 Hd1 Hsm1') as Hsm1p.
        pose proof (pt_slot_mem_mpatch_win la (pte_set_ad w av dv) sg p0
                      Hwf0 Hsm0') as Hsm0p.
        pose proof (wpt_read_pte_slot (mpatch la 8 (pte_set_ad w av dv) sg) _ p2
                      region2 Hsm2p HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2p.
        pose proof (wpt_read_pte_slot (mpatch la 8 (pte_set_ad w av dv) sg) _ p1
                      region1 Hsm1p HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1p.
        pose proof (wpt_read_pte_slot (mpatch la 8 (pte_set_ad w av dv) sg) _
                      (pte_set_ad w av dv)
                      region0 Hsm0p HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0p.
        destruct (WeakWalkStale.exec_stale_translateAddr_pt_miss_cases acc p
                    vpn root_ppn p2 p1 (pte_set_ad w av dv) p0 a0 d0
                    satp0 va pa MENVCFG_S sg
                    Hwf0 Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon eq_refl Hlk Hidv
                    Hwv2 Hn2 Hwv1 Hn1 (Hval av dv) Hleafv
                    (fun mxr ds => Hchk av dv mxr ds) Hnapv
                    Habs (Hval a0 d0) Hl0 (fun mxr ds => Hchk a0 d0 mxr ds) Hnap
                    Hrd2p Hrd1p Hrd0p Hrdx Hwrite Hmisa Hmenv HPBMTE HADUE)
          as (sg' & es & Heq & Hmdev & Hsregs & Harm).
        exists sg', es. split_and!.
        - exact Heq.
        - exact Hmdev.
        - destruct Hsregs as (ae & de & Hsr). exists ae, de.
          rewrite Hsr Htlbv pte_set_ad_absorb. reflexivity.
        - destruct Harm as [(Hmem0 & [(Hg & Hes)|(Hg & Hes)]) | (q & Hq' & Hmem0 & Hes)].
          + left. split; [exact Hmem0|]. left. split; [exact Hg|exact Hes].
          + left. split; [exact Hmem0|]. right. split; [exact Hg|exact Hes].
          + right. exists q. split; [exact Hq'|]. split; [exact Hmem0|exact Hes]. }
      (* the top-level arm is decided by the LATEST word, uniformly *)
      destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hup.
      - (* WRITE-BACK *)
        destruct (update_PTE_Bits_set_ad _ _ _ Hup) as (a1 & d1 & Hq).
        right. exists a1, d1. split; [rewrite <- Hq; reflexivity|].
        intros av dv Hle.
        destruct (Hfam av dv) as (sg' & es & Heq & Hmdev & Hsregs & Harm).
        destruct Harm as [(Hmem0 & [(Hg & Hes)|(Hg & Hes)]) | (q & Hq' & Hmem0 & Hes)].
        + exfalso.
          destruct (update_PTE_Bits_fires_mono (pte_set_ad w av dv) p0 acc Hle
                      (mk_is_Some _ _ Hup)) as (x & Hx). congruence.
        + exfalso. congruence.
        + assert (Hqe : q = pte_set_ad p0 a1 d1) by congruence.
          rewrite Hqe in Hmem0, Hes.
          exists sg', es. split_and!.
          * exact Heq.
          * exact Hmem0.
          * exact Hmdev.
          * exact Hsregs.
          * left. exact Hes.
      - (* READ-ONLY *)
        left. intros av dv Hle.
        destruct (Hfam av dv) as (sg' & es & Heq & Hmdev & Hsregs & Harm).
        destruct Harm as [(Hmem0 & [(Hg & Hes)|(Hg & Hes)]) | (q & Hq' & Hmem0 & Hes)];
          [ | | exfalso; congruence ].
        + exists sg', es. split_and!.
          * exact Heq.
          * exact Hmem0.
          * exact Hmdev.
          * right. exact Hsregs.
          * right. left. exact Hes.
        + exists sg', es. split_and!.
          * exact Heq.
          * exact Hmem0.
          * exact Hmdev.
          * right. exact Hsregs.
          * right. right. right. exact Hes. }
    (* ---------------------------------------------------------------- *)
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - (* resident entry *)
      destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* HIT on this vpn's own (A/D-variant) entry: no PLAIN read runs,
           so the whole family rides the [exec_eff] run unchanged *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  wpte_check_ok acc p mxr do_sum (pte_set_ad p0 a' d')).
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
        * assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
          { exists a0, d0. rewrite pte_set_ad_absorb.
            unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
          destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* O3, hit path: the CAS pair lands *)
             pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 p1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec_eff (write_pte_conditional (Physaddr la) 8
                        (p0' : mword 64)) sg
                      = Some (Ok true, MState sg.(sregs)
                                 (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev),
                              [WEwrite (AkInfo false true false) (pt_addr0 p1 vpn) 8 p0']))
               by exact (exec_eff_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             assert (Hqw : p0' = pte_set_ad w a1 d1)
               by (rewrite Hq; exact (pte_set_ad_absorb w a0 d0 a1 d1)).
             assert (Hhit : exists (sgh : mstate) (esh : list weff),
                 exec_eff (translateAddr (Virtaddr va) acc) sg
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgh, esh)
                 /\ mem sgh = write_bytes sg.(mem) la 8 (pte_set_ad p0 a1 d1)
                 /\ mdev sgh = sg.(mdev)
                 /\ (exists ae de : mword 1,
                       sregs sgh = register_set tlb
                         (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad w ae de)
                                     (mword_of_int 0))))
                         sg.(sregs))
                 /\ esh = [WEread (AkInfo false true false) la 8;
                           WEwrite (AkInfo false true false) la 8
                             (pte_set_ad p0 a1 d1 : mword 64)]).
             { do 2 eexists. split_and!.
               - apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                          (autocast (T := mword) ((autocast (T := mword)
                             (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                          satp0 va pa _ sg _
                          Heff Hss Hcp Htm Hsatp Hppn Hasid
                          Hcanon eq_refl).
                 2:{ exact Hidc. }
                 intros mxr do_sum.
                 apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                          (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                          (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
                 apply (exec_eff_translate_TLB_hit_pt_upd acc p mxr do_sum
                          vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S (mword_of_int 0)
                          (tlb_hash (__id 39) vpn) _ _
                          (MState sg.(sregs) (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev)) sg
                          (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                          Hrdx (Hval a0 d0) Hl0 (Hchk a0 d0 mxr do_sum) Hnap Hmisa HPBMTE
                          Hvarm Hupm Hwr eq_refl).
               - rewrite mem_set_reg. rewrite <- Hq. reflexivity.
               - by rewrite mdev_set_reg.
               - exists a1, d1. rewrite sregs_set_reg Htlbv. rewrite <- Hqw. reflexivity.
               - rewrite <- Hq. reflexivity. }
             destruct Hhit as (sgh & esh & Hrun & Hmm & Hdd & Hss' & Hee).
             right. exists a1, d1. split; [rewrite <- Hq; reflexivity|].
             intros av dv Hle. exists sgh, esh. split_and!.
             ++ apply (exec_stale_of_exec_eff la 8 (pte_set_ad w av dv) _ Hwf0 sg _ _ _ Hrun).
                rewrite Hee. apply trace_off_win_pinned. pinned_trace.
             ++ exact Hmm.
             ++ exact Hdd.
             ++ exact Hss'.
             ++ right. exact Hee.
          -- (* O2', hit path: refresh only — trace is the CAS read *)
             assert (Hhit : exists (sgh : mstate) (esh : list weff),
                 exec_eff (translateAddr (Virtaddr va) acc) sg
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgh, esh)
                 /\ mem sgh = sg.(mem)
                 /\ mdev sgh = sg.(mdev)
                 /\ (exists ae de : mword 1,
                       sregs sgh = register_set tlb
                         (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad w ae de)
                                     (mword_of_int 0))))
                         sg.(sregs))
                 /\ esh = [WEread (AkInfo false true false) la 8]).
             { do 2 eexists. split_and!.
               - apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                          (autocast (T := mword) ((autocast (T := mword)
                             (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                          satp0 va pa _ sg _
                          Heff Hss Hcp Htm Hsatp Hppn Hasid
                          Hcanon eq_refl).
                 2:{ exact Hidc. }
                 intros mxr do_sum.
                 apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                          (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                          (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                             (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
                 apply (exec_eff_translate_TLB_hit_pt_refresh acc p mxr do_sum
                          vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S (mword_of_int 0)
                          (tlb_hash (__id 39) vpn) _ sg
                          (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                          Hrdx (Hval a0 d0) Hl0 (Hchk a0 d0 mxr do_sum) Hnap Hmisa HPBMTE
                          Hvarm Hupm).
               - by rewrite mem_set_reg.
               - by rewrite mdev_set_reg.
               - exists a0, d0. rewrite sregs_set_reg Htlbv. reflexivity.
               - reflexivity. }
             destruct Hhit as (sgh & esh & Hrun & Hmm & Hdd & Hss' & Hee).
             left. intros av dv Hle. exists sgh, esh. split_and!.
             ++ apply (exec_stale_of_exec_eff la 8 (pte_set_ad w av dv) _ Hwf0 sg _ _ _ Hrun).
                rewrite Hee. apply trace_off_win_pinned. pinned_trace.
             ++ exact Hmm.
             ++ exact Hdd.
             ++ right. exact Hss'.
             ++ right. right. left. exact Hee.
        * (* O1: hit, the cached variant needs nothing — no access at all *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          assert (Hrun : exec_eff (translateAddr (Virtaddr va) acc) sg
                         = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg, [])).
          { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa [] sg sg
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                     (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                        (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            apply (exec_eff_translate_TLB_hit_pt acc p mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) sg
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. intros av dv Hle. exists sg, ([] : list weff). split_and!.
          -- apply (exec_stale_of_exec_eff la 8 (pte_set_ad w av dv) _ Hwf0 sg _ _ _ Hrun).
             apply trace_off_win_pinned. pinned_trace.
          -- reflexivity.
          -- reflexivity.
          -- left. reflexivity.
          -- left. reflexivity.
      + (* foreign entry: rejected by the tag, so the walk runs *)
        apply Hmiss.
        exact (exec_eff_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec sg Htlbv Hslot
                 (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                    (mword_of_int 0) Hne)).
    - (* empty slot: the walk runs *)
      apply Hmiss.
      exact (exec_eff_lookup_TLB_miss vpn (mword_of_int 0) tlbvec sg Htlbv Hslot).
  Qed.

End WeakKptStaleDispatch.

(* ====================================================================== *)
(** ** 3. THE RACY ABSORPTION THEOREM *)

Section WeakKptStaleAbsorb.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma wtlb_res_pt_translateAddr_stale_at (root_ppn : mword 44) (T_kpt : nat)
      (tid : option nat) (va pa : mword 64) (ppn : mword 44) (pc : kperm)
      (σ : wmstate) (E : coPset) :
    ↑wkptN ⊆ E ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    (forall a d : mword 1,
       wpte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    wlog_wf (wm_log σ) ->
    register_lookup misa (wm_regs σ) = MISA_C ->
    register_lookup menvcfg (wm_regs σ) = MENVCFG_S ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup cur_privilege (wm_regs σ) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus (wm_regs σ)) = 'b"10" ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus (wm_regs σ)) Supervisor)
      (wflat_st σ) = Some (Supervisor, wflat_st σ, []) ->
    exec_eff (is_shadow_stack_access acc) (wflat_st σ)
      = Some (false, wflat_st σ, []) ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    (T_kpt <= w_vrNew (wm_ws σ))%nat ->
    kmap_at (svpn_of va) ppn pc -∗
    reg_interp (wm_regs σ) -∗
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wtlb_res_pt root_ppn T_kpt
    ={E}=∗
    ∃ (p2 p1 lw : mword 64),
      let vpn := svpn_of va in
      let w0 := mk_pte ppn (kperm_flags pc) in
      let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
      let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
      let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
      ⌜exists a d : mword 1, lw = pte_set_ad w0 a d⌝ ∗
      ⌜pt_slot_mem (wflat_st σ) a2 p2 /\ pt_slot_mem (wflat_st σ) a1 p1 /\
       pt_slot_mem (wflat_st σ) la lw⌝ ∗
      ⌜forall j : nat, (j < 8)%nat ->
         pinned_read σ (acc_addr a2 j) /\ pinned_read σ (acc_addr a1 j)⌝ ∗
      ⌜forall (rak : akinfo) (wv : bv (8 * 8)%N),
         wadm σ rak la 8 wv ->
         (exists a d : mword 1,
            (wv : mword 64) = pte_set_ad w0 a d) /\
         pte_ad_le (wv : mword 64) lw⌝ ∗
      ⌜forall j : nat, (j < 8)%nat -> nv_free (wm_log σ) (acc_addr la j)⌝ ∗
      reg_interp (wm_regs σ) ∗
      (* the REGISTER WAND: [exec_stale] is a function, so the caller's
         equation for the family member that ACTUALLY ran pins [sg'], and
         the wand advances the ghost registers to it and hands the residue
         back — [tlb_ok_pt_fill] absorbs whichever A/D-variant entry the
         run installed. *)
      (∀ (av dv : mword 1) (sg' : mstate) (es : list weff),
         ⌜pte_ad_le (pte_set_ad w0 av dv) lw⌝ -∗
         ⌜exec_stale la 8 (pte_set_ad w0 av dv)
            (translateAddr (Virtaddr va) acc) (wflat_st σ)
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)⌝ -∗
         reg_interp (wm_regs σ) ==∗
         reg_interp (sregs sg') ∗ wtlb_res_pt root_ppn T_kpt) ∗
      ( (* READ-ONLY: the log does not move *)
        (⌜forall av dv : mword 1,
            pte_ad_le (pte_set_ad w0 av dv) lw ->
            exists (sg' : mstate) (es : list weff),
              exec_stale la 8 (pte_set_ad w0 av dv)
                (translateAddr (Virtaddr va) acc) (wflat_st σ)
              = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es) /\
              mem sg' = wflat (wm_img σ) (wm_log σ) /\
              mdev sg' = wm_dev σ /\
              (es = [] \/
               es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                     WEread wak_plain la 8] \/
               es = [WEread (AkInfo false true false) la 8] \/
               es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                     WEread wak_plain la 8;
                     WEread (AkInfo false true false) la 8])⌝ ∗
         wlog_auth (wm_log σ) ∗ wlat_interp (wm_img σ) (wm_log σ))
        ∨
        (* WRITE-BACK: one message, the same for every family member *)
        (∃ (lw' : mword 64) (kcls : wm_class),
           ⌜update_PTE_Bits (lw : mword 64) acc = Some lw'⌝ ∗
           ⌜forall av dv : mword 1,
              pte_ad_le (pte_set_ad w0 av dv) lw ->
              exists (sg' : mstate) (es : list weff),
                exec_stale la 8 (pte_set_ad w0 av dv)
                  (translateAddr (Virtaddr va) acc) (wflat_st σ)
                = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es) /\
                mem sg' = write_bytes (wflat (wm_img σ) (wm_log σ)) (la : Arch.pa) 8 lw' /\
                mdev sg' = wm_dev σ /\
                (es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                       WEread wak_plain la 8;
                       WEread (AkInfo false true false) la 8;
                       WEwrite (AkInfo false true false) la 8 (lw' : mword 64)] \/
                 es = [WEread (AkInfo false true false) la 8;
                       WEwrite (AkInfo false true false) la 8 (lw' : mword 64)])⌝ ∗
           wlog_auth (wm_log σ ++ [wwrite_msg tid kcls (la : Arch.pa) 8 (lw' : mword 64)]) ∗
           wlat_interp (wm_img σ)
             (wm_log σ ++ [wwrite_msg tid kcls (la : Arch.pa) 8 (lw' : mword 64)]))).
  Proof.
    intros HE Hchk Hval Hcanon Hid4k Hwlog Hmisa Hmenv Hhtif Hcp HSXL Heff Hss
           Hall Hrcpt.
    iIntros "Hat Hri Hla Hi Hres".
    iDestruct "Hres" as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & Hsnap & Hpmp & #Hkinv)".
    iDestruct "Hsnap" as (t0) "(%Htlbok0 & #Hlb0)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof (pma_allows_all_pte_write _ Hall) as Hpmaw.
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n (wm_regs σ)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (HW' : eq_vec (_get_Pmpcfg_ent_W
      (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HW).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n (wm_regs σ)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    assert (Htm : exec_eff (translationMode Supervisor) (wflat_st σ)
                  = Some (Sv39, wflat_st σ, []))
      by exact (exec_eff_translationMode_S_sv39 satp0 (wflat_st σ) HSXL Hsatpv Hmode).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags pc) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn pc ('b"1") ('b"1")) in Hid4k.
      rewrite pte_set_ad_ppn in Hid4k. exact Hid4k. }
    assert (Hvarp : forall a d : mword 1,
       pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d))
      by (intros a d; apply kperm_variant_pbmt0).
    (* ---- open the shared table ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /wkpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(#Hlbt & HM & %Hspec & Hmap)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan0.
    assert (Htlbok : tlb_ok_pt (mword_of_int 0) t tlbvec)
      by exact (tlb_ok_pt_canon (mword_of_int 0) t0 t tlbvec Hcan0 Htlbok0).
    set (vpn := svpn_of va) in *.
    pose proof Hspec as (Hbase & Hmapspec).
    (* ---- the vpn's bundle ---- *)
    iDestruct (big_sepM_delete _ M vpn _ HMlk with "Hmap") as "[Hvpn Hrest]".
    iDestruct "Hvpn" as (p2 p1 a0 d0) "(%Hmaps & #Hptr2 & #Hptr1 & Hleaf)".
    assert (Hlf : kpt_leaf_pte_of vpn (ppn, pc) = mk_pte ppn (kperm_flags pc))
      by reflexivity.
    rewrite Hlf in Hmaps.
    iEval (rewrite Hlf) in "Hleaf".
    set (w0 := mk_pte ppn (kperm_flags pc)) in *.
    set (lw := pte_set_ad w0 a0 d0) in *.
    iDestruct "Hptr2" as (ts2) "(%Hts2 & %Hg2 & %Hwv2 & #Hel2)".
    iDestruct "Hptr1" as (ts1) "(%Hts1 & %Hg1 & %Hwv1 & #Hel1)".
    iDestruct "Hleaf" as (ts T0 log0)
      "(%Hg0 & %Hbnds & %Hinst0 & %Hvars0 & %Hfresh0 & #Hlblog & Hel0)".
    destruct Hbnds as (HT01 & HT0K & HT0ts & Htslen).
    (* ---- the slots at the flat state ---- *)
    pose proof (wslot_geom_acc_wf _ Hg2) as Hwf2.
    pose proof (wslot_geom_acc_wf _ Hg1) as Hwf1.
    pose proof (wslot_geom_acc_wf _ Hg0) as Hwf0.
    iDestruct (wlat8_flat_gen σ (pt_addr2 t vpn) DfracDiscarded ts2 p2
                 Hwlog Hwf2 with "Hi Hel2") as %[Hfl2 Hlat2].
    iDestruct (wlat8_flat_gen σ (pt_addr1 p2 vpn) DfracDiscarded ts1 p1
                 Hwlog Hwf1 with "Hi Hel1") as %[Hfl1 Hlat1].
    iDestruct (wlat8_flat_gen σ (pt_addr0 p1 vpn) (DfracOwn 1) ts lw
                 Hwlog Hwf0 with "Hi Hel0") as %[Hfl0 Hlat0].
    pose proof (wslot_mem_of_flat σ (pt_addr2 t vpn) p2 Hg2 Hfl2) as Hsm2.
    pose proof (wslot_mem_of_flat σ (pt_addr1 p2 vpn) p1 Hg1 Hfl1) as Hsm1.
    pose proof (wslot_mem_of_flat σ (pt_addr0 p1 vpn) lw Hg0 Hfl0) as Hsm0.
    (* ---- the clipped closure, extended to the current log ---- *)
    iDestruct (wlog_valid with "Hla Hlblog") as %Hpref.
    pose proof (prefix_length _ _ Hpref) as Hlen0.
    set (la := pt_addr0 p1 vpn) in *.
    assert (Hnw : forall (i : nat) (m : wmsg),
              wm_log σ !! i = Some m -> (ts <= i)%nat ->
              forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None)
      by exact (wwin_no_write_above σ la ts Hlat0).
    assert (Hvars : wlog_variants_from T0 (wm_log σ) (pa_z la) w0).
    { refine (wlog_variants_from_ext T0 log0 (wm_log σ) (pa_z la) w0
                Hvars0 Hpref _).
      intros i m Hm Hge j Hj. exact (Hnw i m Hm ltac:(lia) j Hj). }
    assert (Hfresh : forall img : image, wfresh_from T0 img (wm_log σ) (pa_z la)).
    { intros img.
      refine (wfresh_from_ext T0 img log0 (wm_log σ) (pa_z la)
                (Hfresh0 img) Hpref _).
      intros i m Hm Hge.
      rewrite -(acc_addr_0 la). exact (Hnw i m Hm ltac:(lia) 0%nat ltac:(lia)). }
    assert (Hinst : wwin_install (wm_log σ) T0 la)
      by exact (wwin_install_prefix log0 (wm_log σ) T0 la Hinst0 Hpref).
    assert (Hcovg : (T0 <= w_vrNew (wm_ws σ))%nat) by lia.
    (* ---- the racy-leaf collapse facts ---- *)
    iDestruct (wlat8_win_latest σ la (DfracOwn 1) ts lw with "Hi Hel0")
      as %Hwlat.
    iDestruct (nv_free_wlat8 (wm_img σ) (wm_log σ) la (DfracOwn 1) ts lw
                 with "Hi Hel0") as %Hnvfree.
    assert (Hcoll : forall (rak : akinfo) (wv : bv (8 * 8)%N),
              wadm σ rak la 8 wv ->
              (exists a d : mword 1, (wv : mword 64) = pte_set_ad w0 a d) /\
              pte_ad_le (wv : mword 64) (lw : mword 64)).
    { intros rak wv Hadm. split.
      - exact (wadm_variant_from σ rak la w0 T0 wv Hvars Hinst Hcovg Hadm).
      - exact (wadm_pte_ad_le_latest_from σ rak la w0 T0 wv lw
                 Hvars (Hfresh (wimg σ)) Hinst Hcovg Hwlat Hadm). }
    (* ---- pointer pinnedness for the caller's trace_pin ---- *)
    assert (Hpin : forall j : nat, (j < 8)%nat ->
              pinned_read σ (acc_addr (pt_addr2 t vpn) j) /\
              pinned_read σ (acc_addr (pt_addr1 p2 vpn) j)).
    { intros j Hj. split; rewrite /pinned_read.
      - rewrite (Hlat2 j Hj). lia.
      - rewrite (Hlat1 j Hj). lia. }
    (* ---- the leaf's byte-0 latest value, for the write-back arm ---- *)
    iDestruct (wlat_lookup with "Hi [Hel0]") as %Hlv0;
      [iDestruct "Hel0" as "(E0 & _)"; iExact "E0"|].
    (* the walk-spelled slot facts for the conclusion *)
    assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
      by (unfold pt_addr2; rewrite Hbase; reflexivity).
    (* ---- run the STALE dispatch at the flat state ---- *)
    destruct (wptree_translateAddr_stale_cases acc Supervisor root_ppn va w0 pa
                satp0 t tlbvec p2 p1 a0 d0 (wflat_st σ)
                Hchk Hval Hcanon Hout Hvarp Hwv2 Hwv1 Hbase Hmaps Htlbok
                Hsm2 Hsm1 Hsm0 Hmisa Hmenv Hhtif Hcp Htm Heff Hss
                Hsatpv Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as [Hfam | (a1 & d1 & Hupd & Hfam)].
    - (* ================= READ-ONLY: nothing moved ================= *)
      assert (Hfam' : forall av dv : mword 1,
          pte_ad_le (pte_set_ad w0 av dv) lw ->
          exists (sgx : mstate) (esx : list weff),
            exec_stale la 8 (pte_set_ad w0 av dv)
              (translateAddr (Virtaddr va) acc) (wflat_st σ)
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx)
            /\ mem sgx = wflat (wm_img σ) (wm_log σ)
            /\ mdev sgx = wm_dev σ
            /\ (sregs sgx = wm_regs σ \/
                (exists ae de : mword 1,
                   sregs sgx = register_set tlb
                     (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                        (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                                 (mword_of_int 0))))
                     (wm_regs σ)))
            /\ (esx = [] \/
                esx = [WEread wak_plain
                         (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                       WEread wak_plain
                         (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                       WEread wak_plain la 8] \/
                esx = [WEread (AkInfo false true false) la 8] \/
                esx = [WEread wak_plain
                         (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                       WEread wak_plain
                         (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                       WEread wak_plain la 8;
                       WEread (AkInfo false true false) la 8]))
        by exact Hfam.
      clear Hfam.
      iMod ("Hclose" with "[HM Hrest Hel0]") as "_".
      { iNext. iExists t, M. iFrame "Hlbt HM".
        iSplitR; [iPureIntro; exact Hspec|].
        iApply (big_sepM_delete _ M vpn _ HMlk). iFrame "Hrest".
        iExists p2, p1, a0, d0.
        iSplitR; [iPureIntro; exact Hmaps|].
        iSplitR; [iExists ts2; iFrame "Hel2"; iPureIntro; tauto|].
        iSplitR; [iExists ts1; iFrame "Hel1"; iPureIntro; tauto|].
        iExists ts, T0, log0. iFrame "Hlblog Hel0". iPureIntro. tauto. }
      iModIntro.
      iExists p2, p1, lw.
      iSplitR; [iPureIntro; exists a0, d0; reflexivity|].
      iSplitR; [iPureIntro; rewrite -Ha2; auto|].
      iSplitR; [iPureIntro; rewrite -Ha2; exact Hpin|].
      iSplitR; [iPureIntro; exact Hcoll|].
      iSplitR; [iPureIntro; exact Hnvfree|].
      iFrame "Hri".
      iSplitL "Hsatp Htlb Hpc Hpa".
      { (* ---- the REGISTER WAND (read-only arm) ---- *)
        iIntros (av dv sgc esc) "%Hle %Hrun Hri".
        assert (Hrun' : exec_stale la 8 (pte_set_ad w0 av dv)
                          (translateAddr (Virtaddr va) acc) (wflat_st σ)
                        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgc, esc))
          by exact Hrun.
        destruct (Hfam' av dv Hle) as (sgx & esx & Hrunx & _ & _ & Hsrx & _).
        rewrite Hrun' in Hrunx.
        assert (Hsgeq : sgx = sgc) by congruence.
        subst sgx.
        destruct Hsrx as [Hsr | (ae & de & Hsr)].
        - (* no register moved *)
          iModIntro. rewrite Hsr. iFrame "Hri".
          iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 tlbvec t
                    Hmode Hasid Hppn Htlbok with "Hsatp Htlb Hlbt [Hpc Hpa] Hkinv").
          iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                    HA Hord HX HW HR Hcov with "Hpc Hpa").
        - (* a TLB entry carrying an A/D variant of the mapped leaf *)
          assert (Hokf : tlb_ok_pt (mword_of_int 0) t
                    (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                                (mword_of_int 0))))).
          { apply (tlb_ok_pt_fill (mword_of_int 0) t tlbvec vpn p2 p1 lw
                     (pte_set_ad w0 ae de) Hmaps); [|exact Htlbok].
            exists ae, de. symmetry. exact (pte_set_ad_absorb w0 a0 d0 ae de). }
          iMod (reg_update (wm_regs σ) tlb tlbvec
                  (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                     (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                              (mword_of_int 0))))
                  with "Hri Htlb") as "[Hri Htlb]".
          iModIntro. rewrite Hsr. iFrame "Hri".
          iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 _ t
                    Hmode Hasid Hppn Hokf with "Hsatp Htlb Hlbt [Hpc Hpa] Hkinv").
          iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                    HA Hord HX HW HR Hcov with "Hpc Hpa"). }
      iLeft. iFrame "Hla Hi". iPureIntro.
      intros av dv Hle.
      destruct (Hfam' av dv Hle) as (sgx & esx & H1 & H2 & H3 & _ & H5).
      exists sgx, esx. split_and!; [exact H1|exact H2|exact H3|exact H5].
    - (* ================= WRITE-BACK, absorbed ================= *)
      set (lw' := pte_set_ad lw a1 d1) in *.
      assert (Habs : lw' = pte_set_ad w0 a1 d1)
        by exact (pte_set_ad_absorb w0 a0 d0 a1 d1).
      assert (Hupd' : update_PTE_Bits (lw : mword 64) acc = Some (lw' : mword 64))
        by exact Hupd.
      assert (Hfam' : forall av dv : mword 1,
          pte_ad_le (pte_set_ad w0 av dv) lw ->
          exists (sgx : mstate) (esx : list weff),
            exec_stale la 8 (pte_set_ad w0 av dv)
              (translateAddr (Virtaddr va) acc) (wflat_st σ)
            = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx)
            /\ mem sgx = write_bytes (wflat (wm_img σ) (wm_log σ))
                           (la : Arch.pa) 8 (lw' : mword 64)
            /\ mdev sgx = wm_dev σ
            /\ (exists ae de : mword 1,
                  sregs sgx = register_set tlb
                    (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                                (mword_of_int 0))))
                    (wm_regs σ))
            /\ (esx = [WEread wak_plain
                         (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                       WEread wak_plain
                         (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                       WEread wak_plain la 8;
                       WEread (AkInfo false true false) la 8;
                       WEwrite (AkInfo false true false) la 8 (lw' : mword 64)] \/
                esx = [WEread (AkInfo false true false) la 8;
                       WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]))
        by exact Hfam.
      clear Hfam.
      assert (Hv' : pte_valid lw')
        by (rewrite Habs; exact (kperm_variant_valid ppn pc a1 d1)).
      assert (Hl' : pte_leaf lw')
        by (rewrite Habs; exact (kperm_variant_leaf ppn pc a1 d1)).
      assert (Hn' : pte_no_napot lw')
        by (rewrite Habs; exact (kperm_variant_no_napot ppn pc a1 d1)).
      assert (Hp' : pte_pbmt0 lw')
        by (rewrite Habs; exact (kperm_variant_pbmt0 ppn pc a1 d1)).
      (* the tree moves by the leaf write; the canonical table does not *)
      assert (Hcan' : ptree_canon t = ptree_canon (ptree_set_leaf t vpn lw')).
      { rewrite Habs.
        rewrite <- (pte_set_ad_absorb w0 a0 d0 a1 d1).
        symmetry.
        exact (ptree_canon_set_leaf t vpn p2 p1 lw a1 d1 Hmaps). }
      iDestruct (kpt_lb_canon t (ptree_set_leaf t vpn lw') Hcan' with "Hlbt")
        as "#Hlb'".
      assert (Hspec' : kpt_tree_spec_gen root_ppn M (ptree_set_leaf t vpn lw')).
      { rewrite Habs.
        rewrite <- (pte_set_ad_absorb w0 a0 d0 a1 d1).
        apply (kpt_tree_spec_gen_set_leaf root_ppn M t vpn (ppn, pc) p2 p1
                 lw a1 d1 Hspec Hmaps HMlk).
        exists a0, d0. rewrite Hlf. reflexivity. }
      pose proof Hspec' as (Hbase' & _).
      assert (Hmaps' : ptree_maps (ptree_set_leaf t vpn lw') vpn p2 p1 lw')
        by exact (ptree_set_leaf_maps_self t vpn p2 p1 lw lw' Hmaps Hv' Hl' Hn' Hp').
      assert (Htlbokt : tlb_ok_pt (mword_of_int 0) (ptree_set_leaf t vpn lw') tlbvec)
        by exact (tlb_ok_pt_set_leaf (mword_of_int 0) t tlbvec vpn p2 p1 lw a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok).
      (* ghost: append the message, retarget the leaf element *)
      iMod (wlog_update (wm_log σ) [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)]
              with "Hla") as "Hla".
      iDestruct (wlog_snapshot with "Hla") as "[Hla #Hlb'']".
      iEval (rewrite /wlat8) in "Hel0".
      iDestruct "Hel0" as "(E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7)".
      iMod (wlat8_store_prim tid WCexcl σ (la : Arch.pa) (lw' : mword 64)
              ts ts ts ts ts ts ts ts _ _ _ _ _ _ _ _
              ltac:(discriminate)
              with "Hi E0 E1 E2 E3 E4 E5 E6 E7") as "[Hi Hel0']".
      (* the new leaf bundle's clipped facts *)
      assert (Hlatbyte : forall img : image,
                log_byte img (wm_log σ) (latest_ts (wm_log σ) (pa_z la)) (pa_z la)
                = Some (nth_byte lw 0)).
      { intros img.
        pose proof (Hlat0 0%nat ltac:(lia)) as Hlt0.
        rewrite acc_addr_0 in Hlt0. rewrite Hlt0.
        rewrite (log_byte_img_irrel img (wimg σ) (wm_log σ) ts (pa_z la)
                   ltac:(lia)).
        pose proof (proj1 Hlv0) as Hlb.
        rewrite acc_addr_0 in Hlb. exact Hlb. }
      assert (Hvars' : wlog_variants_from T0
                (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                (pa_z la) w0).
      { apply (wlog_variants_from_snoc T0 (wm_log σ) (pa_z la) w0 _ Hvars).
        apply (wmsg_variant_write tid WCexcl (la : Arch.pa) (lw' : mword 64) (pa_z la) w0
                 eq_refl).
        exists a1, d1. exact Habs. }
      assert (Hfresh' : forall img : image,
                wfresh_from T0 img
                  (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                  (pa_z la)).
      { intros img.
        exact (wfresh_from_writeback T0 img (wm_log σ) tid WCexcl (la : Arch.pa) acc
                 lw lw' (lw' : mword 64) (Hlatbyte img) Hupd' eq_refl (Hfresh img)). }
      assert (Hinst' : wwin_install
                (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                T0 la).
      { refine (wwin_install_prefix (wm_log σ) _ T0 la Hinst _).
        by eexists. }
      (* re-close the invariant at the new tree *)
      iMod ("Hclose" with "[HM Hrest Hel0']") as "_".
      { iNext. iExists (ptree_set_leaf t vpn lw'), M. iFrame "Hlb' HM".
        iSplitR; [iPureIntro; exact Hspec'|].
        iApply (big_sepM_delete _ M vpn _ HMlk).
        assert (Haddr2 : pt_addr2 (ptree_set_leaf t vpn lw') vpn = pt_addr2 t vpn)
          by (unfold pt_addr2; rewrite Hbase' Hbase; reflexivity).
        assert (Hmaps'' : ptree_maps (ptree_set_leaf t vpn lw') vpn p2 p1
                            (pte_set_ad w0 a1 d1))
          by (rewrite -Habs; exact Hmaps').
        iEval (rewrite Habs) in "Hel0'".
        iSplitL "Hel0'".
        { iExists p2, p1, a1, d1.
          iSplitR; [iPureIntro; exact Hmaps''|].
          iEval (rewrite Haddr2).
          iSplitR.
          { iExists ts2.
            iSplitR; [iPureIntro; exact Hts2|].
            iSplitR; [iPureIntro; exact Hg2|].
            iSplitR; [iPureIntro; exact Hwv2|].
            iExact "Hel2". }
          iSplitR.
          { iExists ts1.
            iSplitR; [iPureIntro; exact Hts1|].
            iSplitR; [iPureIntro; exact Hg1|].
            iSplitR; [iPureIntro; exact Hwv1|].
            iExact "Hel1". }
          iExists (S (length (wm_log σ))), T0,
            ((wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])%list).
          iSplitR; [iPureIntro; exact Hg0|].
          iSplitR.
          { iPureIntro. split_and!; [lia|lia|lia|].
            rewrite length_app /=. lia. }
          iSplitR; [iPureIntro; exact Hinst'|].
          iSplitR; [iPureIntro; exact Hvars'|].
          iSplitR; [iPureIntro; exact Hfresh'|].
          iSplitR; [iExact "Hlb''"|].
          iExact "Hel0'". }
        iApply (big_sepM_mono with "Hrest").
        intros vpn' e' Hlk'.
        apply lookup_delete_Some in Hlk' as [Hne' _].
        apply (wvpn_res_maps_mono T_kpt t (ptree_set_leaf t vpn lw') vpn' e').
        - intros q2 q1 q0 Hm'.
          exact (ptree_set_leaf_maps_other t vpn vpn' q2 q1 q0 lw'
                   (fun He => Hne' (eq_sym He)) Hm').
        - rewrite Hbase' Hbase. reflexivity. }
      iModIntro.
      iExists p2, p1, lw.
      iSplitR; [iPureIntro; exists a0, d0; reflexivity|].
      iSplitR; [iPureIntro; rewrite -Ha2; auto|].
      iSplitR; [iPureIntro; rewrite -Ha2; exact Hpin|].
      iSplitR; [iPureIntro; exact Hcoll|].
      iSplitR; [iPureIntro; exact Hnvfree|].
      iFrame "Hri".
      iSplitL "Hsatp Htlb Hpc Hpa".
      { (* ---- the REGISTER WAND (write-back arm) ---- *)
        iIntros (av dv sgc esc) "%Hle %Hrun Hri".
        assert (Hrun' : exec_stale la 8 (pte_set_ad w0 av dv)
                          (translateAddr (Virtaddr va) acc) (wflat_st σ)
                        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgc, esc))
          by exact Hrun.
        destruct (Hfam' av dv Hle) as (sgx & esx & Hrunx & _ & _ & Hsrx & _).
        rewrite Hrun' in Hrunx.
        assert (Hsgeq : sgx = sgc) by congruence.
        subst sgx.
        destruct Hsrx as (ae & de & Hsr).
        assert (Hokf : tlb_ok_pt (mword_of_int 0) (ptree_set_leaf t vpn lw')
                  (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                     (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                              (mword_of_int 0))))).
        { apply (tlb_ok_pt_fill (mword_of_int 0) (ptree_set_leaf t vpn lw') tlbvec
                   vpn p2 p1 lw' (pte_set_ad w0 ae de) Hmaps'); [|exact Htlbokt].
          exists ae, de. rewrite Habs pte_set_ad_absorb. reflexivity. }
        iMod (reg_update (wm_regs σ) tlb tlbvec
                (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                   (Some (u_walk_entry vpn p2 p1 (pte_set_ad w0 ae de)
                            (mword_of_int 0))))
                with "Hri Htlb") as "[Hri Htlb]".
        iModIntro. rewrite Hsr. iFrame "Hri".
        iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 _ (ptree_set_leaf t vpn lw')
                  Hmode Hasid Hppn Hokf with "Hsatp Htlb Hlb' [Hpc Hpa] Hkinv").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA Hord HX HW HR Hcov with "Hpc Hpa"). }
      iRight. iExists (lw' : mword 64), WCexcl.
      iSplitR; [iPureIntro; exact Hupd'|].
      iSplitR.
      { iPureIntro. intros av dv Hle.
        destruct (Hfam' av dv Hle) as (sgx & esx & H1 & H2 & H3 & _ & H5).
        exists sgx, esx. split_and!; [exact H1|exact H2|exact H3|exact H5]. }
      iFrame "Hla Hi".
  Qed.

End WeakKptStaleAbsorb.

(* ====================================================================== *)
(** ** 4. Soundness checks *)

Print Assumptions pt_slot_racc_disj.
Print Assumptions wptree_translateAddr_stale_cases.
Print Assumptions wtlb_res_pt_translateAddr_stale_at.
