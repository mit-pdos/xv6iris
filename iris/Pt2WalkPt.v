(* Pt2WalkPt.v -- THE SATP-SWITCH WINDOW'S WALK, PER NODE.

   [TransPt.tlb_inv_pt2_kcur] / [_kprev] hold TWO live page tables: one
   EXCLUSIVELY OWNED ([ptree_own], an abstract spec [Sp] / [Sc]) and one
   SHARED ([KptShare.kpt_inv], reached only through a snapshot).  So the
   window's walk cannot take either of the two routes whole:

     - [UptWalkPt.swp_translate_upt]'s route ([HartMemRun.swp_hmrun_of_exec]
       under a [goodmb] certificate) answers every memory access out of an
       OWNED byte map, and the shared table's bytes are not owned;
     - [HartSKpt.swp_translate_kpt]'s route (a per-node open of [kptN], with
       the read/write seams as PERSISTENT-backed iProps) cannot serve the
       owned table, whose [ptree_own] is linear and so cannot back five
       independently-consumed seams.

   THE TWO ROUTES DO NOT HAVE TO MIX, because the arms of
   [TransPt.ptree2_translateAddr_cases] each touch exactly ONE tree, and
   which one is decided by a PURE case split on the TLB slot the va hashes
   to -- available before any [swp] reasoning, off [tlb_ok_pt2]:

     slot empty, or its entry's tag rejects this vpn  -> the walk runs on
       the CURRENT tree (three reads, maybe one write-back);
     the entry is this vpn's, CURRENT provenance      -> the CURRENT tree's
       leaf slot only (one exclusive read, maybe one write-back);
     the entry is this vpn's, PREVIOUS provenance     -> the PREVIOUS
       tree's leaf slot only.

   So each window walk dispatches once and then runs the route that fits the
   tree that arm touches.  [Pt2Walk.tlb_slot_pt] is what makes the owned
   route usable here at all: the exec fact and the certificate need only the
   ONE slot's provenance, never [tlb_ok_pt] over the whole vector.

   [upt_Dr] / [upt_Dw] / [upt_satp_ok_pt] are reused from [UptWalkPt]: they
   are the WALK's footprint and the satp cell's agreement with a root, and
   neither mentions the user table. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodeCore SmodePte.
Require Import PtreeType PtTree PtBytes PtBuild KptTree UptTree UserPtTree TrampPt.
Require Import CommonWalk Pt4kWalk KptPt PtAdBits PtTreeAdue SRegime.
Require Import KMap KptGhost KptShare KptGoodb KptExecMap.
Require Import UserBytes UserFetchCert PtWalkCert UserClassifyAsm.
Require Import HartSwp HartLift HartSpan HartSpanChar HartSFrame HartMemRun.
Require Import HartMStore HartSTrans HartSKpt.
Require Import WpDecodeBridge.
Require Import SmodeCorePt TrampStepPt.
Require Import UptWalkPt Pt2Walk TransPt.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. A TREE'S BYTES.  [UptWalkPt.upt_tmem] with the SPEC half dropped as  *)
(*    well as the data half: the window's trees carry an ABSTRACT spec,    *)
(*    and none of the four consequences below ever looked at it.           *)
(* ===================================================================== *)

Definition pt_tmem (t : ptree) (mm : pamap) : Prop :=
  maps_disj (pt_maps 2 t) /\
  mm = ptree_bytes 2 t /\
  (forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> addr_is_ram a).

Lemma pt_tmem_sub (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  pt_tmem t mm -> word_bytes a q ∈ pt_maps 2 t -> word_bytes a q ⊆ mm.
Proof.
  intros (Hdisj & -> & _) Hin. rewrite /ptree_bytes.
  exact (maps_disj_subseteq (pt_maps 2 t) _ Hdisj Hin).
Qed.

Lemma pt_tmem_owned (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  pt_tmem t mm -> word_bytes a q ∈ pt_maps 2 t -> bytes_owned mm a 8 = true.
Proof.
  intros Hwf Hin.
  pose proof (pt_tmem_sub t mm a q Hwf Hin) as Hsub.
  apply bytes_owned_of_dom. intros j Hj. apply elem_of_dom.
  exists (nth_byte q j).
  exact (lookup_weaken (word_bytes a q) mm _ _ (word_bytes_lookup a q j Hj) Hsub).
Qed.

Lemma pt_slot_mem_at (t : ptree) (mm : pamap) (rs : regstate)
    (b : mword 44) (i : mword 9) (q : mword 64) :
  pt_tmem t mm ->
  word_bytes (u_pte_addr b i) q ∈ pt_maps 2 t ->
  pt_slot_mem (MState rs mm dev0_state) (u_pte_addr b i) q.
Proof.
  intros Hwf Hin.
  pose proof (pt_tmem_sub t mm _ q Hwf Hin) as Hsub.
  assert (Hlk : forall j : nat, (N.of_nat j < 8)%N ->
            mm !! pa_add (u_pte_addr b i) j = Some (nth_byte q j)).
  { intros j Hj. apply (lookup_weaken (word_bytes (u_pte_addr b i) q) mm);
      [ apply word_bytes_lookup; lia | exact Hsub ]. }
  assert (Hram : forall j : nat, (N.of_nat j < 8)%N ->
            addr_is_ram (pa_add (u_pte_addr b i) j)).
  { intros j Hj. destruct Hwf as (_ & _ & Hr).
    apply Hr. apply elem_of_dom. exists (nth_byte q j). exact (Hlk j Hj). }
  split_and!.
  - exact Hlk.
  - rewrite <- (pa_add_0 (u_pte_addr b i)). apply Hram. lia.
  - apply Hram. lia.
  - exact (pte_addr_at_aligned8 b i).
Qed.

Lemma pt_tmem_writeback (t : ptree) (mm : pamap) (vpn : mword 27)
    (p2 p1 p0 q : mword 64) :
  pt_tmem t mm ->
  ptree_maps t vpn p2 p1 p0 ->
  pt_tmem (ptree_set_leaf t vpn q) (write_bytes mm (pt_addr0 p1 vpn) 8 q).
Proof.
  intros Hwf Hmaps.
  pose proof (pt_same_shape_set_leaf t vpn p2 p1 p0 q Hmaps) as Hshape.
  pose proof Hwf as (Hdisj & Hmm & Hram).
  assert (Heq : ptree_bytes 2 (ptree_set_leaf t vpn q)
                = write_bytes mm (pt_addr0 p1 vpn) 8 q).
  { rewrite Hmm. exact (ptree_bytes_set_leaf t vpn p2 p1 p0 q Hdisj Hmaps). }
  split_and!.
  - exact (pt_maps_disj_shape 2 t (ptree_set_leaf t vpn q) Hshape Hdisj).
  - symmetry. exact Heq.
  - intros a Ha. apply Hram.
    rewrite Hmm (ptree_bytes_dom_shape 2 t _ Hshape) Heq. exact Ha.
Qed.

(* ===================================================================== *)
(* 2. THE OWNED TREE'S WALK, AT ONE SLOT.                                 *)
(*                                                                        *)
(* [UptWalkPt.swp_translate_upt] with the user table's spec replaced by a  *)
(* bare [ptree_maps] + A/D variance premise, and [tlb_ok_pt] by            *)
(* [Pt2Walk.tlb_slot_pt].  The landing tree and the landing tlb value come *)
(* out SPELLED, so a two-table caller can rebuild [tlb_ok_pt2] on the side *)
(* the walk actually filled from and re-establish its own spec itself.     *)
(* ===================================================================== *)
Section Pt2OwnedWalk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_translate_pt_slot (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (root_ppn : mword 44) (t : ptree)
      (va pa satp0 w mst0 : mword 64) (p2 p1 : mword 64) (a0 d0 : mword 1)
      (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (rr : option resv) :
    Drw ## Dro ->
    (forall r : register, upt_Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, upt_Dw r = true -> r ∈ Drw) ->
    s_acc_ok acc ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mstatus rs = mst0 ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbv ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup pma_regions rs = pmar0 ->
    upt_satp_ok_pt root_ppn satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    pt_base t = root_ppn ->
    ptree_maps t (svpn_of va) p2 p1 (pte_set_ad w a0 d0) ->
    tlb_slot_pt (mword_of_int 0) t tlbv (svpn_of va) ->
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc Supervisor mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
    gen_cert -∗ resv_frag cpu_id rr -∗
    ptree_own 2 (DfracOwn 1) t -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ (rsf : regstate) (t' : ptree),
                  ⌜ (rsf = rs /\ t' = t) \/
                    (exists a1 d1 : mword 1,
                       rsf = register_set tlb
                               (vec_update_dec tlbv
                                  (tlb_hash (__id 39) (svpn_of va))
                                  (Some (u_walk_entry (svpn_of va) p2 p1
                                           (pte_set_ad w a1 d1)
                                           (mword_of_int 0)))) rs /\
                       (t' = t \/
                        t' = ptree_set_leaf t (svpn_of va)
                               (pte_set_ad w a1 d1))) ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  ptree_own 2 (DfracOwn 1) t' ∗ resv_any cpu_id).
  Proof.
    intros Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
           Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
           Hbase Hmaps Hslotok Hvar Hchk Hgchk Hcanon Hout.
    pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
    pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hcert Hfrag Htree Hrw Hro".
    iDestruct (ptree_own_bytes 2 t with "Htree") as "(#Hclaims & %Hdisj & Hmm)".
    iDestruct (bytes_own_ram with "Hmm") as %Hram.
    assert (Hwf : pt_tmem t (ptree_bytes 2 t)).
    { split_and!; [ exact Hdisj | reflexivity | exact Hram ]. }
    (* the three slots, as reads and as ownership *)
    assert (Hsm2 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr2 t (svpn_of va)) p2)
      by exact (pt_slot_mem_at t _ rs (pt_base t)
                  (vpn_idx 2 (svpn_of va)) p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm1 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr1 p2 (svpn_of va)) p1)
      by exact (pt_slot_mem_at t _ rs (u_next_base p2)
                  (vpn_idx 1 (svpn_of va)) p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm0 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr0 p1 (svpn_of va)) (pte_set_ad w a0 d0))
      by exact (pt_slot_mem_at t _ rs (u_next_base p1)
                  (vpn_idx 0 (svpn_of va)) _ Hwf
                  (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown2 : bytes_owned (ptree_bytes 2 t) (pt_addr2 t (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown1 : bytes_owned (ptree_bytes 2 t) (pt_addr1 p2 (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown0 : bytes_owned (ptree_bytes 2 t) (pt_addr0 p1 (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ _ Hwf
                  (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
    (* every lookup, at THIS HART'S OWN FILE as the reference state -- which
       is what makes [swp_hmrun_of_exec]'s agreement premise [reflexivity] *)
    assert (Lmisa : register_lookup misa
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = MISA_C)
      by exact Hmisa.
    assert (Lmenv : register_lookup menvcfg
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = MENVCFG_S)
      by exact Hmenv.
    assert (Lhtif : register_lookup htif_tohost_base
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = None)
      by exact Hhtif.
    assert (Lcp : register_lookup cur_privilege
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = Supervisor)
      by exact Hcp.
    assert (Lsatp : register_lookup satp
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = satp0)
      by exact Hsatp.
    assert (Ltlb : register_lookup tlb
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = tlbv)
      by exact Htlb.
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) = 'b"10").
    { change (register_lookup mstatus
                (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
        with (register_lookup mstatus rs). rewrite Hms. exact HSXL. }
    assert (LMPRV : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs))) ('b"1") = false).
    { change (register_lookup mstatus
                (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
        with (register_lookup mstatus rs). rewrite Hms. exact HMPRV. }
    assert (LA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) = TOR)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HA).
    assert (Lord : zopz0zKzJ_u (zeros' 64) (vec_access_dec
              (register_lookup pmpaddr_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0) = false)
      by (change (register_lookup pmpaddr_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpaddr_n rs); rewrite Hpaddr; exact Hord).
    assert (LR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec
              (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) ('b"1") = true)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HR).
    assert (LW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec
              (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) ('b"1") = true)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HW).
    assert (Lcov : (ram_base + ram_size <= uint (vec_access_dec
              (register_lookup pmpaddr_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0) * 4)%Z)
      by (change (register_lookup pmpaddr_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpaddr_n rs); rewrite Hpaddr; exact Hcov).
    assert (Lpmar : pma_allows_pte_read (register_lookup pma_regions
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)))
      by (change (register_lookup pma_regions
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pma_regions rs); rewrite Hpma;
          exact (pma_allows_all_pte_read _ Hall)).
    assert (Lpmaw : pma_allows_pte_write (register_lookup pma_regions
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)))
      by (change (register_lookup pma_regions
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pma_regions rs); rewrite Hpma;
          exact (Hpmaw_of _ Hall)).
    (* the read-only probes, at that same state *)
    assert (Htm : exec (translationMode Supervisor)
                    (MState rs (ptree_bytes 2 t) dev0_state)
                  = Some (Sv39, MState rs (ptree_bytes 2 t) dev0_state))
      by exact (exec_translationMode_S_sv39 satp0
                  (MState rs (ptree_bytes 2 t) dev0_state) LSXL Lsatp Hmode).
    assert (Htmg : goodb upt_Dr (translationMode Supervisor)
                     (MState rs (ptree_bytes 2 t) dev0_state) = true)
      by exact (goodb_translationMode_S_sv39 upt_Dr satp0
                  (MState rs (ptree_bytes 2 t) dev0_state)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  LSXL Lsatp Hmode).
    assert (Heff : exec (effectivePrivilege acc (register_lookup mstatus
                     (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) Supervisor)
                     (MState rs (ptree_bytes 2 t) dev0_state)
                   = Some (Supervisor, MState rs (ptree_bytes 2 t) dev0_state))
      by exact (s_eff_exec acc _ Supervisor _ LMPRV).
    assert (Heffg : goodb upt_Dr (effectivePrivilege acc (register_lookup mstatus
                      (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) Supervisor)
                      (MState rs (ptree_bytes 2 t) dev0_state) = true)
      by exact (s_eff_goodb acc _ Supervisor upt_Dr _ LMPRV).
    (* the three PTE validity tests, certified *)
    assert (Hg2 : forall (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                          (ext_bits_of_PTE p2)) s0 = true).
    { intros Db s0. apply goodb_pte_is_invalid_valid.
      pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & Hv2 & _).
      exact Hv2. }
    assert (Hg1 : forall (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                          (ext_bits_of_PTE p1)) s0 = true).
    { intros Db s0. apply goodb_pte_is_invalid_valid.
      pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv1 & _).
      exact Hv1. }
    assert (Hg0 : forall (a d : mword 1) (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid
                          (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                          (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true)
      by (intros a d Db s0;
          exact (goodb_pte_is_invalid_valid _ Db s0 (proj1 (Hvar a d)))).
    (* THE TRANSLATION, exec side and certificate side *)
    destruct (ptree_translateAddr_cases_slot acc Supervisor root_ppn va w pa satp0 t
                tlbv p2 p1 a0 d0 (MState rs (ptree_bytes 2 t) dev0_state)
                Hchk Hcanon Hout (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
                Hbase Hmaps Hslotok Hsm2 Hsm1 Hsm0
                Lmisa Lmenv Lhtif Lcp Htm Heff
                (s_acc_ssa_exec acc _ Hacc)
                Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw)
      as (sf & Htr & Harms).
    assert (Htrg : goodmb upt_Dr upt_Dw (translateAddr (Virtaddr va) acc)
                     (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
                   = true).
    { apply (goodmb_ptree_translateAddr_slot upt_Dr upt_Dw acc Supervisor
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               root_ppn t va w pa satp0 tlbv p2 p1 a0 d0
               (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
               Hchk Hgchk Hcanon Hout
               (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
               Hbase Hmaps Hslotok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
               Lmisa Lmenv Lhtif Lcp Htm Htmg Heff Heffg
               (s_acc_ssa_exec acc _ Hacc) (s_acc_ssa_goodb acc upt_Dr _ Hacc)
               Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw). }
    (* WHERE THE WALK LANDED.  The three arms of the case analysis, each with
       its tree and its file; nothing after this looks at which. *)
    assert (Hland : exists (rsf : regstate) (t' : ptree),
              sf = MState rsf (ptree_bytes 2 t') dev0_state /\
              ((rsf = rs /\ t' = t) \/
               (exists a1 d1 : mword 1,
                  rsf = register_set tlb
                          (vec_update_dec tlbv (tlb_hash (__id 39) (svpn_of va))
                             (Some (u_walk_entry (svpn_of va) p2 p1
                                      (pte_set_ad w a1 d1) (mword_of_int 0)))) rs /\
                  (t' = t \/
                   t' = ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1)))) /\
              pt_same_shape 2 t t').
    { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
      - exists rs, t. split_and!;
          [ reflexivity | left; split; reflexivity | apply pt_same_shape_refl ].
      - eexists _, t. split_and!.
        + reflexivity.
        + right. exists a0, d0. rewrite <- Htlb.
          split; [reflexivity | left; reflexivity].
        + apply pt_same_shape_refl.
      - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
          by exact (pte_set_ad_absorb w a0 d0 a1 d1).
        rewrite Habs.
        eexists _, (ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1)).
        split_and!.
        + rewrite /set_reg. cbn [sregs mem mdev].
          rewrite (proj1 (proj2
            (pt_tmem_writeback t (ptree_bytes 2 t) (svpn_of va)
               p2 p1 (pte_set_ad w a0 d0) _ Hwf Hmaps))).
          reflexivity.
        + right. exists a1, d1. rewrite <- Htlb.
          split; [reflexivity | right; reflexivity].
        + exact (pt_same_shape_set_leaf t (svpn_of va) p2 p1 _ _ Hmaps). }
    destruct Hland as (rsf & t' & -> & Hshapef & Hshape).
    assert (Hdisj' : maps_disj (pt_maps 2 t'))
      by exact (pt_maps_disj_shape 2 t t' Hshape Hdisj).
    assert (Hdomt : (dom (ptree_bytes 2 t') : gset Arch.pa) = dom (ptree_bytes 2 t))
      by (symmetry; exact (ptree_bytes_dom_shape 2 t t' Hshape)).
    iDestruct (bi.equiv_entails_1_1 _ _ (pt_claims_shape 2 t t' Hshape)
                 with "Hclaims") as "#Hclaims'".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hmrun_of_exec upt_Dr upt_Dw Drw Dro Df _
                   (MState rs (ptree_bytes 2 t) dev0_state) _ _ rs
                   (ptree_bytes 2 t) Hdisjf HDr HDw (fun r _ => eq_refl)
                   ltac:(reflexivity) Htrg Htr
                   with "Hcert [Hfrag] Hrw Hro Hmm") ].
    2:{ iExists rr. iExact "Hfrag". }
    iIntros (v) "(-> & Hf)".
    iDestruct "Hf" as (rs' mm') "(%Hag' & %Hsub' & %Hdom' & Hrw & Hro & Hmm' & Hany)".
    assert (Hmmeq : mm' = ptree_bytes 2 t')
      by exact (u_map_eq mm' (ptree_bytes 2 t') Hsub'
                  ltac:(rewrite Hdom' Hdomt; reflexivity)).
    subst mm'.
    iSplitR; [done|].
    iExists rsf, t'.
    rewrite (hreg_frame_ext rs' rsf Drw
               (fun r Hr => Hag' r (elem_of_union_l _ _ _ Hr))).
    rewrite (hreg_frame_ro_ext Df rs' rsf Dro
               (fun r Hr => Hag' r (elem_of_union_r _ _ _ Hr))).
    iSplitR; [iPureIntro; exact Hshapef |].
    iFrame "Hrw Hro Hany".
    iApply (ptree_own_of_bytes 2 t' Hdisj' with "Hclaims' Hmm'").
  Qed.


  (* the HIT arm on its own, at a tree that need NOT be [satp]'s root: the
     switch window's PREVIOUS table is owned and mapped, and the walk never
     starts there.  [Pt2Walk.ptree_translateAddr_hit_slot] and its certificate
     are what drop [pt_base t = root_ppn] and the two upper slots. *)
  Lemma swp_translate_pt_hit_slot (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (root_ppn : mword 44) (t : ptree)
      (va pa satp0 w mst0 : mword 64) (p2 p1 : mword 64) (a0 d0 a' d' : mword 1)
      (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (rr : option resv) :
    Drw ## Dro ->
    (forall r : register, upt_Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, upt_Dw r = true -> r ∈ Drw) ->
    s_acc_ok acc ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mstatus rs = mst0 ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbv ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup pma_regions rs = pmar0 ->
    upt_satp_ok_pt root_ppn satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    ptree_maps t (svpn_of va) p2 p1 (pte_set_ad w a0 d0) ->
    vec_access_dec tlbv (tlb_hash (__id 39) (svpn_of va))
      = Some (u_walk_entry (svpn_of va) p2 p1
                (pte_set_ad (pte_set_ad w a0 d0) a' d') (mword_of_int 0)) ->
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc Supervisor mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
    gen_cert -∗ resv_frag cpu_id rr -∗
    ptree_own 2 (DfracOwn 1) t -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ (rsf : regstate) (t' : ptree),
                  ⌜ (rsf = rs /\ t' = t) \/
                    (exists a1 d1 : mword 1,
                       rsf = register_set tlb
                               (vec_update_dec tlbv
                                  (tlb_hash (__id 39) (svpn_of va))
                                  (Some (u_walk_entry (svpn_of va) p2 p1
                                           (pte_set_ad w a1 d1)
                                           (mword_of_int 0)))) rs /\
                       (t' = t \/
                        t' = ptree_set_leaf t (svpn_of va)
                               (pte_set_ad w a1 d1))) ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  ptree_own 2 (DfracOwn 1) t' ∗ resv_any cpu_id).
  Proof.
    intros Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
           Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
           Hmaps Hslot Hvar Hchk Hgchk Hcanon Hout.
    pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
    pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hcert Hfrag Htree Hrw Hro".
    iDestruct (ptree_own_bytes 2 t with "Htree") as "(#Hclaims & %Hdisj & Hmm)".
    iDestruct (bytes_own_ram with "Hmm") as %Hram.
    assert (Hwf : pt_tmem t (ptree_bytes 2 t)).
    { split_and!; [ exact Hdisj | reflexivity | exact Hram ]. }
    (* the three slots, as reads and as ownership *)
    assert (Hsm2 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr2 t (svpn_of va)) p2)
      by exact (pt_slot_mem_at t _ rs (pt_base t)
                  (vpn_idx 2 (svpn_of va)) p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm1 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr1 p2 (svpn_of va)) p1)
      by exact (pt_slot_mem_at t _ rs (u_next_base p2)
                  (vpn_idx 1 (svpn_of va)) p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm0 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr0 p1 (svpn_of va)) (pte_set_ad w a0 d0))
      by exact (pt_slot_mem_at t _ rs (u_next_base p1)
                  (vpn_idx 0 (svpn_of va)) _ Hwf
                  (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown2 : bytes_owned (ptree_bytes 2 t) (pt_addr2 t (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown1 : bytes_owned (ptree_bytes 2 t) (pt_addr1 p2 (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown0 : bytes_owned (ptree_bytes 2 t) (pt_addr0 p1 (svpn_of va)) 8 = true)
      by exact (pt_tmem_owned t _ _ _ Hwf
                  (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
    (* every lookup, at THIS HART'S OWN FILE as the reference state -- which
       is what makes [swp_hmrun_of_exec]'s agreement premise [reflexivity] *)
    assert (Lmisa : register_lookup misa
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = MISA_C)
      by exact Hmisa.
    assert (Lmenv : register_lookup menvcfg
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = MENVCFG_S)
      by exact Hmenv.
    assert (Lhtif : register_lookup htif_tohost_base
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = None)
      by exact Hhtif.
    assert (Lcp : register_lookup cur_privilege
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = Supervisor)
      by exact Hcp.
    assert (Lsatp : register_lookup satp
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = satp0)
      by exact Hsatp.
    assert (Ltlb : register_lookup tlb
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs) = tlbv)
      by exact Htlb.
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) = 'b"10").
    { change (register_lookup mstatus
                (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
        with (register_lookup mstatus rs). rewrite Hms. exact HSXL. }
    assert (LMPRV : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs))) ('b"1") = false).
    { change (register_lookup mstatus
                (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
        with (register_lookup mstatus rs). rewrite Hms. exact HMPRV. }
    assert (LA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) = TOR)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HA).
    assert (Lord : zopz0zKzJ_u (zeros' 64) (vec_access_dec
              (register_lookup pmpaddr_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0) = false)
      by (change (register_lookup pmpaddr_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpaddr_n rs); rewrite Hpaddr; exact Hord).
    assert (LR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec
              (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) ('b"1") = true)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HR).
    assert (LW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec
              (register_lookup pmpcfg_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0)) ('b"1") = true)
      by (change (register_lookup pmpcfg_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpcfg_n rs); rewrite Hpcfg; exact HW).
    assert (Lcov : (ram_base + ram_size <= uint (vec_access_dec
              (register_lookup pmpaddr_n
                 (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) 0) * 4)%Z)
      by (change (register_lookup pmpaddr_n
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pmpaddr_n rs); rewrite Hpaddr; exact Hcov).
    assert (Lpmar : pma_allows_pte_read (register_lookup pma_regions
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)))
      by (change (register_lookup pma_regions
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pma_regions rs); rewrite Hpma;
          exact (pma_allows_all_pte_read _ Hall)).
    assert (Lpmaw : pma_allows_pte_write (register_lookup pma_regions
              (MState rs (ptree_bytes 2 t) dev0_state).(sregs)))
      by (change (register_lookup pma_regions
                    (MState rs (ptree_bytes 2 t) dev0_state).(sregs))
            with (register_lookup pma_regions rs); rewrite Hpma;
          exact (Hpmaw_of _ Hall)).
    (* the read-only probes, at that same state *)
    assert (Htm : exec (translationMode Supervisor)
                    (MState rs (ptree_bytes 2 t) dev0_state)
                  = Some (Sv39, MState rs (ptree_bytes 2 t) dev0_state))
      by exact (exec_translationMode_S_sv39 satp0
                  (MState rs (ptree_bytes 2 t) dev0_state) LSXL Lsatp Hmode).
    assert (Htmg : goodb upt_Dr (translationMode Supervisor)
                     (MState rs (ptree_bytes 2 t) dev0_state) = true)
      by exact (goodb_translationMode_S_sv39 upt_Dr satp0
                  (MState rs (ptree_bytes 2 t) dev0_state)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  LSXL Lsatp Hmode).
    assert (Heff : exec (effectivePrivilege acc (register_lookup mstatus
                     (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) Supervisor)
                     (MState rs (ptree_bytes 2 t) dev0_state)
                   = Some (Supervisor, MState rs (ptree_bytes 2 t) dev0_state))
      by exact (s_eff_exec acc _ Supervisor _ LMPRV).
    assert (Heffg : goodb upt_Dr (effectivePrivilege acc (register_lookup mstatus
                      (MState rs (ptree_bytes 2 t) dev0_state).(sregs)) Supervisor)
                      (MState rs (ptree_bytes 2 t) dev0_state) = true)
      by exact (s_eff_goodb acc _ Supervisor upt_Dr _ LMPRV).
    (* the three PTE validity tests, certified *)
    assert (Hg2 : forall (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                          (ext_bits_of_PTE p2)) s0 = true).
    { intros Db s0. apply goodb_pte_is_invalid_valid.
      pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & Hv2 & _).
      exact Hv2. }
    assert (Hg1 : forall (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                          (ext_bits_of_PTE p1)) s0 = true).
    { intros Db s0. apply goodb_pte_is_invalid_valid.
      pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv1 & _).
      exact Hv1. }
    assert (Hg0 : forall (a d : mword 1) (Db : register -> bool) (s0 : mstate),
              goodb Db (pte_is_invalid
                          (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                          (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true)
      by (intros a d Db s0;
          exact (goodb_pte_is_invalid_valid _ Db s0 (proj1 (Hvar a d)))).
    (* THE TRANSLATION, exec side and certificate side *)
    destruct (ptree_translateAddr_hit_slot acc Supervisor root_ppn va w pa satp0 t
                tlbv p2 p1 a0 d0 a' d' (MState rs (ptree_bytes 2 t) dev0_state)
                Hchk Hcanon Hout (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
                Hmaps Hslot Hsm0
                Lmisa Lmenv Lhtif Lcp Htm Heff
                (s_acc_ssa_exec acc _ Hacc)
                Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw)
      as (sf & Htr & Harms).
    assert (Htrg : goodmb upt_Dr upt_Dw (translateAddr (Virtaddr va) acc)
                     (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
                   = true).
    { apply (goodmb_ptree_translateAddr_hit_slot upt_Dr upt_Dw acc Supervisor
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               root_ppn t va w pa satp0 tlbv p2 p1 a0 d0 a' d'
               (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
               Hchk Hgchk Hcanon Hout
               (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
               Hmaps Hslot Hg0 Hsm0 Hown0
               Lmisa Lmenv Lhtif Lcp Htm Htmg Heff Heffg
               (s_acc_ssa_exec acc _ Hacc) (s_acc_ssa_goodb acc upt_Dr _ Hacc)
               Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw). }
    (* WHERE THE WALK LANDED.  The three arms of the case analysis, each with
       its tree and its file; nothing after this looks at which. *)
    assert (Hland : exists (rsf : regstate) (t' : ptree),
              sf = MState rsf (ptree_bytes 2 t') dev0_state /\
              ((rsf = rs /\ t' = t) \/
               (exists a1 d1 : mword 1,
                  rsf = register_set tlb
                          (vec_update_dec tlbv (tlb_hash (__id 39) (svpn_of va))
                             (Some (u_walk_entry (svpn_of va) p2 p1
                                      (pte_set_ad w a1 d1) (mword_of_int 0)))) rs /\
                  (t' = t \/
                   t' = ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1)))) /\
              pt_same_shape 2 t t').
    { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
      - exists rs, t. split_and!;
          [ reflexivity | left; split; reflexivity | apply pt_same_shape_refl ].
      - eexists _, t. split_and!.
        + reflexivity.
        + right. exists a0, d0. rewrite <- Htlb.
          split; [reflexivity | left; reflexivity].
        + apply pt_same_shape_refl.
      - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
          by exact (pte_set_ad_absorb w a0 d0 a1 d1).
        rewrite Habs.
        eexists _, (ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1)).
        split_and!.
        + rewrite /set_reg. cbn [sregs mem mdev].
          rewrite (proj1 (proj2
            (pt_tmem_writeback t (ptree_bytes 2 t) (svpn_of va)
               p2 p1 (pte_set_ad w a0 d0) _ Hwf Hmaps))).
          reflexivity.
        + right. exists a1, d1. rewrite <- Htlb.
          split; [reflexivity | right; reflexivity].
        + exact (pt_same_shape_set_leaf t (svpn_of va) p2 p1 _ _ Hmaps). }
    destruct Hland as (rsf & t' & -> & Hshapef & Hshape).
    assert (Hdisj' : maps_disj (pt_maps 2 t'))
      by exact (pt_maps_disj_shape 2 t t' Hshape Hdisj).
    assert (Hdomt : (dom (ptree_bytes 2 t') : gset Arch.pa) = dom (ptree_bytes 2 t))
      by (symmetry; exact (ptree_bytes_dom_shape 2 t t' Hshape)).
    iDestruct (bi.equiv_entails_1_1 _ _ (pt_claims_shape 2 t t' Hshape)
                 with "Hclaims") as "#Hclaims'".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hmrun_of_exec upt_Dr upt_Dw Drw Dro Df _
                   (MState rs (ptree_bytes 2 t) dev0_state) _ _ rs
                   (ptree_bytes 2 t) Hdisjf HDr HDw (fun r _ => eq_refl)
                   ltac:(reflexivity) Htrg Htr
                   with "Hcert [Hfrag] Hrw Hro Hmm") ].
    2:{ iExists rr. iExact "Hfrag". }
    iIntros (v) "(-> & Hf)".
    iDestruct "Hf" as (rs' mm') "(%Hag' & %Hsub' & %Hdom' & Hrw & Hro & Hmm' & Hany)".
    assert (Hmmeq : mm' = ptree_bytes 2 t')
      by exact (u_map_eq mm' (ptree_bytes 2 t') Hsub'
                  ltac:(rewrite Hdom' Hdomt; reflexivity)).
    subst mm'.
    iSplitR; [done|].
    iExists rsf, t'.
    rewrite (hreg_frame_ext rs' rsf Drw
               (fun r Hr => Hag' r (elem_of_union_l _ _ _ Hr))).
    rewrite (hreg_frame_ro_ext Df rs' rsf Dro
               (fun r Hr => Hag' r (elem_of_union_r _ _ _ Hr))).
    iSplitR; [iPureIntro; exact Hshapef |].
    iFrame "Hrw Hro Hany".
    iApply (ptree_own_of_bytes 2 t' Hdisj' with "Hclaims' Hmm'").
  Qed.

End Pt2OwnedWalk.

(* ===================================================================== *)
(* 3. THE SHARED TREE'S WALK, AT ONE SLOT.                                *)
(*                                                                        *)
(* [HartSKpt.swp_translate_kpt] with its whole-vector [tlb_snap_ok]       *)
(* premise weakened to [Pt2Walk.tlb_slot_pt] at the walked vpn against a   *)
(* snapshot the CALLER names, and with the landing file spelled out       *)
(* ([kpt_slot_land]) instead of resealed into [tlb_snap_ok] -- the window  *)
(* has to rebuild [tlb_ok_pt2], not [tlb_ok_pt], and does it off the       *)
(* [ptree_maps] this hands back.                                          *)
(* ===================================================================== *)

(* the walk either left the file alone, or filled the slot with an entry
   whose three words come off the SNAPSHOT's own path and whose leaf is an
   A/D variant of the snapshot's leaf -- exactly what [tlb_ok_pt2_fill_cur]
   / [_fill_prev] consume. *)
Definition kpt_slot_land (t0 : ptree) (rs : regstate)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (vpn : mword 27)
    (rsf : regstate) : Prop :=
  rsf = rs \/
  (exists (q2 q1 q0 qf : mword 64) (a d : mword 1),
     ptree_maps t0 vpn q2 q1 q0 /\ qf = pte_set_ad q0 a d /\
     rsf = register_set tlb
             (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                (Some (u_walk_entry vpn q2 q1 qf (mword_of_int 0)))) rs).

Section Pt2SharedWalk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_translate_kpt_slot
      (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (root_ppn : mword 44) (t0 : ptree) (va pa satp0 menvcfg0 : mword 64)
      (ppn : mword 44) (kp : kperm)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbvec ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
      = Some (Supervisor, dst) ->
    goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
      dst = true ->
    exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
    goodb Db (is_shadow_stack_access acc) dst = true ->
    exec (translationMode Supervisor) dst = Some (Sv39, dst) ->
    goodb Db (translationMode Supervisor) dst = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64))
      = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    (* the claim's permission check, A/D-quantified (KptShare's premise) *)
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    tlb_slot_pt (mword_of_int 0) t0 tlbvec (svpn_of va) ->
    kmap_at (svpn_of va) ppn kp -∗
    kpt_inv root_ppn -∗
    kpt_lb t0 -∗
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ kpt_slot_land t0 rs tlbvec (svpn_of va) rsf ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif
      HDb Hag HDlc Haglc Hcp Hsatp Htlb Hhtif Hpma Hpcfg Hpaddr Hmstag
      Hmisa Hmenv HPBMTE HADUE Heff Heffg Hss Hssg Htm Htmg Hppn Hasid
      Hcanon Hident HA Hord HR HW Hcov Hpallow Hchk Htlbok0.
    iIntros "#Hat #Hkinv #Hlb0 #Hcert Hfrag Hrw Hro".
    assert (HDtlb : (tlb : register) ∈ Drw ∪ Dro) by set_solver.
    iApply swp_fupd.
    iMod (kpt_path_at root_ppn t0 (svpn_of va) ppn kp ⊤ ltac:(solve_ndisj)
            with "Hat Hlb0 Hkinv") as (p2 p1 a0 d0) "%Hpath".
    destruct Hpath as (Hbase & Hmaps & Hok2 & Hok1 & Hok0).
    iModIntro.
    (* the two internal levels' pure facts, off [ptree_maps] *)
    pose proof Hmaps as Hmapsd.
    destruct Hmapsd as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                        Hv2 & Hn2 & Hv1 & Hn1 & _ & _ & _ & _).
    (* the swp layer's footprint companions, which the exec layer never
       needed.  At the two INTERNAL levels they come off [ptree_maps]'
       own [pte_valid] + [pte_ptr] pair ([KptGoodb.pte_ptr_goodb_invalid];
       [pte_ptr] alone would be FALSE -- see that file's header), and at
       the claim's LEAF off the canonical class, with the shadow-stack
       tail taken from the caller's own [Hssg]. *)
    pose proof (pte_ptr_goodb_invalid p2 Hv2 Hn2) as Higptr2.
    pose proof (pte_ptr_goodb_invalid p1 Hv1 Hn1) as Higptr1.
    pose proof (kperm_canon_goodb_invalid ppn kp) as Higleaf.
    pose proof (fun w Hc => kperm_canon_goodb_check ppn kp w acc Db dst Hssg Hc)
      as Hchkgleaf.
    (* the leaf predicate, and its three closure facts *)
    assert (HP0i : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                                (ext_bits_of_PTE w)) s = Some (false, s)).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_valid. }
    assert (HP0nl : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_leaf. }
    assert (HP0chk : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall (mxr do_sum : bool) s,
                exec (check_PTE_permission acc Supervisor mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                        (ext_bits_of_PTE w) tt) s
                = Some (PTE_Check_Success tt, s)).
    { intros w Hc mxr do_sum. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply (Hchk a d mxr do_sum). }
    assert (HP0N : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE w)) ('b"1") = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_no_napot. }
    assert (HP0pb : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_pbmt0 w).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_pbmt0. }
    assert (HPvar : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              exists a d : mword 1, w = pte_set_ad w' a d).
    { intros w w' Hw Hw'.
      destruct (pte_canon_inv _ _ Hw) as (a & d & ->).
      destruct (pte_canon_inv _ _ Hw') as (a' & d' & ->).
      exists a, d. symmetry. apply pte_set_ad_absorb. }
    assert (HPupd : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w' ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp))).
    { intros w w' Hw Hu. rewrite autocast_id in Hu.
      destruct (update_PTE_Bits_set_ad _ _ _ Hu) as (a & d & ->).
      rewrite pte_canon_set_ad. exact Hw. }
    (* [P0] admits the claim's own A/D variant, which is the tree's leaf *)
    assert (HP0leaf : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0)
                      = pte_canon (mk_pte ppn (kperm_flags kp)))
      by apply pte_canon_set_ad.
    (* the three slot addresses, in the walk's spelling *)
    assert (Ha2 : pt_addr2 t0 (svpn_of va)
                  = u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18))
      by (unfold pt_addr2; rewrite Hbase; reflexivity).
    (* the head *)
    iApply (swp_translateAddr_pt_front_ex acc Supervisor Drw Dro Df rs dst
              (∃ rsf : regstate,
                 ⌜ kpt_slot_land t0 rs tlbvec (svpn_of va) rsf ⌝ ∗
                 hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                 resv_any cpu_id)%I
              Db (svpn_of va) root_ppn ppn satp0 va pa
              Hdisj HDmst HDpriv HDsatp HDb Hag Hcp Hsatp Hmstag
              Heff Heffg Hss Hssg Htm Htmg Hppn Hasid Hcanon eq_refl Hident
              with "Hcert Hrw Hro [Hfrag]").
    iIntros (mxr do_sum) "Hrw Hro".
    (* the read seams *)
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               ⌜read_bytes σ.(mem)
                  (u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18)) 8
                  = Some p2⌝ ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrd2".
    { rewrite <- Ha2.
      iApply (kpt_pte2_node root_ppn t0 (svpn_of va) p2 p1 _ Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               ⌜read_bytes σ.(mem)
                  (u_pte_addr (u_next_base p2) (subrange_vec_dec (svpn_of va) 17 9)) 8
                  = Some p1⌝ ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrd1".
    { iApply (kpt_pte1_node root_ppn t0 (svpn_of va) p2 p1 _ Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               (∃ w : mword 64,
                  ⌜read_bytes σ.(mem)
                     (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                     = Some w⌝ ∗
                  ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝) ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrdl".
    { iApply (kpt_leaf_node_canon root_ppn t0 (svpn_of va) p2 p1 _ a0 d0 Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               (∃ w : mword 64,
                  ⌜read_bytes σ.(mem)
                     (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                     = Some w⌝ ∗
                  ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝) ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrdx".
    { iApply (kpt_leaf_node_canon root_ppn t0 (svpn_of va) p2 p1 _ a0 d0 Hmaps
                with "Hlb0 Hkinv"). }
    (* the WRITE seam, in the shape the [_ex] write-back takes *)
    iAssert (∀ (w w' : mword 64),
               ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝ -∗
               ⌜update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w'⌝ -∗
               ∀ σ, ⌜read_bytes σ.(mem)
                       (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                       = Some w⌝ -∗
                   mstate_interp σ ={⊤,∅}=∗
                   ▷ (|={∅,⊤}=> mstate_interp
                        (MState σ.(sregs)
                           (write_bytes σ.(mem)
                              (u_pte_addr (u_next_base p1)
                                 (subrange_vec_dec (svpn_of va) 8 0)) 8
                              (Interface.WriteReq.value
                                 (mwrite_req8_con
                                    (u_pte_addr (u_next_base p1)
                                       (subrange_vec_dec (svpn_of va) 8 0))
                                    (autocast (T := mword) w'))))
                           σ.(mdev)) ∗ True))%I as "Hwr".
    { iIntros (w w') "%HPw %Hu".
      iApply (kpt_leaf_write_node root_ppn t0 (svpn_of va) ppn kp p2 p1 a0 d0
                w w' Hmaps
                ltac:(destruct (pte_canon_inv _ _ (HPupd w w' HPw Hu))
                        as (a & d & Hw'); exists a, d; exact Hw')
                with "Hat Hlb0 Hkinv"). }
    (* the three read obligations, in the shape the walk takes *)
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr root_ppn
                                (subrange_vec_dec (svpn_of va) 26 18))) 8)
                 (fun r => ⌜r = Values.Ok p2⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrd2]" as "Hob2".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt Drw Dro Df rs
                (u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18)) p2
                pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow
                ltac:(rewrite <- Ha2; exact Hok2)
                with "Hcert Hrw Hro Hrd2"). }
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr (u_next_base p2)
                                (subrange_vec_dec (svpn_of va) 17 9))) 8)
                 (fun r => ⌜r = Values.Ok p1⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrd1]" as "Hob1".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt Drw Dro Df rs _ p1 pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow Hok1
                with "Hcert Hrw Hro Hrd1"). }
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr (u_next_base p1)
                                (subrange_vec_dec (svpn_of va) 8 0))) 8)
                 (fun r => ∃ q0, ⌜r = Values.Ok q0⌝ ∗
                           ⌜pte_canon q0 = pte_canon (mk_pte ppn (kperm_flags kp))⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrdl]" as "Hob0".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt_ex Drw Dro Df rs _ _ pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow Hok0
                with "Hcert Hrw Hro Hrdl"). }
    (* the dispatch: hit or miss, off the caller's own TLB vector *)
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of va)))
      as [ent |] eqn:Hslot.
    - destruct (Htlbok0 ent Hslot)
        as [(q2 & q1 & qp0 & a' & d' & Hm0 & Hent) | Hnm].
      + (* HIT on this vpn's own (A/D-stale) entry *)
        destruct (ptree_maps_det t0 (svpn_of va) q2 q1 qp0 p2 p1 _ Hm0 Hmaps)
          as (-> & -> & ->).
        rewrite pte_set_ad_absorb in Hent. subst ent.
        assert (HPq0 : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                       = pte_canon (mk_pte ppn (kperm_flags kp)))
          by apply pte_canon_set_ad.
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_translate_hit_ex acc Supervisor mxr do_sum
                      Drw Dro Df rs dst Db (svpn_of va) (mword_of_int 0) root_ppn
                      tlbvec p2 p1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                      menvcfg0
                      (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                      pmar0 pcfg paddr rr
                      Hdisj HWtlb Htlb Hslot
                      (uwe_match_self (svpn_of va) p2 p1 _)
                      HDb Hag HDlc Haglc
                      (Hchk a' d' mxr do_sum) (Hchkgleaf _ HPq0 mxr do_sum Db)
                      (HP0pb _ HPq0) HPq0 HPvar HPupd
                      HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                      Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                      Hmisa Hmenv HPBMTE HADUE
                      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                      (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                      HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                      (proj1 Hok0) (proj2 (proj2 Hok0))
                      with "Hcert Hfrag Hrw Hro Hrdx Hwr"). }
        iIntros (v) "(%rsf & -> & %Hshape & Hrw & Hro & Hany)".
        rewrite (kperm_variant_ppn' ppn kp a' d').
        iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany".
        destruct Hshape as [-> | (q0f & HPf & ->)].
        * iPureIntro. left. reflexivity.
        * iPureIntro. right.
          destruct (HPvar q0f _ HPf HP0leaf) as (aq & dq & Hq).
          exists p2, p1, (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0), q0f, aq, dq.
          split; [exact Hmaps |]. split; [exact Hq |]. reflexivity.
      + (* a FOREIGN entry in the slot: the tag rejects it, so the walk runs *)
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_translate_miss_ex acc Supervisor mxr do_sum
                      Drw Dro Df rs dst (svpn_of va) root_ppn (mword_of_int 0)
                      p2 p1 menvcfg0
                      (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                      tlbvec (Some ent) pmar0 pcfg paddr rr
                      Hv2 Hn2 Hv1 Hn1 Higptr1 Higptr2
                      HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                      Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                      HPvar HPupd
                      Hdisj HDtlb HWtlb Htlb Hslot Hnm
                      HDlc Haglc Hmisa Hmenv HPBMTE HADUE
                      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                      (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                      HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                      (proj1 Hok0) (proj2 (proj2 Hok0))
                      with "Hcert Hfrag Hrw Hro Hob2 Hob1 Hob0 Hrdx Hwr"). }
        iIntros (v) "(%q0 & %q0f & %HPq0 & %HPq0f & -> & Hrw & Hro & Hany)".
        destruct (pte_canon_inv _ _ HPq0) as (aq & dq & Hq0).
        rewrite Hq0. rewrite (kperm_variant_ppn' ppn kp aq dq).
        iSplitR; [done |].
        iExists _. iFrame "Hrw Hro Hany".
        iPureIntro. right.
        destruct (HPvar _ _ HPq0f HP0leaf) as (aq2 & dq2 & Hq2).
        exists p2, p1, (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0), q0f, aq2, dq2.
        split; [exact Hmaps |]. split; [exact Hq2 |]. rewrite Htlb. reflexivity.
    - (* an EMPTY slot: the walk runs *)
      iApply (swp_mono with "[] [-]").
      2:{ iApply (swp_translate_miss_ex acc Supervisor mxr do_sum
                    Drw Dro Df rs dst (svpn_of va) root_ppn (mword_of_int 0)
                    p2 p1 menvcfg0
                    (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                    tlbvec None pmar0 pcfg paddr rr
                    Hv2 Hn2 Hv1 Hn1 Higptr1 Higptr2
                    HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                    Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                    HPvar HPupd
                    Hdisj HDtlb HWtlb Htlb Hslot I
                    HDlc Haglc Hmisa Hmenv HPBMTE HADUE
                    HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                    (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                    HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                    (proj1 Hok0) (proj2 (proj2 Hok0))
                    with "Hcert Hfrag Hrw Hro Hob2 Hob1 Hob0 Hrdx Hwr"). }
      iIntros (v) "(%q0 & %q0f & %HPq0 & %HPq0f & -> & Hrw & Hro & Hany)".
      destruct (pte_canon_inv _ _ HPq0) as (aq & dq & Hq0).
      rewrite Hq0. rewrite (kperm_variant_ppn' ppn kp aq dq).
      iSplitR; [done |].
      iExists _. iFrame "Hrw Hro Hany".
      iPureIntro. right.
      destruct (HPvar _ _ HPq0f HP0leaf) as (aq2 & dq2 & Hq2).
      exists p2, p1, (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0), q0f, aq2, dq2.
      split; [exact Hmaps |]. split; [exact Hq2 |]. rewrite Htlb. reflexivity.
  Qed.


  (* the HIT arm on its own, and at a tree that need NOT be [satp]'s root:
     the switch window's PREVIOUS table can be the SHARED kernel one, mapped
     and cached but not the root the walk would start from.  [kroot] is the
     invariant's root, [root_ppn] is [satp]'s; [swp_translate_kpt_slot] above
     needs them equal because its miss arm walks, and this one does not. *)
  Lemma swp_translate_kpt_hit_slot
      (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (root_ppn kroot : mword 44) (t0 : ptree) (va pa satp0 menvcfg0 : mword 64)
      (ppn : mword 44) (kp : kperm)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbvec ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
      = Some (Supervisor, dst) ->
    goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
      dst = true ->
    exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
    goodb Db (is_shadow_stack_access acc) dst = true ->
    exec (translationMode Supervisor) dst = Some (Sv39, dst) ->
    goodb Db (translationMode Supervisor) dst = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64))
      = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    (* the claim's permission check, A/D-quantified (KptShare's premise) *)
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    tlb_slot_hit_pt (mword_of_int 0) t0 tlbvec (svpn_of va) ->
    kmap_at (svpn_of va) ppn kp -∗
    kpt_inv kroot -∗
    kpt_lb t0 -∗
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ kpt_slot_land t0 rs tlbvec (svpn_of va) rsf ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif
      HDb Hag HDlc Haglc Hcp Hsatp Htlb Hhtif Hpma Hpcfg Hpaddr Hmstag
      Hmisa Hmenv HPBMTE HADUE Heff Heffg Hss Hssg Htm Htmg Hppn Hasid
      Hcanon Hident HA Hord HR HW Hcov Hpallow Hchk Htlbok0.
    iIntros "#Hat #Hkinv #Hlb0 #Hcert Hfrag Hrw Hro".
    assert (HDtlb : (tlb : register) ∈ Drw ∪ Dro) by set_solver.
    iApply swp_fupd.
    iMod (kpt_path_at kroot t0 (svpn_of va) ppn kp ⊤ ltac:(solve_ndisj)
            with "Hat Hlb0 Hkinv") as (p2 p1 a0 d0) "%Hpath".
    destruct Hpath as (Hbase & Hmaps & Hok2 & Hok1 & Hok0).
    iModIntro.
    (* the two internal levels' pure facts, off [ptree_maps] *)
    pose proof Hmaps as Hmapsd.
    destruct Hmapsd as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                        Hv2 & Hn2 & Hv1 & Hn1 & _ & _ & _ & _).
    (* the swp layer's footprint companions, which the exec layer never
       needed.  At the two INTERNAL levels they come off [ptree_maps]'
       own [pte_valid] + [pte_ptr] pair ([KptGoodb.pte_ptr_goodb_invalid];
       [pte_ptr] alone would be FALSE -- see that file's header), and at
       the claim's LEAF off the canonical class, with the shadow-stack
       tail taken from the caller's own [Hssg]. *)
    pose proof (kperm_canon_goodb_invalid ppn kp) as Higleaf.
    pose proof (fun w Hc => kperm_canon_goodb_check ppn kp w acc Db dst Hssg Hc)
      as Hchkgleaf.
    (* the leaf predicate, and its three closure facts *)
    assert (HP0i : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                                (ext_bits_of_PTE w)) s = Some (false, s)).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_valid. }
    assert (HP0nl : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_leaf. }
    assert (HP0chk : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall (mxr do_sum : bool) s,
                exec (check_PTE_permission acc Supervisor mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                        (ext_bits_of_PTE w) tt) s
                = Some (PTE_Check_Success tt, s)).
    { intros w Hc mxr do_sum. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply (Hchk a d mxr do_sum). }
    assert (HP0N : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE w)) ('b"1") = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_no_napot. }
    assert (HP0pb : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_pbmt0 w).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_pbmt0. }
    assert (HPvar : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              exists a d : mword 1, w = pte_set_ad w' a d).
    { intros w w' Hw Hw'.
      destruct (pte_canon_inv _ _ Hw) as (a & d & ->).
      destruct (pte_canon_inv _ _ Hw') as (a' & d' & ->).
      exists a, d. symmetry. apply pte_set_ad_absorb. }
    assert (HPupd : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w' ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp))).
    { intros w w' Hw Hu. rewrite autocast_id in Hu.
      destruct (update_PTE_Bits_set_ad _ _ _ Hu) as (a & d & ->).
      rewrite pte_canon_set_ad. exact Hw. }
    (* [P0] admits the claim's own A/D variant, which is the tree's leaf *)
    assert (HP0leaf : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0)
                      = pte_canon (mk_pte ppn (kperm_flags kp)))
      by apply pte_canon_set_ad.
    (* the head *)
    iApply (swp_translateAddr_pt_front_ex acc Supervisor Drw Dro Df rs dst
              (∃ rsf : regstate,
                 ⌜ kpt_slot_land t0 rs tlbvec (svpn_of va) rsf ⌝ ∗
                 hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                 resv_any cpu_id)%I
              Db (svpn_of va) root_ppn ppn satp0 va pa
              Hdisj HDmst HDpriv HDsatp HDb Hag Hcp Hsatp Hmstag
              Heff Heffg Hss Hssg Htm Htmg Hppn Hasid Hcanon eq_refl Hident
              with "Hcert Hrw Hro [Hfrag]").
    iIntros (mxr do_sum) "Hrw Hro".
    (* the leaf re-read and write-back seams; the hit path never walks,
       so the miss path's three read obligations are not needed *)
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               (∃ w : mword 64,
                  ⌜read_bytes σ.(mem)
                     (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                     = Some w⌝ ∗
                  ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝) ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrdx".
    { iApply (kpt_leaf_node_canon kroot t0 (svpn_of va) p2 p1 _ a0 d0 Hmaps
                with "Hlb0 Hkinv"). }
    (* the WRITE seam, in the shape the [_ex] write-back takes *)
    iAssert (∀ (w w' : mword 64),
               ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝ -∗
               ⌜update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w'⌝ -∗
               ∀ σ, ⌜read_bytes σ.(mem)
                       (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                       = Some w⌝ -∗
                   mstate_interp σ ={⊤,∅}=∗
                   ▷ (|={∅,⊤}=> mstate_interp
                        (MState σ.(sregs)
                           (write_bytes σ.(mem)
                              (u_pte_addr (u_next_base p1)
                                 (subrange_vec_dec (svpn_of va) 8 0)) 8
                              (Interface.WriteReq.value
                                 (mwrite_req8_con
                                    (u_pte_addr (u_next_base p1)
                                       (subrange_vec_dec (svpn_of va) 8 0))
                                    (autocast (T := mword) w'))))
                           σ.(mdev)) ∗ True))%I as "Hwr".
    { iIntros (w w') "%HPw %Hu".
      iApply (kpt_leaf_write_node kroot t0 (svpn_of va) ppn kp p2 p1 a0 d0
                w w' Hmaps
                ltac:(destruct (pte_canon_inv _ _ (HPupd w w' HPw Hu))
                        as (a & d & Hw'); exists a, d; exact Hw')
                with "Hat Hlb0 Hkinv"). }
    (* THE HIT, off the caller-supplied slot fact *)
    destruct Htlbok0 as (q2 & q1 & qp0 & a' & d' & Hm0 & Hslot).
    destruct (ptree_maps_det t0 (svpn_of va) q2 q1 qp0 p2 p1 _ Hm0 Hmaps)
      as (-> & -> & ->).
    rewrite pte_set_ad_absorb in Hslot.
        assert (HPq0 : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                       = pte_canon (mk_pte ppn (kperm_flags kp)))
          by apply pte_canon_set_ad.
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_translate_hit_ex acc Supervisor mxr do_sum
                      Drw Dro Df rs dst Db (svpn_of va) (mword_of_int 0) root_ppn
                      tlbvec p2 p1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                      menvcfg0
                      (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                      pmar0 pcfg paddr rr
                      Hdisj HWtlb Htlb Hslot
                      (uwe_match_self (svpn_of va) p2 p1 _)
                      HDb Hag HDlc Haglc
                      (Hchk a' d' mxr do_sum) (Hchkgleaf _ HPq0 mxr do_sum Db)
                      (HP0pb _ HPq0) HPq0 HPvar HPupd
                      HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                      Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                      Hmisa Hmenv HPBMTE HADUE
                      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                      (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                      HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                      (proj1 Hok0) (proj2 (proj2 Hok0))
                      with "Hcert Hfrag Hrw Hro Hrdx Hwr"). }
        iIntros (v) "(%rsf & -> & %Hshape & Hrw & Hro & Hany)".
        rewrite (kperm_variant_ppn' ppn kp a' d').
        iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany".
        destruct Hshape as [-> | (q0f & HPf & ->)].
        * iPureIntro. left. reflexivity.
        * iPureIntro. right.
          destruct (HPvar q0f _ HPf HP0leaf) as (aq & dq & Hq).
          exists p2, p1, (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0), q0f, aq, dq.
          split; [exact Hmaps |]. split; [exact Hq |]. reflexivity.

  Qed.

End Pt2SharedWalk.

(* ===================================================================== *)
(* 4. THE WINDOW'S RESIDUE, AND THE WINDOW'S WALK.                        *)
(*                                                                        *)
(* The residue is what is left of [TransPt.tlb_inv_pt2_kcur] / [_kprev]    *)
(* once the four CELLS the walk reads and writes -- satp, tlb, pmpcfg_n,   *)
(* pmpaddr_n -- move into the engine's frame; the split is exactly the one *)
(* [UptWalkPt.upt_swp_open] / [_close] makes for the user table.           *)
(*                                                                        *)
(* The walk dispatches ONCE on the slot [va] hashes to and then runs the   *)
(* single route that fits the tree that arm touches -- section 2's for the *)
(* owned table, section 3's for the shared one.                            *)
(* ===================================================================== *)

Section Pt2Window.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- uservec's window: the SHARED kernel table is CURRENT ---------- *)

  Definition pt2_res_kcur (rc : mword 44) (Sp : ptree -> Prop)
      (tv : type_of_register tlb) : iProp Σ :=
    (∃ tp tc0 : ptree,
       ⌜ tlb_ok_pt2 (mword_of_int 0) tp tc0 tv ⌝ ∗ ⌜ Sp tp ⌝ ∗
       ptree_own 2 (DfracOwn 1) tp ∗ kpt_lb tc0 ∗ kpt_inv rc)%I.

  Lemma pt2_kcur_swp_open (rc : mword 44) (Sp : ptree -> Prop) :
    tlb_inv_pt2_kcur rc Sp -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ upt_satp_ok_pt rc satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      pt2_res_kcur rc Sp tlbv.
  Proof.
    iIntros "H".
    iDestruct (tlb_inv_pt2_kcur_open with "H") as (satp0 tlbvec tp tc0)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSp & %Hpmaw &
        Htp & Hpmp & #Hlb0 & #Hkinv)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists satp0, tlbvec, pcfg, paddr.
    iSplitR;
      [ iPureIntro; unfold upt_satp_ok_pt; split_and!; assumption |].
    iSplitR;
      [ iPureIntro; unfold pmp_ent0_ok; split_and!; assumption |].
    iFrame "Hsatp Htlb Hpcfg Hpaddr".
    iExists tp, tc0. iFrame "Htp Hlb0 Hkinv". iPureIntro.
    split; [ exact Hok2 | exact HSp ].
  Qed.

  Lemma pt2_kcur_swp_close (rc : mword 44) (Sp : ptree -> Prop)
      (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
    pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    pt2_res_kcur rc Sp tlbv -∗
    tlb_inv_pt2_kcur rc Sp.
  Proof.
    intros (Hmode & Hasid & Hppn & Hpmaw) (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlb Hpcfg Hpaddr Hres".
    iDestruct "Hres" as (tp tc0) "(%Hok2 & %HSp & Htp & #Hlb0 & #Hkinv)".
    iApply (tlb_inv_pt2_kcur_intro rc Sp satp0 tlbv tp tc0
              Hmode Hasid Hppn Hok2 HSp Hpmaw
              with "Hsatp Htlb Htp [Hpcfg Hpaddr] Hlb0 Hkinv").
    iApply (pmp_config_intro rc pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

  (* ---- userret's window: the SHARED kernel table is PREVIOUS --------- *)

  Definition pt2_res_kprev (rc kroot : mword 44) (Sc : ptree -> Prop)
      (tv : type_of_register tlb) : iProp Σ :=
    (∃ tp0 tc : ptree,
       ⌜ tlb_ok_pt2 (mword_of_int 0) tp0 tc tv ⌝ ∗ ⌜ Sc tc ⌝ ∗
       ptree_own 2 (DfracOwn 1) tc ∗ kpt_lb tp0 ∗ kpt_inv kroot)%I.

  Lemma pt2_kprev_swp_open (rc kroot : mword 44) (Sc : ptree -> Prop) :
    tlb_inv_pt2_kprev rc kroot Sc -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ upt_satp_ok_pt rc satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      pt2_res_kprev rc kroot Sc tlbv.
  Proof.
    iIntros "H".
    iDestruct (tlb_inv_pt2_kprev_open with "H") as (satp0 tlbvec tp0 tc)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok2 & %HSc & %Hpmaw &
        Htc & Hpmp & #Hlb0 & #Hkinv)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists satp0, tlbvec, pcfg, paddr.
    iSplitR;
      [ iPureIntro; unfold upt_satp_ok_pt; split_and!; assumption |].
    iSplitR;
      [ iPureIntro; unfold pmp_ent0_ok; split_and!; assumption |].
    iFrame "Hsatp Htlb Hpcfg Hpaddr".
    iExists tp0, tc. iFrame "Htc Hlb0 Hkinv". iPureIntro.
    split; [ exact Hok2 | exact HSc ].
  Qed.

  Lemma pt2_kprev_swp_close (rc kroot : mword 44) (Sc : ptree -> Prop)
      (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
    pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    pt2_res_kprev rc kroot Sc tlbv -∗
    tlb_inv_pt2_kprev rc kroot Sc.
  Proof.
    intros (Hmode & Hasid & Hppn & Hpmaw) (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlb Hpcfg Hpaddr Hres".
    iDestruct "Hres" as (tp0 tc) "(%Hok2 & %HSc & Htc & #Hlb0 & #Hkinv)".
    iApply (tlb_inv_pt2_kprev_intro rc kroot Sc satp0 tlbv tp0 tc
              Hmode Hasid Hppn Hok2 HSc Hpmaw
              with "Hsatp Htlb Htc [Hpcfg Hpaddr] Hlb0 Hkinv").
    iApply (pmp_config_intro rc pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

  (* ---- the two walks ------------------------------------------------- *)

  Lemma swp_translate_pt2_kcur (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (rc : mword 44) (Sp : ptree -> Prop) (ppn : mword 44) (kp : kperm)
      (va pa satp0 mst0 : mword 64)
      (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (rr : option resv) :
    Drw ## Dro ->
    (forall r : register, upt_Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, upt_Dw r = true -> r ∈ Drw) ->
    s_acc_ok acc ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mstatus rs = mst0 ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbv ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup pma_regions rs = pmar0 ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    (forall t, Sp t -> exists p2 p1 (a d : mword 1),
       ptree_maps t (svpn_of va) p2 p1
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    (forall t (a1 d1 : mword 1), Sp t ->
       Sp (ptree_set_leaf t (svpn_of va)
             (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1))) ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc Supervisor mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) 7 0))
                   (ext_bits_of_PTE
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) tt)
              s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    kmap_at (svpn_of va) ppn kp -∗
    gen_cert -∗ resv_frag cpu_id rr -∗
    pt2_res_kcur rc Sp tlbv -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  pt2_res_kcur rc Sp (register_lookup tlb rsf) ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
           Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
           Hsel Hpres Hchk Hgchk Hcanon Hident.
    pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
    pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hat #Hcert Hfrag Hres Hrw Hro".
    iDestruct "Hres" as (tp tc0) "(%Hok2 & %HSp & Htp & #Hlb0 & #Hkinv)".
    destruct (Hsel tp HSp) as (pp2 & pp1 & ap & dp & Hmaps_p).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags kp) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn kp ('b"1") ('b"1")) in Hident.
      rewrite pte_set_ad_ppn in Hident. exact Hident. }
    assert (Hvar : forall a d : mword 1,
              pte_valid (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_leaf (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_no_napot (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)).
    { intros a d. split_and!;
        [ apply kperm_variant_valid | apply kperm_variant_leaf
        | apply kperm_variant_no_napot | apply kperm_variant_pbmt0 ]. }
    (* THE DISPATCH.  Either the slot holds this vpn's entry off the OWNED
       (previous) table -- and then the walk touches only that table's leaf --
       or whatever it holds leaves the SHARED (current) table's own walk
       admissible. *)
    assert (Hdisp : tlb_slot_hit_pt (mword_of_int 0) tp tlbv (svpn_of va)
                    \/ tlb_slot_pt (mword_of_int 0) tc0 tlbv (svpn_of va)).
    { destruct (vec_access_dec tlbv (tlb_hash (__id 39) (svpn_of va)))
        as [ent |] eqn:Hslot.
      - destruct (Hok2 (svpn_of va) ent Hslot) as [Hp | Hc].
        + destruct Hp as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & Hent).
          destruct (decide (vpn0 = svpn_of va)) as [-> | Hne].
          * left. exists q2, q1, qp0, a', d'.
            split; [ exact Hm0 | rewrite Hslot Hent; reflexivity ].
          * right. apply (tlb_slot_pt_one_nomatch tc0 tlbv _ ent Hslot).
            rewrite Hent.
            exact (uwe_match_other vpn0 (svpn_of va) q2 q1 (pte_set_ad qp0 a' d')
                     (mword_of_int 0) Hne).
        + right. exact (tlb_slot_pt_one tc0 tlbv _ ent Hslot Hc).
      - right. exact (tlb_slot_pt_none tc0 tlbv _ Hslot). }
    destruct Hdisp as [Hhit | Hslotc].
    - (* the OWNED (previous) table's own hit *)
      destruct Hhit as (q2 & q1 & q0 & a' & d' & Hm0 & Hslot).
      destruct (ptree_maps_det tp (svpn_of va) q2 q1 q0 pp2 pp1 _ Hm0 Hmaps_p)
        as (-> & -> & ->).
      iApply (swp_mono with "[] [-]").
      2:{ iApply (swp_translate_pt_hit_slot acc Drw Dro Df rs rc tp
                    va pa satp0 (mk_pte ppn (kperm_flags kp)) mst0
                    pp2 pp1 ap dp a' d' tlbv pcfg paddr pmar0 rr
                    Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
                    Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
                    Hmaps_p Hslot Hvar Hchk Hgchk Hcanon Hout
                    with "Hcert Hfrag Htp Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf t') "(%Hshapef & Hrw & Hro & Htp & Hany)".
      iSplitR; [done|]. iExists rsf. iFrame "Hrw Hro Hany".
      destruct Hshapef as [(-> & ->) | (a1 & d1 & -> & Ht')].
      + iSplitR; [iPureIntro; left; reflexivity |].
        rewrite Htlb. iExists tp, tc0. iFrame "Htp Hlb0 Hkinv". iPureIntro.
        split; [ exact Hok2 | exact HSp ].
      + assert (Habs : pte_set_ad (pte_set_ad (mk_pte ppn (kperm_flags kp)) ap dp) a1 d1
                       = pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1)
          by exact (pte_set_ad_absorb (mk_pte ppn (kperm_flags kp)) ap dp a1 d1).
        pose proof (Hvar a1 d1) as (Hv1' & Hl1' & Hn1' & Hp1').
        rewrite <- Habs in Hv1', Hl1', Hn1', Hp1'.
        iSplitR; [iPureIntro; right; eexists; reflexivity |].
        rewrite register_lookup_set_tlb.
        destruct Ht' as [-> | ->].
        * iExists tp, tc0. iFrame "Htp Hlb0 Hkinv". iPureIntro.
          split; [| exact HSp ].
          apply (tlb_ok_pt2_fill_prev (mword_of_int 0) tp tc0 tlbv (svpn_of va)
                   pp2 pp1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) ap dp)
                   (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1) Hmaps_p
                   (ex_intro _ a1 (ex_intro _ d1 (eq_sym Habs))) Hok2).
        * iExists (ptree_set_leaf tp (svpn_of va)
                     (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1)), tc0.
          iFrame "Htp Hlb0 Hkinv". iPureIntro.
          split; [| exact (Hpres tp a1 d1 HSp) ].
          rewrite <- Habs.
          apply (tlb_ok_pt2_fill_prev (mword_of_int 0)
                   (ptree_set_leaf tp (svpn_of va)
                      (pte_set_ad (pte_set_ad (mk_pte ppn (kperm_flags kp)) ap dp) a1 d1))
                   tc0 tlbv (svpn_of va) pp2 pp1 _ _
                   (ptree_set_leaf_maps_self tp (svpn_of va) pp2 pp1
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) ap dp) _ Hmaps_p
                      Hv1' Hl1' Hn1' Hp1')
                   (pte_set_ad_refl _)
                   (tlb_ok_pt2_set_leaf_prev (mword_of_int 0) tp tc0 tlbv
                      (svpn_of va) pp2 pp1
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) ap dp) a1 d1
                      Hmaps_p Hv1' Hl1' Hn1' Hp1' Hok2)).
    - (* the SHARED (current) table's walk *)
      assert (Lmst : (mstatus : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpriv : (cur_privilege : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lsatpin : (satp : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Ltlbw : (tlb : register) ∈ Drw)
        by (apply HDw; vm_compute; reflexivity).
      assert (Lpmain : (pma_regions : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpcfgin : (pmpcfg_n : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpaddrin : (pmpaddr_n : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lhtifin : (htif_tohost_base : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Llc : forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro)
        by (intros r Hr; apply HDr;
            exact (D_leafchk_sub upt_Dr ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity) r Hr)).
      set (dst := MState rs (∅ : pamap) dev0_state).
      assert (LMPRV : eq_vec (_get_Mstatus_MPRV
                (register_lookup mstatus dst.(sregs))) ('b"1") = false)
        by (unfold dst; cbn [sregs]; rewrite Hms; exact HMPRV).
      assert (LSXL : _get_Mstatus_SXL
                (register_lookup mstatus dst.(sregs)) = 'b"10")
        by (unfold dst; cbn [sregs]; rewrite Hms; exact HSXL).
      iApply (swp_mono with "[Htp] [-]").
      2:{ iApply (swp_translate_kpt_slot acc Drw Dro Df rs dst upt_Dr
                    rc tc0 va pa satp0 MENVCFG_S ppn kp tlbv pmar0 pcfg paddr rr
                    Hdisjf Lmst Lpriv Lsatpin Ltlbw Lpmain Lpcfgin Lpaddrin
                    Lhtifin HDr (fun r _ => eq_refl) Llc (fun r _ => eq_refl)
                    Hcp Hsatp Htlb Hhtif Hpma Hpcfg Hpaddr eq_refl
                    Hmisa Hmenv
                    ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    (s_eff_exec acc _ Supervisor dst LMPRV)
                    (s_eff_goodb acc _ Supervisor upt_Dr dst LMPRV)
                    (s_acc_ssa_exec acc dst Hacc)
                    (s_acc_ssa_goodb acc upt_Dr dst Hacc)
                    (exec_translationMode_S_sv39 satp0 dst LSXL Hsatp Hmode)
                    (goodb_translationMode_S_sv39 upt_Dr satp0 dst
                       ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) LSXL Hsatp Hmode)
                    Hppn Hasid Hcanon Hident HA Hord HR HW Hcov
                    (pma_all_ram Hall) Hchk Hslotc
                    with "Hat Hkinv Hlb0 Hcert Hfrag Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf) "(%Hland & Hrw & Hro & Hany)".
      iSplitR; [done|]. iExists rsf. iFrame "Hrw Hro Hany".
      destruct Hland as [-> | (q2 & q1 & q0 & qf & aq & dq & Hm & -> & ->)].
      + iSplitR; [iPureIntro; left; reflexivity |].
        rewrite Htlb. iExists tp, tc0. iFrame "Htp Hlb0 Hkinv". iPureIntro.
        split; [ exact Hok2 | exact HSp ].
      + iSplitR; [iPureIntro; right; eexists; reflexivity |].
        rewrite register_lookup_set_tlb.
        iExists tp, tc0. iFrame "Htp Hlb0 Hkinv". iPureIntro.
        split; [| exact HSp ].
        apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp tc0 tlbv (svpn_of va)
                 q2 q1 q0 (pte_set_ad q0 aq dq) Hm
                 (ex_intro _ aq (ex_intro _ dq eq_refl)) Hok2).
  Qed.

  Lemma swp_translate_pt2_kprev (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (rc kroot : mword 44) (Sc : ptree -> Prop) (ppn : mword 44) (kp : kperm)
      (va pa satp0 mst0 : mword 64)
      (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (rr : option resv) :
    Drw ## Dro ->
    (forall r : register, upt_Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, upt_Dw r = true -> r ∈ Drw) ->
    s_acc_ok acc ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mstatus rs = mst0 ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbv ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup pma_regions rs = pmar0 ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    (forall t, Sc t -> pt_base t = rc) ->
    (forall t, Sc t -> exists p2 p1 (a d : mword 1),
       ptree_maps t (svpn_of va) p2 p1
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    (forall t (a1 d1 : mword 1), Sc t ->
       Sc (ptree_set_leaf t (svpn_of va)
             (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1))) ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc Supervisor mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) 7 0))
                   (ext_bits_of_PTE
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) tt)
              s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    kmap_at (svpn_of va) ppn kp -∗
    gen_cert -∗ resv_frag cpu_id rr -∗
    pt2_res_kprev rc kroot Sc tlbv -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  pt2_res_kprev rc kroot Sc (register_lookup tlb rsf) ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
           Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
           Hbc Hsel Hpres Hchk Hgchk Hcanon Hident.
    pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
    pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hat #Hcert Hfrag Hres Hrw Hro".
    iDestruct "Hres" as (tp0 tc) "(%Hok2 & %HSc & Htc & #Hlb0 & #Hkinv)".
    destruct (Hsel tc HSc) as (uc2 & uc1 & au & du & Hmaps_c).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags kp) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn kp ('b"1") ('b"1")) in Hident.
      rewrite pte_set_ad_ppn in Hident. exact Hident. }
    assert (Hvar : forall a d : mword 1,
              pte_valid (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_leaf (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_no_napot (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
              pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)).
    { intros a d. split_and!;
        [ apply kperm_variant_valid | apply kperm_variant_leaf
        | apply kperm_variant_no_napot | apply kperm_variant_pbmt0 ]. }
    (* THE DISPATCH, mirrored: the SHARED table is now the previous one *)
    assert (Hdisp : tlb_slot_hit_pt (mword_of_int 0) tp0 tlbv (svpn_of va)
                    \/ tlb_slot_pt (mword_of_int 0) tc tlbv (svpn_of va)).
    { destruct (vec_access_dec tlbv (tlb_hash (__id 39) (svpn_of va)))
        as [ent |] eqn:Hslot.
      - destruct (Hok2 (svpn_of va) ent Hslot) as [Hp | Hc].
        + destruct Hp as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & Hent).
          destruct (decide (vpn0 = svpn_of va)) as [-> | Hne].
          * left. exists q2, q1, qp0, a', d'.
            split; [ exact Hm0 | rewrite Hslot Hent; reflexivity ].
          * right. apply (tlb_slot_pt_one_nomatch tc tlbv _ ent Hslot).
            rewrite Hent.
            exact (uwe_match_other vpn0 (svpn_of va) q2 q1 (pte_set_ad qp0 a' d')
                     (mword_of_int 0) Hne).
        + right. exact (tlb_slot_pt_one tc tlbv _ ent Hslot Hc).
      - right. exact (tlb_slot_pt_none tc tlbv _ Hslot). }
    destruct Hdisp as [Hhit | Hslotc].
    - (* the SHARED (previous) table's own hit *)
      assert (Lmst : (mstatus : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpriv : (cur_privilege : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lsatpin : (satp : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Ltlbw : (tlb : register) ∈ Drw)
        by (apply HDw; vm_compute; reflexivity).
      assert (Lpmain : (pma_regions : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpcfgin : (pmpcfg_n : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lpaddrin : (pmpaddr_n : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Lhtifin : (htif_tohost_base : register) ∈ Drw ∪ Dro)
        by (apply HDr; vm_compute; reflexivity).
      assert (Llc : forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro)
        by (intros r Hr; apply HDr;
            exact (D_leafchk_sub upt_Dr ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity) r Hr)).
      set (dst := MState rs (∅ : pamap) dev0_state).
      assert (LMPRV : eq_vec (_get_Mstatus_MPRV
                (register_lookup mstatus dst.(sregs))) ('b"1") = false)
        by (unfold dst; cbn [sregs]; rewrite Hms; exact HMPRV).
      assert (LSXL : _get_Mstatus_SXL
                (register_lookup mstatus dst.(sregs)) = 'b"10")
        by (unfold dst; cbn [sregs]; rewrite Hms; exact HSXL).
      iApply (swp_mono with "[Htc] [-]").
      2:{ iApply (swp_translate_kpt_hit_slot acc Drw Dro Df rs dst upt_Dr
                    rc kroot tp0 va pa satp0 MENVCFG_S ppn kp tlbv pmar0
                    pcfg paddr rr
                    Hdisjf Lmst Lpriv Lsatpin Ltlbw Lpmain Lpcfgin Lpaddrin
                    Lhtifin HDr (fun r _ => eq_refl) Llc (fun r _ => eq_refl)
                    Hcp Hsatp Htlb Hhtif Hpma Hpcfg Hpaddr eq_refl
                    Hmisa Hmenv
                    ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    (s_eff_exec acc _ Supervisor dst LMPRV)
                    (s_eff_goodb acc _ Supervisor upt_Dr dst LMPRV)
                    (s_acc_ssa_exec acc dst Hacc)
                    (s_acc_ssa_goodb acc upt_Dr dst Hacc)
                    (exec_translationMode_S_sv39 satp0 dst LSXL Hsatp Hmode)
                    (goodb_translationMode_S_sv39 upt_Dr satp0 dst
                       ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) LSXL Hsatp Hmode)
                    Hppn Hasid Hcanon Hident HA Hord HR HW Hcov
                    (pma_all_ram Hall) Hchk Hhit
                    with "Hat Hkinv Hlb0 Hcert Hfrag Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf) "(%Hland & Hrw & Hro & Hany)".
      iSplitR; [done|]. iExists rsf. iFrame "Hrw Hro Hany".
      destruct Hland as [-> | (q2 & q1 & q0 & qf & aq & dq & Hm & -> & ->)].
      + iSplitR; [iPureIntro; left; reflexivity |].
        rewrite Htlb. iExists tp0, tc. iFrame "Htc Hlb0 Hkinv". iPureIntro.
        split; [ exact Hok2 | exact HSc ].
      + iSplitR; [iPureIntro; right; eexists; reflexivity |].
        rewrite register_lookup_set_tlb.
        iExists tp0, tc. iFrame "Htc Hlb0 Hkinv". iPureIntro.
        split; [| exact HSc ].
        apply (tlb_ok_pt2_fill_prev (mword_of_int 0) tp0 tc tlbv (svpn_of va)
                 q2 q1 q0 (pte_set_ad q0 aq dq) Hm
                 (ex_intro _ aq (ex_intro _ dq eq_refl)) Hok2).
    - (* the OWNED (current) table's walk *)
      iApply (swp_mono with "[] [-]").
      2:{ iApply (swp_translate_pt_slot acc Drw Dro Df rs rc tc
                    va pa satp0 (mk_pte ppn (kperm_flags kp)) mst0
                    uc2 uc1 au du tlbv pcfg paddr pmar0 rr
                    Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
                    Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall
                    (Hbc tc HSc) Hmaps_c Hslotc Hvar Hchk Hgchk Hcanon Hout
                    with "Hcert Hfrag Htc Hrw Hro"). }
      iIntros (v) "(-> & Hf)".
      iDestruct "Hf" as (rsf t') "(%Hshapef & Hrw & Hro & Htc & Hany)".
      iSplitR; [done|]. iExists rsf. iFrame "Hrw Hro Hany".
      destruct Hshapef as [(-> & ->) | (a1 & d1 & -> & Ht')].
      + iSplitR; [iPureIntro; left; reflexivity |].
        rewrite Htlb. iExists tp0, tc. iFrame "Htc Hlb0 Hkinv". iPureIntro.
        split; [ exact Hok2 | exact HSc ].
      + assert (Habs : pte_set_ad (pte_set_ad (mk_pte ppn (kperm_flags kp)) au du) a1 d1
                       = pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1)
          by exact (pte_set_ad_absorb (mk_pte ppn (kperm_flags kp)) au du a1 d1).
        pose proof (Hvar a1 d1) as (Hv1' & Hl1' & Hn1' & Hp1').
        rewrite <- Habs in Hv1', Hl1', Hn1', Hp1'.
        iSplitR; [iPureIntro; right; eexists; reflexivity |].
        rewrite register_lookup_set_tlb.
        destruct Ht' as [-> | ->].
        * iExists tp0, tc. iFrame "Htc Hlb0 Hkinv". iPureIntro.
          split; [| exact HSc ].
          apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp0 tc tlbv (svpn_of va)
                   uc2 uc1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) au du)
                   (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1) Hmaps_c
                   (ex_intro _ a1 (ex_intro _ d1 (eq_sym Habs))) Hok2).
        * iExists tp0, (ptree_set_leaf tc (svpn_of va)
                          (pte_set_ad (mk_pte ppn (kperm_flags kp)) a1 d1)).
          iFrame "Htc Hlb0 Hkinv". iPureIntro.
          split; [| exact (Hpres tc a1 d1 HSc) ].
          rewrite <- Habs.
          apply (tlb_ok_pt2_fill_cur (mword_of_int 0) tp0
                   (ptree_set_leaf tc (svpn_of va)
                      (pte_set_ad (pte_set_ad (mk_pte ppn (kperm_flags kp)) au du) a1 d1))
                   tlbv (svpn_of va) uc2 uc1 _ _
                   (ptree_set_leaf_maps_self tc (svpn_of va) uc2 uc1
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) au du) _ Hmaps_c
                      Hv1' Hl1' Hn1' Hp1')
                   (pte_set_ad_refl _)
                   (tlb_ok_pt2_set_leaf_cur (mword_of_int 0) tp0 tc tlbv
                      (svpn_of va) uc2 uc1
                      (pte_set_ad (mk_pte ppn (kperm_flags kp)) au du) a1 d1
                      Hmaps_c Hv1' Hl1' Hn1' Hp1' Hok2)).
  Qed.

End Pt2Window.

(* ===================================================================== *)
(* 5. THE TRAMPOLINE FETCH, ON THE SWITCH WINDOW.                         *)
(*                                                                        *)
(* [TrampStepPt.tramp_tr_obl] at [Res := pt2_res_kcur rc Sp] resp.         *)
(* [pt2_res_kprev rc kroot Sc].  BESPOKE, exactly as the user table's      *)
(* [UptWalkPt.utramp_tr_obl] is: the window is not an [SRegime.s_regime]   *)
(* -- [sr_inv] is keyed on ONE table's claim, and the window's two are     *)
(* asymmetric (one owned + abstract, one shared + snapshot).               *)
(*                                                                        *)
(* The claim side is the caller's own [kmap_at tramp_vpn tramp_ppn KP_rx]  *)
(* -- the same resource [TransPt.pt2_tramp_fetch_habs_kcur] / [_kprev]     *)
(* took, and their geometry premises carry over verbatim.  The class-KP_rx *)
(* leaf [mk_pte tramp_ppn (kperm_flags KP_rx)] IS [pte_tramp] modulo A/D   *)
(* ([KptTree.kperm_rx_tramp_variant]), which is what lets the OWNED side's *)
(* [TransPt.pt2_tramp_spec] clauses discharge the walk's premises.         *)
(* ===================================================================== *)

Section Pt2Tramp.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac tlbpeel :=
    rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  (* the trampoline leaf's fetch check, in the class-keyed spelling the
     window's walk takes *)
  Local Lemma rx_chk (a d : mword 1) (mxr do_sum : bool) :
    pte_check_ok (InstructionFetch tt) Supervisor mxr do_sum
      (pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a d).
  Proof. exact (kperm_variant_check_fetch tramp_ppn a d mxr do_sum). Qed.

  Local Lemma rx_gchk (a d : mword 1) (mxr do_sum : bool)
      (Db : register -> bool) (s0 : mstate) :
    goodb Db (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
                (Mk_PTE_Flags (subrange_vec_dec
                   (pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a d) 7 0))
                (ext_bits_of_PTE
                   (pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a d)) tt)
           s0 = true.
  Proof.
    exact (kperm_variant_goodb_check tramp_ppn KP_rx a d (InstructionFetch tt)
             mxr do_sum Db s0
             (s_acc_ssa_goodb (InstructionFetch tt) Db s0 (or_introl eq_refl))
             Db s0).
  Qed.

  (* [TransPt.pt2_tramp_spec]'s two clauses, moved onto the class-keyed leaf
     and onto the fetched va's own vpn *)
  Local Lemma rx_sel (S : ptree -> Prop) (va : mword 64) :
    svpn_of va = tramp_vpn -> pt2_tramp_spec S ->
    forall t, S t -> exists p2 p1 (a d : mword 1),
      ptree_maps t (svpn_of va) p2 p1
        (pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a d).
  Proof.
    intros Hvpn (Hsel & _) t HS. rewrite Hvpn.
    destruct (Hsel t HS) as (p2 & p1 & a & d & Hm).
    exists p2, p1, a, d. rewrite kperm_rx_tramp_variant. exact Hm.
  Qed.

  Local Lemma rx_pres (S : ptree -> Prop) (va : mword 64) :
    svpn_of va = tramp_vpn -> pt2_tramp_spec S ->
    forall t (a1 d1 : mword 1), S t ->
      S (ptree_set_leaf t (svpn_of va)
           (pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a1 d1)).
  Proof.
    intros Hvpn (_ & Hpres) t a1 d1 HS.
    rewrite Hvpn kperm_rx_tramp_variant. exact (Hpres t a1 d1 HS).
  Qed.

  (* ---- uservec's window ---------------------------------------------- *)

  Lemma pt2_tramp_tr_obl_kcur (rc : mword 44) (Sp : ptree -> Prop)
      (Df : register -> dfrac)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) :
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    pt2_tramp_spec Sp ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    gen_cert -∗
    tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
      (pt2_res_kcur rc Sp).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma HSp.
    iIntros "#Hat #Hcert". rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hatva".
    { rewrite Hvpn. iApply "Hat". }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_translate_pt2_kcur (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  rc Sp tramp_ppn KP_rx va pax satp0 mst0 tv pcfg paddr pmar0 rr
                  s_disj upt_Dr_in_s upt_Dw_in_s (or_introl eq_refl)
                  ltac:(rewrite s_rs_misa; exact Hmisa)
                  ltac:(rewrite s_rs_menv; exact Hmenv)
                  ltac:(apply s_rs_htif) ltac:(apply s_rs_priv)
                  ltac:(apply s_rs_mst) HSXL HMPRV
                  ltac:(apply s_rs_satp) ltac:(apply s_rs_tlb)
                  ltac:(apply s_rs_pcfg) ltac:(apply s_rs_paddr)
                  ltac:(apply s_rs_pma)
                  Hsatpok Hpmpok Hpma
                  (rx_sel Sp va Hvpn HSp) (rx_pres Sp va Hvpn HSp)
                  rx_chk rx_gchk Hcanon Hident
                  with "Hatva Hcert Hfrag HRes Hrw Hro"). }
    iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & HRes & Hany)".
    iSplitR; [done |].
    destruct Hshape as [-> | (tvx & ->)].
    - iExists tv. rewrite s_rs_tlb. iFrame "Hany Hrw Hro HRes".
    - assert (Ltlbv : register_lookup tlb
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = tvx)
        by apply register_lookup_set.
      assert (Hag : reg_agree_on (s_Drw ∪ s_Dro)
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx)).
      { apply (s_rs_agree pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx);
          [ tlbpeel; apply s_rs_PC
          | tlbpeel; apply s_rs_nPC
          | tlbpeel; apply s_rs_ms
          | tlbpeel; apply s_rs_mi
          | tlbpeel; apply s_rs_cy
          | tlbpeel; apply s_rs_ti
          | tlbpeel; apply s_rs_ip
          | exact Ltlbv
          | tlbpeel; apply s_rs_priv
          | tlbpeel; apply s_rs_mst
          | tlbpeel; apply s_rs_hart
          | tlbpeel; apply s_rs_pcfg
          | tlbpeel; apply s_rs_paddr
          | tlbpeel; apply s_rs_mc
          | tlbpeel; apply s_rs_micfg
          | tlbpeel; apply s_rs_misa
          | tlbpeel; apply s_rs_sec
          | tlbpeel; apply s_rs_pma
          | tlbpeel; apply s_rs_htif
          | tlbpeel; apply s_rs_elp
          | tlbpeel; apply s_rs_senv
          | tlbpeel; apply s_rs_satp
          | tlbpeel; apply s_rs_mie
          | tlbpeel; apply s_rs_mdl
          | tlbpeel; apply s_rs_menv ]. }
      iDestruct (s_rw_ext _ _ Hag with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen Df _ _ Hag with "Hro") as "Hro".
      iExists tvx. rewrite Ltlbv. iFrame "Hany Hrw Hro HRes".
  Qed.

  Lemma pt2_tramp_fetch_tr_kcur (rc : mword 44) (Sp : ptree -> Prop)
      (dq : dfrac) (pc mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pt2_tramp_spec Sp ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (pt2_res_kcur rc Sp) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok HSp.
    iIntros "#Hat #Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /tramp_fetch_tr.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (pt2_tramp_tr_obl_kcur rc Sp (s_Df_mix dq) pc ms bmi cy ti ip mst0
                 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0 satp0
                 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma
                 HSp with "Hat Hcert") as "#Hobl".
    iApply ("Hobl" $! va pax tv rr with "[%] [%] [%] Hfrag HRes Hrw Hro");
      [ exact Hcanon | exact Hvpn | exact Hident ].
  Qed.

  (* ---- userret's window ---------------------------------------------- *)

  Lemma pt2_tramp_tr_obl_kprev (rc kroot : mword 44) (Sc : ptree -> Prop)
      (Df : register -> dfrac)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) :
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    pt2_tramp_spec Sc ->
    (forall t, Sc t -> pt_base t = rc) ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    gen_cert -∗
    tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
      (pt2_res_kprev rc kroot Sc).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma HSc Hbc.
    iIntros "#Hat #Hcert". rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hatva".
    { rewrite Hvpn. iApply "Hat". }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_translate_pt2_kprev (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  rc kroot Sc tramp_ppn KP_rx va pax satp0 mst0 tv pcfg paddr
                  pmar0 rr
                  s_disj upt_Dr_in_s upt_Dw_in_s (or_introl eq_refl)
                  ltac:(rewrite s_rs_misa; exact Hmisa)
                  ltac:(rewrite s_rs_menv; exact Hmenv)
                  ltac:(apply s_rs_htif) ltac:(apply s_rs_priv)
                  ltac:(apply s_rs_mst) HSXL HMPRV
                  ltac:(apply s_rs_satp) ltac:(apply s_rs_tlb)
                  ltac:(apply s_rs_pcfg) ltac:(apply s_rs_paddr)
                  ltac:(apply s_rs_pma)
                  Hsatpok Hpmpok Hpma Hbc
                  (rx_sel Sc va Hvpn HSc) (rx_pres Sc va Hvpn HSc)
                  rx_chk rx_gchk Hcanon Hident
                  with "Hatva Hcert Hfrag HRes Hrw Hro"). }
    iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & HRes & Hany)".
    iSplitR; [done |].
    destruct Hshape as [-> | (tvx & ->)].
    - iExists tv. rewrite s_rs_tlb. iFrame "Hany Hrw Hro HRes".
    - assert (Ltlbv : register_lookup tlb
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = tvx)
        by apply register_lookup_set.
      assert (Hag : reg_agree_on (s_Drw ∪ s_Dro)
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx)).
      { apply (s_rs_agree pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx);
          [ tlbpeel; apply s_rs_PC
          | tlbpeel; apply s_rs_nPC
          | tlbpeel; apply s_rs_ms
          | tlbpeel; apply s_rs_mi
          | tlbpeel; apply s_rs_cy
          | tlbpeel; apply s_rs_ti
          | tlbpeel; apply s_rs_ip
          | exact Ltlbv
          | tlbpeel; apply s_rs_priv
          | tlbpeel; apply s_rs_mst
          | tlbpeel; apply s_rs_hart
          | tlbpeel; apply s_rs_pcfg
          | tlbpeel; apply s_rs_paddr
          | tlbpeel; apply s_rs_mc
          | tlbpeel; apply s_rs_micfg
          | tlbpeel; apply s_rs_misa
          | tlbpeel; apply s_rs_sec
          | tlbpeel; apply s_rs_pma
          | tlbpeel; apply s_rs_htif
          | tlbpeel; apply s_rs_elp
          | tlbpeel; apply s_rs_senv
          | tlbpeel; apply s_rs_satp
          | tlbpeel; apply s_rs_mie
          | tlbpeel; apply s_rs_mdl
          | tlbpeel; apply s_rs_menv ]. }
      iDestruct (s_rw_ext _ _ Hag with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen Df _ _ Hag with "Hro") as "Hro".
      iExists tvx. rewrite Ltlbv. iFrame "Hany Hrw Hro HRes".
  Qed.

  Lemma pt2_tramp_fetch_tr_kprev (rc kroot : mword 44) (Sc : ptree -> Prop)
      (dq : dfrac) (pc mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt rc satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pt2_tramp_spec Sc ->
    (forall t, Sc t -> pt_base t = rc) ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (pt2_res_kprev rc kroot Sc) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok HSc Hbc.
    iIntros "#Hat #Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /tramp_fetch_tr.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (pt2_tramp_tr_obl_kprev rc kroot Sc (s_Df_mix dq) pc ms bmi cy ti ip
                 mst0 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0 satp0
                 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma
                 HSc Hbc with "Hat Hcert") as "#Hobl".
    iApply ("Hobl" $! va pax tv rr with "[%] [%] [%] Hfrag HRes Hrw Hro");
      [ exact Hcanon | exact Hvpn | exact Hident ].
  Qed.

End Pt2Tramp.

(* ===================================================================== *)
(* 6. THE SWITCH-WINDOW STEP ENGINES.                                     *)
(*                                                                        *)
(* [TrampStepPt.wp_instr_tramp_pt] at [Res :=] the window's residue, with  *)
(* the window invariant opened on the way in and resealed on the way out   *)
(* -- [SmodeCorePt.wp_instr_s_config_tlbinv_pt]'s shape for the shared     *)
(* kernel table, over [pt2_kcur_swp_open] / [_close] instead.              *)
(*                                                                        *)
(* The instruction the two call sites step is the window's closing         *)
(* [sfence.vma], which moves neither satp nor the PMP cells, so the        *)
(* engine's landing values for those are the ones it went in with; the     *)
(* execute phase is handed them as a [swp (execute i)] continuation, and   *)
(* hands the tlb back at whatever value it left.                          *)
(* ===================================================================== *)

Section Pt2Engine.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_instr_pt2_tramp_kcur (rc : mword 44) (Sp : ptree -> Prop)
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pt2_tramp_spec Sp ->
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
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt2_kcur rc Sp -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       ⌜ upt_satp_ok_pt rc satp0 ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ pt2_res_kcur rc Sp tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie_v ∗
                   menvcfg ↦ᵣ{ dq } menvcfg0 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ pt2_res_kcur rc Sp tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie_v -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg0 -∗
         tlb_inv_pt2_kcur rc Sp -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval HSp
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hat #Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv
             Hpc Hinstr Hex Hcont".
    iDestruct (pt2_kcur_swp_open with "Hinv") as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & Hres)".
    iApply (wp_instr_tramp_pt (pt2_res_kcur rc Sp) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie_v menvcfg0 satp0 pcfg paddr Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc Hres Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (pt2_tramp_fetch_tr_kcur rc Sp dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok HSp
                with "Hat Hhw").
    - iIntros (tv') "%Hpmp2 Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg
                     Hpaddr Htlbc HRes Hclk Hpcc Hnpcc Hany".
      iApply ("Hex" $! satp0 pcfg paddr tv' with
                "[%] [%] Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr
                 Htlbc HRes Hclk Hpcc Hnpcc Hany");
        [ exact Hpmp2 | exact Hsatpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (pt2_kcur_swp_close rc Sp satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

  Lemma wp_instr_pt2_tramp_kprev (rc kroot : mword 44) (Sc : ptree -> Prop)
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pt2_tramp_spec Sc ->
    (forall t, Sc t -> pt_base t = rc) ->
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
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt2_kprev rc kroot Sc -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       ⌜ upt_satp_ok_pt rc satp0 ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ pt2_res_kprev rc kroot Sc tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie_v ∗
                   menvcfg ↦ᵣ{ dq } menvcfg0 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ pt2_res_kprev rc kroot Sc tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie_v -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg0 -∗
         tlb_inv_pt2_kprev rc kroot Sc -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval HSc Hbc
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hat #Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv
             Hpc Hinstr Hex Hcont".
    iDestruct (pt2_kprev_swp_open with "Hinv") as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & Hres)".
    iApply (wp_instr_tramp_pt (pt2_res_kprev rc kroot Sc) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie_v menvcfg0 satp0 pcfg paddr Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc Hres Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (pt2_tramp_fetch_tr_kprev rc kroot Sc dq pc mstatus0 satp0 mie_v
                mdv0 menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                HSc Hbc with "Hat Hhw").
    - iIntros (tv') "%Hpmp2 Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg
                     Hpaddr Htlbc HRes Hclk Hpcc Hnpcc Hany".
      iApply ("Hex" $! satp0 pcfg paddr tv' with
                "[%] [%] Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr
                 Htlbc HRes Hclk Hpcc Hnpcc Hany");
        [ exact Hpmp2 | exact Hsatpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (pt2_kprev_swp_close rc kroot Sc satp0 tv1 pcfg paddr
                Hsatpok Hpmpok with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

End Pt2Engine.
