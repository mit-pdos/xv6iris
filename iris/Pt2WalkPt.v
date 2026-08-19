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


End Pt2SharedWalk.
