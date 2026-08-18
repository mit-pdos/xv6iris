(* HartSTrans.v -- the S-mode translation at the [swp] layer.

   THE POINT OF THIS FILE IS HOW LITTLE IS IN IT.  The page-table proofs
   (PtTree / KptTree / CommonWalk / Pt4kWalk) already establish what the walk
   does; what the per-node port needs is the same facts in FOOTPRINTED form --
   reads confined to a declared set, writes named, and the file the walk lands
   on spelled out -- because under per-node stepping another hart steps
   between this walk's nodes, so a successor computed from the whole state is
   stale.

   Those proofs are NOT restated.  Two seams carry them across:

   - [PtTree.hval_translate_TLB_hit_pt] (spliced in beside its exec twin):
     the hit path makes NO events, so [WpDecodeBridge.goodb] certifies the
     footprint along the same chain the exec proof walks and
     [HartGoodb.hval_of_goodb] pairs it with the exec lemma.

   - the [tlb] read below, which the bridge CANNOT carry: [goodb] transports
     only reads whose values are pinned in the reference state, and the TLB's
     contents are whatever this hart's frame says.  So the lookup is a real
     footprinted node, and it is the only new walk here.

   The MISS path is different in kind and is not bridged: it reads PTEs from
   memory and writes the [tlb] register, so it needs the [swp] event rules --
   which is also why [HartRunGen]'s fetch obligation lets the fetch land on a
   different file than it started from. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras
        RiscvFetchExec RiscvTryStep.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb HartEvents.
Require Import WpDecodeBridge Pt4kWalk CommonWalk PtTree PtTreeAdue.
Require Import HartMFetch HartMPmp HartMStore SmodePte PtAdBits.
Local Open Scope Z_scope.

(* the same spelling [HartMFetch] uses for the misalignment tests *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

(* the lookup, as a footprinted walk: one register read and a pure match.
   [Pt4kWalk.exec_lookup_TLB_hit_ent]'s twin, and stated with exactly its
   premises. *)
Lemma hfrun_lookup_TLB_hit_ent (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (ent : TLB_Entry) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = true ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn)
  = Some (Some (tlb_hash (__id 39) vpn, ent), rs).
Proof.
  intros HD Htlb Hvec Hm. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec Hm.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* the lookup's MISS cases, footprinted.  Like the hit
   ([HartSTrans.hfrun_lookup_TLB_hit_ent]) these cannot go through the
   [goodb] bridge: the [tlb] register's value is whatever this hart's frame
   says, not what the reference state says.  One read, then a pure match --
   [SmodePte.exec_lookup_TLB_nomatch_s]'s twin, stated with its premises. *)
Lemma hfrun_lookup_TLB_nomatch (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16) (ent' : TLB_Entry)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' asid (sign_extend' (57 - 12) vpn) = false ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn) = Some (None, rs).
Proof.
  intros HD Htlb Hvec Hnm. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec Hnm.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* ...and the EMPTY slot, which the model treats identically. *)
Lemma hfrun_lookup_TLB_empty (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn) = Some (None, rs).
Proof.
  intros HD Htlb Hvec. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Section strans.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* [translate] on a TLB HIT whose cached leaf needs no A/D update: the
     lookup is one node at the frame, the rest is the bridged exec fact. *)
  Lemma swp_translate_hit (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (vpn : mword 27) (asid : mword 16) (root : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (p2 p1 q0 : mword 64) :
    Drw ## Dro ->
    (tlb : register) ∈ Drw ∪ Dro ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn p2 p1 q0 asid) ->
    match_TLB_Entry (u_walk_entry vpn p2 p1 q0 asid) asid
      (sign_extend' (57 - 12) vpn) = true ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    pte_check_ok acc p mxr do_sum q0 ->
    pte_check_pure acc p mxr do_sum Db q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : mword 64) acc = None ->
    pte_pbmt0 q0 ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Ok (autocast (T := mword)
                           ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44),
                         PBMT_PMA, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDtlb Htlb Hvec Hm HDb Hag Hchk Hpure Hupd Hpb.
    iIntros "#Hcert Hrw Hro".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_lookup_TLB_hit_ent (Drw ∪ Dro) Drw rs vpn asid tlbvec _
                   HDtlb Htlb Hvec Hm)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
              (hval_translate_TLB_hit_pt acc p mxr do_sum Db (Drw ∪ Dro) Drw rs
                 dst vpn p2 p1 q0 asid (tlb_hash (__id 39) vpn)
                 HDb Hag Hchk Hpure Hupd Hpb)
              with "Hcert Hrw Hro").
  Qed.

  (* the TLB write of the write-back's refreshed entry: two register nodes *)
  Local Lemma hfrun_write_TLB (D Drw : gset register) (rs : regstate)
      (idx : Z) (ent : TLB_Entry) :
    (tlb : register) ∈ D -> (tlb : register) ∈ Drw ->
    hfrun 3 D Drw rs (write_TLB idx ent)
    = Some (tt, register_set tlb
                  (vec_update_dec (register_lookup tlb rs) idx (Some ent)) rs).
  Proof.
    intros HD HDw. unfold write_TLB.
    cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
      Defs.write_reg Defs.returnm returnM].
    rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
    rewrite hfrun_write (bool_decide_eq_true_2 _ HDw).
    apply hfrun_ret.
  Qed.

  (* the entry's pbmt, pure at a pbmt-0 leaf *)
  Local Lemma hfrun_uwe_pbmt (D Drw : gset register) (rs : regstate)
      (vpn : mword 27) (p2 p1 q : mword 64) (asid : mword 16) :
    pte_pbmt0 q ->
    hfrun 1 D Drw rs (tlb_get_pbmt (u_walk_entry vpn p2 p1 q asid))
    = Some (PBMT_PMA, rs).
  Proof.
    intros Hpb. unfold tlb_get_pbmt, u_walk_entry. cbn [TLB_Entry_pte]. cbn zeta.
    rewrite zero_extend64_id autocast_id.
    unfold pte_pbmt0 in Hpb. rewrite Hpb.
    vm_compute (page_based_mem_type_forwards _). apply hfrun_ret.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [translate] on a TLB HIT whose cached leaf NEEDS the A/D update: the  *)
  (* write-back path (design §3a item (e)) -- the check on the cached      *)
  (* word, [swp_update_and_write_pte_upd] (exclusive re-read, re-check,    *)
  (* conditional write), the TLB refresh, the pbmt.  Mirrors               *)
  (* [PtTreeAdue.exec_translate_TLB_hit_pt_upd].                           *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translate_hit_upd (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (vpn : mword 27) (asid : mword 16) (root : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (q2 q1 q0 q0g m0 m0' menvcfg0 : mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (tlb : register) ∈ Drw ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn q2 q1 q0 asid) ->
    match_TLB_Entry (u_walk_entry vpn q2 q1 q0 asid) asid
      (sign_extend' (57 - 12) vpn) = true ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    (* the CACHED word: passes the check, needs the update, pbmt 0 *)
    pte_check_ok acc p mxr do_sum q0 ->
    pte_check_pure acc p mxr do_sum Db q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    (* the RE-READ word: an A/D variant of the cached one, valid leaf that
       passes the check, needs the update *)
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                       (ext_bits_of_PTE m0)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec m0 7 0)) = false ->
    (forall s, exec (check_PTE_permission acc p mxr do_sum
                       (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                       (ext_bits_of_PTE m0) tt) s
               = Some (PTE_Check_Success tt, s)) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE m0)) ('b"1") = false ->
    (forall (Db' : register -> bool) s,
       goodb Db' (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                    (ext_bits_of_PTE m0)) s = true) ->
    (forall (Db' : register -> bool) s,
       goodb Db' (check_PTE_permission acc p mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                    (ext_bits_of_PTE m0) tt) s = true) ->
    update_PTE_Bits (autocast (T := mword) m0 : mword 64) acc = Some m0' ->
    (* the machine facts *)
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    (* the PTE slot's PMP/PMA facts *)
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
      (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    pma_allows_ram pmar0 ->
    pma_ram_access (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)) 8 ->
    addr_is_ram (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)) ->
    is_aligned_paddr
      (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)) 8
           = Some m0⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, ⌜read_bytes σ.(mem) (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)) 8
             = Some m0⌝ -∗
        mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem)
                   (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)) 8
                   (Interface.WriteReq.value
                      (mwrite_req8_con
                         (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))
                         (autocast (T := mword) m0'))))
                σ.(mdev)) ∗ R)) -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Ok (autocast (T := mword)
                           ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44),
                         PBMT_PMA, tt)⌝ ∗
                hreg_frame
                  (register_set tlb
                     (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                        (Some (u_walk_entry vpn q2 q1 m0' asid))) rs) Drw ∗
                hreg_frame_ro Df
                  (register_set tlb
                     (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                        (Some (u_walk_entry vpn q2 q1 m0' asid))) rs) Dro ∗
                R ∗ resv_frag cpu_id None).
  Proof.
    intros Hdisj HWtlb Htlb Hvec Hm HDb Hag HDlc Haglc Hchk Hpure Hupd0 Hpb
      Hvar H0i H0nl Hchk0 H0N H0ig Hchk0g Hupd Hmisa Hmenv HPBMTE HADUE
      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord Hrange HR HW
      Hpallow Hacc Hram Hpa.
    assert (HDtlb : (tlb : register) ∈ Drw ∪ Dro) by set_solver.
    iIntros "#Hcert Hfrag Hrw Hro Hrd Hwr".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_lookup_TLB_hit_ent (Drw ∪ Dro) Drw rs vpn asid tlbvec _
                   HDtlb Htlb Hvec Hm)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    (* the check on the cached word *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag
                   (Hpure dst) (Hchk dst))
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    (* the write-back *)
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (Some (autocast (T := mword) m0'), tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I) _
              with "[Hrw Hro Hfrag Hrd Hwr] [-]").
    { iApply (swp_update_and_write_pte_upd Drw Dro Df rs dst vpn _ q0 q0g m0 m0'
                menvcfg0 acc p mxr do_sum pmar0 pcfg paddr R rr
                H0i H0nl Hchk0 H0N H0ig Hchk0g Hdisj HDlc Haglc Hmisa Hmenv
                HPBMTE HADUE Hupd0 Hupd HDpma HDcfg HDaddr HDhtif Hhtif Hpma
                Hpcfg Hpaddr HA Hord Hrange HR HW Hpallow Hacc Hram Hpa
                with "Hcert Hfrag Hrw Hro Hrd Hwr"). }
    iIntros (v) "(-> & Hrw & Hro & HR & Hfrag)". cbn match.
    (* the TLB refresh *)
    destruct Hvar as (a2 & d2 & Hm0).
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    assert (Hqc : m0' = pte_set_ad q0 a d)
      by (rewrite Hq; rewrite Hm0; apply pte_set_ad_absorb).
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 m0' asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 m0' asid a d Hqc) end.
    rewrite Hent.
    (* the TLB refresh then the pbmt of the (unchanged) cached entry: four
       silent nodes *)
    assert (Hwb : hfrun 4 (Drw ∪ Dro) Drw rs
                    (Defs.bind0
                       (write_TLB (tlb_hash (__id 39) vpn)
                          (u_walk_entry vpn q2 q1 m0' asid))
                       (tlb_get_pbmt (u_walk_entry vpn q2 q1 q0 asid)))
                  = Some (PBMT_PMA,
                          register_set tlb
                            (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                               (Some (u_walk_entry vpn q2 q1 m0' asid))) rs)).
    { unfold Defs.bind0.
      change 4%nat with (3 + 1)%nat.
      eapply hfrun_bind.
      - rewrite (hfrun_write_TLB (Drw ∪ Dro) Drw rs (tlb_hash (__id 39) vpn)
                   (u_walk_entry vpn q2 q1 m0' asid) HDtlb HWtlb).
        by rewrite Htlb.
      - exact (hfrun_uwe_pbmt (Drw ∪ Dro) Drw _ vpn q2 q1 q0 asid Hpb). }
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs _ _ _ Hdisj Hwb with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite uwe_ppn.
    iApply swp_ret. by iFrame.
  Qed.

  (* the walk's TLB fill, at ARBITRARY arguments (the write-back's fill
     carries the UPDATED word) *)
  Local Lemma hfrun_add_to_TLB_pt (D Drw : gset register) (rs : regstate)
      (asid : mword 16) (vpn : mword 27) (pp : mword 44) (pte : mword 64)
      (ptea : physaddr) (g : bool) :
    (tlb : register) ∈ D -> (tlb : register) ∈ Drw ->
    hfrun 4 D Drw rs (add_to_TLB 39 asid vpn pp pte ptea 0 g)
    = Some (tt, register_set tlb
                  (vec_update_dec (register_lookup tlb rs) (tlb_hash (__id 39) vpn)
                     (Some (pt_fill_ent asid vpn pp pte ptea g))) rs).
  Proof.
    intros HD HW. unfold add_to_TLB. cbn zeta.
    cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
      Defs.write_reg Defs.returnm returnM].
    rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
    rewrite hfrun_write (bool_decide_eq_true_2 _ HW).
    rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
    apply hfrun_ret.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [translate] on a MISS whose leaf NEEDS the A/D update: the walk, the  *)
  (* write-back (design §3a item (e)), the fill with the UPDATED word.     *)
  (* Mirrors [PtTreeAdue.exec_translate_TLB_miss_pt_upd].                  *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translate_miss_upd (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate)
      (vpn : mword 27) (root : mword 44) (asid : mword 16)
      (pte2 pte1 pte0 q0g m0 m0' : mword 64) (menvcfg0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (slot : option TLB_Entry)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) (rr : option resv) :
    (* the walk's own hypotheses, in the section's order *)
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                      (ext_bits_of_PTE pte2)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                      (ext_bits_of_PTE pte1)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                      (ext_bits_of_PTE pte0)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
    (forall s, exec (check_PTE_permission acc p mxr do_sum
                       (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                       (ext_bits_of_PTE pte0) tt) s
               = Some (PTE_Check_Success tt, s)) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s = true) ->
    (forall Db s, goodb Db (check_PTE_permission acc p mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s = true) ->
    Drw ## Dro ->
    (tlb : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = slot ->
    match slot with
    | None => True
    | Some e => match_TLB_Entry e asid (sign_extend' (57 - 12) vpn) = false
    end ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    (* the walked leaf needs the update; the RE-READ word (an A/D variant of
       it) is a valid leaf that passes the check and needs it too *)
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = Some q0g ->
    (exists a2 d2 : mword 1, m0 = pte_set_ad pte0 a2 d2) ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                       (ext_bits_of_PTE m0)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec m0 7 0)) = false ->
    (forall s, exec (check_PTE_permission acc p mxr do_sum
                       (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                       (ext_bits_of_PTE m0) tt) s
               = Some (PTE_Check_Success tt, s)) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE m0)) ('b"1") = false ->
    (forall (Db' : register -> bool) s,
       goodb Db' (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                    (ext_bits_of_PTE m0)) s = true) ->
    (forall (Db' : register -> bool) s,
       goodb Db' (check_PTE_permission acc p mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec m0 7 0))
                    (ext_bits_of_PTE m0) tt) s = true) ->
    update_PTE_Bits (autocast (T := mword) m0 : mword 64) acc = Some m0' ->
    (* the leaf slot's PMP/PMA facts *)
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)))
      (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    pma_allows_ram pmar0 ->
    pma_ram_access (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)) 8 ->
    addr_is_ram (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)) ->
    is_aligned_paddr
      (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
         (fun r => ⌜r = Values.Ok pte2⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte2)
                        (subrange_vec_dec vpn 17 9))) 8)
         (fun r => ⌜r = Values.Ok pte1⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte1)
                        (subrange_vec_dec vpn 8 0))) 8)
         (fun r => ⌜r = Values.Ok pte0⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (* the write-back's re-read witness and its write *)
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)) 8
           = Some m0⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, ⌜read_bytes σ.(mem) (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)) 8
             = Some m0⌝ -∗
        mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem)
                   (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0)) 8
                   (Interface.WriteReq.value
                      (mwrite_req8_con
                         (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))
                         (autocast (T := mword) m0'))))
                σ.(mdev)) ∗ R)) -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Values.Ok (autocast (T := mword)
                       ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44),
                     PBMT_PMA, tt)⌝ ∗
                hreg_frame (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 m0' asid))) rs) Drw ∗
                hreg_frame_ro Df (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 m0' asid))) rs) Dro ∗
                R ∗ resv_frag cpu_id None).
  Proof.
    intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
      Hdisj HDtlb HWtlb Htlb Hvec Hslot HD Hag Hmisa Hmenv HPBMTE HADUE
      Hupd0 Hvar Hm0i Hm0nl Hchkm H0Nm Hm0ig Hchkmg Hupd
      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord Hrange HR HW
      Hpallow Hacc Hram Hpa.
    iIntros "#Hcert Hfrag Hrw Hro Hrd2 Hrd1 Hrd0 Hrdx Hwr".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { destruct slot as [e |].
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_nomatch (Drw ∪ Dro) Drw rs vpn asid e tlbvec
                     HDtlb Htlb Hvec Hslot)
                  with "Hcert Hrw Hro").
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_empty (Drw ∪ Dro) Drw rs vpn asid tlbvec
                     HDtlb Htlb Hvec)
                  with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    unfold translate_TLB_miss. cbn zeta.
    (* the walk *)
    iApply (swp_bind_use (pt_walk 39 vpn acc p mxr do_sum root 2 false tt)
              _ _ _ with "[Hrw Hro Hrd2 Hrd1 Hrd0] [-]").
    { iApply (swp_pt_walk_user vpn root pte2 pte1 pte0 acc p mxr do_sum
                H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
                Drw Dro Df rs dst menvcfg0 Hdisj HD Hag Hmisa Hmenv HPBMTE
                with "Hcert Hrw Hro Hrd2 Hrd1 Hrd0"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    (* the write-back *)
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (Some (autocast (T := mword) m0'), tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                         resv_frag cpu_id None)%I) _
              with "[Hrw Hro Hfrag Hrdx Hwr] [-]").
    { iApply (swp_update_and_write_pte_upd Drw Dro Df rs dst vpn _
                (autocast (T := mword) pte0) q0g m0 m0'
                menvcfg0 acc p mxr do_sum pmar0 pcfg paddr R rr
                Hm0i Hm0nl Hchkm H0Nm Hm0ig Hchkmg Hdisj HD Hag Hmisa Hmenv
                HPBMTE HADUE ltac:(first [exact Hupd0 | by rewrite autocast_id]) Hupd HDpma HDcfg HDaddr HDhtif Hhtif Hpma
                Hpcfg Hpaddr HA Hord Hrange HR HW Hpallow Hacc Hram Hpa
                with "Hcert Hfrag Hrw Hro Hrdx Hwr"). }
    iIntros (v) "(-> & Hrw & Hro & HR & Hfrag)". cbn match.
    (* the fill, with the UPDATED word *)
    destruct Hvar as (a2 & d2 & Hm0).
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    assert (Hqc : m0' = pte_set_ad pte0 a d)
      by (rewrite Hq; rewrite Hm0; apply pte_set_ad_absorb).
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs _ _ _ Hdisj
                (hfrun_add_to_TLB_pt (Drw ∪ Dro) Drw rs asid vpn _ _ _ _
                   HDtlb HWtlb)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn pte2 pte1 m0' asid)
        by exact (pt_fill_ent_uwe vpn pte2 pte1 pte0 m0' asid a d Hqc) end.
    rewrite Hent.
    iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [translate] on a MISS.  Assembly only: the lookup is the footprinted  *)
  (* node above, the walk and the install are CommonWalk's converted        *)
  (* chain.  The walk's per-PTE hypotheses are threaded positionally, the   *)
  (* same way KptTree threads them on the exec side.                       *)
  (*                                                                      *)
  (* This is the first rule in the S-mode translation whose POST-FILE       *)
  (* differs from its pre-file: the miss installs a TLB entry.             *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translate_miss (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate)
      (vpn : mword 27) (root : mword 44) (asid : mword 16)
      (pte2 pte1 pte0 : mword 64) (menvcfg0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (slot : option TLB_Entry) :
    (* the walk's own hypotheses, in the section's order *)
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                      (ext_bits_of_PTE pte2)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                      (ext_bits_of_PTE pte1)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                      (ext_bits_of_PTE pte0)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
    (forall s, exec (check_PTE_permission acc p mxr do_sum
                       (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                       (ext_bits_of_PTE pte0) tt) s
               = Some (PTE_Check_Success tt, s)) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s = true) ->
    (forall Db s, goodb Db (check_PTE_permission acc p mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s = true) ->
    (* the lookup misses: the slot is empty, or holds a foreign entry *)
    Drw ## Dro ->
    (tlb : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = slot ->
    match slot with
    | None => True
    | Some e => match_TLB_Entry e asid (sign_extend' (57 - 12) vpn) = false
    end ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = None ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
         (fun r => ⌜r = Values.Ok pte2⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte2)
                        (subrange_vec_dec vpn 17 9))) 8)
         (fun r => ⌜r = Values.Ok pte1⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte1)
                        (subrange_vec_dec vpn 8 0))) 8)
         (fun r => ⌜r = Values.Ok pte0⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Values.Ok (autocast (T := mword)
                       ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44),
                     PBMT_PMA, tt)⌝ ∗
                hreg_frame (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 pte0 asid))) rs) Drw ∗
                hreg_frame_ro Df (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 pte0 asid))) rs) Dro).
  Proof.
    intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
      Hdisj HDtlb HWtlb Htlb Hvec Hslot HD Hag Hmisa Hmenv HPBMTE Hnoupd.
    iIntros "#Hcert Hrw Hro Hrd2 Hrd1 Hrd0".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { destruct slot as [e |].
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_nomatch (Drw ∪ Dro) Drw rs vpn asid e tlbvec
                     HDtlb Htlb Hvec Hslot)
                  with "Hcert Hrw Hro").
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_empty (Drw ∪ Dro) Drw rs vpn asid tlbvec
                     HDtlb Htlb Hvec)
                  with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_translate_TLB_miss_user vpn root pte2 pte1 pte0 acc p mxr do_sum
              H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
              Drw Dro Df rs dst asid menvcfg0 Hdisj HD Hag HWtlb Hmisa Hmenv
              HPBMTE Hnoupd with "Hcert Hrw Hro Hrd2 Hrd1 Hrd0").
  Qed.


  (* ------------------------------------------------------------------ *)
  (* [fetch_bytes] AT SUPERVISOR.  Structurally the M-mode twin           *)
  (* ([HartMFetch.swp_fetch_bytes_M]) and it takes the same shape of        *)
  (* obligation, but the address the READ uses is the TRANSLATED one:       *)
  (* M-mode reads at [Physaddr pc] only because Bare translation is the     *)
  (* identity.  The translation is an obligation because it may WRITE (the  *)
  (* TLB fill), which is why the read runs at a different file [rsf].       *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_bytes_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rsf = Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M Drw Dro Df rsf (Physaddr pa) w Supervisor Hdisj
                HDmst HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)). by iFrame.
  Qed.


  (* ==================================================================== *)
  (* THE S-MODE FETCH.  This is [HartRunGen]'s outstanding obligation, and  *)
  (* it needed no new fetch rule: [HartMFetch.swp_fetch] was already        *)
  (* privilege-generic, and once its LANDING FILE became a parameter it     *)
  (* serves both modes.  What is S-mode-specific is entirely below it --    *)
  (* the translation walks and may fill the TLB, which is what [rsf] is.    *)
  (* ==================================================================== *)
  Lemma swp_fetch_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rsf = Supervisor ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (swp_fetch Drw Dro Df rs rsf pc w Hdisj HDpc Hpc Hb0 Hb1 Hal
              with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_S Drw Dro Df rs rsf pc pa w Hdisj HDmst HDpriv
              Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.


  (* the HALFWORD fetch_bytes at Supervisor, [swp_fetch_bytes_S]'s twin one
     width down: the model translates and reads at [granule_start], and a
     base instruction's second halfword is fetched at [pc+2] while
     [fetch_start] stays [pc] -- so the two addresses are separate here for
     the same reason they are in [HartMFetch.swp_fetch_bytes_M2]. *)
  Lemma swp_fetch_bytes_S2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (fs gs pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rsf = Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr gs) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes fs gs 2)
      (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr gs) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M2 Drw Dro Df rsf (Physaddr pa) h Supervisor Hdisj
                HDmst HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 2 h)). by iFrame.
  Qed.

  (* the 2-mod-4 COMPRESSED shape at Supervisor *)
  Lemma swp_fetch_S_rvc2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rsf = Supervisor ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpriv HmisaC Hb0 Hb1 Hal4 Hrvc.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (swp_fetch_rvc2 Drw Dro Df rs rsf pc h Hdisj HDpc HDmisa Hpc Hb0
              Hb1 Hal4 HmisaC Hrvc with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_S2 Drw Dro Df rs rsf pc pc pa h Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.


  (* the 2-mod-4 BASE shape at Supervisor: TWO halfword fetches, so TWO
     translations -- and the first may already have filled the TLB, which is
     why [swp_fetch_base2] threads an intermediate file.  The second
     translation therefore starts at [rsf1], and the PC the model re-reads
     between them is pinned there. *)
  Lemma swp_fetch_S_base2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf1 rsf2 : regstate) (pc pa1 pa2 : mword 64)
      (ilo ihi : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup (R_bitvector_64 PC) rsf1 = pc ->
    register_lookup cur_privilege rsf1 = Supervisor ->
    register_lookup cur_privilege rsf2 = Supervisor ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* the low halfword: translate pc, read there *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf1 Drw ∗ hreg_frame_ro Df rsf1 Dro)) -∗
    (hreg_frame rsf1 Drw -∗ hreg_frame_ro Df rsf1 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa1) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ilo, tt)⌝ ∗
                   hreg_frame rsf1 Drw ∗ hreg_frame_ro Df rsf1 Dro)) -∗
    (* the high halfword: translate pc+2, read there *)
    (hreg_frame rsf1 Drw -∗ hreg_frame_ro Df rsf1 Dro -∗
       swp (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa2, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro)) -∗
    (hreg_frame rsf2 Drw -∗ hreg_frame_ro Df rsf2 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa2) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ihi, tt)⌝ ∗
                   hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpc1 Hpriv1 Hpriv2 HmisaC
      Hb0 Hb1 Hal4 Hnrvc.
    iIntros "#Hcert Hrw Hro Htr1 Hcmr1 Htr2 Hcmr2".
    iApply (swp_fetch_base2 Drw Dro Df rs rsf1 rsf2 pc ilo ihi Hdisj HDpc
              HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc Hpc1
              with "Hcert Hrw Hro [Htr1 Hcmr1] [Htr2 Hcmr2]").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_S2 Drw Dro Df rs rsf1 pc pc pa1 ilo Hdisj HDmst
                HDpriv Hpriv1 with "Hcert Hrw Hro Htr1 Hcmr1").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_S2 Drw Dro Df rsf1 rsf2 pc (add_vec_int pc 2)
                pa2 ihi Hdisj HDmst HDpriv Hpriv2
                with "Hcert Hrw Hro Htr2 Hcmr2").
  Qed.


End strans.

