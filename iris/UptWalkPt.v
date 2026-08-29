(* UptWalkPt.v -- THE USER PAGE TABLE'S WALK, PER NODE.

   [UptTree.utlb_inv_pt] owns its table outright ([ptree_own]), so the whole
   of [translateAddr] over it is a run whose memory accesses are answered
   from an OWNED byte map -- and [HartMemRun.swp_hmrun_of_exec] carries such
   a run from [exec] to [swp] under a [goodmb] certificate.  That is the
   route this file takes, rather than re-deriving the walk at the node
   layer: the exec fact is [KptTree.ptree_translateAddr_cases] and the
   certificate is [PtWalkCert.goodmb_ptree_translateAddr], both already
   proved, and the only new content is the BYTE VIEW of a bare [ptree_own]
   (section 1) and the residue split the engine's frame forces (section 2).

   Section 1 is [UserBytes.u_mem_wf] with the DATA half dropped.  It cannot
   be an instance of it: [u_mem_wf] pins the data bytes into the same map
   ([udata_cov] over [ud_data]), and a caller holding only [utlb_inv_pt] --
   which is every trampoline/trapframe caller, whose statements name only
   the table -- does not own them. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import RiscvExtras.
Require Import SmodePte.
Require Import PtreeType PtTree PtBytes KptTree UptTree TrampPt.
Require Import CommonWalk Pt4kWalk KptPt PtAdBits PtTreeAdue SRegime.
Require Import UserBytes UserFetchCert PtWalkCert UserClassifyAsm.
Require Import HartSwp HartLift HartSpan HartSFrame HartMemRun.
Require Import WpDecodeBridge KptGoodb.
Require Import SmodeCorePt TrampStepPt WpSmodePtEngine.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. THE TABLE'S BYTES, WITHOUT THE DATA PAGES.                          *)
(* ===================================================================== *)

Definition upt_tmem (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (mm : pamap) : Prop :=
  maps_disj (pt_maps 2 t) /\
  mm = ptree_bytes 2 t /\
  (forall a : Arch.pa, a ∈ (dom mm : gset Arch.pa) -> addr_is_ram a) /\
  upt_map_wf um /\
  upt_tree_spec uroot tfp um t.

Lemma upt_tmem_sub (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  upt_tmem uroot tfp um t mm -> word_bytes a q ∈ pt_maps 2 t ->
  word_bytes a q ⊆ mm.
Proof.
  intros (Hdisj & -> & _) Hin. rewrite /ptree_bytes.
  exact (maps_disj_subseteq (pt_maps 2 t) _ Hdisj Hin).
Qed.

Lemma upt_tmem_owned (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  upt_tmem uroot tfp um t mm -> word_bytes a q ∈ pt_maps 2 t ->
  bytes_owned mm a 8 = true.
Proof.
  intros Hwf Hin.
  pose proof (upt_tmem_sub uroot tfp um t mm a q Hwf Hin) as Hsub.
  apply bytes_owned_of_dom. intros j Hj. apply elem_of_dom.
  exists (nth_byte q j).
  exact (lookup_weaken (word_bytes a q) mm _ _ (word_bytes_lookup a q j Hj) Hsub).
Qed.

Lemma upt_slot_mem_at (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (mm : pamap) (rs : regstate) (b : mword 44) (i : mword 9)
    (q : mword 64) :
  upt_tmem uroot tfp um t mm ->
  word_bytes (u_pte_addr b i) q ∈ pt_maps 2 t ->
  pt_slot_mem (MState rs mm dev0_state) (u_pte_addr b i) q.
Proof.
  intros Hwf Hin.
  pose proof (upt_tmem_sub uroot tfp um t mm _ q Hwf Hin) as Hsub.
  assert (Hlk : forall j : nat, (N.of_nat j < 8)%N ->
            mm !! pa_add (u_pte_addr b i) j = Some (nth_byte q j)).
  { intros j Hj. apply (lookup_weaken (word_bytes (u_pte_addr b i) q) mm);
      [ apply word_bytes_lookup; lia | exact Hsub ]. }
  assert (Hram : forall j : nat, (N.of_nat j < 8)%N ->
            addr_is_ram (pa_add (u_pte_addr b i) j)).
  { intros j Hj. destruct Hwf as (_ & _ & Hr & _).
    apply Hr. apply elem_of_dom. exists (nth_byte q j). exact (Hlk j Hj). }
  split_and!.
  - exact Hlk.
  - rewrite <- (pa_add_0 (u_pte_addr b i)). apply Hram. lia.
  - apply Hram. lia.
  - exact (pte_addr_at_aligned8 b i).
Qed.

(* THE A/D WRITE-BACK, at the byte level: writing the leaf slot IS setting
   the leaf ([UserFetchCert.ptree_bytes_set_leaf]), and the domain does not
   move, so the RAM clause carries over. *)
Lemma upt_tmem_writeback (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (mm : pamap) (vpn : mword 27) (p2 p1 p0 q : mword 64) :
  upt_tmem uroot tfp um t mm ->
  ptree_maps t vpn p2 p1 p0 ->
  upt_tree_spec uroot tfp um (ptree_set_leaf t vpn q) ->
  upt_tmem uroot tfp um (ptree_set_leaf t vpn q)
    (write_bytes mm (pt_addr0 p1 vpn) 8 q).
Proof.
  intros Hwf Hmaps Hspec'.
  pose proof (pt_same_shape_set_leaf t vpn p2 p1 p0 q Hmaps) as Hshape.
  pose proof Hwf as (Hdisj & Hmm & Hram & Hwfm & Hspec).
  assert (Heq : ptree_bytes 2 (ptree_set_leaf t vpn q)
                = write_bytes mm (pt_addr0 p1 vpn) 8 q).
  { rewrite Hmm. exact (ptree_bytes_set_leaf t vpn p2 p1 p0 q Hdisj Hmaps). }
  split_and!.
  - exact (pt_maps_disj_shape 2 t (ptree_set_leaf t vpn q) Hshape Hdisj).
  - symmetry. exact Heq.
  - intros a Ha. apply Hram.
    rewrite Hmm (ptree_bytes_dom_shape 2 t _ Hshape) Heq. exact Ha.
  - exact Hwfm.
  - exact Hspec'.
Qed.

(* the domain never moves along a same-shaped tree change -- which is what
   [HartMemRun]'s [dom mm' = dom mm] obligation pins the landing map with *)
Lemma upt_tmem_dom (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t t' : ptree) (mm mm' : pamap) :
  upt_tmem uroot tfp um t mm -> upt_tmem uroot tfp um t' mm' ->
  pt_same_shape 2 t t' -> (dom mm' : gset Arch.pa) = dom mm.
Proof.
  intros (_ & -> & _) (_ & -> & _) Hshape.
  symmetry. exact (ptree_bytes_dom_shape 2 t t' Hshape).
Qed.

(* ===================================================================== *)
(* 2. THE RESIDUE.  [utlb_inv_pt] owns four CELLS the walk reads and       *)
(*    writes -- satp, tlb, pmpcfg_n, pmpaddr_n -- and the per-node engine  *)
(*    keeps them in its FRAME, so the invariant has to be split exactly    *)
(*    as [SRegime.kpt_swp_open] / [_close] split [tlb_res_pt].             *)
(* ===================================================================== *)

Definition upt_satp_ok_pt (uroot : mword 44) (satp0 : mword 64) : Prop :=
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) /\
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
    = (mword_of_int 0 : mword 16) /\
  autocast (T := mword)
    (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = uroot /\
  (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0).

Section UptRes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the NON-CELL residue, keyed on the tlb value the cell carries *)
  Definition upt_res_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (tlbv : type_of_register tlb) : iProp Σ :=
    (∃ t : ptree,
       ⌜ tlb_ok_pt (mword_of_int 0) t tlbv ⌝ ∗
       ⌜ upt_tree_spec uroot tfp um t ⌝ ∗
       ⌜ upt_map_wf um ⌝ ∗
       ptree_own 2 (DfracOwn 1) t)%I.

  Lemma upt_swp_open (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
    utlb_inv_pt uroot tfp um -∗
    ∃ (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜ upt_satp_ok_pt uroot satp0 ⌝ ∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      satp ↦ᵣ satp0 ∗ tlb ↦ᵣ tlbv ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      upt_res_pt uroot tfp um tlbv.
  Proof.
    iIntros "H". iDestruct "H" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlbc & %Hok & %Hspec & %Hwfm &
        %Hpmaw & Htree & Hpmp)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iExists usatp, tlbvec, pcfg, paddr.
    iSplitR;
      [ iPureIntro; unfold upt_satp_ok_pt; split_and!; assumption |].
    iSplitR;
      [ iPureIntro; unfold pmp_ent0_ok; split_and!; assumption |].
    iFrame "Hsatp Htlbc Hpcfg Hpaddr".
    iExists t. iFrame "Htree". iPureIntro. split_and!;
      [ exact Hok | exact Hspec | exact Hwfm ].
  Qed.

  Lemma upt_swp_close (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (satp0 : mword 64) (tlbv : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbv -∗
    pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    upt_res_pt uroot tfp um tlbv -∗
    utlb_inv_pt uroot tfp um.
  Proof.
    intros (Hmode & Hasid & Hppn & Hpmaw) (HA & Hord & HX & HW & HR & Hcov).
    iIntros "Hsatp Htlbc Hpcfg Hpaddr Hres".
    iDestruct "Hres" as (t) "(%Hok & %Hspec & %Hwfm & Htree)".
    iApply (utlb_inv_pt_intro uroot tfp um satp0 tlbv t
              Hmode Hasid Hppn Hok Hspec Hwfm Hpmaw with "Hsatp Htlbc Htree").
    iApply (pmp_config_intro uroot pcfg paddr HA Hord HX HW HR Hcov
              with "Hpcfg Hpaddr").
  Qed.

End UptRes.

(* ===================================================================== *)
(* 3. THE WALK'S FOOTPRINT.                                               *)
(* ===================================================================== *)

Definition upt_Dr (r : register) : bool :=
  orb (register_beq r (misa : register))
 (orb (register_beq r (menvcfg : register))
 (orb (register_beq r (mstatus : register))
 (orb (register_beq r (cur_privilege : register))
 (orb (register_beq r (satp : register))
 (orb (register_beq r (tlb : register))
 (orb (register_beq r (pmpcfg_n : register))
 (orb (register_beq r (pmpaddr_n : register))
 (orb (register_beq r (pma_regions : register))
      (register_beq r (htif_tohost_base : register)))))))))).

Definition upt_Dw (r : register) : bool := register_beq r (tlb : register).

(* ===================================================================== *)
(* 4. THE WALK, PER NODE.  [SRegime.sr_swp_translate]'s conclusion         *)
(*    verbatim, over the USER table.                                      *)
(*                                                                        *)
(* The whole of [translateAddr] here reads and writes only bytes the hart  *)
(* OWNS (its own page table), so it is carried from [exec] to [swp] by     *)
(* [HartMemRun.swp_hmrun_of_exec] rather than re-derived node by node:     *)
(* the exec fact is [KptTree.ptree_translateAddr_cases] and the            *)
(* certificate [PtWalkCert.goodmb_ptree_translateAddr], both already       *)
(* proved with the SAME five-way case split (hit, hit+refresh,            *)
(* hit+write-back, fill, fill+write-back).  The reference state is THIS    *)
(* HART'S OWN FILE over its own byte map, which is what makes              *)
(* [swp_hmrun_of_exec]'s agreement premise [reflexivity].                  *)
(* ===================================================================== *)
Section UptWalk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_translate_upt (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (va pa satp0 w mst0 : mword 64)
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
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    upt_leaf_at tfp um (svpn_of va) w ->
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
    upt_res_pt uroot tfp um tlbv -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  upt_res_pt uroot tfp um (register_lookup tlb rsf) ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisjf HDr HDw Hacc Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV
           Hsatp Htlb Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall Hleaf Hchk Hgchk
           Hcanon Hout.
    pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
    pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hcert Hfrag Hres Hrw Hro".
    iDestruct "Hres" as (t) "(%Hok & %Hspec & %Hwfm & Htree)".
    iDestruct (ptree_own_bytes 2 t with "Htree") as "(#Hclaims & %Hdisj & Hmm)".
    iDestruct (bytes_own_ram with "Hmm") as %Hram.
    pose proof Hspec as (Hbase & _).
    destruct (upt_spec_maps uroot tfp um t (svpn_of va) w Hspec Hleaf)
      as (p2 & p1 & a0 & d0 & Hmaps).
    pose proof (upt_variant tfp um (svpn_of va) w Hwfm Hleaf) as Hvar.
    assert (Hwf : upt_tmem uroot tfp um t (ptree_bytes 2 t)).
    { split_and!; [ exact Hdisj | reflexivity | exact Hram | exact Hwfm
                  | exact Hspec ]. }
    (* the three slots, as reads and as ownership *)
    assert (Hsm2 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr2 t (svpn_of va)) p2)
      by exact (upt_slot_mem_at uroot tfp um t _ rs (pt_base t)
                  (vpn_idx 2 (svpn_of va)) p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm1 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr1 p2 (svpn_of va)) p1)
      by exact (upt_slot_mem_at uroot tfp um t _ rs (u_next_base p2)
                  (vpn_idx 1 (svpn_of va)) p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hsm0 : pt_slot_mem (MState rs (ptree_bytes 2 t) dev0_state)
                     (pt_addr0 p1 (svpn_of va)) (pte_set_ad w a0 d0))
      by exact (upt_slot_mem_at uroot tfp um t _ rs (u_next_base p1)
                  (vpn_idx 0 (svpn_of va)) _ Hwf
                  (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown2 : bytes_owned (ptree_bytes 2 t) (pt_addr2 t (svpn_of va)) 8 = true)
      by exact (upt_tmem_owned uroot tfp um t _ _ p2 Hwf
                  (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown1 : bytes_owned (ptree_bytes 2 t) (pt_addr1 p2 (svpn_of va)) 8 = true)
      by exact (upt_tmem_owned uroot tfp um t _ _ p1 Hwf
                  (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
    assert (Hown0 : bytes_owned (ptree_bytes 2 t) (pt_addr0 p1 (svpn_of va)) 8 = true)
      by exact (upt_tmem_owned uroot tfp um t _ _ _ Hwf
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
    destruct (ptree_translateAddr_cases acc Supervisor uroot va w pa satp0 t
                tlbv p2 p1 a0 d0 (MState rs (ptree_bytes 2 t) dev0_state)
                Hchk Hcanon Hout (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
                Hbase Hmaps Hok Hsm2 Hsm1 Hsm0
                Lmisa Lmenv Lhtif Lcp Htm Heff
                (s_acc_ssa_exec acc _ Hacc)
                Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw)
      as (sf & Htr & Harms).
    assert (Htrg : goodmb upt_Dr upt_Dw (translateAddr (Virtaddr va) acc)
                     (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
                   = true).
    { apply (goodmb_ptree_translateAddr upt_Dr upt_Dw acc Supervisor
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               uroot t va w pa satp0 tlbv p2 p1 a0 d0
               (MState rs (ptree_bytes 2 t) dev0_state) (ptree_bytes 2 t)
               Hchk Hgchk Hcanon Hout
               (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
               Hbase Hmaps Hok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
               Lmisa Lmenv Lhtif Lcp Htm Htmg Heff Heffg
               (s_acc_ssa_exec acc _ Hacc) (s_acc_ssa_goodb acc upt_Dr _ Hacc)
               Lsatp Hppn Hasid Ltlb LA Lord LR LW Lcov Lpmar Lpmaw). }
    (* WHERE THE WALK LANDED.  The three arms of [ptree_translateAddr_cases],
       each with its tree and its file; nothing after this looks at which. *)
    assert (Hland : exists (rsf : regstate) (t' : ptree),
              sf = MState rsf (ptree_bytes 2 t') dev0_state /\
              (rsf = rs \/ exists tv, rsf = register_set tlb tv rs) /\
              tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) /\
              pt_same_shape 2 t t' /\
              upt_tree_spec uroot tfp um t').
    { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
      - exists rs, t. split_and!;
          [ reflexivity | left; reflexivity | rewrite Htlb; exact Hok
          | apply pt_same_shape_refl | exact Hspec ].
      - eexists _, t. split_and!.
        + reflexivity.
        + right. eexists. reflexivity.
        + rewrite register_lookup_set.
          rewrite <- Htlb.
          exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rs)
                   (svpn_of va) p2 p1 _ Hmaps ltac:(rewrite Htlb; exact Hok)).
        + apply pt_same_shape_refl.
        + exact Hspec.
      - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
          by exact (pte_set_ad_absorb w a0 d0 a1 d1).
        assert (Hv' : pte_valid (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
          by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
        assert (Hl' : pte_leaf (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
          by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
        assert (Hn' : pte_no_napot (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
          by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
        assert (Hp' : pte_pbmt0 (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
          by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
        assert (Hspec' : upt_tree_spec uroot tfp um
                  (ptree_set_leaf t (svpn_of va)
                     (pte_set_ad (pte_set_ad w a0 d0) a1 d1))).
        { rewrite Habs.
          exact (upt_tree_spec_set_leaf uroot tfp um t (svpn_of va) w p2 p1
                   a0 d0 a1 d1 Hwfm Hspec Hleaf Hmaps). }
        eexists _,
          (ptree_set_leaf t (svpn_of va) (pte_set_ad (pte_set_ad w a0 d0) a1 d1)).
        split_and!.
        + rewrite /set_reg. cbn [sregs mem mdev].
          rewrite (proj1 (proj2
            (upt_tmem_writeback uroot tfp um t (ptree_bytes 2 t) (svpn_of va)
               p2 p1 (pte_set_ad w a0 d0) _ Hwf Hmaps Hspec'))).
          reflexivity.
        + right. eexists. reflexivity.
        + rewrite register_lookup_set. rewrite <- Htlb.
          exact (tlb_ok_pt_fill_self (mword_of_int 0)
                   (ptree_set_leaf t (svpn_of va)
                      (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                   (register_lookup tlb rs) (svpn_of va) p2 p1 _
                   (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                      (pte_set_ad w a0 d0) _ Hmaps Hv' Hl' Hn' Hp')
                   (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rs)
                      (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                      Hmaps Hv' Hl' Hn' Hp' ltac:(rewrite Htlb; exact Hok))).
        + exact (pt_same_shape_set_leaf t (svpn_of va) p2 p1 _ _ Hmaps).
        + exact Hspec'. }
    destruct Hland as (rsf & t' & -> & Hfile & Hok' & Hshape & Hspec').
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
    iExists rsf.
    rewrite (hreg_frame_ext rs' rsf Drw
               (fun r Hr => Hag' r (elem_of_union_l _ _ _ Hr))).
    rewrite (hreg_frame_ro_ext Df rs' rsf Dro
               (fun r Hr => Hag' r (elem_of_union_r _ _ _ Hr))).
    iSplitR; [iPureIntro; exact Hfile |].
    iFrame "Hrw Hro Hany".
    iExists t'.
    iSplitR; [iPureIntro; exact Hok' |].
    iSplitR; [iPureIntro; exact Hspec' |].
    iSplitR; [iPureIntro; exact Hwfm |].
    iApply (ptree_own_of_bytes 2 t' Hdisj' with "Hclaims' Hmm'").
  Qed.

End UptWalk.

(* ===================================================================== *)
(* 5. THE TRAMPOLINE FETCH, on the USER table.                            *)
(*                                                                        *)
(* [TrampStepPt.tramp_tr_obl] at [Res := upt_res_pt uroot tfp um].  The    *)
(* claim side is the trampoline CLAUSE of [upt_tree_spec] -- the user      *)
(* table maps [tramp_vpn] to [pte_tramp] on every A/D variant -- so the    *)
(* obligation's own geometry premises are all it takes; nothing outside    *)
(* the invariant is consulted.                                            *)
(* ===================================================================== *)

(* the trampoline leaf's fetch check, certified (the [goodb] twin of
   [KptTree.tramp_variant_check_fetch], same proof) *)
Lemma tramp_variant_goodb_check_fetch (a d : mword 1) (mxr do_sum : bool)
    (Db : register -> bool) (s : mstate) :
  goodb Db (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad pte_tramp a d) 7 0))
              (ext_bits_of_PTE (pte_set_ad pte_tramp a d)) tt) s = true.
Proof.
  unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma upt_Dr_in_s (r : register) : upt_Dr r = true -> r ∈ s_Drw ∪ s_Dro.
Proof.
  unfold upt_Dr. intros Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr|Hr]);
    apply register_beq_eq in Hr; subst r;
    solve [ exact s_in_misa | exact s_in_menv | exact s_in_mst | exact s_in_priv
          | exact s_in_satp | exact s_in_tlb | exact s_in_pcfg | exact s_in_paddr
          | exact s_in_pma | exact s_in_htif ].
Qed.

Lemma upt_Dw_in_s (r : register) : upt_Dw r = true -> r ∈ s_Drw.
Proof.
  unfold upt_Dw. intros Hr. apply register_beq_eq in Hr. subst r. exact s_w_tlb.
Qed.

(* the same two at the DATA-access frame, which is what a memory leaf runs
   the walk on ([WpSmodePtEngine.sda_Drw] / [sda_Dro]) *)
Lemma upt_Dr_in_sda (r : register) : upt_Dr r = true -> r ∈ sda_Drw ∪ sda_Dro.
Proof.
  unfold upt_Dr. intros Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr|Hr]);
    apply register_beq_eq in Hr; subst r;
    solve [ exact sda_in_misa | exact sda_in_menv | exact sda_in_mst
          | exact sda_in_priv | exact sda_in_satp | exact sda_in_tlb
          | exact sda_in_pcfg | exact sda_in_paddr | exact sda_in_pma
          | exact sda_in_htif ].
Qed.

Lemma upt_Dw_in_sda (r : register) : upt_Dw r = true -> r ∈ sda_Drw.
Proof.
  unfold upt_Dw. intros Hr. apply register_beq_eq in Hr. subst r.
  exact sda_w_tlb.
Qed.

(* the user table is Sv39, in the shape [HartSMem]'s engines want *)
Lemma upt_swp_mode_ok (uroot : mword 44) (satp0 : mword 64) :
  upt_satp_ok_pt uroot satp0 ->
  satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 satp0)) = Some Sv39.
Proof. intros (Hmode & _ & _ & _). rewrite Hmode. vm_compute. reflexivity. Qed.

Section UptTramp.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac tlbpeel :=
    rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma utramp_tr_obl (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
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
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    gen_cert -∗
    tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
      (upt_res_pt uroot tfp um).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma.
    iIntros "#Hcert". rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pax).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hident.
      rewrite pte_set_ad_ppn in Hident. exact Hident. }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (swp_translate_upt (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  uroot tfp um va pax satp0 pte_tramp mst0 tv pcfg paddr pmar0 rr
                  s_disj upt_Dr_in_s upt_Dw_in_s (or_introl eq_refl)
                  ltac:(rewrite s_rs_misa; exact Hmisa)
                  ltac:(rewrite s_rs_menv; exact Hmenv)
                  ltac:(apply s_rs_htif) ltac:(apply s_rs_priv)
                  ltac:(apply s_rs_mst) HSXL HMPRV
                  ltac:(apply s_rs_satp) ltac:(apply s_rs_tlb)
                  ltac:(apply s_rs_pcfg) ltac:(apply s_rs_paddr)
                  ltac:(apply s_rs_pma)
                  Hsatpok Hpmpok Hpma
                  (or_introl (conj Hvpn eq_refl))
                  (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
                  (fun a d mxr do_sum Db s0 =>
                     tramp_variant_goodb_check_fetch a d mxr do_sum Db s0)
                  Hcanon Hout
                  with "Hcert Hfrag HRes Hrw Hro"). }
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

  (* the whole-tower form the engine takes.  [tramp_fetch_tr] ∀-quantifies
     misa and pma_regions, which [utramp_tr_obl] wants as literals, so -- as
     in [WpSmodePtFetch.spt_fetch_tr_of_regime] -- the producer applies only
     from INSIDE the box, where the frame's own discarded cells and
     [hw_config]'s pins turn the two ∀-bound components into those literals. *)
  Lemma utramp_fetch_tr (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (dq : dfrac) (pc mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (upt_res_pt uroot tfp um) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok.
    iIntros "#Hhw".
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
    iDestruct (utramp_tr_obl uroot tfp um (s_Df_mix dq) pc ms bmi cy ti ip mst0
                 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0 satp0
                 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV Hsatpok Hpmpok Hpma
                 with "Hcert") as "#Hobl".
    iApply ("Hobl" $! va pax tv rr with "[%] [%] [%] Hfrag HRes Hrw Hro");
      [ exact Hcanon | exact Hvpn | exact Hident ].
  Qed.

  (* ==================================================================== *)
  (* THE USER-TABLE STEP ENGINE.                                           *)
  (*                                                                      *)
  (* [TrampStepPt.wp_instr_tramp_pt] at [Res := upt_res_pt uroot tfp um],   *)
  (* on the bundle [UptTree.utlb_inv_pt] -- i.e. the shape                 *)
  (* [SmodeCorePt.wp_instr_s_config_tlbinv_pt] has on [tlb_res_pt], with   *)
  (* [upt_swp_open]/[upt_swp_close] as the bundle face and the trampoline   *)
  (* fetch underneath.  The user table is NOT an [s_regime] and cannot be   *)
  (* one ([sr_swp_translate] is keyed on a [kmap_at] claim, and the user    *)
  (* table's mapping facts come from [um]), so this is the bespoke twin of  *)
  (* [TrampStepPt.wp_instr_ktramp_pt_share] rather than an instance.        *)
  (*                                                                      *)
  (* The fetch obligation costs the caller NOTHING beyond [hw_config]: the  *)
  (* trampoline claim is the trampoline CLAUSE of [upt_tree_spec], i.e. it  *)
  (* is already inside the bundle.                                          *)
  (* ==================================================================== *)
  Lemma wp_instr_u_pt (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
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
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ upt_satp_ok_pt uroot satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ upt_res_pt uroot tfp um tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ upt_res_pt uroot tfp um tv2) ∗
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
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         utlb_inv_pt uroot tfp um -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc
             Hinstr Hex Hcont".
    iDestruct (upt_swp_open uroot tfp um with "Hinv")
      as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt (upt_res_pt uroot tfp um)
              (upt_res_pt uroot tfp um) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr Supervisor Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (utramp_fetch_tr uroot tfp um dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                with "Hhw").
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (upt_swp_close uroot tfp um satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

  (* ==================================================================== *)
  (* THE USER-LANDING TWIN.                                                *)
  (*                                                                      *)
  (* Every trampoline instruction RUNS at Supervisor -- the trap raised    *)
  (* the privilege before the pc reached the trampoline page -- and all    *)
  (* but one of them LANDS there too.  The exception is userret's [sret],  *)
  (* which lands in User; this is [wp_instr_u_pt] with that one cell's     *)
  (* post value spelled out.  Stated CONCRETELY rather than as a           *)
  (* privilege-parametric wrapper, so that a leaf's [iApply] against the   *)
  (* cycle's WP goal has nothing extra to unify.                           *)
  (* ==================================================================== *)
  Lemma wp_instr_u_pt_user (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
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
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ upt_satp_ok_pt uroot satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ upt_res_pt uroot tfp um tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } User ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ upt_res_pt uroot tfp um tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } User -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         utlb_inv_pt uroot tfp um -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc
             Hinstr Hex Hcont".
    iDestruct (upt_swp_open uroot tfp um with "Hinv")
      as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt (upt_res_pt uroot tfp um)
              (upt_res_pt uroot tfp um) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr User Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (utramp_fetch_tr uroot tfp um dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                with "Hhw").
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (upt_swp_close uroot tfp um satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

End UptTramp.

(* ===================================================================== *)
(* 6. THE TRAPFRAME DATA ACCESS.                                          *)
(*                                                                        *)
(* [HartSMem]'s LOAD/STORE engines take the translation as an obligation   *)
(* whose shape is [SRegime.sr_swp_translate]'s conclusion at an ABSTRACT   *)
(* residue [Rt : regstate -> iProp Sigma] -- so they are regime-AGNOSTIC   *)
(* and the user table feeds them directly, with                            *)
(* [Rt := fun rs => upt_res_pt uroot tfp um (register_lookup tlb rs)].     *)
(* These two corollaries are [swp_translate_upt] at the trapframe leaf,    *)
(* in exactly that shape, with the leaf's permission check and its         *)
(* footprint certificate discharged.                                      *)
(* ===================================================================== *)

(* [UservecPt]'s [tf_variant_check_store] lives here now: the store side of
   the trapframe leaf is needed BELOW that file. *)
Lemma tf_variant_check_store (tfp : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Store Data) Supervisor mxr do_sum (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

(* the two [goodb] twins, same proof as the [exec] ones *)
Lemma tf_variant_goodb_check_load (tfp : mword 44) (a d : mword 1)
    (mxr do_sum : bool) (Db : register -> bool) (s : mstate) :
  goodb Db (check_PTE_permission (Load Data) Supervisor mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad (pte_tf tfp) a d) 7 0))
              (ext_bits_of_PTE (pte_set_ad (pte_tf tfp) a d)) tt) s = true.
Proof.
  unfold Mk_PTE_Flags.
  rewrite tf_variant_flags tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma tf_variant_goodb_check_store (tfp : mword 44) (a d : mword 1)
    (mxr do_sum : bool) (Db : register -> bool) (s : mstate) :
  goodb Db (check_PTE_permission (Store Data) Supervisor mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad (pte_tf tfp) a d) 7 0))
              (ext_bits_of_PTE (pte_set_ad (pte_tf tfp) a d)) tt) s = true.
Proof.
  unfold Mk_PTE_Flags.
  rewrite tf_variant_flags tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Section UptData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma utf_translate (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (va pa satp0 mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (rr : option resv) :
    (acc = Load Data \/ acc = Store Data) ->
    Drw ## Dro ->
    (forall r : register, upt_Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, upt_Dw r = true -> r ∈ Drw) ->
    register_lookup misa rs = MISA_C ->
    register_lookup menvcfg rs = MENVCFG_S ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mstatus rs = mst0 ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    register_lookup satp rs = satp0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup pma_regions rs = pmar0 ->
    upt_satp_ok_pt uroot satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_all pmar0 ->
    svpn_of va = tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    upt_res_pt uroot tfp um (register_lookup tlb rs) -∗
    hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  upt_res_pt uroot tfp um (register_lookup tlb rsf) ∗
                  resv_any cpu_id).
  Proof.
    intros Hacc Hdisjf HDr HDw Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV Hsatp
           Hpcfg Hpaddr Hpma Hsatpok Hpmpok Hall Hvpn Hcanon Hid.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tf tfp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
           (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tf_variant_ppn tfp ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    iIntros "#Hcert Hfrag Hres Hrw Hro".
    destruct Hacc as [-> | ->].
    - iApply (swp_translate_upt (Load Data) Drw Dro Df rs uroot tfp um
                va pa satp0 (pte_tf tfp) mst0 (register_lookup tlb rs)
                pcfg paddr pmar0 rr Hdisjf HDr HDw
                (or_intror (or_introl eq_refl))
                Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV Hsatp eq_refl Hpcfg
                Hpaddr Hpma Hsatpok Hpmpok Hall
                (or_intror (or_introl (conj Hvpn eq_refl)))
                (fun a d mxr do_sum => tf_variant_check_load tfp a d mxr do_sum)
                (fun a d mxr do_sum Db s0 =>
                   tf_variant_goodb_check_load tfp a d mxr do_sum Db s0)
                Hcanon Hout with "Hcert Hfrag Hres Hrw Hro").
    - iApply (swp_translate_upt (Store Data) Drw Dro Df rs uroot tfp um
                va pa satp0 (pte_tf tfp) mst0 (register_lookup tlb rs)
                pcfg paddr pmar0 rr Hdisjf HDr HDw
                (or_intror (or_intror (or_introl eq_refl)))
                Hmisa Hmenv Hhtif Hcp Hms HSXL HMPRV Hsatp eq_refl Hpcfg
                Hpaddr Hpma Hsatpok Hpmpok Hall
                (or_intror (or_introl (conj Hvpn eq_refl)))
                (fun a d mxr do_sum => tf_variant_check_store tfp a d mxr do_sum)
                (fun a d mxr do_sum Db s0 =>
                   tf_variant_goodb_check_store tfp a d mxr do_sum Db s0)
                Hcanon Hout with "Hcert Hfrag Hres Hrw Hro").
  Qed.

End UptData.
