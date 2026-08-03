(* KptShare.v -- THE SHARED KERNEL PAGE TABLE.

   [KptTree.tlb_inv_pt] bundles per-hart register cells (satp, tlb,
   pmp_config) with the GLOBALLY UNIQUE tree ownership [ptree_own 2 1 t] and
   mapping auth [kmap_auth M].  That makes it unshareable, so
   [kvminithart] could only ever be proved for one hart.  A fraction cannot
   help: the tree genuinely MUTATES (the Svadu/ADUE walk writes A/D bits
   back), and a memory write needs full ownership of the written bytes.

   This file splits the bundle (claude-notes/completed/kpt-share.md):

     [kpt_inv root]   -- an Iris INVARIANT holding the globally unique
                         parts: the tree, its A/D-monotone auth
                         ([KptGhost.kpt_lb], the one-shot agreement on
                         its A/D-canonical form), the mapping auth, and the
                         representation fact.  Persistent, allocated once
                         out of kvminit's exclusive post.

     [tlb_res_pt root] -- the PER-HART residue: this hart's satp cell (+
                         the three Sv39/asid/root facts), this hart's tlb
                         cell, its cached-entry coherence stated against a
                         SNAPSHOT ([∃ t0, ⌜tlb_ok_pt 0 t0 tlbvec⌝ ∗
                         kpt_lb t0]), its pmp cells, and [kpt_inv root]
                         riding along (persistent, so every hart has it).

   The absorption theorem becomes MASK-CARRYING: it opens [kptN], reads the
   snapshot order back off the auth, lifts the hart's TLB coherence to the
   live tree with [tlb_ok_pt_ad_mono], performs the write-back against the
   invariant's tree ownership, bumps the auth along [ptree_ad_le], mints a
   fresh snapshot for the hart, and re-closes.  Everything the invariant
   holds is TIMELESS ([PtTree.ptree_own_timeless]), which is what lets the
   write-back happen in the same fupd the invariant was opened in.

   [KptTree.tlb_inv_pt] itself is UNCHANGED and still serves the exclusive
   single-table settings that genuinely need to own the tree -- above all
   the satp-switch window (TransPt.v / UserretEntryPt.v / UservecExitPt.v),
   which parks the kernel table while a user table is installed and so
   cannot be re-based on a shared invariant.  Bridging those two worlds is
   a separate sweep; [tlb_inv_pt_share] is the one-way door.           *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import SmodePte PtAdBits Pt4kWalk.
Require Import PtTree PtTreeAdue KptPt KMap SmodeCore KptTree.
Require Import KptGhost.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section KptShare.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* §1 The shared invariant.                                            *)
  (* ------------------------------------------------------------------- *)

  (* [kptN] itself lives in KptGhost.v -- SRegime's absorb field names it in
     its mask premise. *)

  Definition kpt_body (root_ppn : mword 44) : iProp Σ :=
    (∃ (t : ptree) (M : gmap (mword 27) (mword 44 * kperm)),
       ptree_own 2 (DfracOwn 1) t ∗
       kpt_lb t ∗
       kmap_auth M ∗
       ⌜ kpt_tree_spec_gen root_ppn M t ⌝)%I.

  Global Instance kpt_body_timeless root_ppn : Timeless (kpt_body root_ppn).
  Proof. rewrite /kpt_body. apply _. Qed.

  Definition kpt_inv (root_ppn : mword 44) : iProp Σ :=
    inv kptN (kpt_body root_ppn).

  Global Instance kpt_inv_persistent root_ppn : Persistent (kpt_inv root_ppn).
  Proof. apply _. Qed.

  Lemma kpt_inv_alloc (root_ppn : mword 44)
      (t : ptree) (M : gmap (mword 27) (mword 44 * kperm)) (E : coPset) :
    kpt_tree_spec_gen root_ppn M t ->
    ptree_own 2 (DfracOwn 1) t -∗ kmap_auth M -∗ kpt_unset ={E}=∗
    kpt_inv root_ppn ∗ kpt_lb t.
  Proof.
    intros Hspec. iIntros "Ht HM Hunset".
    iMod (kpt_shoot t with "Hunset") as "#Hlb".
    iMod (inv_alloc kptN _ (kpt_body root_ppn) with "[Ht HM]") as "#Hinv".
    { iNext. iExists t, M. iFrame "Ht HM Hlb". iPureIntro. exact Hspec. }
    iModIntro. iFrame "Hinv Hlb".
  Qed.

  (* A SNAPSHOT off the shared invariant: the persistent [kpt_lb] of
     whatever tree is current.  This is the whole of what a hart needs to
     re-enter the KPT arm without ever owning the table -- [tlb_res_pt_intro]
     asks for a snapshot and nothing else -- and it is what makes
     kvminithart's contract hart-generic (claude-notes/completed/kpt-share.md
     §5): the switching hart's TLB is empty (both sfence.vmas), so
     [tlb_ok_pt_empty] holds at ANY tree and the snapshot may be arbitrary.
     [kpt_body] is Timeless, so this costs one [iMod] and no later. *)
  Lemma kpt_inv_snapshot (E : coPset) (root_ppn : mword 44) :
    ↑kptN ⊆ E ->
    kpt_inv root_ppn ={E}=∗ ∃ t : ptree, kpt_lb t.
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc E kptN with "Hinv") as "[>Hbody Hclose]"; [ exact HE | ].
    iDestruct "Hbody" as (t M) "(Ht & #Hlb & HM & %Hspec)".
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists t, M. iFrame "Ht HM Hlb". iPureIntro. exact Hspec. }
    iModIntro. iExists t. iExact "Hlb".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 The per-hart residue.                                            *)
  (* ------------------------------------------------------------------- *)

  (* the hart's TLB coherence, stated against a SNAPSHOT of the shared tree *)
  Definition tlb_snap_ok (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : iProp Σ :=
    (∃ t0 : ptree, ⌜ tlb_ok_pt (mword_of_int 0) t0 tlbvec ⌝ ∗ kpt_lb t0)%I.

  Definition tlb_res_pt (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ tlb_snap_ok tlbvec ∗
       pmp_config root_ppn ∗
       kpt_inv root_ppn)%I.

  Lemma tlb_res_pt_intro (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t0 : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_ok_pt (mword_of_int 0) t0 tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_lb t0 -∗
    pmp_config root_ppn -∗ kpt_inv root_ppn -∗
    tlb_res_pt root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hok. iIntros "Hsatp Htlb Hlb Hpmp Hinv".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpmp Hinv".
    iSplitR; [iPureIntro; exact Hmode |].
    iSplitR; [iPureIntro; exact Hasid |].
    iSplitR; [iPureIntro; exact Hppn |].
    iExists t0. iFrame "Hlb". iPureIntro. exact Hok.
  Qed.

  Lemma tlb_res_pt_open (root_ppn : mword 44) :
    tlb_res_pt root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ tlb_snap_ok tlbvec ∗
      pmp_config root_ppn ∗ kpt_inv root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

  (* the PMP grant facts, straight off the residue's own pmp cells *)
  Lemma tlb_res_pt_grant_facts (root_ppn : mword 44) (σ : mstate) :
    reg_interp σ.(sregs) -∗ tlb_res_pt root_ppn -∗
    ⌜ pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
      zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ⌝.
  Proof.
    iIntros "Hri Hres".
    iDestruct (tlb_res_pt_open with "Hres") as (satp0 tlbvec)
      "(_ & _ & _ & _ & _ & _ & Hpmp & _)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro. rewrite Hpcv Hpav. tauto.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 The one-way door from the exclusive bundle.                      *)
  (* ------------------------------------------------------------------- *)

  Lemma tlb_inv_pt_share (root_ppn : mword 44) (E : coPset) :
    tlb_inv_pt root_ppn -∗ kpt_unset ={E}=∗ tlb_res_pt root_ppn.
  Proof.
    iIntros "Hinv Hnone".
    iDestruct (tlb_inv_pt_open with "Hinv") as (satp0 tlbvec t M)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hok & %Hspec & HM & Ht & Hpmp)".
    iMod (kpt_inv_alloc root_ppn t M E Hspec with "Ht HM Hnone") as "[#Hkinv #Hlb]".
    iModIntro.
    iApply (tlb_res_pt_intro root_ppn satp0 tlbvec t Hmode Hasid Hppn Hok
              with "Hsatp Htlb Hlb Hpmp Hkinv").
  Qed.

End KptShare.

(* ===================================================================== *)
(* §4 THE MASK-CARRYING ABSORPTION THEOREM.  The [tlb_inv_pt_            *)
(*    translateAddr_at] mirror over the shared table: same claim-keyed    *)
(*    interface, but a fupd at any mask containing [↑kptN].               *)
(* ===================================================================== *)

Section KptShareTranslate.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma tlb_res_pt_translateAddr_at (root_ppn : mword 44) (va pa : mword 64)
      (ppn : mword 44) (pc : kperm) (σ : mstate) (E : coPset) :
    ↑kptN ⊆ E ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    kmap_at (svpn_of va) ppn pc -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_res_pt root_ppn
    ={E}=∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_res_pt root_ppn.
  Proof.
    intros HE Hchk Hcanon Hid4k Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hat Hri Hgh Hres".
    iDestruct (tlb_res_pt_open with "Hres") as (satp0 tlbvec)
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
      by exact (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags pc) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn pc ('b"1") ('b"1")) in Hid4k.
      rewrite pte_set_ad_ppn in Hid4k. exact Hid4k. }
    assert (Hvar : forall a d : mword 1,
       pte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_leaf (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_no_napot (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)).
    { intros a d. repeat split.
      - apply kperm_variant_valid.
      - apply kperm_variant_leaf.
      - apply kperm_variant_no_napot.
      - apply kperm_variant_pbmt0. }
    (* ---- open the shared table ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan0.
    (* the hart's cached entries are coherent with the LIVE tree: coherence
       depends on the table only through its canonical form *)
    assert (Htlbok : tlb_ok_pt (mword_of_int 0) t tlbvec)
      by exact (tlb_ok_pt_canon (mword_of_int 0) t0 t tlbvec Hcan0 Htlbok0).
    set (vpn := svpn_of va) in *.
    pose proof Hspec as (Hbase & Hmapspec).
    pose proof (Hmapspec vpn) as Hmapv. rewrite HMlk in Hmapv.
    destruct Hmapv as (p2 & p1 & a0 & d0 & Hmaps).
    assert (Hlf : kpt_leaf_pte_of vpn (ppn, pc) = mk_pte ppn (kperm_flags pc))
      by reflexivity.
    rewrite Hlf in Hmaps.
    iMod (ptree_translateAddr_own acc Supervisor root_ppn t
            (mk_pte ppn (kperm_flags pc)) va pa satp0
            tlbvec p2 p1 a0 d0 σ
            Hchk Hvar Hcanon Hout Hbase Hmaps Htlbok
            Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
            HA' Hord' HR' HW' Hcov' Hpmar Hpmaw
            with "Hri Hgh Htlb Ht")
      as (σ' t' tlbvec') "(%Htrans & %Hmdev & %Hsregs & %Htsh & %Htlbok' & Hri & Hgh & Htlb & Ht)".
    (* ---- the write-back does NOT move the canonical table, so the
       snapshot is re-derived by a rewrite: no ghost update at all ---- *)
    assert (Hcan' : ptree_canon t = ptree_canon t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [reflexivity |].
      rewrite <- (pte_set_ad_absorb (mk_pte ppn (kperm_flags pc)) a0 d0 a1 d1).
      symmetry.
      exact (ptree_canon_set_leaf t vpn p2 p1
               (pte_set_ad (mk_pte ppn (kperm_flags pc)) a0 d0) a1 d1 Hmaps). }
    iDestruct (kpt_lb_canon t t' Hcan' with "Hlbt") as "#Hlb'".
    assert (Hspec' : kpt_tree_spec_gen root_ppn M t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [exact Hspec |].
      rewrite <- (pte_set_ad_absorb (mk_pte ppn (kperm_flags pc)) a0 d0 a1 d1).
      apply (kpt_tree_spec_gen_set_leaf root_ppn M t vpn (ppn, pc) p2 p1
               (pte_set_ad (mk_pte ppn (kperm_flags pc)) a0 d0) a1 d1
               Hspec Hmaps HMlk).
      exists a0, d0. rewrite Hlf. reflexivity. }
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists t', M. iFrame "Ht HM Hlb'". iPureIntro. exact Hspec'. }
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htrans |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsregs |].
    iFrame "Hri Hgh".
    iDestruct (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                 HA Hord HX HW HR Hcov with "Hpc Hpa") as "Hpmp".
    iApply (tlb_res_pt_intro root_ppn satp0 tlbvec' t'
              Hmode Hasid Hppn Htlbok'
              with "Hsatp Htlb Hlb' Hpmp Hkinv").
  Qed.

End KptShareTranslate.
