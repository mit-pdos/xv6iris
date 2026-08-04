(* UserPtTree.v -- U-MODE translation over the ptree user table
   (UptTree.v): the successor of UserPt.v's upt record for arbitrary
   user-mode execution.

   Layers:
     §1 privilege bricks: effectivePrivilege at MPRV=0 (access-generic)
        and is_shadow_stack for every access user execution can issue;
     §2 the per-leaf ACCESS classification: at User, a mapped leaf either
        passes the permission check on every A/D variant ([uleaf_ok]) or
        is denied on every variant ([uleaf_denied]) -- decided once per
        map entry from its concrete R/W/X/U flag byte ([upt_acc_wf]).
        The S-mode-only trampoline / trapframe leaves are DENIED for
        every user access (U = 0);
     §3 the user-execution page-table bundle [user_pt_inv]: the tree
        invariant [utlb_inv_pt] + ownership of the mapped pages' bytes
        with EXISTENTIAL contents ([udata_own], a flat pa-set -- two
        vpns may map one page, a gset dedups) + the coverage fact;
     §4 the U-mode Ok absorption instance: a user-mapped, check-passing
        va translates to its leaf page and the invariant absorbs
        whatever the walk did (hit / TLB fill / Svadu A/D write-back).

   The FAULT side (non-canonical / unmapped / denied / hit-denied) is §5.  *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import TrampPt.
Require Import Pt4kWalk.
Require Import SmodePte.
Require Import KptTree.
Require Import UptTree.
Require Import UserTranslate.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Privilege bricks.                                                    *)
(* ===================================================================== *)

(* with MPRV clear the effective privilege is the current one, for EVERY
   access type (the fetch special case never consults MPRV) *)
Lemma exec_effectivePrivilege_mprv0 (acc : MemoryAccessType mem_payload)
    (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  exec (effectivePrivilege acc m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  apply exec_returnM.
Qed.

(* the access types arbitrary user-mode execution can issue *)
Definition u_acc (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  acc = LoadReserved Data \/ acc = StoreConditional Data \/
  (exists op, acc = Atomic (op, Data, Data)).

Lemma exec_is_shadow_stack_u_acc (acc : MemoryAccessType mem_payload) s :
  u_acc acc ->
  exec (is_shadow_stack_access acc) s = Some (false, s).
Proof.
  intros [-> | [-> | [-> | [-> | [-> | (op & ->)]]]]];
    unfold is_shadow_stack_access; cbn match; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §2 The per-leaf access classification at User.                          *)
(* ===================================================================== *)

(* the check passes on every A/D variant (check_PTE_permission never
   reads A/D, so this is a fact about the R/W/X/U byte of [w] alone) *)
Definition uleaf_ok (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_ok acc User mxr do_sum (pte_set_ad w a d).

(* ... or is denied on every variant.  NOTE the mxr quantifier: a leaf
   with X=1, R=0 would be load-DENIED only at mxr=0 -- such execute-only
   user pages fall in neither class and are excluded by [upt_acc_wf]
   (xv6 never builds them; user execution pins mstatus.MXR=0 anyway). *)
Definition uleaf_denied (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_denied acc User mxr do_sum (PTE_No_Permission tt) (pte_set_ad w a d).

(* the classification each user-map entry carries: decided once when the
   map is built, from the entry's concrete flag byte (each side is a
   4-way a/d x 4-way mxr/do_sum vm_compute) *)
Definition upt_acc_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn w, um !! vpn = Some w ->
    forall acc, u_acc acc -> uleaf_ok acc w \/ uleaf_denied acc w.

(* the S-mode-only top pages deny every user access before the access
   type is even consulted (U = 0 fails the privilege step) *)
Lemma uleaf_denied_tramp (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc pte_tramp.
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags. rewrite tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

Lemma uleaf_denied_tf (tfp : mword 44) (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc (pte_tf tfp).
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The user-execution page-table bundle.                                *)
(* ===================================================================== *)

(* the pas a mapped leaf can output: its page, at every offset *)
Definition udata_cov (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa) : Prop :=
  forall vpn w va, um !! vpn = Some w -> u_walk_pa w va ∈ data.

(* ONE pure description of a live user page table, so the whole
   user-execution development closes over a single parameter (the
   [upt]-record successor): the root and trapframe ppns, the abstract
   user map, and the data-page footprint. *)
Record uptd := UPTD {
  ud_root : mword 44;
  ud_tfp  : mword 44;
  ud_um   : gmap (mword 27) (mword 64);
  ud_data : gset Arch.pa
}.

Section UserPtInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the owned bytes of the mapped pages, contents EXISTENTIAL: user-mode
     safety never depends on what the pages hold.  One aggregated byte
     map -- accesses look up plain addresses, no per-page decomposition;
     a flat pa-set dedups pages shared by several vpns. *)
  Definition udata_own (data : gset Arch.pa) : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8),
       ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₚ b)%I.

  (* THE USER-EXECUTION PT BUNDLE: the tree invariant + the data pages +
     the pure coverage and access-classification facts. *)
  Definition user_pt_inv (P : uptd) : iProp Σ :=
    (utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) ∗
     udata_own P.(ud_data) ∗
     ⌜udata_cov P.(ud_um) P.(ud_data)⌝ ∗
     ⌜upt_acc_wf P.(ud_um)⌝)%I.

End UserPtInv.

(* ===================================================================== *)
(* §4 The U-mode Ok absorption instance: a user-mapped va whose leaf       *)
(*    passes the check translates to the leaf page; the invariant absorbs  *)
(*    whatever the walk did (hit / TLB fill / A-D write-back).             *)
(* ===================================================================== *)

Section UserPtTranslate.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma utlb_inv_pt_translateAddr_u (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va pa : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok acc w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hl Hchk Hcanon Hout Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    apply (utlb_inv_pt_translateAddr acc User uroot tfp um w va pa σ
             Hchk (or_intror (or_intror Hl))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_U_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.


  (* §4b pure-fact extraction: the PMP entry-0 facts, borrowed from the
     bundle (used before a translation move and, transported, after it) *)
  Lemma utlb_inv_pt_pmp_facts (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (σ : mstate) :
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜(pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
      zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)%type⌝.
  Proof.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro.
    rewrite Hpcv Hpav. auto 8.
  Qed.

End UserPtTranslate.

(* ===================================================================== *)
(* §5 The U-mode FAULT head: non-canonical / unmapped / denied vas page-  *)
(*    fault with the state UNCHANGED (fault paths write nothing), the     *)
(*    invariant merely borrowed.  The exception value comes through a     *)
(*    [translationException] premise the caller discharges per access     *)
(*    (fetch -> E_Fetch_Page_Fault, load -> E_Load_Page_Fault,            *)
(*    store/AMO -> E_SAMO_Page_Fault) by [cbn; apply exec_returnm].       *)
(* ===================================================================== *)

Section UserPtFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  (* NON-CANONICAL va: faults at the canonicality test; the invariant is
     borrowed only for the satp mode dispatch *)
  Lemma utlb_inv_pt_translateAddr_u_noncanon (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    exec (translationException acc (PTW_Invalid_Addr tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hcanon Hcp HSXL Heff Hss Hte.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_translateAddr_pt_front_noncanon acc User e usatp va σ
             Heff Hss Hcp
             (exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode)
             Hsatpv Hcanon Hte).
  Qed.

  (* UNMAPPED vpn (not the trampoline/trapframe, not in the user map):
     never TLB-resident (the keystone), and the walk stops at an invalid
     word in the owned tree *)
  Lemma utlb_inv_pt_translateAddr_u_unmapped (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    um !! svpn_of va = None ->
    svpn_of va <> tramp_vpn ->
    svpn_of va <> tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_Invalid_PTE tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hnone Hnt Hntf Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof Hspec as (Hbase & _ & _ & _ & Hblkspec).
    (* the spec blocks in the xv6 ZERO shape; the ownership lemma only needs
       model-invalidity *)
    pose proof (PtBuild.ptree_blocks0_blocks t (svpn_of va)
                  (Hblkspec (svpn_of va) Hnt Hntf Hnone)) as Hblk.
    iDestruct (ptree_own_blocked_mem σ (DfracOwn 1) t (svpn_of va) Hblk with "Hgh Ht")
      as %Hstop.
    iPureIntro.
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
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
      by exact (tlb_ok_pt_lookup_blocked t vpn tlbvec σ Htlbok Hblk Htlbv).
    (* the stopping prefix, as [read_pte] facts at the walk's spellings *)
    assert (Hstop' :
      (exists w2,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok w2, σ) /\ pte_invalid w2)
      \/ (exists p2 w1,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok p2, σ) /\ pte_valid p2 /\ pte_ptr p2 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) σ
            = Some (Ok w1, σ) /\ pte_invalid w1)
      \/ (exists p2 p1 w0,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok p2, σ) /\ pte_valid p2 /\ pte_ptr p2 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) σ
            = Some (Ok p1, σ) /\ pte_valid p1 /\ pte_ptr p1 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) σ
            = Some (Ok w0, σ) /\ pte_invalid w0)).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr uroot (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      destruct Hstop as
        [ (w2 & Hsm2 & Hinv2)
        | [ (p2 & w1 & Hsm2 & Hv2 & Hn2 & Hsm1 & Hinv1)
          | (p2 & p1 & w0 & Hsm2 & Hv2 & Hn2 & Hsm1 & Hv1 & Hn1 & Hsm0 & Hinv0) ] ].
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region2 & Hm2 & Hs2).
        left. exists w2.
        split; [| exact Hinv2].
        exact (pt_read_pte_slot σ _ w2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif).
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region2 & Hm2 & Hs2).
        destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region1 & Hm1 & Hs1).
        right; left. exists p2, w1.
        split; [exact (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif) |].
        split; [exact Hv2 |]. split; [exact Hn2 |].
        split; [| exact Hinv1].
        exact (pt_read_pte_slot σ _ w1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif).
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region2 & Hm2 & Hs2).
        destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region1 & Hm1 & Hs1).
        destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
          as (region0 & Hm0 & Hs0).
        right; right. exists p2, p1, w0.
        split; [exact (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif) |].
        split; [exact Hv2 |]. split; [exact Hn2 |].
        split; [exact (pt_read_pte_slot σ _ p1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif) |].
        split; [exact Hv1 |]. split; [exact Hn1 |].
        split; [| exact Hinv0].
        exact (pt_read_pte_slot σ _ w0 region0 Hsm0 HA' Hord' HR' Hcov' Hm0 Hs0 Hhtif). }
    apply (exec_translateAddr_pt_front_err acc User vpn uroot
             (PTW_Invalid_PTE tt) e usatp va σ
             Heff Hss Hcp
             (exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode)
             Hsatpv Hppn Hasid Hcanon eq_refl
             (fun mxr do_sum =>
                exec_translate_pt_blocks acc User mxr do_sum vpn uroot σ Hstop' Hlk)
             Hte).
  Qed.

  (* MAPPED but DENIED (kernel-only trampoline/trapframe pages, or a user
     page whose flags deny this access): the walk reaches the leaf and the
     check fails; a RESIDENT entry (cached by an S-phase access or an
     earlier permitted access) replays the stored check and fails the same
     way -- either way no write, no fill, state unchanged. *)
  Lemma utlb_inv_pt_translateAddr_u_denied (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va : mword 64) (e : ExceptionType) (σ : mstate) :
    upt_leaf_at tfp um (svpn_of va) w ->
    uleaf_denied acc w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_No_Permission tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hleaf Hden Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof Hspec as (Hbase & _).
    destruct (upt_spec_maps uroot tfp um t (svpn_of va) w Hspec Hleaf)
      as (p2 & p1 & a0 & d0 & Hmaps).
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & _ & _).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) t (svpn_of va) p2 p1 _ Hmaps
                 with "Hgh Ht") as %(Hsm2 & Hsm1 & Hsm0).
    iPureIntro.
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
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Htm := exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode).
    (* the walk-DENIED translate (shared by the empty-slot and
       foreign-entry cases) *)
    assert (Hwalk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ) ->
      forall mxr do_sum,
        exec (translate 39 (mword_of_int 0 : mword 16) uroot vpn acc User mxr do_sum tt) σ
        = Some (Err (PTW_No_Permission tt, tt), σ)).
    { intros Hlk mxr do_sum.
      assert (Ha2 : pt_addr2 t vpn = u_pte_addr uroot (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2.
      destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
        as (region2 & Hm2 & Hs2).
      destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
        as (region1 & Hm1 & Hs1).
      destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (u_pte_addr_no_wrap _ _ 8 eq_refl))
        as (region0 & Hm0 & Hs0).
      exact (exec_translate_pt_denied acc User mxr do_sum vpn uroot
               p2 p1 (pte_set_ad w a0 d0) σ
               Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hden a0 d0 mxr do_sum)
               (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif)
               (pt_read_pte_slot σ _ p1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif)
               (pt_read_pte_slot σ _ (pte_set_ad w a0 d0) region0 Hsm0
                  HA' Hord' HR' Hcov' Hm0 Hs0 Hhtif)
               Hlk). }
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & q0 & a' & d' & Hm0' & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* own (A/D-variant) entry resident: the HIT replays the check *)
        destruct (ptree_maps_det t vpn q2 q1 q0 p2 p1 (pte_set_ad w a0 d0) Hm0' Hmaps)
          as (-> & -> & ->).
        assert (Htr : forall mxr do_sum,
          exec (translate 39 (mword_of_int 0 : mword 16) uroot vpn acc User mxr do_sum tt) σ
          = Some (Err (PTW_No_Permission tt, tt), σ)).
        { intros mxr do_sum.
          unfold translate.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlbv Hslot
                        (uwe_match_self vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')))).
          cbn match.
          assert (Hdenc : pte_check_denied acc User mxr do_sum
                    (PTE_No_Permission tt)
                    (pte_set_ad (pte_set_ad w a0 d0) a' d')).
          { rewrite (pte_set_ad_absorb w a0 d0 a' d'). apply Hden. }
          apply (exec_translate_TLB_hit_denied_pt acc User mxr do_sum
                   vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')
                   (mword_of_int 0) (tlb_hash (__id 39) vpn) σ Hdenc). }
        apply (exec_translateAddr_pt_front_err acc User vpn uroot
                 (PTW_No_Permission tt) e usatp va σ
                 Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
                 Htr Hte).
      + (* foreign entry: rejected by the tag, the walk runs and denies *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlbv Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a' d')
                         (mword_of_int 0) Hne)).
        apply (exec_translateAddr_pt_front_err acc User vpn uroot
                 (PTW_No_Permission tt) e usatp va σ
                 Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
                 (Hwalk Hlk) Hte).
    - (* empty slot: the walk runs and denies *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlbv Hslot).
      apply (exec_translateAddr_pt_front_err acc User vpn uroot
               (PTW_No_Permission tt) e usatp va σ
               Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
               (Hwalk Hlk) Hte).
  Qed.

End UserPtFault.

(* ===================================================================== *)
(* §5b The COMBINED fault wrapper: the three fault flavors, as ONE        *)
(*     access-generic predicate and one dispatch lemma.  (For every       *)
(*     access user execution issues, translationException maps all three  *)
(*     PTW errors to the same page-fault exception -- the caller passes   *)
(*     the three concrete mappings, each a [cbn]-discharge.)              *)
(* ===================================================================== *)

(* the ways a user access at [va] can fault in translation *)
Definition u_fault_flavor (acc : MemoryAccessType mem_payload)
    (tfp : mword 44) (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true
  \/ (neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
      um !! svpn_of va = None /\
      svpn_of va <> tramp_vpn /\ svpn_of va <> tf_vpn)
  \/ (neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
      exists w, upt_leaf_at tfp um (svpn_of va) w /\
                uleaf_denied acc w).

Section UserPtFaultCombined.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma utlb_inv_pt_translateAddr_u_fault (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    u_fault_flavor acc tfp um va ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_Invalid_Addr tt)) σ = Some (e, σ) ->
    exec (translationException acc (PTW_Invalid_PTE tt)) σ = Some (e, σ) ->
    exec (translationException acc (PTW_No_Permission tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hflavor Hhtif Hcp HSXL Heff Hss Hall Hte1 Hte2 Hte3.
    iIntros "Hri Hgh Hinv".
    destruct Hflavor as
      [ Hnc | [ (Hcanon & Hnone & Hnt & Hntf) | (Hcanon & w & Hleaf & Hden) ] ].
    - iApply (utlb_inv_pt_translateAddr_u_noncanon acc uroot tfp um va e σ
                Hnc Hcp HSXL Heff Hss Hte1 with "Hri Hinv").
    - iApply (utlb_inv_pt_translateAddr_u_unmapped acc uroot tfp um va e σ
                Hnone Hnt Hntf Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte2
                with "Hri Hgh Hinv").
    - iApply (utlb_inv_pt_translateAddr_u_denied acc uroot tfp um w va e σ
                Hleaf Hden Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte3
                with "Hri Hgh Hinv").
  Qed.

End UserPtFaultCombined.

