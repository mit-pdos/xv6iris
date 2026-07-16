(* UserPt.v -- the USER page-table invariant for arbitrary user-mode
   execution: the generalization of [utlb_inv] (WpUserret.v) from the fixed
   trampoline+trapframe table to an ARBITRARY set of user mappings.

   A user page table is described by ONE pure object [upt]:
     - [u_root]  : the root PT ppn (what satp points at);
     - [u_slots] : the populated PT slots, an address-indexed map of 8-byte
                   PTE words.  Ownership is per SLOT, not per vpn: upper-level
                   slots are shared by many vpns, so a per-vpn big-op would
                   duplicate ownership.  A kernel instantiation puts EVERY
                   slot of every PT page in the map (zeroed slots hold the
                   zero word = an invalid PTE), so the walk for EVERY vpn
                   only ever reads owned slots;
     - [u_map]   : the mapped vpns, each with its 3-level walk description
                   [umap_ent] (the three PTE words the walk reads).  The
                   LEAF's permission/A/D bits are ARBITRARY -- [umap_ent_wf]
                   constrains only the STRUCTURE (valid non-leaf pointers,
                   a valid 4K leaf, no NAPOT, non-global, PBMT off).  Whether
                   a given access succeeds, is denied (e.g. U=0 kernel pages
                   like the trampoline, or a store to a read-only page), or
                   needs an A/D update (page fault under Svade) is decided
                   PER ACCESS from the actual bits -- all outcomes are safe;
     - [u_data]  : the physical footprint of the mapped pages.  The invariant
                   owns every byte of it with EXISTENTIAL contents: user-mode
                   safety never depends on what the pages hold.

   The Iris half [upt_inv pt] bundles -- mirroring the kernel's [tlb_inv] --
   the satp cell (pinned to Sv39/asid 0/[u_root]), the tlb cell together with
   [upt_tlb_ok] (every resident entry is the walk entry of some mapped vpn),
   ownership of the slots and the data bytes, the PMP configuration, and the
   pure well-formedness [upt_wf].  Because the invariant OWNS the slot bytes
   and the page bytes, separation guarantees the mapped pages are disjoint
   from the PT itself and from everything else the kernel owns: no user
   store can corrupt the table or any kernel data structure.               *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte Pt4kWalk KptPt SmodeCore.
Require Import CommonWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 PTE-word predicates: the shapes CommonWalk's walk lemmas consume.    *)
(* ===================================================================== *)

(* the PTE word is valid (V=1, and no reserved-bit violation) *)
Definition upte_valid (w : mword 64) : Prop :=
  forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w)) s = Some (false, s).

(* the PTE word is invalid: the walk stops here with PTW_Invalid_PTE *)
Definition upte_invalid (w : mword 64) : Prop :=
  forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w)) s = Some (true, s).

(* non-leaf (pointer to the next level) vs leaf *)
Definition upte_nonleaf (w : mword 64) : Prop :=
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = true.
Definition upte_leaf (w : mword 64) : Prop :=
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = false.

(* leaf extras: no NAPOT, PBMT bits off (the TLB-hit path recomputes the
   page type from the STORED pte, so the spec pins it; the walk path only
   needs menvcfg.PBMTE = 0) *)
Definition upte_no_napot (w : mword 64) : Prop :=
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE w)) ('b"1") = false.
Definition upte_pbmt0 (w : mword 64) : Prop :=
  _get_PTE_Ext_PBMT (ext_bits_of_PTE w) = ('b"00" : mword 2).

(* the per-access permission check on a leaf, at User privilege, at a
   CONCRETE mxr/do_sum (the user frame pins mstatus.MXR = 0; SUM does not
   affect U-mode accesses, but the model threads it, so it stays a
   parameter).  With the leaf's R/W/X/A/D arbitrary, each access either
   passes or is denied -- BOTH are safe outcomes, dispatched per access. *)
Definition upte_check_ok (acc : MemoryAccessType mem_payload)
    (mxr do_sum : bool) (w : mword 64) : Prop :=
  forall s, exec (check_PTE_permission acc User mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w) tt) s
            = Some (PTE_Check_Success tt, s).
Definition upte_check_denied (acc : MemoryAccessType mem_payload)
    (mxr do_sum : bool) (w : mword 64) : Prop :=
  forall s, exec (check_PTE_permission acc User mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w) tt) s
            = Some (PTE_Check_Failure (tt, PTE_No_Permission tt), s).

(* ===================================================================== *)
(* §2 The pure page-table description.                                     *)
(* ===================================================================== *)

(* one mapped vpn = the three PTE words its walk reads *)
Record umap_ent := UMapEnt {
  um_pte2 : mword 64;   (* root level: valid non-leaf *)
  um_pte1 : mword 64;   (* mid level:  valid non-leaf *)
  um_pte0 : mword 64    (* leaf: 4K, arbitrary permission/A/D bits *)
}.

(* the three slot addresses the walk for [vpn] reads *)
Definition um_addr2 (root : mword 44) (vpn : mword 27) : mword 64 :=
  u_pte_addr root (subrange_vec_dec vpn 26 18).
Definition um_addr1 (e : umap_ent) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base (um_pte2 e)) (subrange_vec_dec vpn 17 9).
Definition um_addr0 (e : umap_ent) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base (um_pte1 e)) (subrange_vec_dec vpn 8 0).

(* structural well-formedness: exactly CommonWalk's UserWalk hypotheses,
   MINUS the per-access permission check (arbitrary bits; decided per
   access by [upte_check_ok]/[upte_check_denied]/[update_PTE_Bits]) *)
Definition umap_ent_wf (e : umap_ent) : Prop :=
  upte_valid (um_pte2 e) /\ upte_nonleaf (um_pte2 e) /\
  upte_valid (um_pte1 e) /\ upte_nonleaf (um_pte1 e) /\
  upte_valid (um_pte0 e) /\ upte_leaf (um_pte0 e) /\
  upte_no_napot (um_pte0 e) /\
  u_global (um_pte2 e) (um_pte1 e) (um_pte0 e) = false /\
  upte_pbmt0 (um_pte0 e).

(* the whole table *)
Record upt := UPT {
  u_root  : mword 44;
  u_slots : gmap (mword 64) (mword 64);
  u_map   : gmap (mword 27) umap_ent;
  u_data  : gset Arch.pa
}.

(* every mapped vpn's walk reads exactly its recorded slots *)
Definition upt_map_spec (pt : upt) : Prop :=
  forall vpn e, pt.(u_map) !! vpn = Some e ->
    pt.(u_slots) !! um_addr2 pt.(u_root) vpn = Some (um_pte2 e) /\
    pt.(u_slots) !! um_addr1 e vpn = Some (um_pte1 e) /\
    pt.(u_slots) !! um_addr0 e vpn = Some (um_pte0 e) /\
    umap_ent_wf e.

(* every UNMAPPED vpn's walk stops at an INVALID slot (all three stopping
   levels).  This pins the table to the 3-level-4K shape xv6 builds: no
   superpage leaves, no L0 non-leaf junk.  Kernel-only pages (trampoline,
   trapframe) are NOT "unmapped" -- they are [u_map] entries whose leaf
   denies user access (U = 0). *)
Definition upt_unmapped_spec (pt : upt) : Prop :=
  forall vpn, pt.(u_map) !! vpn = None ->
    (* the root slot is invalid *)
    (exists w2,
        pt.(u_slots) !! um_addr2 pt.(u_root) vpn = Some w2 /\ upte_invalid w2)
    (* the root descends but the mid slot is invalid *)
    \/ (exists w2 w1,
        pt.(u_slots) !! um_addr2 pt.(u_root) vpn = Some w2 /\
        upte_valid w2 /\ upte_nonleaf w2 /\
        pt.(u_slots) !! u_pte_addr (u_next_base w2) (subrange_vec_dec vpn 17 9)
          = Some w1 /\
        upte_invalid w1)
    (* both levels descend; the leaf slot is invalid *)
    \/ (exists w2 w1 w0,
        pt.(u_slots) !! um_addr2 pt.(u_root) vpn = Some w2 /\
        upte_valid w2 /\ upte_nonleaf w2 /\
        pt.(u_slots) !! u_pte_addr (u_next_base w2) (subrange_vec_dec vpn 17 9)
          = Some w1 /\
        upte_valid w1 /\ upte_nonleaf w1 /\
        pt.(u_slots) !! u_pte_addr (u_next_base w1) (subrange_vec_dec vpn 8 0)
          = Some w0 /\
        upte_invalid w0).

(* the data footprint covers every mapped leaf page: any pa a mapped vpn's
   leaf can translate to (any va -- only the low 12 bits enter) is owned *)
Definition upt_data_cov (pt : upt) : Prop :=
  forall vpn e va, pt.(u_map) !! vpn = Some e ->
    u_walk_pa (um_pte0 e) va ∈ pt.(u_data).

Definition upt_wf (pt : upt) : Prop :=
  upt_map_spec pt /\ upt_unmapped_spec pt /\ upt_data_cov pt.

(* ===================================================================== *)
(* §3 TLB consistency: user execution only ever installs walk entries.     *)
(* ===================================================================== *)

(* the entry a completed walk for [vpn] installs (asid 0 throughout) *)
Definition um_tlb_ent (vpn : mword 27) (e : umap_ent) : TLB_Entry :=
  u_walk_entry vpn (um_pte2 e) (um_pte1 e) (um_pte0 e) (mword_of_int 0).

(* every resident TLB slot is the walk entry of some mapped vpn (quantified
   through the hash so the fill lemma needs no hash injectivity) *)
Definition upt_tlb_ok (m : gmap (mword 27) umap_ent)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  forall (vpn' : mword 27) ent,
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = Some ent ->
    exists vpn e, m !! vpn = Some e /\
      tlb_hash (__id 39) vpn = tlb_hash (__id 39) vpn' /\
      ent = um_tlb_ent vpn e.

(* an all-empty TLB is consistent with any map *)
Lemma upt_tlb_ok_empty (m : gmap (mword 27) umap_ent)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall vpn', vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = None) ->
  upt_tlb_ok m tlbvec.
Proof.
  intros Hnone vpn' ent Hget. rewrite Hnone in Hget. discriminate.
Qed.

(* consistency survives a walk-induced fill -- the ONLY TLB write user
   execution can cause (add_to_TLB at the end of a successful miss walk) *)
Lemma upt_tlb_ok_fill (m : gmap (mword 27) umap_ent)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (e : umap_ent) :
  m !! vpn = Some e ->
  upt_tlb_ok m tlbvec ->
  upt_tlb_ok m (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                  (Some (um_tlb_ent vpn e))).
Proof.
  intros Hvpn Hok vpn' ent Hget.
  rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)) in Hget.
  destruct (Z.eqb (tlb_hash (__id 39) vpn') (tlb_hash (__id 39) vpn)) eqn:Hh.
  - apply Z.eqb_eq in Hh. injection Hget as <-.
    exists vpn, e. auto.
  - exact (Hok vpn' ent Hget).
Qed.

(* ===================================================================== *)
(* §3b Stored-entry bridges: a resident [um_tlb_ent] recovers the leaf     *)
(* facts the TLB-hit translation consumes, matches exactly its own vpn     *)
(* (asid 0), and an UNMAPPED vpn can never be cached.                      *)
(* ===================================================================== *)

Lemma upt_subrange64_id (w : mword 64) : subrange_vec_dec w 63 0 = w.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (63 - 0 + 1)) with 64%N.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma upt_eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply bool_decide_eq_true_2. reflexivity. Qed.

(* dropping a zero-width mask is a no-op, at the two widths the entry uses *)
Lemma upt_and_ones45 (x : mword 45) :
  and_vec x (not_vec (zero_extend' (57 - 12) (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  change (Z.sub 57 12) with 45.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 45) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

Lemma upt_and_ones27 (x : mword 27) :
  and_vec x (not_vec (zero_extend' 27 (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 27) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

(* the stored 8-byte PTE is the walk's leaf *)
Lemma um_tlb_ent_pte (vpn : mword 27) (e : umap_ent) :
  tlb_get_pte 8 (um_tlb_ent vpn e) = um_pte0 e.
Proof.
  unfold tlb_get_pte, um_tlb_ent, u_walk_entry. cbn [TLB_Entry_pte].
  rewrite autocast_id. rewrite zero_extend'_id.
  change (Z.sub (Z.mul 8 8) 1) with 63.
  rewrite upt_subrange64_id. apply autocast_id.
Qed.

(* a stored walk entry matches a lookup for vpn' iff the sign-extended
   vpns agree (asid is 0 on both sides, the entry is non-global) *)
Lemma um_tlb_ent_match_gen (vpn vpn' : mword 27) (e : umap_ent) :
  match_TLB_Entry (um_tlb_ent vpn e) (mword_of_int 0) (sign_extend' (57 - 12) vpn')
  = eq_vec (sign_extend' (57 - 12) vpn) (sign_extend' (57 - 12) vpn').
Proof.
  unfold match_TLB_Entry, um_tlb_ent, u_walk_entry.
  cbn [TLB_Entry_global TLB_Entry_asid TLB_Entry_vpn TLB_Entry_levelMask].
  rewrite upt_and_ones45. rewrite upt_and_ones27. rewrite upt_eq_vec_refl.
  rewrite orb_true_r. reflexivity.
Qed.

Lemma um_tlb_ent_match_inj (vpn vpn' : mword 27) (e : umap_ent) :
  match_TLB_Entry (um_tlb_ent vpn e) (mword_of_int 0) (sign_extend' (57 - 12) vpn')
    = true ->
  vpn = vpn'.
Proof.
  rewrite um_tlb_ent_match_gen. intros He.
  apply u_sext45_inj. apply eq_vec_true_iff. exact He.
Qed.

(* dropping the zero-width mask at the entry's ppn width *)
Lemma upt_and_ones44 (x : mword 44) :
  and_vec x (not_vec (zero_extend' 44 (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 44) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

Lemma upt_zext44_id (a : mword 44) : zero_extend' 44 a = a.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.zero_extend].
  apply bv_eq. rewrite bv_zero_extend_unsigned. reflexivity. lia.
Qed.

(* the stored entry's page type is PBMT_PMA (leaf PBMT bits pinned 0) *)
Lemma um_tlb_ent_pbmt (vpn : mword 27) (e : umap_ent) (s : mstate) :
  upte_pbmt0 (um_pte0 e) ->
  exec (tlb_get_pbmt (um_tlb_ent vpn e)) s = Some (PBMT_PMA, s).
Proof.
  intros Hp.
  unfold tlb_get_pbmt, um_tlb_ent, u_walk_entry. cbn [TLB_Entry_pte].
  rewrite autocast_id. rewrite zero_extend'_id.
  rewrite Hp.
  apply exec_returnm.
Qed.

(* [tlb_get_ppn] on a stored (4K, levelMask-0) entry is the leaf's ppn,
   for ANY looked-up vpn -- the SAME ppn the walk path outputs, so the
   hit and walk translations agree on the physical address *)
Lemma um_tlb_ent_ppn (vpn vpn' : mword 27) (e : umap_ent) :
  tlb_get_ppn 39 (um_tlb_ent vpn e) vpn'
  = autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (um_pte0 e))) : mword 44).
Proof.
  unfold tlb_get_ppn, um_tlb_ent, u_walk_entry.
  cbn [TLB_Entry_levelMask TLB_Entry_ppn].
  match goal with |- context[and_vec ?x ?m] =>
    replace (and_vec x m) with (zeros' 64 : mword 64);
    [| symmetry; apply and64_zero_r; vm_compute; reflexivity] end.
  rewrite or64_zeros_r.
  rewrite upt_and_ones44.
  rewrite upt_zext44_id.
  apply trunc44_zext.
Qed.

(* an UNMAPPED vpn can never hit the TLB: a colliding resident entry is
   some mapped vpn's walk entry, whose match would force vpn equality *)
Lemma upt_lookup_TLB_unmapped
    (m : gmap (mword 27) umap_ent) (vpn : mword 27)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) :
  m !! vpn = None ->
  upt_tlb_ok m tlbvec ->
  register_lookup tlb σ.(sregs) = tlbvec ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ).
Proof.
  intros Hvpn Hok Ltlb.
  destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
  - destruct (Hok vpn ent Hslot) as (vpn' & e & Hvpn' & _ & ->).
    apply (exec_lookup_TLB_nomatch vpn (mword_of_int 0) (um_tlb_ent vpn' e) tlbvec σ
             Ltlb Hslot).
    rewrite um_tlb_ent_match_gen.
    match goal with |- ?E = false => destruct E eqn:He; [exfalso|reflexivity] end.
    apply eq_vec_true_iff in He.
    apply u_sext45_inj in He.
    rewrite He in Hvpn'.
    rewrite Hvpn in Hvpn'. discriminate.
  - exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Ltlb Hslot).
Qed.

(* ===================================================================== *)
(* §4 The Iris half: ownership + the invariant bundle.                     *)
(* ===================================================================== *)
Section UserPtIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the owned PT slots (full fraction: slots stay writable, so a future
     hardware-A/D-update extension could write them back in place) *)
  Definition upt_slots_own (slots : gmap (mword 64) (mword 64)) : iProp Σ :=
    ([∗ map] a ↦ w ∈ slots, a ↦₈ w)%I.

  (* the owned bytes of the mapped pages, contents EXISTENTIAL: safety
     never depends on what user memory holds.  One aggregated byte map --
     accesses (including page-straddling ones) look up plain addresses,
     no per-page decomposition. *)
  Definition upt_data_own (data : gset Arch.pa) : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8),
       ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₘ b)%I.

  (* satp geometry: Sv39, asid 0, root ppn *)
  Definition upt_satp_ok (pt : upt) (usatp : mword 64) : Prop :=
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) /\
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64))
      = (mword_of_int 0 : mword 16) /\
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64))
      = pt.(u_root).

  (* ------------------------------------------------------------------- *)
  (* THE USER PAGE-TABLE INVARIANT (the [tlb_inv] mirror for a user        *)
  (* table): satp + tlb cells with their pure consistency, ownership of    *)
  (* the PT slots and the mapped pages, the PMP configuration, and the     *)
  (* pure table shape.                                                     *)
  (* ------------------------------------------------------------------- *)
  Definition upt_inv (pt : upt) : iProp Σ :=
    (∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ usatp ∗ ⌜upt_satp_ok pt usatp⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜upt_tlb_ok pt.(u_map) tlbvec⌝ ∗
       upt_slots_own pt.(u_slots) ∗
       upt_data_own pt.(u_data) ∗
       pmp_config pt.(u_root) ∗
       ⌜upt_wf pt⌝)%I.

  Lemma upt_inv_intro (pt : upt) (usatp : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    upt_satp_ok pt usatp ->
    upt_tlb_ok pt.(u_map) tlbvec ->
    upt_wf pt ->
    satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec -∗
    upt_slots_own pt.(u_slots) -∗ upt_data_own pt.(u_data) -∗
    pmp_config pt.(u_root) -∗
    upt_inv pt.
  Proof.
    intros Hsatp Hok Hwf. iIntros "Hsatp Htlb Hslots Hdata Hpmp".
    iExists usatp, tlbvec. iFrame. iPureIntro. tauto.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5 Reading PT slots: one owned slot word yields its [read_pte] exec   *)
  (* fact at any machine state consistent with the frame.  Alignment and   *)
  (* RAM-ness travel with [↦₈]; PMP entry 0 is the frame's all-of-RAM TOR  *)
  (* entry; PMA / CLINT / SIG / HTIF discharge from [hw_config].           *)
  (* ------------------------------------------------------------------- *)
  Lemma upt_slot_read_pte (a : mword 64) (w : bv 64) (dq : dfrac) (σ : mstate) :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    (a ↦₈{dq} w) -∗
    ⌜exec (read_pte (Physaddr a) 8) σ = Some (Ok w, σ)⌝.
  Proof.
    iIntros (HA Hord HR Hcov Hpter) "Hhw [Hreg [Hmem Hdev]] Hw".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hpmm & %Hmlpe & %Help_ne & %HmisaA &
        %Hmisa_val & %Hmseccfg_val)".
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hbytes".
    (* the byte heap agrees with [w] on the 8-byte window *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add a j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    (* RAM-ness of both window ends, for the PMP range fact *)
    iAssert (⌜addr_is_ram a⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hram7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    iPureIntro.
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    destruct (Hpter pmar0 Hpma_all a) as (region & Hpmam & Hptep).
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr a) 8 = Some region) by (rewrite Lpma; exact Hpmam).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint a) (uint (to_bits 64 8)) = PMP_Match).
    { exact (ram_fetch_pmp a (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram7 Hcov). }
    exact (exec_read_pte_S a region w σ
             HA Hord Hrange HR Hpmam' Hal Hptep
             (within_clint_false a 8 σ Hnc ltac:(lia))
             (within_sig_false a 8 σ Hns ltac:(lia))
             (within_htif_false a 8 σ Lhtif)
             (addr_is_ram_not_dev _ Hram)
             Hbf).
  Qed.

  (* the aggregated MAPPED form: a mapped vpn yields all three walk reads
     (the conclusion is pure, so the invariant is only borrowed) *)
  Lemma upt_read_walk_ptes (pt : upt) (vpn : mword 27) (e : umap_ent) (σ : mstate) :
    pt.(u_map) !! vpn = Some e ->
    upt_map_spec pt ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_slots_own pt.(u_slots) -∗
    ⌜exec (read_pte (Physaddr (um_addr2 pt.(u_root) vpn)) 8) σ = Some (Ok (um_pte2 e), σ) /\
     exec (read_pte (Physaddr (um_addr1 e vpn)) 8) σ = Some (Ok (um_pte1 e), σ) /\
     exec (read_pte (Physaddr (um_addr0 e vpn)) 8) σ = Some (Ok (um_pte0 e), σ) /\
     umap_ent_wf e⌝.
  Proof.
    iIntros (Hvpn Hspec HA Hord HR Hcov Hpter) "#Hhw Hint Hslots".
    destruct (Hspec vpn e Hvpn) as (Hs2 & Hs1 & Hs0 & Hwf).
    (* each application borrows [Hint]/[Hslots] inside a pure iAssert, so
       the spatial context survives all three *)
    iAssert (⌜exec (read_pte (Physaddr (um_addr2 pt.(u_root) vpn)) 8) σ
               = Some (Ok (um_pte2 e), σ)⌝)%I as %Hr2.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw2 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw2"). }
    iAssert (⌜exec (read_pte (Physaddr (um_addr1 e vpn)) 8) σ
               = Some (Ok (um_pte1 e), σ)⌝)%I as %Hr1.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw1 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw1"). }
    iAssert (⌜exec (read_pte (Physaddr (um_addr0 e vpn)) 8) σ
               = Some (Ok (um_pte0 e), σ)⌝)%I as %Hr0.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs0 with "Hslots") as "[Hw0 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw0"). }
    iPureIntro. auto.
  Qed.

  (* the UNMAPPED form: the walk for an unmapped vpn stops at an invalid
     PTE, touching only owned slots and writing nothing.  Access-generic. *)
  Lemma upt_unmapped_walk_fault (pt : upt) (vpn : mword 27)
      (acc : MemoryAccessType mem_payload) (mxr do_sum : bool) (σ : mstate) :
    pt.(u_map) !! vpn = None ->
    upt_unmapped_spec pt ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_slots_own pt.(u_slots) -∗
    ⌜exec (pt_walk 39 vpn acc User mxr do_sum pt.(u_root) 2 false tt) σ
       = Some (Err (PTW_Invalid_PTE tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hfwf HA Hord HR Hcov Hpter) "#Hhw Hint Hslots".
    destruct (Hfwf vpn Hvpn) as
      [ (w2 & Hs2 & Hi2)
      | [ (w2 & w1 & Hs2 & Hv2 & Hn2 & Hs1 & Hi1)
        | (w2 & w1 & w0 & Hs2 & Hv2 & Hn2 & Hs1 & Hv1 & Hn1 & Hs0 & Hi0) ] ].
    - (* root invalid *)
      iAssert (⌜exec (read_pte (Physaddr (um_addr2 pt.(u_root) vpn)) 8) σ
                 = Some (Ok w2, σ)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro.
      exact (exec_pt_walk_user_l2_invalid vpn acc User mxr do_sum pt.(u_root) w2 σ Hr2 Hi2).
    - (* mid invalid *)
      iAssert (⌜exec (read_pte (Physaddr (um_addr2 pt.(u_root) vpn)) 8) σ
                 = Some (Ok w2, σ)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w2)
                        (subrange_vec_dec vpn 17 9))) 8) σ
                 = Some (Ok w1, σ)⌝)%I as %Hr1.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro.
      apply (exec_pt_walk_user_sub vpn acc User mxr do_sum pt.(u_root) w2 _ σ Hr2 Hv2 Hn2).
      intros g' a.
      exact (exec_rec_walk_l1_invalid vpn acc User mxr do_sum
               (u_next_base w2) w1 g' a σ Hr1 Hi1).
    - (* leaf invalid *)
      iAssert (⌜exec (read_pte (Physaddr (um_addr2 pt.(u_root) vpn)) 8) σ
                 = Some (Ok w2, σ)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w2)
                        (subrange_vec_dec vpn 17 9))) 8) σ
                 = Some (Ok w1, σ)⌝)%I as %Hr1.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w1)
                        (subrange_vec_dec vpn 8 0))) 8) σ
                 = Some (Ok w0, σ)⌝)%I as %Hr0.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs0 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro.
      apply (exec_pt_walk_user_sub vpn acc User mxr do_sum pt.(u_root) w2 _ σ Hr2 Hv2 Hn2).
      intros g' a.
      apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum
               (u_next_base w2) w1 g' _ a σ Hr1 Hv1 Hn1).
      intros g'' a0.
      exact (exec_rec_walk_leaf_invalid vpn acc User mxr do_sum
               (u_next_base w1) w0 g'' a0 σ Hr0 Hi0).
  Qed.

  (* the DENIED form: a MAPPED vpn whose leaf fails the permission check
     for this access (kernel page U=0, store to a read-only page, fetch
     from a non-executable page, ...).  The check hypothesis is supplied
     per access from the leaf's actual bits. *)
  Lemma upt_denied_walk_fault (pt : upt) (vpn : mword 27) (e : umap_ent)
      (acc : MemoryAccessType mem_payload) (mxr do_sum : bool) (σ : mstate) :
    pt.(u_map) !! vpn = Some e ->
    upt_map_spec pt ->
    upte_check_denied acc mxr do_sum (um_pte0 e) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_slots_own pt.(u_slots) -∗
    ⌜exec (pt_walk 39 vpn acc User mxr do_sum pt.(u_root) 2 false tt) σ
       = Some (Err (PTW_No_Permission tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hspec Hden HA Hord HR Hcov Hpter) "#Hhw Hint Hslots".
    iDestruct (upt_read_walk_ptes pt vpn e σ Hvpn Hspec HA Hord HR Hcov Hpter
                 with "Hhw Hint Hslots") as %(Hr2 & Hr1 & Hr0 & Hwf).
    iPureIntro.
    destruct Hwf as (Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hn0 & _).
    apply (exec_pt_walk_user_sub vpn acc User mxr do_sum pt.(u_root) (um_pte2 e) _ σ Hr2 Hv2 Hn2).
    intros g' a.
    apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum
             (u_next_base (um_pte2 e)) (um_pte1 e) g' _ a σ Hr1 Hv1 Hn1).
    intros g'' a0.
    exact (exec_rec_walk_leaf_noperm vpn acc User mxr do_sum
             (u_next_base (um_pte1 e)) (um_pte0 e) g'' (PTE_No_Permission tt) a0 σ
             Hr0 Hv0 Hn0 (fun s0 => Hden s0)).
  Qed.

End UserPtIris.
