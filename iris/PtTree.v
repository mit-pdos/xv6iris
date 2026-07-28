(* PtTree.v -- the GENERAL-PURPOSE page-table abstraction: an Iris
   ownership predicate over a recursive tree of page-table NODES, each
   claiming one page worth of entries (512 x 8-byte slots), with
   recursion down the hierarchy for every present child pointer.

   Motivation (see claude-notes/design/tlb-translation.md): the
   kernel S-mode invariant [tlb_inv] enumerates the kvmmake layout slot
   by slot with PRESET A/D bits, and the user page table (UserPt.v) is a
   separate ad-hoc {slots, map, data} record.  This file provides ONE
   abstraction serving both.

   Design (the iProp is the core; the pure side is deliberately shallow):

     - [ptree]        : an inert DESCRIPTION of a table: one node = its
                        page's base ppn, its 512 raw slot words, and a
                        subtree wherever the description claims a child.
                        The slot words are ARBITRARY -- in particular
                        the leaf A/D bits are "whatever happens to be in
                        the page-table page", as Svadu/ADUE requires.
     - [ptree_own]    : THE recursive definition: own every slot of the
                        node's page (whatever words the description
                        says) and, recursively, every described child.
                        Separation makes page/slot disjointness free,
                        lets a kernel build the table incrementally
                        (graft a subtree under one slot), and absorbs
                        the ADUE A/D write-back (the written slot is
                        owned here, so clients never see the change).
     - [ptree_maps] / [ptree_blocks] : SHALLOW (non-recursive) per-vpn
                        walk facts over the description -- the explicit
                        3-level path with the classification facts the
                        exec walk needs (valid pointers down to a valid
                        leaf / a stop at an invalid word).  There is no
                        recursive well-formedness predicate and no
                        recursive walk function: instances prove these
                        facts per vpn directly, and determinism is free
                        because a [ptree]'s slots are functions.
     - [pte_set_ad]   : the A/D-variance constructor (the EXACT update
                        shape [update_PTE_Bits] produces), used to state
                        "same mapping, arbitrary A/D" -- both for leaf
                        words in memory and for resident TLB entries
                        (which may hold a stale-A/D copy of a leaf).
     - [tlb_ok_pt]    : TLB consistency modulo A/D: every resident entry
                        is the walk entry of some vpn the tree maps,
                        with the leaf word an A/D variant of the tree's
                        current leaf word.
     - exec layer     : hypothesis-style (the abstract-word analogue of
                        Pt4kWalk's TrampTranslate, built on CommonWalk's
                        privilege/access-generic core) -- one success
                        translate for any mapped vpn, one fault
                        translate for any blocked vpn.  Tree-free: the
                        Iris layer extracts the per-slot facts from
                        [ptree_own] and instantiates.

   Instances: the kernel S-mode table (KptTree.v) and, eventually, the
   user table (UserPt.v -- worklist).                                    *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import WpDecodeBridge.
Require Import CommonWalk.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 PTE-word predicates: the shapes the walk lemmas consume, over a     *)
(*    fully abstract 64-bit slot word.  Same shapes as UserPt.v §1 but    *)
(*    PRIVILEGE-PARAMETRIC (the walk itself is privilege-generic; only    *)
(*    the leaf permission check mentions the privilege).                  *)
(* ===================================================================== *)

(* the word is a valid PTE (V=1, no reserved-encoding violation) *)
Definition pte_valid (w : mword 64) : Prop :=
  forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w)) s = Some (false, s).

(* the word is an invalid PTE: the walk stops here with PTW_Invalid_PTE *)
Definition pte_invalid (w : mword 64) : Prop :=
  forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w)) s = Some (true, s).

(* non-leaf (pointer to the next level) vs leaf *)
Definition pte_ptr (w : mword 64) : Prop :=
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = true.
Definition pte_leaf (w : mword 64) : Prop :=
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = false.

(* V and U both set -- the pair of bits [walkaddr] tests in one [andi]
   ([( *pte & (PTE_V|PTE_U)) == PTE_V|PTE_U]).  This is the verdict that
   makes a slot word a page the process may reach FROM USER MODE, and so
   -- for a table described by [UptTree.upt_tree_spec] -- the verdict that
   places its vpn in the user MAP rather than at the trampoline or the
   trapframe, whose leaves both have U = 0.  Stated over the model's flag
   accessors; the [andi] bit-test bridge is [ProofWalkaddr.wa_pte_vu_bits]
   (which belongs in PtBuild.v next to [pte_valid_bit0] -- see the cleanup
   sweep in claude-notes/projects/copy-inout.md). *)
Definition pte_vu (w : mword 64) : Prop :=
  _get_PTE_Flags_V (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = ('b"1" : mword 1) /\
  _get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = ('b"1" : mword 1).

(* leaf extras consumed by the success walk / TLB-hit path *)
Definition pte_no_napot (w : mword 64) : Prop :=
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE w)) ('b"1") = false.
Definition pte_pbmt0 (w : mword 64) : Prop :=
  _get_PTE_Ext_PBMT (ext_bits_of_PTE w) = ('b"00" : mword 2).

(* the per-access permission check on a leaf, at privilege [p].  With the
   leaf's R/W/X/U/A/D arbitrary, each access either passes or is denied --
   both are safe outcomes, dispatched per access by the instance. *)
Definition pte_check_ok (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr do_sum : bool) (w : mword 64) : Prop :=
  forall s, exec (check_PTE_permission acc p mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w) tt) s
            = Some (PTE_Check_Success tt, s).
Definition pte_check_denied (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr do_sum : bool) (f : pte_check_failure) (w : mword 64) : Prop :=
  forall s, exec (check_PTE_permission acc p mxr do_sum
                    (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                    (ext_bits_of_PTE w) tt) s
            = Some (PTE_Check_Failure (tt, f), s).

(* ===================================================================== *)
(* §2 The description.  One node = one PT page: its base ppn, its 512     *)
(*    raw slot words, and a subtree for every child the description       *)
(*    claims.  Purely inert data -- all meaning comes from [ptree_own]    *)
(*    (ownership) and [ptree_maps]/[ptree_blocks] (per-vpn walk facts).   *)
(* ===================================================================== *)

Inductive ptree : Type :=
  | PtNode (base : mword 44)
           (ents : mword 9 -> mword 64)
           (kids : mword 9 -> option ptree).

Definition pt_base (t : ptree) : mword 44 :=
  match t with PtNode b _ _ => b end.
Definition pt_ents (t : ptree) : mword 9 -> mword 64 :=
  match t with PtNode _ e _ => e end.
Definition pt_kids (t : ptree) : mword 9 -> option ptree :=
  match t with PtNode _ _ k => k end.

(* The identity vpn of a node page at ppn [b]: all 512 slots
   ([u_pte_addr b idx], idx*8 < 4096) sit in the SAME page, so share this
   vpn.  [node_kdata b]: that page lies wholly in RAM memory. *)
Definition pt_page_vpn (b : mword 44) : mword 27 :=
  svpn_of (u_pte_addr b (mword_of_int 0)).

(* the node page at ppn [b] lies wholly in RAM memory.  Implies VA
   canonicality of every slot ([b*4096+4096 <= ram_base+ram_size < 2^38]) --
   both pure facts [mem_pointsto] needs for the [↦ₚ₈ -> ↦₈] slot reconstruction. *)
Definition node_kdata (b : mword 44) : Prop :=
  (ram_base <= bv_unsigned b * 4096)%Z /\
  (bv_unsigned b * 4096 + 4096 <= ram_base + ram_size)%Z.

(* the 9-bit walk index a level-[lvl] node decodes from [vpn] (Sv39:
   levels 2,1,0 top-down) *)
Definition vpn_idx (lvl : nat) (vpn : mword 27) : mword 9 :=
  match lvl with
  | 2%nat => subrange_vec_dec vpn 26 18
  | 1%nat => subrange_vec_dec vpn 17 9
  | _     => subrange_vec_dec vpn 8 0
  end.

(* the three slot addresses [vpn]'s walk reads, spelled exactly as the
   walk computes them (CommonWalk's addr2/addr1/addr0) *)
Definition pt_addr2 (t : ptree) (vpn : mword 27) : mword 64 :=
  u_pte_addr (pt_base t) (vpn_idx 2 vpn).
Definition pt_addr1 (p2 : mword 64) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base p2) (vpn_idx 1 vpn).
Definition pt_addr0 (p1 : mword 64) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base p1) (vpn_idx 0 vpn).

(* ===================================================================== *)
(* §3 Per-vpn walk facts (SHALLOW: the explicit 3-level path).            *)
(* ===================================================================== *)

(* [t] 4K-maps [vpn] through pointer words p2, p1 to the leaf word p0:
   the description routes the walk through its own child nodes (whose
   pages are the ones the pointers name), and the words classify as the
   walk needs (valid pointers; a valid no-NAPOT pbmt-0 leaf).  The
   leaf's PERMISSION/A/D bits stay arbitrary -- each access dispatches
   on them separately ([pte_check_ok] / [update_PTE_Bits]).              *)
Definition ptree_maps (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) : Prop :=
  exists c1 c0,
    pt_kids t (vpn_idx 2 vpn) = Some c1 /\
    pt_kids c1 (vpn_idx 1 vpn) = Some c0 /\
    pt_ents t (vpn_idx 2 vpn) = p2 /\
    pt_ents c1 (vpn_idx 1 vpn) = p1 /\
    pt_ents c0 (vpn_idx 0 vpn) = p0 /\
    u_next_base p2 = pt_base c1 /\
    u_next_base p1 = pt_base c0 /\
    pte_valid p2 /\ pte_ptr p2 /\
    pte_valid p1 /\ pte_ptr p1 /\
    pte_valid p0 /\ pte_leaf p0 /\ pte_no_napot p0 /\ pte_pbmt0 p0.

(* the walk of [vpn] page-faults: it stops at an INVALID word at level
   2, 1 or 0 (after valid pointers above it).  A valid pointer-shaped
   word at level 0 also faults in the model; add that disjunct here if
   an instance ever needs it -- xv6 tables stop at zero words.           *)
Definition ptree_blocks (t : ptree) (vpn : mword 27) : Prop :=
  (* the root slot is invalid (no child claimed) *)
  (pt_kids t (vpn_idx 2 vpn) = None /\ pte_invalid (pt_ents t (vpn_idx 2 vpn)))
  (* the root descends; the mid slot is invalid *)
  \/ (exists c1,
        pt_kids t (vpn_idx 2 vpn) = Some c1 /\
        pt_kids c1 (vpn_idx 1 vpn) = None /\
        pte_valid (pt_ents t (vpn_idx 2 vpn)) /\
        pte_ptr (pt_ents t (vpn_idx 2 vpn)) /\
        u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 /\
        pte_invalid (pt_ents c1 (vpn_idx 1 vpn)))
  (* both levels descend; the leaf slot is invalid *)
  \/ (exists c1 c0,
        pt_kids t (vpn_idx 2 vpn) = Some c1 /\
        pt_kids c1 (vpn_idx 1 vpn) = Some c0 /\
        pte_valid (pt_ents t (vpn_idx 2 vpn)) /\
        pte_ptr (pt_ents t (vpn_idx 2 vpn)) /\
        pte_valid (pt_ents c1 (vpn_idx 1 vpn)) /\
        pte_ptr (pt_ents c1 (vpn_idx 1 vpn)) /\
        u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1 /\
        u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0 /\
        pte_invalid (pt_ents c0 (vpn_idx 0 vpn))).

(* determinism: the description's slots are functions, so the mapped
   path of a vpn is unique *)
Lemma ptree_maps_det (t : ptree) (vpn : mword 27) (p2 p1 p0 q2 q1 q0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> ptree_maps t vpn q2 q1 q0 ->
  p2 = q2 /\ p1 = q1 /\ p0 = q0.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & _)
         (d1 & d0 & Hk2' & Hk1' & He2' & He1' & He0' & _).
  assert (Hc1 : c1 = d1) by congruence. subst d1.
  assert (Hc0 : c0 = d0) by congruence. subst d0.
  repeat split; congruence.
Qed.

(* ===================================================================== *)
(* §4 A/D variance: [pte_set_ad w a d] (PtAdBits.v) rewrites the A/D flag  *)
(*    bits -- the EXACT update shape [update_PTE_Bits] produces on the    *)
(*    Svadu/ADUE write-back path, so <<w' is an A/D variant of w>> is     *)
(*    [exists a d, w' = pte_set_ad w a d].  The bit-level laws (refl /    *)
(*    absorb / PPN, ext, leafness stability) live in PtAdBits.v (iris-    *)
(*    free testbit dialect).                                              *)
(* ===================================================================== *)

(* [pte_valid] / [pte_invalid] are mutually exclusive (exec is a function;
   witnessed at the concrete bridge state) *)
Lemma pte_valid_invalid_excl (w : mword 64) :
  pte_valid w -> pte_invalid w -> False.
Proof.
  intros Hv Hi.
  specialize (Hv dstateM). specialize (Hi dstateM).
  rewrite Hv in Hi. discriminate.
Qed.

(* a vpn cannot both map and block: the description's slot and kid maps
   are functions, so the two walks agree down to the stopping word,
   which would have to be valid and invalid at once *)
Lemma ptree_maps_blocks_excl (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> ptree_blocks t vpn -> False.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
          Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & _)
         [ (Hk2n & _)
         | [ (c1' & Hk2' & Hk1n & _)
           | (c1' & c0' & Hk2' & Hk1' & _ & _ & _ & _ & _ & _ & Hinv0) ] ].
  - congruence.
  - assert (Hc : c1' = c1) by congruence. subst c1'. congruence.
  - assert (Hc : c1' = c1) by congruence. subst c1'.
    assert (Hc : c0' = c0) by congruence. subst c0'.
    rewrite He0 in Hinv0.
    exact (pte_valid_invalid_excl p0 Hv0 Hinv0).
Qed.

(* ===================================================================== *)
(* §5 The leaf write-back on the description side: [ptree_set_leaf]       *)
(*    replaces the LEAF word on [vpn]'s path (what the ADUE write-back    *)
(*    does to memory), shallowly (fixed 3-level depth, no recursion).     *)
(* ===================================================================== *)

Definition pt_upd_ent (t : ptree) (i : mword 9) (w : mword 64) : ptree :=
  PtNode (pt_base t)
         (fun j => if decide (j = i) then w else pt_ents t j)
         (pt_kids t).
Definition pt_upd_kid (t : ptree) (i : mword 9) (c : option ptree) : ptree :=
  PtNode (pt_base t) (pt_ents t)
         (fun j => if decide (j = i) then c else pt_kids t j).

Definition ptree_set_leaf (t : ptree) (vpn : mword 27) (w : mword 64) : ptree :=
  match pt_kids t (vpn_idx 2 vpn) with
  | Some c1 =>
      match pt_kids c1 (vpn_idx 1 vpn) with
      | Some c0 =>
          pt_upd_kid t (vpn_idx 2 vpn)
            (Some (pt_upd_kid c1 (vpn_idx 1 vpn)
                     (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))))
      | None => t
      end
  | None => t
  end.

(* ---- vpn chunk arithmetic: the three 9-bit indices determine the vpn   *)
(*      (27-bit clones of KptPt's subrange facts).                        *)

Lemma pt_sub27_26_18 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 26 18) = (bv_unsigned x ≫ 18) `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 18)) with 18.
  change (MachineWord.MachineWord.Z_idx (26 - 18 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma pt_sub27_17_9 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 17 9) = (bv_unsigned x ≫ 9) `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 9)) with 9.
  change (MachineWord.MachineWord.Z_idx (17 - 9 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma pt_sub27_8_0 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 8 0) = bv_unsigned x `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (8 - 0 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma vpn_idx_inj (x y : mword 27) :
  vpn_idx 2 x = vpn_idx 2 y -> vpn_idx 1 x = vpn_idx 1 y ->
  vpn_idx 0 x = vpn_idx 0 y -> x = y.
Proof.
  cbn [vpn_idx]. intros H2 H1 H0.
  apply (f_equal bv_unsigned) in H2. apply (f_equal bv_unsigned) in H1.
  apply (f_equal bv_unsigned) in H0.
  rewrite !pt_sub27_26_18 in H2. rewrite !pt_sub27_17_9 in H1.
  rewrite !pt_sub27_8_0 in H0.
  apply bv_eq.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  pose proof (bv_unsigned_in_range _ y) as Hy.
  assert (Hm27 : bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728)
    by (vm_compute; reflexivity).
  rewrite Hm27 in Hx, Hy.
  set (ux := bv_unsigned x) in *. set (uy := bv_unsigned y) in *.
  rewrite !Z.shiftr_div_pow2 in H2; [| lia | lia].
  rewrite !Z.shiftr_div_pow2 in H1; [| lia | lia].
  change (2 ^ 9) with 512 in *. change (2 ^ 18) with 262144 in *.
  assert (Hx2 : ux / 262144 < 512) by (apply Z.div_lt_upper_bound; lia).
  assert (Hy2 : uy / 262144 < 512) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (ux / 262144) 512) in H2;
    [| split; [apply Z.div_pos; lia | exact Hx2]].
  rewrite (Z.mod_small (uy / 262144) 512) in H2;
    [| split; [apply Z.div_pos; lia | exact Hy2]].
  pose proof (Z.div_mod ux 512 ltac:(lia)) as Dx0.
  pose proof (Z.div_mod uy 512 ltac:(lia)) as Dy0.
  pose proof (Z.div_mod (ux / 512) 512 ltac:(lia)) as Dx1.
  pose proof (Z.div_mod (uy / 512) 512 ltac:(lia)) as Dy1.
  rewrite (Z.div_div ux 512 512 ltac:(lia) ltac:(lia)) in Dx1.
  rewrite (Z.div_div uy 512 512 ltac:(lia) ltac:(lia)) in Dy1.
  change (512 * 512) with 262144 in Dx1, Dy1.
  lia.
Qed.

(* contrapositive form: two distinct vpns differ in some chunk *)

(* ---- projection laws of the two updates ----------------------------- *)

Lemma pt_upd_ent_base (t : ptree) (i : mword 9) (w : mword 64) :
  pt_base (pt_upd_ent t i w) = pt_base t.
Proof. reflexivity. Qed.
Lemma pt_upd_ent_kids (t : ptree) (i : mword 9) (w : mword 64) (j : mword 9) :
  pt_kids (pt_upd_ent t i w) j = pt_kids t j.
Proof. reflexivity. Qed.
Lemma pt_upd_ent_same (t : ptree) (i : mword 9) (w : mword 64) :
  pt_ents (pt_upd_ent t i w) i = w.
Proof. cbn. case_decide; [reflexivity | contradiction]. Qed.
Lemma pt_upd_ent_other (t : ptree) (i : mword 9) (w : mword 64) (j : mword 9) :
  j <> i -> pt_ents (pt_upd_ent t i w) j = pt_ents t j.
Proof. intros Hne. cbn. case_decide; [contradiction | reflexivity]. Qed.

Lemma pt_upd_kid_base (t : ptree) (i : mword 9) (c : option ptree) :
  pt_base (pt_upd_kid t i c) = pt_base t.
Proof. reflexivity. Qed.
Lemma pt_upd_kid_ents (t : ptree) (i : mword 9) (c : option ptree) (j : mword 9) :
  pt_ents (pt_upd_kid t i c) j = pt_ents t j.
Proof. reflexivity. Qed.
Lemma pt_upd_kid_same (t : ptree) (i : mword 9) (c : option ptree) :
  pt_kids (pt_upd_kid t i c) i = c.
Proof. cbn. case_decide; [reflexivity | contradiction]. Qed.
Lemma pt_upd_kid_other (t : ptree) (i : mword 9) (c : option ptree) (j : mword 9) :
  j <> i -> pt_kids (pt_upd_kid t i c) j = pt_kids t j.
Proof. intros Hne. cbn. case_decide; [contradiction | reflexivity]. Qed.

(* ---- stability of the walk facts under the leaf write-back ---------- *)

(* the written vpn maps to the new word (which must still be a valid
   4K leaf -- true of every [pte_set_ad] variant of a valid leaf, cf.
   the A/D write-back lemmas) *)
Lemma ptree_set_leaf_maps_self (t : ptree) (vpn : mword 27) (p2 p1 p0 w : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  pte_valid w -> pte_leaf w -> pte_no_napot w -> pte_pbmt0 w ->
  ptree_maps (ptree_set_leaf t vpn w) vpn p2 p1 w.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
          Hv2 & Hn2 & Hv1 & Hn1 & _ & _ & _ & _) Hv Hl Hnap Hpb.
  unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
  exists (pt_upd_kid c1 (vpn_idx 1 vpn)
            (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))),
         (pt_upd_ent c0 (vpn_idx 0 vpn) w).
  rewrite !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
          !pt_upd_ent_base !pt_upd_ent_same.
  repeat split; try reflexivity; assumption.
Qed.

(* every OTHER vpn's mapping is untouched *)
Lemma ptree_set_leaf_maps_other (t : ptree) (vpn vpn' : mword 27)
    (q2 q1 q0 w : mword 64) :
  vpn' <> vpn ->
  ptree_maps t vpn' q2 q1 q0 ->
  ptree_maps (ptree_set_leaf t vpn w) vpn' q2 q1 q0.
Proof.
  intros Hne (d1 & d0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
              Hv2 & Hp2 & Hv1 & Hp1 & Hv0 & Hl0 & Hnap & Hpb).
  unfold ptree_set_leaf.
  destruct (pt_kids t (vpn_idx 2 vpn)) as [c1|] eqn:Hc2;
    [| exists d1, d0; repeat split; assumption].
  destruct (pt_kids c1 (vpn_idx 1 vpn)) as [c0|] eqn:Hc1;
    [| exists d1, d0; repeat split; assumption].
  destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
  2:{ (* different root slot: everything below is the old subtree *)
    exists d1, d0.
    rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
    repeat split; assumption. }
  (* same root slot: vpn' routes through the rebuilt c1 *)
  rewrite Ei2 in Hk2. rewrite Ei2 in He2.
  assert (Hd1 : d1 = c1) by congruence. subst d1.
  destruct (decide (vpn_idx 1 vpn' = vpn_idx 1 vpn)) as [Ei1|Ei1].
  2:{ exists (pt_upd_kid c1 (vpn_idx 1 vpn)
                (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))), d0.
    rewrite Ei2 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
      (pt_upd_kid_other _ _ _ _ Ei1).
    repeat split; try reflexivity; assumption. }
  (* same root and mid slot: vpn' routes into the rebuilt c0; its leaf
     index must differ (else vpn' = vpn) *)
  rewrite Ei1 in Hk1. rewrite Ei1 in He1.
  assert (Hd0 : d0 = c0) by congruence. subst d0.
  destruct (decide (vpn_idx 0 vpn' = vpn_idx 0 vpn)) as [Ei0|Ei0].
  { exfalso. apply Hne. apply vpn_idx_inj; assumption. }
  exists (pt_upd_kid c1 (vpn_idx 1 vpn)
            (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))),
         (pt_upd_ent c0 (vpn_idx 0 vpn) w).
  rewrite Ei2 Ei1 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
    !pt_upd_ent_base (pt_upd_ent_other _ _ _ _ Ei0).
  repeat split; try reflexivity; assumption.
Qed.

(* every blocked vpn stays blocked (the write-back targets a MAPPED
   vpn's leaf slot, which no blocked vpn's walk reads) *)
Lemma ptree_set_leaf_blocks (t : ptree) (vpn vpn' : mword 27)
    (p2 p1 p0 w : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  ptree_blocks t vpn' ->
  ptree_blocks (ptree_set_leaf t vpn w) vpn'.
Proof.
  intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 &
          Hv2 & Hp2 & Hv1 & Hp1 & Hv0 & Hl0 & Hnap & Hpb) Hbl.
  unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
  destruct Hbl as [ (Hn2 & Hi2)
                  | [ (d1 & Hd2 & Hd1 & Hv2' & Hp2' & Hb1' & Hi1')
                    | (d1 & d0 & Hd2 & Hd1 & Hv2' & Hp2' & Hv1' & Hp1' &
                       Hb1' & Hb0' & Hi0') ] ].
  - (* blocked at root: the root slot of vpn' is kid-free, so it is not
       vpn's root slot *)
    left.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    { exfalso. rewrite Ei2 in Hn2. congruence. }
    rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
    split; assumption.
  - (* blocked at mid level *)
    right. left.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    2:{ exists d1.
        rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
        repeat split; assumption. }
    rewrite Ei2 in Hd2. rewrite Ei2 in Hv2'. rewrite Ei2 in Hp2'.
    rewrite Ei2 in Hb1'.
    assert (Hd1c : d1 = c1) by congruence. subst d1.
    destruct (decide (vpn_idx 1 vpn' = vpn_idx 1 vpn)) as [Ei1|Ei1].
    { exfalso. rewrite Ei1 in Hd1. congruence. }
    exists (pt_upd_kid c1 (vpn_idx 1 vpn)
              (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))).
    rewrite Ei2 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
      (pt_upd_kid_other _ _ _ _ Ei1).
    repeat split; try reflexivity; assumption.
  - (* blocked at the leaf level: the stop word is INVALID, so its slot
       is not vpn's (whose leaf word is a VALID leaf) *)
    right. right.
    destruct (decide (vpn_idx 2 vpn' = vpn_idx 2 vpn)) as [Ei2|Ei2].
    2:{ exists d1, d0.
        rewrite (pt_upd_kid_other _ _ _ _ Ei2) !pt_upd_kid_ents.
        repeat split; assumption. }
    rewrite Ei2 in Hd2. rewrite Ei2 in Hv2'. rewrite Ei2 in Hp2'.
    rewrite Ei2 in Hb1'.
    assert (Hd1c : d1 = c1) by congruence. subst d1.
    destruct (decide (vpn_idx 1 vpn' = vpn_idx 1 vpn)) as [Ei1|Ei1].
    2:{ exists (pt_upd_kid c1 (vpn_idx 1 vpn)
                  (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))), d0.
        rewrite Ei2 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
          (pt_upd_kid_other _ _ _ _ Ei1).
        repeat split; try reflexivity; assumption. }
    rewrite Ei1 in Hd1. rewrite Ei1 in Hv1'. rewrite Ei1 in Hp1'.
    rewrite Ei1 in Hb0'.
    assert (Hd0c : d0 = c0) by congruence. subst d0.
    destruct (decide (vpn_idx 0 vpn' = vpn_idx 0 vpn)) as [Ei0|Ei0].
    { exfalso. rewrite Ei0 in Hi0'. rewrite He0 in Hi0'.
      exact (pte_valid_invalid_excl p0 Hv0 Hi0'). }
    exists (pt_upd_kid c1 (vpn_idx 1 vpn)
              (Some (pt_upd_ent c0 (vpn_idx 0 vpn) w))),
           (pt_upd_ent c0 (vpn_idx 0 vpn) w).
    rewrite Ei2 Ei1 !pt_upd_kid_same !pt_upd_kid_ents !pt_upd_kid_base
      !pt_upd_ent_base (pt_upd_ent_other _ _ _ _ Ei0).
    repeat split; try reflexivity; assumption.
Qed.

(* the pure per-slot memory facts the exec walk consumes: the slot's 8
   bytes present in the state's heap, both ends in RAM, 8-byte aligned *)
Definition pt_slot_mem (sg : mstate) (a : Arch.pa) (w : mword 64) : Prop :=
  (forall j : nat, (N.of_nat j < 8)%N ->
     sg.(mem) !! pa_add a j = Some (nth_byte w j)) /\
  addr_is_ram a /\ addr_is_ram (pa_add a 7) /\
  is_aligned_paddr (Physaddr a) 8 = true.

Lemma addr_is_ram_pa0 (a : Arch.pa) : addr_is_ram (pa_add a 0) -> addr_is_ram a.
Proof.
  unfold addr_is_ram. intros H.
  assert (Hnw : (uint a + Z.of_nat 0 < 18446744073709551616)%Z).
  { rewrite uint_unsigned. change (Z.of_nat 0) with 0%Z.
    pose proof (bv_unsigned_in_range _ a) as Hr.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
      by (vm_compute; reflexivity).
    rewrite Hm in Hr. rewrite Z.add_0_r. exact (proj2 Hr). }
  rewrite (uint_pa_add a 0 Hnw) in H. rewrite Z.add_0_r in H. exact H.
Qed.

(* ===================================================================== *)
(* §6 THE OWNERSHIP CORE.  One recursive definition: own every slot of    *)
(*    the node's page (whatever words the description says), and every    *)
(*    described child.  Everything else about a table is derived by       *)
(*    peeling this against a [ptree_maps]/[ptree_blocks] fact.            *)
(* ===================================================================== *)

(* mword_of_int round-trips on 9-bit values *)
Lemma pt_mword9_id (x : mword 9) : mword_of_int (bv_unsigned x) = x.
Proof.
  apply bv_eq.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pt_mword9_unsigned (i : Z) :
  0 <= i < 512 -> bv_unsigned (mword_of_int i : mword 9) = i.
Proof.
  intros Hi.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  apply bv_wrap_small.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
    by (vm_compute; reflexivity).
  rewrite Hm. exact Hi.
Qed.

Section PtTreeIris.
  Context `{!riscvGS Σ}.

  (* PERSISTENT per-node identity claim (uniform-claims PHYSICAL TIER): the
     node page's vpn maps to its own ppn at KP_rw in the kernel map, and the
     page is kdata.  Carried inside [pt_page_own] so a software walk can turn a
     physical slot [↦ₚ₈] into a VA-tier [↦₈] (reconstruct [mem_pointsto]) with
     NOTHING but the tree itself -- [kmap_at] supplies the mapping, [node_kdata]
     the [addr_is_ram] + canonicality conjuncts [mem_pointsto] carries. *)
  Definition pt_node_claim (b : mword 44) : iProp Σ :=
    (⌜node_kdata b⌝ ∗ kmap_at (pt_page_vpn b) b KP_rw)%I.

  Global Instance pt_node_claim_persistent b : Persistent (pt_node_claim b).
  Proof. rewrite /pt_node_claim. apply _. Qed.

  (* one node's page: the identity claim, plus all 512 slots (whatever words
     the description says). *)
  Definition pt_page_own (dq : dfrac) (t : ptree) : iProp Σ :=
    (pt_node_claim (pt_base t) ∗
     [∗ list] i ∈ seqZ 0 512,
       u_pte_addr (pt_base t) (mword_of_int i) ↦ₚ₈{dq} pt_ents t (mword_of_int i))%I.

  Fixpoint ptree_own (lvl : nat) (dq : dfrac) (t : ptree) {struct lvl} : iProp Σ :=
    (pt_page_own dq t ∗
     match lvl with
     | O => emp
     | S lvl' =>
         [∗ list] i ∈ seqZ 0 512,
           match pt_kids t (mword_of_int i) with
           | Some c => ptree_own lvl' dq c
           | None => emp
           end
     end)%I.

  (* the children conjunct, as a named definition for the accessor lemmas *)
  Definition pt_kids_own (lvl : nat) (dq : dfrac) (t : ptree) : iProp Σ :=
    ([∗ list] i ∈ seqZ 0 512,
       match pt_kids t (mword_of_int i) with
       | Some c => ptree_own lvl dq c
       | None => emp
       end)%I.

  Lemma ptree_own_S (lvl : nat) (dq : dfrac) (t : ptree) :
    ptree_own (S lvl) dq t ⊣⊢ pt_page_own dq t ∗ pt_kids_own lvl dq t.
  Proof. reflexivity. Qed.

  (* ---- single-node slot accessor (update form) ---------------------- *)
  Lemma pt_page_own_acc (dq : dfrac) (t : ptree) (i : mword 9) :
    pt_page_own dq t ⊢
      u_pte_addr (pt_base t) i ↦ₚ₈{dq} pt_ents t i ∗
      (∀ w' : mword 64,
         u_pte_addr (pt_base t) i ↦ₚ₈{dq} w' -∗
         pt_page_own dq (pt_upd_ent t i w')).
  Proof.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hpg".
    iEval (rewrite /pt_page_own) in "Hpg".
    iDestruct "Hpg" as "[#Hcl Hpg]".
    iEval (rewrite (big_sepL_delete _ _ _ _ Hlk)) in "Hpg".
    iDestruct "Hpg" as "[Hslot Hrest]".
    iEval (rewrite pt_mword9_id) in "Hslot".
    iFrame "Hslot".
    iIntros (w') "Hslot".
    rewrite /pt_page_own.
    iSplitR; [rewrite pt_upd_ent_base; iExact "Hcl" |].
    rewrite (big_sepL_delete
               (fun _ j => (u_pte_addr (pt_base (pt_upd_ent t i w')) (mword_of_int j)
                            ↦ₚ₈{dq} pt_ents (pt_upd_ent t i w') (mword_of_int j))%I)
               _ _ _ Hlk).
    iSplitL "Hslot".
    { rewrite pt_mword9_id pt_upd_ent_base pt_upd_ent_same. iExact "Hslot". }
    iApply (big_sepL_mono with "Hrest").
    intros k j Hkj. cbn beta.
    case_decide as Hk; [reflexivity |].
    rewrite pt_upd_ent_base.
    rewrite pt_upd_ent_other; [reflexivity |].
    (* mword_of_int j <> i since j <> bv_unsigned i and j in [0,512) *)
    apply lookup_seqZ in Hkj. destruct Hkj as [-> Hjlt].
    intros Heq. apply Hk.
    apply (f_equal bv_unsigned) in Heq.
    rewrite pt_mword9_unsigned in Heq; [| lia].
    lia.
  Qed.

  (* read-only form: restore the SAME description *)
  Lemma pt_page_own_acc_ro (dq : dfrac) (t : ptree) (i : mword 9) :
    pt_page_own dq t ⊢
      u_pte_addr (pt_base t) i ↦ₚ₈{dq} pt_ents t i ∗
      (u_pte_addr (pt_base t) i ↦ₚ₈{dq} pt_ents t i -∗ pt_page_own dq t).
  Proof.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hpg".
    iEval (rewrite /pt_page_own) in "Hpg".
    iDestruct "Hpg" as "[#Hcl Hpg]".
    iDestruct (big_sepL_lookup_acc _ _ _ _ Hlk with "Hpg") as "[Hslot Hrest]".
    iEval (rewrite pt_mword9_id) in "Hslot".
    iFrame "Hslot".
    iIntros "Hslot".
    rewrite /pt_page_own. iFrame "Hcl".
    iApply "Hrest". iEval (rewrite pt_mword9_id). iExact "Hslot".
  Qed.

  (* ---- single-node child accessor (update form) --------------------- *)
  Lemma pt_kids_own_acc (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) (c : ptree) :
    pt_kids t i = Some c ->
    pt_kids_own lvl dq t ⊢
      ptree_own lvl dq c ∗
      (∀ c' : ptree,
         ptree_own lvl dq c' -∗
         pt_kids_own lvl dq (pt_upd_kid t i (Some c'))).
  Proof.
    intros Hk.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hks".
    iEval (rewrite /pt_kids_own (big_sepL_delete _ _ _ _ Hlk)) in "Hks".
    iDestruct "Hks" as "[Hc Hrest]".
    iEval (rewrite pt_mword9_id Hk) in "Hc".
    iFrame "Hc".
    iIntros (c') "Hc".
    rewrite /pt_kids_own.
    rewrite (big_sepL_delete
               (fun _ j => (match pt_kids (pt_upd_kid t i (Some c')) (mword_of_int j) with
                            | Some cc => ptree_own lvl dq cc
                            | None => emp end)%I)
               _ _ _ Hlk).
    iSplitL "Hc".
    { rewrite pt_mword9_id pt_upd_kid_same. iExact "Hc". }
    iApply (big_sepL_mono with "Hrest").
    intros k j Hkj. cbn beta.
    case_decide as Hkk; [reflexivity |].
    rewrite pt_upd_kid_other; [reflexivity |].
    apply lookup_seqZ in Hkj. destruct Hkj as [-> Hjlt].
    intros Heq. apply Hkk.
    apply (f_equal bv_unsigned) in Heq.
    rewrite pt_mword9_unsigned in Heq; [| lia].
    lia.
  Qed.

  (* read-only child accessor *)
  Lemma pt_kids_own_acc_ro (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) (c : ptree) :
    pt_kids t i = Some c ->
    pt_kids_own lvl dq t ⊢
      ptree_own lvl dq c ∗ (ptree_own lvl dq c -∗ pt_kids_own lvl dq t).
  Proof.
    intros Hk.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hks".
    iEval (rewrite /pt_kids_own) in "Hks".
    iDestruct (big_sepL_lookup_acc _ _ _ _ Hlk with "Hks") as "[Hc Hrest]".
    iEval (rewrite pt_mword9_id Hk) in "Hc".
    iFrame "Hc".
    iIntros "Hc".
    iApply "Hrest". iEval (rewrite pt_mword9_id Hk). iExact "Hc".
  Qed.

  (* ---- THE path accessors: peel the three slots a mapped vpn's walk   *)
  (*      reads.  Read-only form (restore the same tree), and the write- *)
  (*      back form (restore [ptree_set_leaf] with any new leaf word).   *)
  Lemma ptree_own_path_ro (dq : dfrac) (t : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) :
    ptree_maps t vpn p2 p1 p0 ->
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦ₚ₈{dq} p2 ∗
      pt_addr1 p2 vpn ↦ₚ₈{dq} p1 ∗
      pt_addr0 p1 vpn ↦ₚ₈{dq} p0 ∗
      (pt_addr2 t vpn ↦ₚ₈{dq} p2 -∗
       pt_addr1 p2 vpn ↦ₚ₈{dq} p1 -∗
       pt_addr0 p1 vpn ↦ₚ₈{dq} p0 -∗
       ptree_own 2 dq t).
  Proof.
    intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & _).
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 Hpg]".
    rewrite He2.
    iDestruct (pt_kids_own_acc_ro 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_page_own_acc_ro dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 Hpg1]".
    rewrite He1.
    iDestruct (pt_kids_own_acc_ro 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1") as "[Hc0 Hks1]".
    iDestruct "Hc0" as "[Hpg0 Hemp]".
    iDestruct (pt_page_own_acc_ro dq c0 (vpn_idx 0 vpn) with "Hpg0") as "[Hs0 Hpg0]".
    rewrite He0.
    unfold pt_addr2, pt_addr1, pt_addr0.
    rewrite Hb1. rewrite Hb0.
    iFrame "Hs2 Hs1 Hs0".
    iIntros "Hs2 Hs1 Hs0".
    iSplitL "Hpg Hs2".
    { iApply "Hpg". iExact "Hs2". }
    iApply "Hks". iSplitL "Hpg1 Hs1".
    { iApply "Hpg1". iExact "Hs1". }
    iApply "Hks1". iSplitL "Hpg0 Hs0".
    { iApply "Hpg0". iExact "Hs0". }
    iExact "Hemp".
  Qed.

  Lemma ptree_own_path_upd (dq : dfrac) (t : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) :
    ptree_maps t vpn p2 p1 p0 ->
    ptree_own 2 dq t ⊢
      pt_addr2 t vpn ↦ₚ₈{dq} p2 ∗
      pt_addr1 p2 vpn ↦ₚ₈{dq} p1 ∗
      pt_addr0 p1 vpn ↦ₚ₈{dq} p0 ∗
      (∀ w' : mword 64,
         pt_addr2 t vpn ↦ₚ₈{dq} p2 -∗
         pt_addr1 p2 vpn ↦ₚ₈{dq} p1 -∗
         pt_addr0 p1 vpn ↦ₚ₈{dq} w' -∗
         ptree_own 2 dq (ptree_set_leaf t vpn w')).
  Proof.
    intros (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hb1 & Hb0 & _).
    iIntros "[Hpg Hks]".
    iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 Hpg]".
    rewrite He2.
    iDestruct (pt_kids_own_acc 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks") as "[Hc1 Hks]".
    iDestruct "Hc1" as "[Hpg1 Hks1]".
    iDestruct (pt_page_own_acc_ro dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 Hpg1]".
    rewrite He1.
    iDestruct (pt_kids_own_acc 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1") as "[Hc0 Hks1]".
    iDestruct "Hc0" as "[Hpg0 Hemp]".
    iDestruct (pt_page_own_acc dq c0 (vpn_idx 0 vpn) with "Hpg0") as "[Hs0 Hpg0]".
    rewrite He0.
    unfold pt_addr2, pt_addr1, pt_addr0.
    rewrite Hb1. rewrite Hb0.
    iFrame "Hs2 Hs1 Hs0".
    iIntros (w') "Hs2 Hs1 Hs0".
    unfold ptree_set_leaf. rewrite Hk2. rewrite Hk1.
    rewrite ptree_own_S.
    iSplitL "Hpg Hs2".
    { iApply "Hpg". iExact "Hs2". }
    iApply "Hks".
    rewrite ptree_own_S.
    iSplitL "Hpg1 Hs1".
    { iApply "Hpg1". iExact "Hs1". }
    iApply "Hks1".
    iSplitL "Hpg0 Hs0".
    { iApply "Hpg0". iExact "Hs0". }
    iExact "Hemp".
  Qed.


  (* ---- pure per-slot memory facts, extracted from ownership --------- *)

  Lemma slot_mem_of_own (sg : mstate) (a : Arch.pa) (dq : dfrac) (w : mword 64) :
    gen_heap_interp sg.(mem) -∗ a ↦ₚ₈{dq} w -∗ ⌜pt_slot_mem sg a w⌝.
  Proof.
    iIntros "Hm Hw".
    iDestruct (phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               sg.(mem) !! pa_add a j = Some (nth_byte w j)⌝)%I as %Hbytes.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hb") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (phys_valid with "Hm Hbj"). }
    iAssert (⌜addr_is_ram (pa_add a 0)⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (phys_ram with "Hb0"). }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hb") as "Hb7";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (phys_ram with "Hb7"). }
    iPureIntro.
    split; [exact Hbytes|].
    split; [exact (addr_is_ram_pa0 a Hr0)|].
    split; [exact Hr7 | exact Hal].
  Qed.

  (* the three slots of a mapped vpn's path, as pure memory facts (one
     extraction per step; every walk of that step consumes them) *)
  Lemma ptree_own_path_mem (sg : mstate) (dq : dfrac) (t : ptree)
      (vpn : mword 27) (p2 p1 p0 : mword 64) :
    ptree_maps t vpn p2 p1 p0 ->
    gen_heap_interp sg.(mem) -∗ ptree_own 2 dq t -∗
    ⌜(pt_slot_mem sg (pt_addr2 t vpn) p2 /\
      pt_slot_mem sg (pt_addr1 p2 vpn) p1 /\
      pt_slot_mem sg (pt_addr0 p1 vpn) p0)%type⌝.
  Proof.
    intros Hmaps.
    iIntros "Hm Ht".
    iDestruct (ptree_own_path_ro dq t vpn p2 p1 p0 Hmaps with "Ht")
      as "(Hs2 & Hs1 & Hs0 & _)".
    iDestruct (slot_mem_of_own with "Hm Hs2") as %H2.
    iDestruct (slot_mem_of_own with "Hm Hs1") as %H1.
    iDestruct (slot_mem_of_own with "Hm Hs0") as %H0.
    iPureIntro. auto.
  Qed.

  (* the stopping prefix of a BLOCKED vpn's walk, as pure memory facts:
     the walk reads owned slots down to the invalid word *)
  Lemma ptree_own_blocked_mem (sg : mstate) (dq : dfrac) (t : ptree)
      (vpn : mword 27) :
    ptree_blocks t vpn ->
    gen_heap_interp sg.(mem) -∗ ptree_own 2 dq t -∗
    ⌜ ((exists w2, pt_slot_mem sg (pt_addr2 t vpn) w2 /\ pte_invalid w2)
       \/ (exists p2 w1,
             pt_slot_mem sg (pt_addr2 t vpn) p2 /\ pte_valid p2 /\ pte_ptr p2 /\
             pt_slot_mem sg (pt_addr1 p2 vpn) w1 /\ pte_invalid w1)
       \/ (exists p2 p1 w0,
             pt_slot_mem sg (pt_addr2 t vpn) p2 /\ pte_valid p2 /\ pte_ptr p2 /\
             pt_slot_mem sg (pt_addr1 p2 vpn) p1 /\ pte_valid p1 /\ pte_ptr p1 /\
             pt_slot_mem sg (pt_addr0 p1 vpn) w0 /\ pte_invalid w0))%type ⌝.
  Proof.
    intros Hblk.
    iIntros "Hm [Hpg Hks]".
    destruct Hblk as
      [ (Hk2 & Hinv2)
      | [ (c1 & Hk2 & Hk1 & Hv2 & Hn2 & Hb1 & Hinv1)
        | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hn2 & Hv1 & Hn1 & Hb1 & Hb0 & Hinv0) ] ].
    - iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 _]".
      iDestruct (slot_mem_of_own with "Hm Hs2") as %H2.
      iPureIntro. left. eexists. exact (conj H2 Hinv2).
    - iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 _]".
      iDestruct (slot_mem_of_own with "Hm Hs2") as %H2.
      iDestruct (pt_kids_own_acc_ro 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks")
        as "[[Hpg1 _] _]".
      iDestruct (pt_page_own_acc_ro dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 _]".
      iDestruct (slot_mem_of_own with "Hm Hs1") as %H1.
      iPureIntro. right; left.
      exists (pt_ents t (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)).
      split; [exact H2 |]. split; [exact Hv2 |]. split; [exact Hn2 |].
      split; [| exact Hinv1].
      unfold pt_addr1. rewrite Hb1. exact H1.
    - iDestruct (pt_page_own_acc_ro dq t (vpn_idx 2 vpn) with "Hpg") as "[Hs2 _]".
      iDestruct (slot_mem_of_own with "Hm Hs2") as %H2.
      iDestruct (pt_kids_own_acc_ro 1 dq t (vpn_idx 2 vpn) c1 Hk2 with "Hks")
        as "[[Hpg1 Hks1] _]".
      iDestruct (pt_page_own_acc_ro dq c1 (vpn_idx 1 vpn) with "Hpg1") as "[Hs1 _]".
      iDestruct (slot_mem_of_own with "Hm Hs1") as %H1.
      iDestruct (pt_kids_own_acc_ro 0 dq c1 (vpn_idx 1 vpn) c0 Hk1 with "Hks1")
        as "[[Hpg0 _] _]".
      iDestruct (pt_page_own_acc_ro dq c0 (vpn_idx 0 vpn) with "Hpg0") as "[Hs0 _]".
      iDestruct (slot_mem_of_own with "Hm Hs0") as %H0.
      iPureIntro. right; right.
      exists (pt_ents t (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)),
             (pt_ents c0 (vpn_idx 0 vpn)).
      split; [exact H2 |]. split; [exact Hv2 |]. split; [exact Hn2 |].
      split; [unfold pt_addr1; rewrite Hb1; exact H1 |].
      split; [exact Hv1 |]. split; [exact Hn1 |].
      split; [unfold pt_addr0; rewrite Hb0; exact H0 | exact Hinv0].
  Qed.

  (* ---- a PARKED page table: full ownership of a spec-constrained tree
     that is not currently installed in satp.  The satp-switch lemmas
     convert between an installed table's invariant and this frame.     *)
  Definition pt_frame (S : ptree -> Prop) : iProp Σ :=
    (∃ t : ptree, ⌜ S t ⌝ ∗ ptree_own 2 (DfracOwn 1) t)%I.

End PtTreeIris.

(* ===================================================================== *)
(* §7 TLB consistency MODULO A/D.  Every resident TLB entry is the walk   *)
(*    entry of some vpn the tree maps, with the leaf word an A/D VARIANT  *)
(*    of the tree's current leaf word: entries may be stale in A/D only   *)
(*    (an ADUE write-back refreshes memory and the touched entry, but     *)
(*    other cached copies keep the old bits).  Quantified through the     *)
(*    hash so the fill lemma needs no hash injectivity (upt_tlb_ok's      *)
(*    shape).                                                             *)
(* ===================================================================== *)

(* the cache-provenance relation: [ent] is a legal resident of slot
   [tlb_hash vpn'] with respect to tree [t] -- the walk entry of some
   vpn [t] maps with the same hash, modulo A/D staleness of the leaf *)
Definition tlb_cache_of (asid : mword 16) (t : ptree)
    (vpn' : mword 27) (ent : TLB_Entry) : Prop :=
  exists vpn p2 p1 p0 (a d : mword 1),
    ptree_maps t vpn p2 p1 p0 /\
    tlb_hash (__id 39) vpn = tlb_hash (__id 39) vpn' /\
    ent = u_walk_entry vpn p2 p1 (pte_set_ad p0 a d) asid.

Definition tlb_ok_pt (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  forall (vpn' : mword 27) (ent : TLB_Entry),
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = Some ent ->
    tlb_cache_of asid t vpn' ent.

(* an all-empty TLB is consistent with any tree *)
Lemma tlb_ok_pt_empty (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall vpn', vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = None) ->
  tlb_ok_pt asid t tlbvec.
Proof.
  intros Hnone vpn' ent Hget. rewrite Hnone in Hget. discriminate.
Qed.

(* consistency survives a walk-induced fill with ANY A/D variant of the
   mapped leaf -- covering both the no-update fill (the leaf itself, via
   [pte_set_ad_refl]) and the ADUE write-back fill (the updated word)    *)
Lemma tlb_ok_pt_fill (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 q0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  (exists a d : mword 1, q0 = pte_set_ad p0 a d) ->
  tlb_ok_pt asid t tlbvec ->
  tlb_ok_pt asid t (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (u_walk_entry vpn p2 p1 q0 asid))).
Proof.
  intros Hmaps (a & d & Hq) Hok vpn' ent Hget.
  rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)) in Hget.
  destruct (Z.eqb (tlb_hash (__id 39) vpn') (tlb_hash (__id 39) vpn)) eqn:Hh.
  - apply Z.eqb_eq in Hh. injection Hget as <-.
    exists vpn, p2, p1, p0, a, d.
    split; [exact Hmaps|]. split; [symmetry; exact Hh|].
    rewrite Hq. reflexivity.
  - exact (Hok vpn' ent Hget).
Qed.

(* the fill with the tree's OWN leaf word (the update_PTE_Bits = None
   path) is the reflexive instance *)
Lemma tlb_ok_pt_fill_self (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  tlb_ok_pt asid t tlbvec ->
  tlb_ok_pt asid t (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (u_walk_entry vpn p2 p1 p0 asid))).
Proof.
  intros Hmaps Hok.
  destruct (pte_set_ad_refl p0) as (a & d & Hp0).
  apply (tlb_ok_pt_fill asid t tlbvec vpn p2 p1 p0 p0 Hmaps); [| exact Hok].
  exists a, d. exact Hp0.
Qed.

(* consistency survives the ADUE write-back itself: replacing the mapped
   leaf by an A/D variant keeps every resident entry a variant of the
   NEW tree's leaf ([pte_set_ad_absorb]) *)
Lemma tlb_cache_of_set_leaf (asid : mword 16) (t : ptree)
    (vpn' : mword 27) (ent : TLB_Entry)
    (vpn : mword 27) (p2 p1 p0 : mword 64) (a d : mword 1) :
  ptree_maps t vpn p2 p1 p0 ->
  pte_valid (pte_set_ad p0 a d) -> pte_leaf (pte_set_ad p0 a d) ->
  pte_no_napot (pte_set_ad p0 a d) -> pte_pbmt0 (pte_set_ad p0 a d) ->
  tlb_cache_of asid t vpn' ent ->
  tlb_cache_of asid (ptree_set_leaf t vpn (pte_set_ad p0 a d)) vpn' ent.
Proof.
  intros Hmaps Hv Hl Hnap Hpb
    (vpn0 & q2 & q1 & q0 & a' & d' & Hm0 & Hh & Hent).
  destruct (decide (vpn0 = vpn)) as [-> | Hne].
  - destruct (ptree_maps_det t vpn q2 q1 q0 p2 p1 p0 Hm0 Hmaps)
      as (-> & -> & ->).
    exists vpn, p2, p1, (pte_set_ad p0 a d), a', d'.
    split.
    { apply (ptree_set_leaf_maps_self t vpn p2 p1 p0 _ Hmaps Hv Hl Hnap Hpb). }
    split; [exact Hh|].
    rewrite Hent. rewrite pte_set_ad_absorb. reflexivity.
  - exists vpn0, q2, q1, q0, a', d'.
    split; [exact (ptree_set_leaf_maps_other t vpn vpn0 q2 q1 q0 _ Hne Hm0)|].
    split; [exact Hh | exact Hent].
Qed.

Lemma tlb_ok_pt_set_leaf (asid : mword 16) (t : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 : mword 64) (a d : mword 1) :
  ptree_maps t vpn p2 p1 p0 ->
  pte_valid (pte_set_ad p0 a d) -> pte_leaf (pte_set_ad p0 a d) ->
  pte_no_napot (pte_set_ad p0 a d) -> pte_pbmt0 (pte_set_ad p0 a d) ->
  tlb_ok_pt asid t tlbvec ->
  tlb_ok_pt asid (ptree_set_leaf t vpn (pte_set_ad p0 a d)) tlbvec.
Proof.
  intros Hmaps Hv Hl Hnap Hpb Hok vpn' ent Hget.
  exact (tlb_cache_of_set_leaf asid t vpn' ent vpn p2 p1 p0 a d
           Hmaps Hv Hl Hnap Hpb (Hok vpn' ent Hget)).
Qed.

(* ===================================================================== *)
(* §7b TWO-TABLE TLB consistency: the satp-switch window.  Between a      *)
(*     [csrw satp] and the following [sfence.vma], resident entries may   *)
(*     have been cached from EITHER the previous table [tp] or the        *)
(*     current one [tc] -- and provenance matters beyond the leaf: a      *)
(*     Svadu hit write-back goes to the pteAddr recorded by the           *)
(*     INSTALLING walk, i.e. into the provenance tree's L0 slot.          *)
(* ===================================================================== *)

Definition tlb_ok_pt2 (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  forall (vpn' : mword 27) (ent : TLB_Entry),
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = Some ent ->
    tlb_cache_of asid tp vpn' ent \/ tlb_cache_of asid tc vpn' ent.

(* weakening injections: a single-table-consistent vector is two-table
   consistent with anything on the other side *)
Lemma tlb_ok_pt2_prev (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_ok_pt asid tp tlbvec -> tlb_ok_pt2 asid tp tc tlbvec.
Proof. intros Hok vpn' ent Hget. left. exact (Hok vpn' ent Hget). Qed.


(* walk-induced fills: the walker consults the CURRENT table, but the
   hit-refresh path re-fills from the entry's own provenance, so both
   sides are provided *)
Lemma tlb_ok_pt2_fill_cur (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 q0 : mword 64) :
  ptree_maps tc vpn p2 p1 p0 ->
  (exists a d : mword 1, q0 = pte_set_ad p0 a d) ->
  tlb_ok_pt2 asid tp tc tlbvec ->
  tlb_ok_pt2 asid tp tc (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                           (Some (u_walk_entry vpn p2 p1 q0 asid))).
Proof.
  intros Hmaps (a & d & Hq) Hok vpn' ent Hget.
  rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)) in Hget.
  destruct (Z.eqb (tlb_hash (__id 39) vpn') (tlb_hash (__id 39) vpn)) eqn:Hh.
  - apply Z.eqb_eq in Hh. injection Hget as <-.
    right. exists vpn, p2, p1, p0, a, d.
    split; [exact Hmaps|]. split; [symmetry; exact Hh|].
    rewrite Hq. reflexivity.
  - exact (Hok vpn' ent Hget).
Qed.

Lemma tlb_ok_pt2_fill_prev (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 q0 : mword 64) :
  ptree_maps tp vpn p2 p1 p0 ->
  (exists a d : mword 1, q0 = pte_set_ad p0 a d) ->
  tlb_ok_pt2 asid tp tc tlbvec ->
  tlb_ok_pt2 asid tp tc (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                           (Some (u_walk_entry vpn p2 p1 q0 asid))).
Proof.
  intros Hmaps (a & d & Hq) Hok vpn' ent Hget.
  rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)) in Hget.
  destruct (Z.eqb (tlb_hash (__id 39) vpn') (tlb_hash (__id 39) vpn)) eqn:Hh.
  - apply Z.eqb_eq in Hh. injection Hget as <-.
    left. exists vpn, p2, p1, p0, a, d.
    split; [exact Hmaps|]. split; [symmetry; exact Hh|].
    rewrite Hq. reflexivity.
  - exact (Hok vpn' ent Hget).
Qed.

(* a Svadu write-back into EITHER side's tree preserves consistency *)
Lemma tlb_ok_pt2_set_leaf_prev (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 : mword 64) (a d : mword 1) :
  ptree_maps tp vpn p2 p1 p0 ->
  pte_valid (pte_set_ad p0 a d) -> pte_leaf (pte_set_ad p0 a d) ->
  pte_no_napot (pte_set_ad p0 a d) -> pte_pbmt0 (pte_set_ad p0 a d) ->
  tlb_ok_pt2 asid tp tc tlbvec ->
  tlb_ok_pt2 asid (ptree_set_leaf tp vpn (pte_set_ad p0 a d)) tc tlbvec.
Proof.
  intros Hmaps Hv Hl Hnap Hpb Hok vpn' ent Hget.
  destruct (Hok vpn' ent Hget) as [Hp | Hc].
  - left. exact (tlb_cache_of_set_leaf asid tp vpn' ent vpn p2 p1 p0 a d
                   Hmaps Hv Hl Hnap Hpb Hp).
  - right. exact Hc.
Qed.

Lemma tlb_ok_pt2_set_leaf_cur (asid : mword 16) (tp tc : ptree)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (p2 p1 p0 : mword 64) (a d : mword 1) :
  ptree_maps tc vpn p2 p1 p0 ->
  pte_valid (pte_set_ad p0 a d) -> pte_leaf (pte_set_ad p0 a d) ->
  pte_no_napot (pte_set_ad p0 a d) -> pte_pbmt0 (pte_set_ad p0 a d) ->
  tlb_ok_pt2 asid tp tc tlbvec ->
  tlb_ok_pt2 asid tp (ptree_set_leaf tc vpn (pte_set_ad p0 a d)) tlbvec.
Proof.
  intros Hmaps Hv Hl Hnap Hpb Hok vpn' ent Hget.
  destruct (Hok vpn' ent Hget) as [Hp | Hc].
  - left. exact Hp.
  - right. exact (tlb_cache_of_set_leaf asid tc vpn' ent vpn p2 p1 p0 a d
                    Hmaps Hv Hl Hnap Hpb Hc).
Qed.

(* ===================================================================== *)
(* §8 The exec layer: hypothesis-style (tree-free) translate lemmas over  *)
(*    ABSTRACT PTE words -- the analogue of Pt4kWalk's TrampTranslate,    *)
(*    built on CommonWalk's privilege/access-generic core.  The Iris      *)
(*    engines extract the hypotheses from [ptree_own] ([ptree_own_path_   *)
(*    mem]) + a [ptree_maps] fact and instantiate.                        *)
(* ===================================================================== *)

(* ---- §8a a slot's read_pte fact from its [pt_slot_mem] + the ambient   *)
(*      PMP/PMA configuration (the facts [pmp_config] stores).            *)
Lemma pt_read_pte_slot (sg : mstate) (a w : mword 64) (region : PMA_Region) :
  pt_slot_mem sg a w ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
  matching_pma_region (register_lookup pma_regions sg.(sregs)) (Physaddr a) 8 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
  register_lookup htif_tohost_base sg.(sregs) = None ->
  exec (read_pte (Physaddr a) 8) sg = Some (Ok w, sg).
Proof.
  intros (Hbytes & Hram & Hram7 & Halign) HA Hord HR Hcov Hmatch Hpma Hhtif.
  assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
  { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
    change (Z.of_nat 7) with 7. lia. }
  assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
  { pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia. }
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0)) 4)
            (uint a) (uint (to_bits 64 8)) = PMP_Match).
  { apply (ram_pmp_match_w a _ 8); [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  apply (exec_read_pte_S a region w sg HA Hord Hrange HR Hmatch Halign Hpma).
  - apply within_clint_false; [apply addr_is_ram_not_in_clint; exact Hram | lia].
  - apply within_sig_false; [apply addr_is_ram_not_in_sig; exact Hram | lia].
  - apply within_htif_false. exact Hhtif.
  - apply addr_is_ram_not_dev. exact Hram.
  - exact Hbytes.
Qed.

(* ---- §8b the stored-entry bridges for [u_walk_entry] (abstract leaf).  *)

Lemma uwe_pte (vpn : mword 27) (p2 p1 q0 : mword 64) (asid : mword 16) :
  tlb_get_pte 8 (u_walk_entry vpn p2 p1 q0 asid) = autocast (T := mword) q0.
Proof.
  unfold tlb_get_pte, u_walk_entry. cbn [TLB_Entry_pte].
  f_equal.
  match goal with |- @subrange_vec_dec ?w _ ?hi ?lo = _ =>
    change hi with 63; change lo with 0 end.
  rewrite subrange64_63_0_id.
  rewrite zero_extend64_id. reflexivity.
Qed.

Lemma uwe_ppn (vpn vpn' : mword 27) (p2 p1 q0 : mword 64) (asid : mword 16) :
  tlb_get_ppn 39 (u_walk_entry vpn p2 p1 q0 asid) vpn'
  = autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44).
Proof.
  unfold tlb_get_ppn, u_walk_entry.
  cbn [TLB_Entry_levelMask TLB_Entry_ppn]. cbn zeta.
  match goal with |- context[and_vec ?x ?m] =>
    replace (and_vec x m) with (zeros' 64 : mword 64);
    [| symmetry; apply and64_zero_r; vm_compute; reflexivity] end.
  rewrite or64_zeros_r.
  match goal with |- context[and_vec ?x ?m] =>
    replace (and_vec x m) with ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44)) : mword 44);
    [| symmetry; apply and44_ones; vm_compute; reflexivity] end.
  rewrite zero_extend44_id.
  apply trunc44_zext.
Qed.

Lemma uwe_pbmt (vpn : mword 27) (p2 p1 q0 : mword 64) (asid : mword 16) s :
  pte_pbmt0 q0 ->
  exec (tlb_get_pbmt (u_walk_entry vpn p2 p1 q0 asid)) s = Some (PBMT_PMA, s).
Proof.
  intros Hpb.
  unfold tlb_get_pbmt, u_walk_entry. cbn [TLB_Entry_pte]. cbn zeta.
  rewrite zero_extend64_id. rewrite autocast_id.
  unfold pte_pbmt0 in Hpb. rewrite Hpb.
  vm_compute (page_based_mem_type_forwards _). apply exec_returnm.
Qed.

(* a walk entry always matches its own vpn under asid 0 (whatever its
   global bit accumulated from the pointer words) *)
Lemma uwe_match_self (vpn : mword 27) (p2 p1 q0 : mword 64) :
  match_TLB_Entry (u_walk_entry vpn p2 p1 q0 (mword_of_int 0))
    (mword_of_int 0) (sign_extend' (57 - 12) vpn) = true.
Proof.
  unfold match_TLB_Entry, u_walk_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  apply andb_true_intro. split.
  - apply orb_true_intro. right. vm_compute. reflexivity.
  - match goal with |- context[and_vec vpn ?m] =>
      replace (and_vec vpn m) with vpn;
      [| symmetry; apply and27_ones; vm_compute; reflexivity] end.
    match goal with |- context[and_vec ?x (not_vec ?m)] =>
      replace (and_vec x (not_vec m)) with x;
      [| symmetry; apply and45_ones; vm_compute; reflexivity] end.
    unfold eq_vec. rewrite MachineWord.MachineWord.eqb_true_iff.
    reflexivity.
Qed.

(* ...and never matches a FOREIGN vpn (the 45-bit tag determines the
   vpn), so a resident walk entry can only serve its own page *)
Lemma uwe_match_other (vpn vpn' : mword 27) (p2 p1 q0 : mword 64) (asid : mword 16) :
  vpn <> vpn' ->
  match_TLB_Entry (u_walk_entry vpn p2 p1 q0 asid)
    asid (sign_extend' (57 - 12) vpn') = false.
Proof.
  intros Hne.
  unfold match_TLB_Entry, u_walk_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  match goal with |- context[and_vec vpn ?m] =>
    replace (and_vec vpn m) with vpn;
    [| symmetry; apply and27_ones; vm_compute; reflexivity] end.
  match goal with |- context[and_vec ?x (not_vec ?m)] =>
    replace (and_vec x (not_vec m)) with x;
    [| symmetry; apply and45_ones; vm_compute; reflexivity] end.
  match goal with |- (_ && ?b)%bool = false => destruct b eqn:E end.
  - exfalso. apply Hne. apply u_sext45_inj.
    unfold eq_vec in E. rewrite MachineWord.MachineWord.eqb_true_iff in E.
    exact E.
  - apply andb_false_r.
Qed.

(* ---- §8c the TLB-HIT translate on a stored walk entry whose cached     *)
(*      leaf word [q0] (an A/D variant of the current one) passes the     *)
(*      check and needs no update.                                        *)
Section PtHit.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Lemma exec_translate_TLB_hit_pt (vpn : mword 27) (p2 p1 q0 : mword 64)
        (asid : mword 16) (idx : Z) s :
    pte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : mword 64) acc = None ->
    pte_pbmt0 q0 ->
    exec (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
            (u_walk_entry vpn p2 p1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44), PBMT_PMA, tt), s).
  Proof.
    intros Hchk Hupd Hpb.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?pv ?ac] =>
      assert (Hu : exec (update_and_write_pte a wd pv ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        change w with 64 end.
      rewrite autocast_id in Hupd. rewrite Hupd.
      cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hu). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (uwe_pbmt vpn p2 p1 q0 asid s Hpb)).
    rewrite uwe_ppn.
    apply exec_returnm.
  Qed.

  (* the hit whose cached leaf word FAILS the check: the fault surfaces
     before any A/D update or pbmt read -- state unchanged.  (The check
     runs FIRST on the hit path, so a denied hit never write-backs.) *)
  Lemma exec_translate_TLB_hit_denied_pt (vpn : mword 27) (p2 p1 q0 : mword 64)
        (asid : mword 16) (idx : Z) s :
    pte_check_denied acc p mxr do_sum (PTE_No_Permission tt) q0 ->
    exec (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
            (u_walk_entry vpn p2 p1 q0 asid)) s
    = Some (Err (PTW_No_Permission tt, tt), s).
  Proof.
    intros Hden.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_bind_Some _ _ _ _ _ (Hden s)). cbn match.
    apply exec_returnm.
  Qed.

  (* ---- §8d THE three-way hit-or-walk translate over abstract words:    *)
  (*      the tree-generic successor of [exec_translate_tramp].  The      *)
  (*      walk path installs [u_walk_entry vpn p2 p1 p0]; a hit serves    *)
  (*      any resident A/D-variant entry (same mapping: its PPN agrees).  *)

End PtHit.

(* ---- §8e the S-mode translateAddr head: front matter (mstatus reads,   *)
(*      Sv39 dispatch, canonicality, satp) + [exec_translate_pt].  The    *)
(*      output pa is hypothesis-shaped ([Hident]) so instances plug in    *)
(*      their own geometry (the kernel: identity via [ram_ident_4k]).     *)
Section PtTranslateAddr.
  Context (acc : MemoryAccessType mem_payload).


End PtTranslateAddr.

(* ---- §8f the FAULT translate: a blocked vpn's walk stops at an invalid *)
(*      word and [translate] returns the page-fault error, state          *)
(*      unchanged.  (The TLB slot always misses on a blocked vpn: under   *)
(*      [tlb_ok_pt] resident entries are mapped vpns' walk entries, and   *)
(*      [uwe_match_other] rejects a foreign tag.)                         *)
Section PtFault.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Lemma exec_translate_pt_blocks (vpn : mword 27) (root : mword 44) s :
    (* the walk stops at an invalid word at level 2, 1 or 0 *)
    ((exists w2,
        exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok w2, s) /\ pte_invalid w2)
     \/ (exists p2 w1,
        exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok p2, s) /\ pte_valid p2 /\ pte_ptr p2 /\
        exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
          = Some (Ok w1, s) /\ pte_invalid w1)
     \/ (exists p2 p1 w0,
        exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok p2, s) /\ pte_valid p2 /\ pte_ptr p2 /\
        exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
          = Some (Ok p1, s) /\ pte_valid p1 /\ pte_ptr p1 /\
        exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
          = Some (Ok w0, s) /\ pte_invalid w0)) ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
    exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_Invalid_PTE tt, tt), s).
  Proof.
    intros Hstop Hlk.
    apply (exec_translate_walk_user_err vpn acc p mxr do_sum (mword_of_int 0) root _ s Hlk).
    apply exec_translate_TLB_miss_user_walk_err.
    destruct Hstop as [ (w2 & Hrd2 & Hi2)
                      | [ (p2 & w1 & Hrd2 & Hv2 & Hn2 & Hrd1 & Hi1)
                        | (p2 & p1 & w0 & Hrd2 & Hv2 & Hn2 & Hrd1 & Hv1 & Hn1 & Hrd0 & Hi0) ] ].
    - exact (exec_pt_walk_user_l2_invalid vpn acc p mxr do_sum root w2 s Hrd2 Hi2).
    - apply (exec_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ s Hrd2 Hv2 Hn2).
      intros g' a.
      exact (exec_rec_walk_l1_invalid vpn acc p mxr do_sum (u_next_base p2) w1 g' a s Hrd1 Hi1).
    - apply (exec_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ s Hrd2 Hv2 Hn2).
      intros g' a.
      apply (exec_rec_walk_l1_sub vpn acc p mxr do_sum (u_next_base p2) p1 g' _ a s Hrd1 Hv1 Hn1).
      intros g'' a'.
      exact (exec_rec_walk_leaf_invalid vpn acc p mxr do_sum (u_next_base p1) w0 g'' a' s Hrd0 Hi0).
  Qed.

  (* mapped but DENIED: the walk reaches the leaf and the permission check
     fails -- no fill, no write-back, state unchanged *)
  Lemma exec_translate_pt_denied (vpn : mword 27) (root : mword 44)
        (p2 p1 p0 : mword 64) s :
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 ->
    pte_check_denied acc p mxr do_sum (PTE_No_Permission tt) p0 ->
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s) ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
    exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_No_Permission tt, tt), s).
  Proof.
    intros Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hden Hrd2 Hrd1 Hrd0 Hlk.
    apply (exec_translate_walk_user_err vpn acc p mxr do_sum (mword_of_int 0) root _ s Hlk).
    apply exec_translate_TLB_miss_user_walk_err.
    apply (exec_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ s Hrd2 Hv2 Hn2).
    intros g' a.
    apply (exec_rec_walk_l1_sub vpn acc p mxr do_sum (u_next_base p2) p1 g' _ a s Hrd1 Hv1 Hn1).
    intros g'' a'.
    change (PTW_No_Permission tt) with (ext_get_ptw_error (PTE_No_Permission tt)).
    exact (exec_rec_walk_leaf_noperm vpn acc p mxr do_sum (u_next_base p1) p0 g''
             (PTE_No_Permission tt) a' s Hrd0 Hv0 Hl0 (fun s0 => Hden s0)).
  Qed.

  (* the soundness KEYSTONE: under [tlb_ok_pt] a BLOCKED vpn is never
     TLB-resident -- a resident entry is some MAPPED vpn's walk entry;
     the blocked vpn cannot be that vpn ([ptree_maps_blocks_excl]), and
     a foreign entry's tag rejects the lookup ([uwe_match_other]). *)
  Lemma tlb_ok_pt_lookup_blocked (t : ptree) (vpn : mword 27)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    ptree_blocks t vpn ->
    register_lookup tlb s.(sregs) = tlbvec ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s).
  Proof.
    intros Hok Hblk Htlb.
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Hok vpn ent Hslot) as (vpn0 & q2 & q1 & q0 & a' & d' & Hm0 & Hh & ->).
      apply (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec s Htlb Hslot).
      apply (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a' d') (mword_of_int 0)).
      intros ->. exact (ptree_maps_blocks_excl t vpn q2 q1 q0 Hm0 Hblk).
    - exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec s Htlb Hslot).
  Qed.

End PtFault.
