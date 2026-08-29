(* ===================================================================== *)
(* UserPerm.v -- THE PER-PAGE PERMISSION VIEW of a user address space:    *)
(* the user-visible PROJECTION of the process's page table.               *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md, "The permission map".  A       *)
(* verified user program OBSERVES page permissions (a store to a read-only *)
(* page faults, a fetch from a non-executable page faults), so by the       *)
(* slot's own principle -- the key is what the process can observe and     *)
(* nothing else -- they belong in the key.  What it cannot observe is the  *)
(* page-table STRUCTURE (PPNs, the tree), and that stays hidden:           *)
(*                                                                         *)
(*   uperm            {X, W} -- the two bits a user page can differ in.     *)
(*                    R is IMPLIED for every page in the map: the          *)
(*                    projection keeps a leaf only if U and R are both     *)
(*                    set (xv6 never builds a user leaf without R; an       *)
(*                    execute-only leaf would be absent).                  *)
(*   perm_of um sz    the projection: every leaf of the user map with U     *)
(*                    set, reduced to its X/W bits, UNION the pages that   *)
(*                    are LIVE (below [PGROUNDUP sz]) but not mapped yet,   *)
(*                    at {X := false; W := true}.                           *)
(*                                                                         *)
(* THE LAZY PAGES ARE FILLED IN AS RW, and here is why (the decision the   *)
(* owner left to the lane).  [proc_priv]'s image is the LAZY sz-region    *)
(* view: a page below [p->sz] that has not been touched yet reads as       *)
(* zeros, and the first touch takes a page fault that [vmfault] serves by  *)
(* mapping a fresh page PTE_R|PTE_W|PTE_U (kernel/vm.c, [vmfault]:         *)
(* [mappages(..., PTE_W | PTE_U | PTE_R)]) -- so, as the PROCESS sees it,  *)
(* such a page IS a writable page whose bytes happen to be zero, and the   *)
(* fault is invisible.  That is exactly what makes the page-fault arm of   *)
(* the trap contract TRANSPARENT ([UexecRet.uexec_ret]: the returned slot  *)
(* is at the SAME key): the image does not move (the lazy view already     *)
(* had the zeros) and the permission map does not move (it already said    *)
(* RW).  Had the lazy pages been ABSENT from the map instead, a page fault *)
(* would change the map (the page appears at RW after [vmfault]) and the   *)
(* transparent arm would be false as stated.  The price is that the        *)
(* projection takes the size beside the leaf map -- but the size is        *)
(* exactly the other datum the kernel keeps for the address space          *)
(* ([pv_sz]), so the kernel's discharge is by computation, and the U-mode  *)
(* leaves never look at it: a fetch needs X, which no filled page has, so  *)
(* an X page is a MAPPED page; a store needs W AND a byte present in the   *)
(* image, and at the tier the leaves run on ([user_pt_inv]'s [dom M =      *)
(* uva_dom pt]) a present byte is a mapped page.  The pages the guard-page *)
(* trick UNMAPS from user mode ([uvmclear], U := 0) are mapped but not     *)
(* user-accessible: they are in [dom M] (the bytes exist) and NOT in the   *)
(* map (nothing the process can do reaches them), which is why the map is *)
(* built with [omap] on the U bit rather than [fmap].                      *)
(*                                                                         *)
(* THE LEAF-BIT TRANSFER (§3).  The engines consume the model's own         *)
(* classification [UserPtTree.uleaf_ok acc w] (the permission check passes  *)
(* on every A/D variant); the key carries bits.  [perm_of_X] / [perm_of_W] *)
(* / [perm_of_R] are the bridge, and they are proved by ENUMERATING the    *)
(* six flag bits the check reads (V R W X U G): the verdict of              *)
(* [check_PTE_permission] depends on the leaf only through the low byte    *)
(* with A/D substituted, so 64 cases x 4 A/D variants of one [vm_compute]  *)
(* each decide everything, with [upt_acc_wf]'s ok-or-denied disjunction    *)
(* ruling out the shapes (write-only, execute-only) that the check answers  *)
(* differently on different machine states.                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import WpDecodeBridge.  (* [dstate] -- one concrete machine state to refute a denial at *)
Require Import PtAdBits PtTree Pt4kWalk UptTree.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The per-page permission and the projection.                          *)
(* ===================================================================== *)

Record uperm := MkUperm { up_X : bool; up_W : bool }.

Global Instance uperm_eq_dec : EqDecision uperm.
Proof. solve_decision. Defined.

(* what [vmfault] maps: PTE_R|PTE_W|PTE_U *)
Definition uperm_rw : uperm := MkUperm false true.

(* the X / W bits of a leaf word (PTE bit 3 / bit 2); the U bit is bit 4 *)
Definition pte_bit (w : mword 64) (k : Z) : bool := Z.testbit (bv_unsigned w) k.

Definition perm_bits (w : mword 64) : uperm :=
  MkUperm (pte_bit w 3) (pte_bit w 2).

(* the leaf's projection: present iff the page is user-accessible (U) and
   readable (R) -- R is IMPLIED for every page in the map (xv6 never builds
   a user leaf without R; an execute-only leaf, which the model would deny
   loads on, is simply absent) *)
Definition perm_leaf (w : mword 64) : option uperm :=
  if pte_bit w 4 && pte_bit w 1 then Some (perm_bits w) else None.

(* the pages below [PGROUNDUP sz] *)
Definition live_pages (sz : Z) : gset (mword 27) :=
  list_to_set ((fun k : Z => Z_to_bv 27 k) <$> seqZ 0 (UserPtTree.pgroundup sz / 4096)).

Definition perm_fill (um : gmap (mword 27) (mword 64)) (sz : Z) : gmap (mword 27) uperm :=
  gset_to_gmap uperm_rw (live_pages sz ∖ dom um).

(* THE PROJECTION *)
Definition perm_of (um : gmap (mword 27) (mword 64)) (sz : Z) : gmap (mword 27) uperm :=
  omap perm_leaf um ∪ perm_fill um sz.

(* the byte-vs-page helper: the permission at a user virtual address *)
Definition uperm_at (π : gmap (mword 27) uperm) (va : mword 64) : option uperm :=
  π !! svpn_of va.

(* ===================================================================== *)
(* §2 Reading the projection.                                              *)
(* ===================================================================== *)

Lemma perm_fill_lookup_Some (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) :
  perm_fill um sz !! p = Some q -> q = uperm_rw /\ um !! p = None.
Proof.
  unfold perm_fill. intros H. apply lookup_gset_to_gmap_Some in H as [Hin ->].
  split; [ reflexivity | ].
  apply elem_of_difference in Hin as [_ Hnot].
  apply not_elem_of_dom. exact Hnot.
Qed.

(* a mapped, user-accessible page reads its own bits *)
Lemma perm_of_lookup_mapped (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (w : mword 64) :
  um !! p = Some w -> pte_bit w 4 = true -> pte_bit w 1 = true ->
  perm_of um sz !! p = Some (perm_bits w).
Proof.
  intros Hl Hu Hr. unfold perm_of. apply lookup_union_Some_l.
  apply lookup_omap_Some. exists w. split; [ | exact Hl ].
  unfold perm_leaf. rewrite Hu, Hr. reflexivity.
Qed.

(* ...and a mapped page that is NOT user-readable is absent *)
Lemma perm_of_lookup_nou (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (w : mword 64) :
  um !! p = Some w -> pte_bit w 4 && pte_bit w 1 = false ->
  perm_of um sz !! p = None.
Proof.
  intros Hl Hu. unfold perm_of. apply lookup_union_None. split.
  - rewrite lookup_omap, Hl. change (perm_leaf w = None). unfold perm_leaf. rewrite Hu. reflexivity.
  - unfold perm_fill. apply lookup_gset_to_gmap_None.
    intros Hin. apply elem_of_difference in Hin as [_ Hnot].
    apply Hnot. apply elem_of_dom. exists w. exact Hl.
Qed.

(* every entry of the projection is either a user leaf's bits or a filled
   lazy page *)
Lemma perm_of_lookup_Some (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) :
  perm_of um sz !! p = Some q ->
  (exists w : mword 64, um !! p = Some w /\ pte_bit w 4 = true /\ pte_bit w 1 = true /\
                        q = perm_bits w)
  \/ (um !! p = None /\ q = uperm_rw).
Proof.
  unfold perm_of. intros H. apply lookup_union_Some_raw in H as [H | [Hn H]].
  - left. apply lookup_omap_Some in H as (w & Hw & Hl).
    unfold perm_leaf in Hw.
    destruct (pte_bit w 4) eqn:Hu; [ | discriminate Hw ].
    destruct (pte_bit w 1) eqn:Hr; [ | discriminate Hw ].
    injection Hw as <-. exists w. split_and!; [ exact Hl | exact Hu | exact Hr | reflexivity ].
  - right. exact (conj (proj2 (perm_fill_lookup_Some _ _ _ _ H))
                       (proj1 (perm_fill_lookup_Some _ _ _ _ H))).
Qed.

(* an X page is a MAPPED user page: the fill carries no X *)
Lemma perm_of_X_mapped (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) :
  perm_of um sz !! p = Some q -> up_X q = true ->
  exists w : mword 64, um !! p = Some w /\ pte_bit w 4 = true /\ pte_bit w 1 = true /\
                       pte_bit w 3 = true.
Proof.
  intros H Hx. destruct (perm_of_lookup_Some _ _ _ _ H) as [(w & Hl & Hu & Hr & ->) | [_ ->]].
  - exists w. split_and!; [ exact Hl | exact Hu | exact Hr | exact Hx ].
  - discriminate Hx.
Qed.

(* a W page that is mapped is a user page with W *)
Lemma perm_of_W_mapped (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) (w : mword 64) :
  perm_of um sz !! p = Some q -> up_W q = true -> um !! p = Some w ->
  pte_bit w 4 = true /\ pte_bit w 1 = true /\ pte_bit w 2 = true.
Proof.
  intros H Hw Hl.
  destruct (perm_of_lookup_Some _ _ _ _ H) as [(w' & Hl' & Hu & Hr & ->) | [Hn _]].
  - rewrite Hl in Hl'. injection Hl' as <-. exact (conj Hu (conj Hr Hw)).
  - rewrite Hl in Hn. discriminate Hn.
Qed.

Lemma perm_of_mapped_U (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) (w : mword 64) :
  perm_of um sz !! p = Some q -> um !! p = Some w ->
  pte_bit w 4 = true /\ pte_bit w 1 = true.
Proof.
  intros H Hl.
  destruct (perm_of_lookup_Some _ _ _ _ H) as [(w' & Hl' & Hu & Hr & _) | [Hn _]].
  - rewrite Hl in Hl'. injection Hl' as <-. exact (conj Hu Hr).
  - rewrite Hl in Hn. discriminate Hn.
Qed.

(* ===================================================================== *)
(* §3 THE LEAF-BIT TRANSFER: from the key's bits to the model's verdict.  *)
(* ===================================================================== *)

(* the six bits the permission check reads, as one number *)
Definition flags6 (w : mword 64) : Z := Z.land (bv_unsigned w) 63.

Lemma flags6_range (w : mword 64) : 0 <= flags6 w < 64.
Proof.
  unfold flags6.
  pose proof (bv_unsigned_in_range _ w) as [H0 _].
  split; [ apply Z.land_nonneg; left; exact H0 | ].
  assert (H : 63 = Z.ones 6) by reflexivity. rewrite H.
  rewrite Z.land_ones; [ | lia ]. apply Z.mod_pos_bound. lia.
Qed.

Lemma flags6_bit (w : mword 64) (k : Z) :
  0 <= k < 6 -> Z.testbit (flags6 w) k = pte_bit w k.
Proof.
  intros Hk. unfold flags6, pte_bit. rewrite Z.land_spec.
  assert (H : Z.testbit 63 k = true).
  { assert (H63 : 63 = Z.ones 6) by reflexivity. rewrite H63.
    apply Z.ones_spec_low. lia. }
  rewrite H. apply andb_true_r.
Qed.

(* the flag byte of an A/D variant of a valid leaf, as a function of its
   six low bits: [mkpte_ad_flags] read modulo 256 *)
Lemma pte_flags_byte_of_flags6 (w : mword 64) (a d : mword 1) :
  bv_unsigned w < 2 ^ 54 ->
  pte_valid w ->
  (subrange_vec_dec (pte_set_ad w a d) 7 0 : mword 8)
  = (mword_of_int (Z.lor (flags6 w)
       (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7))) : mword 8).
Proof.
  intros Hlt Hv.
  pose proof (pte_flags10_range w) as Hf.
  pose proof (pte_flags10_lor1 w Hv) as H1.
  pose proof (mkpte_ad_flags (pte_ppn w) (pte_flags10 w) a d Hf H1) as Hmk.
  rewrite <- (mk_pte_eta w Hlt) in Hmk.
  rewrite Hmk.
  apply bv_eq.
  assert (Hm8 : forall z : Z, bv_unsigned (mword_of_int z : mword 8) = z mod 256).
  { intros z. unfold mword_of_int, SailStdpp.Values.mword_of_int,
      MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite !Hm8.
  (* both sides are the same bit pattern below bit 8 *)
  pose proof (bv_unsigned_in_range _ a) as Ha.
  pose proof (bv_unsigned_in_range _ d) as Hd.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2 in Ha, Hd.
  unfold uvm_flags. rewrite H1.
  apply Z.bits_inj'. intros k Hk.
  assert (H256 : 256 = 2 ^ 8) by reflexivity. rewrite H256.
  destruct (Z_lt_le_dec k 8) as [Hk8 | Hk8].
  - rewrite !Z.mod_pow2_bits_low; [ | lia | lia ].
    rewrite !Z.lor_spec, !Z.land_spec.
    unfold flags6, pte_flags10.
    rewrite !Z.land_spec.
    (* the constant masks, bit by bit *)
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)
      by lia.
    destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      cbn [Z.testbit];
      repeat match goal with
             | |- context [Z.testbit 831 ?j] =>
                 let e := eval vm_compute in (Z.testbit 831 j) in
                 change (Z.testbit 831 j) with e
             | |- context [Z.testbit 1023 ?j] =>
                 let e := eval vm_compute in (Z.testbit 1023 j) in
                 change (Z.testbit 1023 j) with e
             | |- context [Z.testbit 63 ?j] =>
                 let e := eval vm_compute in (Z.testbit 63 j) in
                 change (Z.testbit 63 j) with e
             end;
      rewrite ?andb_true_r, ?andb_false_r, ?orb_false_r, ?orb_false_l;
      try reflexivity;
      (* the shifted A/D bits: below 6 / 7 they are zero, at 6 / 7 they are
         the bit itself *)
      rewrite ?Z.shiftl_spec_low; try lia;
      rewrite ?Z.shiftl_spec; try lia;
      cbn; try reflexivity;
      try (rewrite ?orb_false_r, ?orb_false_l, ?andb_false_r; reflexivity).
  - rewrite !Z.mod_pow2_bits_high; [ reflexivity | lia | lia ].
Qed.

(* the 64 cases *)
Local Lemma z64_cases (x : Z) :
  0 <= x < 64 ->
  x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/
  x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/
  x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/
  x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31 \/
  x = 32 \/ x = 33 \/ x = 34 \/ x = 35 \/ x = 36 \/ x = 37 \/ x = 38 \/ x = 39 \/
  x = 40 \/ x = 41 \/ x = 42 \/ x = 43 \/ x = 44 \/ x = 45 \/ x = 46 \/ x = 47 \/
  x = 48 \/ x = 49 \/ x = 50 \/ x = 51 \/ x = 52 \/ x = 53 \/ x = 54 \/ x = 55 \/
  x = 56 \/ x = 57 \/ x = 58 \/ x = 59 \/ x = 60 \/ x = 61 \/ x = 62 \/ x = 63.
Proof. lia. Qed.

(* the leaf facts [proc_pt_wf] gives about one entry *)
Definition uleaf_wf (w : mword 64) : Prop :=
  (forall a d : mword 1,
     pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
     pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)) /\
  (forall acc : MemoryAccessType mem_payload,
     u_acc acc -> uleaf_ok acc w \/ uleaf_denied acc w).

Lemma proc_pt_wf_uleaf_wf (P : uptd) (p : mword 27) (w : mword 64) :
  proc_pt_wf P -> ud_um P !! p = Some w -> uleaf_wf w.
Proof.
  intros (Hmwf & Hawf & _) Hl. split.
  - exact (proj2 (Hmwf p w Hl)).
  - exact (Hawf p w Hl).
Qed.

Lemma uleaf_wf_lt (w : mword 64) : uleaf_wf w -> bv_unsigned w < 2 ^ 54 /\ pte_valid w.
Proof.
  intros (H1 & _).
  destruct (pte_set_ad_refl w) as (a0 & d0 & Hself).
  destruct (H1 a0 d0) as (Hv & _ & Hn & Hp).
  rewrite <- Hself in Hv, Hn, Hp.
  split; [ | exact Hv ].
  change (2 ^ 54) with 18014398509481984. exact (pte_hi_zero w Hv Hn Hp).
Qed.

(* THE ONE ENUMERATION: with the six bits fixed, each verdict is a
   computation.  [Hb] is the flag-byte equation above, instantiated. *)
(* the verdict a denial claims, as a boolean of the result -- so that the
   refutation's proof term carries [false = true] and never the normal form
   of the machine state (that normal form, stored per case, made Qed a
   50 GB non-terminating check; measured 2026-08-28) *)
Definition is_noperm_result (r : option (PTE_Check * mstate)) : bool :=
  match r with
  | Some (PTE_Check_Failure (_, PTE_No_Permission _), _) => true
  | _ => false
  end.

Local Ltac perm_case_refute Hlt Hv Hd :=
  exfalso;
  specialize (Hd (mword_of_int 0) (mword_of_int 0) false false
                 (dstate MENVCFG_S User));
  unfold pte_check_denied, Mk_PTE_Flags in Hd;
  rewrite (pte_flags_byte_of_flags6 _ _ _ Hlt Hv) in Hd;
  rewrite pte_set_ad_ext in Hd;
  match goal with
  | Hx : ext_bits_of_PTE _ = _ |- _ => rewrite Hx in Hd
  end;
  match goal with
  | Hg : flags6 _ = _ |- _ => rewrite Hg in Hd
  end;
  apply (f_equal is_noperm_result) in Hd;
  vm_compute in Hd; discriminate Hd.

Lemma uleaf_wf_ext (w : mword 64) :
  uleaf_wf w -> ext_bits_of_PTE w = Mk_PTE_Ext (mword_of_int 0).
Proof.
  intros Hwf. destruct (uleaf_wf_lt w Hwf) as [Hlt Hv].
  pose proof (mkpte_ad_ext (pte_ppn w) (pte_flags10 w) (mword_of_int 0) (mword_of_int 0)
                (pte_flags10_range w)) as Hmk.
  rewrite pte_set_ad_ext in Hmk.
  rewrite <- (mk_pte_eta w Hlt) in Hmk.
  exact Hmk.
Qed.

(* Fetch: an X page (U and X set) passes on every variant *)
Lemma uleaf_fetch_of_bits (w : mword 64) :
  uleaf_wf w -> pte_bit w 4 = true -> pte_bit w 3 = true ->
  uleaf_ok (InstructionFetch tt) w.
Proof.
  intros Hwf Hu Hx.
  pose proof (uleaf_wf_ext w Hwf) as Hext.
  destruct (uleaf_wf_lt w Hwf) as [Hlt Hv].
  destruct Hwf as (_ & Hacc).
  destruct (Hacc (InstructionFetch tt) ltac:(left; reflexivity)) as [Hok | Hd];
    [ exact Hok | ].
  rewrite <- (flags6_bit w 4 ltac:(lia)) in Hu.
  rewrite <- (flags6_bit w 3 ltac:(lia)) in Hx.
  destruct (z64_cases (flags6 w) (flags6_range w)) as
    [Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|Hg]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: rewrite Hg in Hu, Hx.
  all: try discriminate Hu.
  all: try discriminate Hx.
  (* NOT [destruct …; first [ … ]] over the 64 cases: as one chained tactic
     this did not terminate; as separate [all:] passes it is a second *)
  all: perm_case_refute Hlt Hv Hd.
Qed.

(* Store: a W page (U and W set) passes on every variant; Load too *)
Lemma uleaf_store_of_bits (w : mword 64) :
  uleaf_wf w -> pte_bit w 4 = true -> pte_bit w 2 = true ->
  uleaf_ok (Store Data) w.
Proof.
  intros Hwf Hu Hx.
  pose proof (uleaf_wf_ext w Hwf) as Hext.
  destruct (uleaf_wf_lt w Hwf) as [Hlt Hv].
  destruct Hwf as (_ & Hacc).
  destruct (Hacc (Store Data) ltac:(right; right; left; reflexivity)) as [Hok | Hd];
    [ exact Hok | ].
  rewrite <- (flags6_bit w 4 ltac:(lia)) in Hu.
  rewrite <- (flags6_bit w 2 ltac:(lia)) in Hx.
  destruct (z64_cases (flags6 w) (flags6_range w)) as
    [Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|Hg]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: rewrite Hg in Hu, Hx.
  all: try discriminate Hu.
  all: try discriminate Hx.
  (* NOT [destruct …; first [ … ]] over the 64 cases: as one chained tactic
     this did not terminate; as separate [all:] passes it is a second *)
  all: perm_case_refute Hlt Hv Hd.
Qed.

(* Load: a readable user leaf passes on every variant *)
Lemma uleaf_load_of_bits (w : mword 64) :
  uleaf_wf w -> pte_bit w 4 = true -> pte_bit w 1 = true ->
  uleaf_ok (Load Data) w.
Proof.
  intros Hwf Hu Hx.
  pose proof (uleaf_wf_ext w Hwf) as Hext.
  destruct (uleaf_wf_lt w Hwf) as [Hlt Hv].
  destruct Hwf as (_ & Hacc).
  destruct (Hacc (Load Data) ltac:(right; left; reflexivity)) as [Hok | Hd];
    [ exact Hok | ].
  rewrite <- (flags6_bit w 4 ltac:(lia)) in Hu.
  rewrite <- (flags6_bit w 1 ltac:(lia)) in Hx.
  destruct (z64_cases (flags6 w) (flags6_range w)) as
    [Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[Hg|Hg]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: rewrite Hg in Hu, Hx.
  all: try discriminate Hu.
  all: try discriminate Hx.
  all: perm_case_refute Hlt Hv Hd.
Qed.

(* ===================================================================== *)
(* §4 The transfers the engines and the program proofs consume, keyed on   *)
(* a table [pt] with [perm_of (ud_um pt) sz = π].                          *)
(* ===================================================================== *)

(* an X page of the key is a fetch-ok leaf of the table *)
Lemma perm_of_X (pt : uptd) (sz : Z) (p : mword 27) (q : uperm) :
  proc_pt_wf pt ->
  perm_of (ud_um pt) sz !! p = Some q -> up_X q = true ->
  exists w : mword 64, ud_um pt !! p = Some w /\ uleaf_ok (InstructionFetch tt) w.
Proof.
  intros Hwf Hl Hx.
  destruct (perm_of_X_mapped _ _ _ _ Hl Hx) as (w & Hw & Hu & _ & Hxb).
  exists w. split; [ exact Hw | ].
  exact (uleaf_fetch_of_bits w (proc_pt_wf_uleaf_wf pt p w Hwf Hw) Hu Hxb).
Qed.

(* a W page of the key that the table maps is a store-ok (and load-ok) leaf *)
Lemma perm_of_W (pt : uptd) (sz : Z) (p : mword 27) (q : uperm) (w : mword 64) :
  proc_pt_wf pt ->
  perm_of (ud_um pt) sz !! p = Some q -> up_W q = true ->
  ud_um pt !! p = Some w ->
  uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w.
Proof.
  intros Hwf Hl Hx Hw.
  destruct (perm_of_W_mapped _ _ _ _ _ Hl Hx Hw) as (Hu & Hr & Hwb).
  pose proof (proc_pt_wf_uleaf_wf pt p w Hwf Hw) as Hlwf.
  split; [ exact (uleaf_store_of_bits w Hlwf Hu Hwb)
         | exact (uleaf_load_of_bits w Hlwf Hu Hr) ].
Qed.

(* a page of the key that the table maps is a load-ok leaf *)
Lemma perm_of_R (pt : uptd) (sz : Z) (p : mword 27) (q : uperm) (w : mword 64) :
  proc_pt_wf pt ->
  perm_of (ud_um pt) sz !! p = Some q ->
  ud_um pt !! p = Some w ->
  uleaf_ok (Load Data) w.
Proof.
  intros Hwf Hl Hw.
  destruct (perm_of_mapped_U _ _ _ _ _ Hl Hw) as [Hu Hr].
  exact (uleaf_load_of_bits w (proc_pt_wf_uleaf_wf pt p w Hwf Hw) Hu Hr).
Qed.

(* ===================================================================== *)
(* §5 From the image's domain to the table: a byte present in an image    *)
(* pinned to the table's address space sits on a mapped page.             *)
(* ===================================================================== *)

Lemma uva_dom_svpn (pt : uptd) (va : Z) :
  upt_map_wf (ud_um pt) ->
  va ∈ uva_dom pt ->
  exists w : mword 64, ud_um pt !! svpn_of (mword_of_int va) = Some w.
Proof.
  intros Hwf Hin.
  apply elem_of_uva_dom in Hin as (vpn & w & j & Hl & Hj & ->).
  exists w.
  destruct (Hwf vpn w Hl) as (Hlt & _).
  rewrite tf_vpn_unsigned in Hlt.
  rewrite (uva_svpn_of vpn j Hj Hlt). exact Hl.
Qed.

Lemma image_byte_mapped (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  upt_map_wf (ud_um pt) ->
  dom M = uva_dom pt ->
  M !! va = Some b ->
  exists w : mword 64, ud_um pt !! svpn_of (mword_of_int va) = Some w.
Proof.
  intros Hwf Hdom Hb. apply (uva_dom_svpn pt va Hwf).
  rewrite <- Hdom. apply elem_of_dom. exists b. exact Hb.
Qed.

(* ===================================================================== *)
(* §6 THE SIZE SIDE CONDITION, and what the FILLED pages can be.          *)
(*                                                                         *)
(* [perm_of]'s fill runs over [live_pages sz], and NOTHING in [perm_of]    *)
(* stops that set from reaching the two vpns xv6 reserves at the top of    *)
(* the user address space (the trapframe's, [tf_vpn], and the              *)
(* trampoline's, [tramp_vpn]).  The kernel's own invariant does:           *)
(* [p->sz] never exceeds MAXVA - 2 pages ([ProcPtOwn.uvm_maxsz] =          *)
(* 2^38 - 8192), and that is [usz_ok].  It rides in the U-mode bundle      *)
(* beside the size, and it is what lets the STORE leaf conclude that a     *)
(* live-but-unmapped page really takes a page fault (rather than being     *)
(* the trapframe page, which is mapped and merely U-less).                 *)
(* ===================================================================== *)

Definition usz_ok (sz : Z) : Prop := (UserPtTree.pgroundup sz <= 274877898752)%Z.

Lemma usz_ok_live (sz va : Z) :
  usz_ok sz -> uva_live sz va -> (0 <= va < 274877898752)%Z.
Proof. unfold usz_ok, uva_live. lia. Qed.

Lemma live_pages_lt (sz : Z) (p : mword 27) :
  usz_ok sz -> p ∈ live_pages sz -> (bv_unsigned p < 67108862)%Z.
Proof.
  unfold usz_ok, live_pages. intros Hsz Hin.
  apply elem_of_list_to_set, elem_of_list_fmap in Hin as (k & -> & Hk).
  apply elem_of_seqZ in Hk.
  assert (Hle : (UserPtTree.pgroundup sz / 4096 <= 67108862)%Z).
  { apply (Z.div_le_mono _ _ 4096 ltac:(lia)) in Hsz.
    change (274877898752 / 4096)%Z with 67108862%Z in Hsz. exact Hsz. }
  assert (Hkb : (0 <= k < 67108862)%Z) by lia.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [ lia | ].
  change (bv_modulus 27) with 134217728%Z. lia.
Qed.

(* a page of the key that the table does NOT map came from the fill *)
Lemma perm_of_unmapped_fill (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) :
  perm_of um sz !! p = Some q -> um !! p = None -> p ∈ live_pages sz.
Proof.
  unfold perm_of, perm_fill. intros H Hn.
  apply lookup_union_Some_raw in H as [H | [_ H]].
  - apply lookup_omap_Some in H as (w & _ & Hl). rewrite Hn in Hl. discriminate Hl.
  - apply lookup_gset_to_gmap_Some in H as [Hin _].
    exact (proj1 (proj1 (elem_of_difference _ _ _) Hin)).
Qed.

(* ...and a filled page is a real user page: its vpn is below the
   trapframe's, so it is neither the trapframe's page nor the
   trampoline's.  This is the fact the store's FAULT arm needs to select
   [u_fault_flavor]'s unmapped disjunct.  (The two reserved vpns are named
   in [UptTree], whose constants this file does not import; the consumer
   turns this bound into the two disequalities with
   [ProcPtOwn.vpn_lt_ne].) *)
Lemma perm_of_unmapped_lt (um : gmap (mword 27) (mword 64)) (sz : Z)
    (p : mword 27) (q : uperm) :
  usz_ok sz -> perm_of um sz !! p = Some q -> um !! p = None ->
  (bv_unsigned p < 67108862)%Z.
Proof.
  intros Hsz H Hn.
  exact (live_pages_lt sz p Hsz (perm_of_unmapped_fill um sz p q H Hn)).
Qed.

(* ===================================================================== *)
(* §7 THE LAZY IMAGE'S WINDOW.                                            *)
(*                                                                         *)
(* Under the LAZY key the bundle's image [M] is NOT pinned to the table's  *)
(* address space -- [dom M] is the live-or-mapped set -- so the engine     *)
(* runs on the MAPPED SUB-IMAGE [Mp] and every byte fact it needs must be  *)
(* transported from [M] to [Mp].  The transport is available exactly on a  *)
(* MAPPED page, and the two lemmas below are what establish that a fetch's *)
(* or a store's whole in-page window IS on one:                            *)
(*                                                                         *)
(*   [uva_of_image_lt]     a va the image records is below 2^39 -- from    *)
(*                         [uva_mapped] (a vpn is a 27-bit page number) or *)
(*                         from [uva_live] under [usz_ok];                 *)
(*   [uva_mapped_window]   so [svpn_of] reads the va's page number back,   *)
(*                         and every offset of a MAPPED page is mapped.    *)
(* ===================================================================== *)

Lemma uva_of_image_lt (pt : uptd) (sz va : Z) :
  upt_map_wf (ud_um pt) -> usz_ok sz ->
  (uva_mapped pt va \/ uva_live sz va) ->
  (0 <= va < 549755813888)%Z.
Proof.
  intros Hwf Hsz [ (vpn & w & j & Hl & Hj & ->) | Hlv ].
  - pose proof (upt_map_wf_vpn_lt _ _ _ Hwf Hl) as Hv.
    pose proof (proj1 (bv_unsigned_in_range _ vpn)) as Hv0.
    pose proof (Nat2Z.is_nonneg j) as Hj0.
    pose proof (proj1 (Nat2Z.inj_lt j 4096) Hj) as Hjz.
    change (Z.of_nat 4096) with 4096%Z in Hjz.
    lia.
  - unfold usz_ok, uva_live in *. lia.
Qed.

Lemma uva_mapped_window (pt : uptd) (pc : mword 64) (j : nat) (w : mword 64) :
  ud_um pt !! svpn_of pc = Some w ->
  (bv_unsigned pc < 549755813888)%Z ->
  (bv_unsigned pc mod 4096 + Z.of_nat j < 4096)%Z ->
  uva_mapped pt (uint pc + Z.of_nat j)%Z.
Proof.
  intros Hl Hb Hoff.
  pose proof (proj1 (bv_unsigned_in_range _ pc)) as Hpc0.
  pose proof (Z.mod_pos_bound (bv_unsigned pc) 4096 ltac:(lia)) as Hmb.
  assert (Hoff0 : (0 <= bv_unsigned pc mod 4096 + Z.of_nat j)%Z) by lia.
  exists (svpn_of pc), w, (Z.to_nat (bv_unsigned pc mod 4096 + Z.of_nat j)).
  split; [ exact Hl | ].
  split; [ lia | ].
  rewrite (Z2Nat.id _ Hoff0).
  rewrite svpn_of_unsigned_gen.
  rewrite (Z.mod_small (bv_unsigned pc / 4096) 134217728);
    [ | split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ] ].
  rewrite uint_unsigned.
  pose proof (Z_div_mod_eq_full (bv_unsigned pc) 4096) as Hdm.
  lia.
Qed.

(* ...and the transport itself: on a mapped va the two images agree. *)
Lemma mapped_lookup_sub (pt : uptd) (M Mp : gmap Z (bv 8)) (va : Z) (b : bv 8) :
  Mp ⊆ M -> dom Mp = uva_dom pt -> uva_mapped pt va ->
  M !! va = Some b -> Mp !! va = Some b.
Proof.
  intros Hsub Hdom Hm Hb.
  assert (Hs : is_Some (Mp !! va))
    by (apply elem_of_dom; rewrite Hdom; by apply elem_of_uva_dom).
  destruct Hs as [b' Hb'].
  pose proof (lookup_weaken _ _ _ _ Hb' Hsub) as H1.
  rewrite Hb in H1. injection H1 as ->. exact Hb'.
Qed.
