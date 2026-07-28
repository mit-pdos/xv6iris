(* ProcPt.v -- THE PROCESS PAGE TABLE: one definition of what [struct
   proc]'s [pagetable] field points at.

   WHAT A PROCESS PAGE TABLE IS (xv6 proc_pagetable()):
   - the TRAMPOLINE page at the top of the VA space (R|X, U=0);
   - the TRAPFRAME page one below it (R|W, U=0), mapping THIS process's
     [p->trapframe];
   - whatever user pages sit below the trapframe;
   - nothing else -- every other vpn blocks;
   and the process OWNS the pages it maps (the trapframe page and every
   user page), so those pages are not aliased by another table and can go
   back to kalloc when the process exits.

   THIS FILE IS THE KERNEL-FACING HALF; THE PURE / TRANSLATION HALF IS
   ALREADY BUILT.  There is no second description of a user table here:

     - [UptTree.upt_tree_spec uroot tfp um] is THE mapping spec (trampoline
       leaf at [tramp_vpn], [pte_tf tfp] at [tf_vpn], the abstract user map
       [um] below, blocked elsewhere, every leaf modulo A/D), with
       [upt_map_wf um] its well-formedness;
     - [UptTree.utlb_inv_pt uroot tfp um] is that table INSTALLED in satp
       (the [tlb_inv_pt] mirror), and [PtTree.pt_frame (upt_tree_spec …)]
       is the same table PARKED (fully owned, not installed) -- which is
       exactly the form [UserretAllPt.wp_userret_pt] consumes;
     - [UserPtTree.uptd] is the descriptor record and [UserPtTree.upt_acc_wf]
       the per-leaf User-access classification the user-execution machinery
       needs.

   What this file ADDS is the part neither had: the table's PAGE FOOTPRINT
   and its OWNERSHIP, the two [struct proc] cells, and the validity
   conjunct that makes the footprint kernel-reachable at all.

   THREE DESIGN DECISIONS worth stating.

   1. THE FOOTPRINT IS DERIVED FROM [um], NOT CARRIED ALONGSIDE IT.  A
      leaf word names a ppn ([pte_ppn]); the pages the table hands the
      process are [um_ppns um], and their bytes [um_pas um].  So the
      coverage side condition the user-execution lemmas take
      ([udata_cov um data]) holds by construction ([um_pas_cov]) instead
      of being a field-to-field coupling inside the descriptor.

   2. THE PAGES ARE OWNED IN THE PHYSICAL TIER ([↦ₚ], [phys_page_own]).
      A page a user table maps is reachable at TWO virtual addresses --
      its identity kernel va (that is the pointer kalloc handed out, and
      how copyin/copyout/kfree reach it) and its user va -- so neither
      belongs baked into the resource, which is what the VA-based
      [KallocInv.page_own] ([↦ₘ]) would do.  The kernel's [page_own] view
      is recovered on demand, per page, by the claim-keyed tier bridge
      (KMap.v's [mem_ident_phys] / [phys_ident_mem]); [udata_own] -- what
      user-mode execution reads and writes -- is already this tier, so the
      satp switch needs no conversion at all.

   3. VALIDITY CARRIES "EVERY MAPPED PAGE IS A KALLOC PAGE"
      ([um_pages_valid]).  This is new content, and it is load-bearing
      twice over: it is what keeps the tier bridge of (2) available (the
      bridge is [kmap_static]-keyed, and [page_in_range_addr_is_kdata] +
      [kdata_svpn_class] supply that for a kalloc page), and it is what
      makes the pages re-freeable on exit (the same role [page_valid]
      plays in [is_pipe]).  Without it a "valid" user table could map
      kernel text or a device page into user space.

   AND ONE NON-DECISION.  Nothing here says the user pages are distinct
   from the table's own node pages, or from the trapframe page, or from
   another process's pages.  It does not have to: those are all SEPARATING
   conjuncts of the same predicate, so an overlap makes [proc_pt] simply
   unsatisfiable.  Carrying the disjointness by separation rather than as
   pure side conditions is the same technique as memmove's non-overlap
   hypothesis (claude-notes/completed/memmove.md).

   The trapframe PAGE's bytes are NOT owned here.  They used to be, as a
   contents-existential [proc_tf_own] conjunct kept separate "precisely so
   it can later gain STRUCTURE".  That day came: the syscall-argument path
   needs the VALUE of [tf->aN], which a contents-existential page cannot
   supply, so the page moved out to [ProcInv.tf_page], which carries all 36
   [struct trapframe] words with their values plus the rest of the 4K as
   anonymous bytes.  What stays here is the table's *description* of it --
   [upt_tree_spec] still maps TRAPFRAME to [ud_tfp], and [proc_pt_wf] still
   demands [page_valid (page_base P.(ud_tfp))] -- and the [p->trapframe]
   CELL in [proc_pt_at].  Mapping and cell stay; bytes leave. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import ByteCursor.   (* the add/sub/mword_of_int unsigned laws *)
Require Import SmodePte.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import KptPt.
Require Import KMap.
Require Import Pt4kWalk.
Require Import PtBuild.
Require Import PtAdBits.
Require Import KptExecMap.
Require Import TrampPt.
Require Import KptTree.   (* [pte_tramp] and its A/D-variant flag byte *)
Require Import UptTree.
Require Import UserPtTree.
Require Import ProcPt.
Require Import KallocInv.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Leaf geometry: the page a leaf word names, and that page's base.    *)
(* ===================================================================== *)

(* the physical page number a leaf word names, spelled exactly as the walk
   layer produces it ([CommonWalk.u_walk_pa], [UptTree.tf_variant_ppn]) *)
Definition pte_ppn (w : mword 64) : mword 44 :=
  autocast (T := mword) ((autocast (T := mword)
    (PPN_of_PTE (w : mword 64))) : mword 44).

(* the base address of a physical page.  This is simultaneously the page's
   physical base and its IDENTITY KERNEL VA -- i.e. the pointer value
   kalloc returned and the one [p->pagetable] / [p->trapframe] hold. *)
Definition page_base (ppn : mword 44) : mword 64 :=
  zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12)).

Lemma page_base_ppn_unsigned (ppn : mword 44) :
  bv_unsigned (page_base ppn) = bv_unsigned ppn * 4096.
Proof. apply page_base_unsigned. Qed.

(* a page's bytes never wrap the address space: ppn < 2^44, so
   ppn*4096 + 4096 <= 2^56. *)
Lemma page_base_no_wrap (ppn : mword 44) (j : nat) :
  (j < 4096)%nat -> bv_unsigned (page_base ppn) + Z.of_nat j < 18446744073709551616.
Proof.
  intros Hj.
  rewrite page_base_ppn_unsigned.
  pose proof (bv_unsigned_in_range _ ppn) as Hr.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr. lia.
Qed.

Lemma pa_add_page_unsigned (ppn : mword 44) (j : nat) :
  (j < 4096)%nat ->
  bv_unsigned (pa_add (page_base ppn) j) = bv_unsigned ppn * 4096 + Z.of_nat j.
Proof.
  intros Hj.
  rewrite <- uint_unsigned.
  rewrite (uint_pa_add (page_base ppn) j);
    [| rewrite uint_unsigned; exact (page_base_no_wrap ppn j Hj)].
  rewrite uint_unsigned page_base_ppn_unsigned. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* PTE2PA, i.e. [srli 10; slli 12] -- how the MACHINE computes the same    *)
(* page base out of a leaf word.                                          *)
(*                                                                        *)
(*   THIS IS NOT UNCONDITIONAL.  The shift pair keeps bits 61:54 of the    *)
(*   word (they land at 63:56 of the result) while [pte_ppn] is bits       *)
(*   53:10, so the two agree exactly when [uint w < 2^54] -- which is what *)
(*   [PtTree.pte_hi_zero] gets out of a model-VALID leaf.                  *)
(* ---------------------------------------------------------------------- *)

Lemma ppn_unsigned (w : mword 64) :
  bv_unsigned (pte_ppn w) = bv_unsigned w / 1024 mod 17592186044416.
Proof.
  unfold pte_ppn. rewrite !autocast_id.
  unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply (subrange_dec_unsigned w 53 10 _ _);
    [lia | lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Local Lemma ppo_shiftr10 (v : mword 64) : bv_unsigned (shiftr v 10) = bv_unsigned v / 1024.
Proof.
  unfold shiftr, with_word, get_word, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word
             (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 10))) with 10
    by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2; [reflexivity | lia].
Qed.

Local Lemma ppo_shiftl12 (v : mword 64) :
  bv_unsigned (shiftl v 12) = bv_unsigned v * 4096 mod 18446744073709551616.
Proof.
  unfold shiftl, with_word, get_word, MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word
             (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12))) with 12
    by (vm_compute; reflexivity).
  rewrite Z.shiftl_mul_pow2; [reflexivity | lia].
Qed.

Local Lemma z_pte2pa (x : Z) :
  0 <= x -> x < 18014398509481984 ->
  x / 1024 * 4096 mod 18446744073709551616 = x / 1024 mod 17592186044416 * 4096.
Proof.
  intros H0 H1.
  assert (Hq : 0 <= x / 1024 < 17592186044416).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small (x / 1024) 17592186044416 Hq).
  apply Z.mod_small. lia.
Qed.

Lemma pte2pa (w : mword 64) (n m : Z) (s10 : mword n) (s12 : mword m) :
  int_of_mword false s10 = 10 -> int_of_mword false s12 = 12 ->
  bv_unsigned w < 18014398509481984 ->
  shift_bits_left (shift_bits_right w s10) s12 = page_base (pte_ppn w).
Proof.
  intros H10 H12 Hlt.
  apply bv_eq.
  unfold shift_bits_left, shift_bits_right. rewrite H10. rewrite H12.
  rewrite ppo_shiftl12. rewrite ppo_shiftr10.
  rewrite page_base_ppn_unsigned. rewrite ppn_unsigned.
  apply z_pte2pa; [ exact (proj1 (bv_unsigned_in_range _ w)) | exact Hlt ].
Qed.

(* ===================================================================== *)
(* §2 The PAGE FOOTPRINT of a user map: the pages it hands the process,   *)
(*    and their bytes.  Both DERIVED from [um] -- nothing to keep in      *)
(*    sync, and [udata_cov] becomes a theorem (§4).                       *)
(* ===================================================================== *)

Definition um_ppns (um : gmap (mword 27) (mword 64)) : gset (mword 44) :=
  list_to_set ((fun vw => pte_ppn (snd vw)) <$> map_to_list um).

Lemma elem_of_um_ppns (um : gmap (mword 27) (mword 64)) (ppn : mword 44) :
  ppn ∈ um_ppns um <-> exists vpn w, um !! vpn = Some w /\ pte_ppn w = ppn.
Proof.
  unfold um_ppns.
  rewrite elem_of_list_to_set elem_of_list_fmap.
  split.
  - intros [[vpn w] [Heq Hin]]. cbn in Heq.
    exists vpn, w. split; [| exact (eq_sym Heq)].
    apply elem_of_map_to_list. exact Hin.
  - intros (vpn & w & Hl & Heq).
    exists (vpn, w). split; [exact (eq_sym Heq) |].
    apply elem_of_map_to_list. exact Hl.
Qed.

(* the 4096 byte addresses of one page *)
Definition page_pas (ppn : mword 44) : gset Arch.pa :=
  list_to_set ((fun j => pa_add (page_base ppn) j) <$> seq 0 4096).

Lemma elem_of_page_pas (ppn : mword 44) (a : Arch.pa) :
  a ∈ page_pas ppn <-> exists j, (j < 4096)%nat /\ a = pa_add (page_base ppn) j.
Proof.
  unfold page_pas.
  rewrite elem_of_list_to_set elem_of_list_fmap.
  split.
  - intros [j [Heq Hin]]. apply elem_of_seq in Hin.
    exists j. split; [lia | exact Heq].
  - intros (j & Hj & Heq).
    exists j. split; [exact Heq |]. apply elem_of_seq. lia.
Qed.

(* the bytes of a SET of pages *)
Definition pages_pas (T : gset (mword 44)) : gset Arch.pa :=
  ⋃ (page_pas <$> elements T).

Lemma elem_of_pages_pas (T : gset (mword 44)) (a : Arch.pa) :
  a ∈ pages_pas T <-> exists ppn, ppn ∈ T /\ a ∈ page_pas ppn.
Proof.
  unfold pages_pas.
  rewrite elem_of_union_list.
  split.
  - intros (X & HX & Ha).
    apply elem_of_list_fmap in HX. destruct HX as (ppn & -> & Hppn).
    exists ppn. split; [| exact Ha].
    apply elem_of_elements. exact Hppn.
  - intros (ppn & Hppn & Ha).
    exists (page_pas ppn). split; [| exact Ha].
    apply elem_of_list_fmap. exists ppn. split; [reflexivity |].
    apply elem_of_elements. exact Hppn.
Qed.

(* the two set equations the ownership bridge (§5) inducts along *)
Lemma pages_pas_empty : pages_pas ∅ = ∅.
Proof. unfold pages_pas. rewrite elements_empty. reflexivity. Qed.

Lemma pages_pas_insert (ppn : mword 44) (T : gset (mword 44)) :
  pages_pas ({[ppn]} ∪ T) = page_pas ppn ∪ pages_pas T.
Proof.
  apply set_eq. intros a.
  rewrite elem_of_union elem_of_pages_pas elem_of_pages_pas.
  split.
  - intros (q & Hq & Ha).
    apply elem_of_union in Hq as [Hq | Hq].
    + apply elem_of_singleton in Hq as ->. left. exact Ha.
    + right. exists q. split; [exact Hq | exact Ha].
  - intros [Ha | (q & Hq & Ha)].
    + exists ppn. split; [| exact Ha].
      apply elem_of_union. left. apply elem_of_singleton. reflexivity.
    + exists q. split; [| exact Ha].
      apply elem_of_union. right. exact Hq.
Qed.

(* the byte footprint of the whole user map *)
Definition um_pas (um : gmap (mword 27) (mword 64)) : gset Arch.pa :=
  pages_pas (um_ppns um).

Lemma elem_of_um_pas (um : gmap (mword 27) (mword 64)) (a : Arch.pa) :
  a ∈ um_pas um <-> exists ppn, ppn ∈ um_ppns um /\ a ∈ page_pas ppn.
Proof. apply elem_of_pages_pas. Qed.

(* ---- disjointness, all of it from [pa_add_page_unsigned] -------------- *)

(* distinct offsets inside one page are distinct addresses *)
Local Lemma z_page_off_inj (x : Z) (j k : nat) :
  x * 4096 + Z.of_nat j = x * 4096 + Z.of_nat k -> j = k.
Proof. lia. Qed.

Lemma page_pa_inj (ppn : mword 44) (j k : nat) :
  (j < 4096)%nat -> (k < 4096)%nat ->
  pa_add (page_base ppn) j = pa_add (page_base ppn) k -> j = k.
Proof.
  intros Hj Hk Heq.
  assert (Hu : bv_unsigned (pa_add (page_base ppn) j)
             = bv_unsigned (pa_add (page_base ppn) k))
    by (rewrite Heq; reflexivity).
  rewrite (pa_add_page_unsigned ppn j Hj) (pa_add_page_unsigned ppn k Hk) in Hu.
  exact (z_page_off_inj _ j k Hu).
Qed.

(* distinct pages are disjoint blocks *)
Local Lemma z_page_block_inj (x y : Z) (j k : nat) :
  (j < 4096)%nat -> (k < 4096)%nat ->
  x * 4096 + Z.of_nat j = y * 4096 + Z.of_nat k -> x = y.
Proof. intros Hj Hk Heq. lia. Qed.

Lemma page_pas_disjoint (p q : mword 44) : p <> q -> page_pas p ## page_pas q.
Proof.
  intros Hne. apply elem_of_disjoint. intros a Hp Hq.
  apply elem_of_page_pas in Hp as (j & Hj & Haj).
  apply elem_of_page_pas in Hq as (k & Hk & Hak).
  apply Hne. apply bv_eq.
  assert (Hu : bv_unsigned (pa_add (page_base p) j)
             = bv_unsigned (pa_add (page_base q) k))
    by (rewrite <- Haj, <- Hak; reflexivity).
  rewrite (pa_add_page_unsigned p j Hj) (pa_add_page_unsigned q k Hk) in Hu.
  exact (z_page_block_inj _ _ j k Hj Hk Hu).
Qed.

Lemma page_pas_disjoint_pages (ppn : mword 44) (T : gset (mword 44)) :
  ppn ∉ T -> page_pas ppn ## pages_pas T.
Proof.
  intros Hnin. apply elem_of_disjoint. intros a Ha Hs.
  apply elem_of_pages_pas in Hs as (q & Hq & Haq).
  destruct (decide (ppn = q)) as [-> | Hne]; [exact (Hnin Hq) |].
  pose proof (page_pas_disjoint ppn q Hne) as Hd.
  apply elem_of_disjoint in Hd. exact (Hd a Ha Haq).
Qed.

(* the descriptor-level footprint (the field [uptd] no longer needs) *)
Definition ud_pas (P : uptd) : gset Arch.pa := um_pas P.(ud_um).

(* a table with no user memory -- what proc_pagetable() delivers -- has an
   empty footprint *)
Lemma not_elem_of_um_ppns_empty (ppn : mword 44) :
  ppn ∉ um_ppns (∅ : gmap (mword 27) (mword 64)).
Proof.
  intros Hin. apply elem_of_um_ppns in Hin.
  destruct Hin as (vpn & w & Hl & _). rewrite lookup_empty in Hl. discriminate.
Qed.

Lemma um_ppns_empty : um_ppns (∅ : gmap (mword 27) (mword 64)) = ∅.
Proof.
  apply set_eq. intros ppn.
  split; intros Hin; exfalso;
    first [ exact (not_elem_of_um_ppns_empty ppn Hin)
          | exact (not_elem_of_empty ppn Hin) ].
Qed.

(* ===================================================================== *)
(* §2b The one-page mapping step, at an ARBITRARY permission.             *)
(*                                                                        *)
(*     [uvm_pte perm r] is the leaf a ONE-PAGE mappages run writes for the *)
(*     kalloc page [r] -- spelled EXACTLY as SpecMappages' [ppn0]/post at  *)
(*     [npages := 1], [k := 1], so a caller meets mappages' postcondition  *)
(*     syntactically.  vmfault is the instance at [perm := 22]             *)
(*     (PTE_W|PTE_U|PTE_R); uvmalloc's is [perm := xperm | 18] and so is   *)
(*     not a literal, which is why the whole leaf layer below is stated    *)
(*     over [perm] with the classification packaged as [uvm_perm_ok]       *)
(*     (§2c) -- a pure premise a caller discharges by [vm_compute] at its  *)
(*     own concrete permission.                                            *)
(* ===================================================================== *)

Definition uvm_pte (perm : Z) (r : mword 64) : mword 64 :=
  mappages_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) perm 0.

(* vmfault's leaf: PTE_R|PTE_W|PTE_U (mappages ors in PTE_V) *)
Definition vmfault_pte (r : mword 64) : mword 64 := uvm_pte 22 r.

Definition uptd_insert_perm (P : uptd) (perm : Z) (vpn : mword 27) (r : mword 64) : uptd :=
  UPTD P.(ud_root) P.(ud_tfp) (<[vpn := uvm_pte perm r]> P.(ud_um))
       (um_pas (<[vpn := uvm_pte perm r]> P.(ud_um))).

Definition uptd_insert (P : uptd) (vpn : mword 27) (r : mword 64) : uptd :=
  uptd_insert_perm P 22 vpn r.

(* one fresh vpn adds exactly one page to the footprint.  (The freshness
   hypothesis is needed: without it the insert would DROP the page the old
   entry named.) *)
Lemma um_ppns_insert (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  um !! vpn = None ->
  um_ppns (<[vpn := w]> um) = {[pte_ppn w]} ∪ um_ppns um.
Proof.
  (* NOTE: proved with explicit [apply]s rather than [rewrite elem_of_union
     elem_of_singleton !elem_of_um_ppns] -- that setoid-rewrite chain costs
     ~1.8 s here. *)
  intros Hn. apply set_eq. intros q. split.
  - intros Hq. apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hl & Hq).
    apply lookup_insert_Some in Hl. destruct Hl as [(_ & Hw) | (_ & Hl)].
    + subst x. apply elem_of_union. left.
      apply elem_of_singleton. exact (eq_sym Hq).
    + apply elem_of_union. right. apply elem_of_um_ppns.
      exists v, x. split; [exact Hl | exact Hq].
  - intros Hq. apply elem_of_union in Hq. apply elem_of_um_ppns.
    destruct Hq as [Hq | Hq].
    + apply elem_of_singleton in Hq. exists vpn, w.
      split; [apply lookup_insert | exact (eq_sym Hq)].
    + apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hl & Hq).
      exists v, x. split; [| exact Hq].
      rewrite lookup_insert_ne; [exact Hl |].
      intro He. rewrite <- He in Hl. rewrite Hn in Hl. discriminate.
Qed.

(* --------------------------------------------------------------------- *)
(* THE USER MAP ONLY GROWS.  A function that may fault pages in during its *)
(* run (copyin, copyout, and anything built over them) cannot name the     *)
(* descriptor it ends with -- how many faults it took depends on the       *)
(* table it started from.  What it CAN promise is that the descriptor it   *)
(* hands back extends the one it was given: same root (so [p->pagetable]   *)
(* still holds [page_base ud_root]), same trapframe, and a user map that   *)
(* only gained entries.  [ud_data] is deliberately unconstrained -- it is  *)
(* the derived footprint, and the field is slated for retirement.          *)
(* --------------------------------------------------------------------- *)
Definition uptd_ext (P P' : uptd) : Prop :=
  P'.(ud_root) = P.(ud_root) /\ P'.(ud_tfp) = P.(ud_tfp) /\
  P.(ud_um) ⊆ P'.(ud_um).

Lemma uptd_ext_refl (P : uptd) : uptd_ext P P.
Proof. split; [reflexivity |]. split; [reflexivity | reflexivity]. Qed.

Lemma uptd_ext_trans (P Q R : uptd) :
  uptd_ext P Q -> uptd_ext Q R -> uptd_ext P R.
Proof.
  intros (H1 & H2 & H3) (H4 & H5 & H6).
  split; [rewrite H4; exact H1 |].
  split; [rewrite H5; exact H2 | exact (transitivity H3 H6)].
Qed.

Lemma uptd_ext_insert (P : uptd) (vpn : mword 27) (r : mword 64) :
  P.(ud_um) !! vpn = None -> uptd_ext P (uptd_insert P vpn r).
Proof.
  intros Hn. unfold uptd_ext, uptd_insert. cbn [ud_root ud_tfp ud_um].
  split; [reflexivity |]. split; [reflexivity |].
  apply insert_subseteq. exact Hn.
Qed.

(* ===================================================================== *)
(* §2c THE MAPPED LEAF, CLASSIFIED -- at an arbitrary permission.          *)
(*                                                                        *)
(*     [uvm_pte perm r] is [mk_pte] of the ppn of [r] at flag byte         *)
(*     [Z.lor perm 1]; the A/D variants add bit 6 and bit 7.  What the     *)
(*     user-page-table invariant needs of such a leaf is exactly           *)
(*     [uvm_perm_ok perm]:                                                 *)
(*       - mappages' own [mappages_perm_ok] precondition,                  *)
(*       - every A/D variant is a proper 4K leaf ([upt_map_wf]'s clause),  *)
(*       - every user access is decided -- passes or is denied, never      *)
(*         stuck ([upt_acc_wf]'s clause).                                  *)
(*     It is a pure, ppn-INDEPENDENT property of the permission, so a      *)
(*     caller discharges it once by [vm_compute] at its own concrete       *)
(*     permission; the instances xv6 actually uses are proved below        *)
(*     (18 = R|U, 22 = R|W|U, 26 = R|X|U, 30 = R|W|X|U).                   *)
(*                                                                        *)
(*     The dispatch recipe is UptTree §1's: [pte_set_ad_zext_concat] turns *)
(*     a variant back into a [mk_pte] at an ADJUSTED flag constant, then   *)
(*     the flag byte / ext field are read off symbolically in the ppn      *)
(*     ([mk_pte_flags1024] / [mk_pte_ext]) and every predicate is one      *)
(*     [vm_compute] per A/D case.  [mxr]/[do_sum] stay SYMBOLIC (at User   *)
(*     [do_sum] is never consulted), so each access is 4 A/D cases, not    *)
(*     16 -- unlike KptPt's Supervisor [kperm_check_*].                    *)
(* ===================================================================== *)

(* ---- two generic [Z] range facts (mword-free, so [lia] behaves) ------ *)

(* NOTE: [lia] is never let near a goal mentioning [Z.lor]/[Z.land] here --
   the zify hook that arrives transitively with [bitvector.tactics] answers
   "Cannot find witness" on them (durable-notes.md).  Every step below feeds
   [lia] only numeral/variable goals. *)

Local Lemma z_pos_of_nonzero (z : Z) : 0 <= z -> z <> 0 -> 0 < z.
Proof.
  intros H1 H2.
  destruct (proj1 (Z.lt_eq_cases 0 z) H1) as [H | H];
    [exact H | exfalso; apply H2; symmetry; exact H].
Qed.

Local Lemma z_log2_lt (n z : Z) : 0 < n -> 0 <= z -> z < 2 ^ n -> Z.log2 z < n.
Proof.
  intros Hn Hz0 Hz. destruct (Z.eq_dec z 0) as [-> | Hnz].
  - rewrite Z.log2_nonpos; [exact Hn | apply Z.le_refl].
  - exact (proj1 (Z.log2_lt_pow2 z n (z_pos_of_nonzero z Hz0 Hnz)) Hz).
Qed.

Lemma z_lor_pow2 (n x y : Z) : 0 < n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
  0 <= Z.lor x y < 2 ^ n.
Proof.
  intros Hn (Hx0 & Hx) (Hy0 & Hy).
  assert (Hge : 0 <= Z.lor x y)
    by (apply Z.lor_nonneg; split; [exact Hx0 | exact Hy0]).
  split; [exact Hge |].
  destruct (Z.eq_dec (Z.lor x y) 0) as [He | Hne].
  { rewrite He. apply Z.pow_pos_nonneg; lia. }
  apply (proj2 (Z.log2_lt_pow2 _ n (z_pos_of_nonzero _ Hge Hne))).
  rewrite Z.log2_lor; [| exact Hx0 | exact Hy0].
  apply Z.max_lub_lt;
    [exact (z_log2_lt n x Hn Hx0 Hx) | exact (z_log2_lt n y Hn Hy0 Hy)].
Qed.

Lemma z_land_pow2 (n x y : Z) : 0 < n -> 0 <= x < 2 ^ n -> 0 <= y ->
  0 <= Z.land x y < 2 ^ n.
Proof.
  intros Hn (Hx0 & Hx) Hy0.
  assert (Hge : 0 <= Z.land x y)
    by (apply Z.land_nonneg; left; exact Hx0).
  split; [exact Hge |].
  destruct (Z.eq_dec (Z.land x y) 0) as [He | Hne].
  { rewrite He. apply Z.pow_pos_nonneg; lia. }
  apply (proj2 (Z.log2_lt_pow2 _ n (z_pos_of_nonzero _ Hge Hne))).
  apply (Z.le_lt_trans _ (Z.min (Z.log2 x) (Z.log2 y)));
    [exact (Z.log2_land x y Hx0 Hy0) |].
  apply (Z.le_lt_trans _ (Z.log2 x));
    [apply Z.le_min_l | exact (z_log2_lt n x Hn Hx0 Hx)].
Qed.

(* the flag byte of the [a]/[d] variant *)
Definition uvm_flags (perm : Z) (a d : mword 1) : Z :=
  Z.lor (Z.land (Z.lor perm 1) 831)
        (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7)).

Lemma uvm_flags_bound (perm : Z) (a d : mword 1) :
  (0 <= perm < 1024)%Z -> (0 <= uvm_flags perm a d < 1024)%Z.
Proof.
  intros Hp.
  pose proof (pb_lor1_range perm Hp) as Hf.
  change 1024 with (2 ^ 10)%Z in *.
  unfold uvm_flags. apply z_lor_pow2; [lia | |].
  - apply z_land_pow2; [lia | exact Hf | lia].
  - apply z_lor_pow2; [lia | |];
      (destruct (mword1_cases a) as [-> | ->];
       destruct (mword1_cases d) as [-> | ->]; vm_compute; intuition congruence).
Qed.

(* the leaf in [mk_pte] shape *)
Lemma uvm_pte_mk (perm : Z) (r : mword 64) :
  uvm_pte perm r
  = mk_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44)
      (Z.lor perm 1).
Proof. unfold uvm_pte. rewrite mappages_pte_0. reflexivity. Qed.

Lemma uvm_variant_mk (perm : Z) (r : mword 64) (a d : mword 1) :
  (0 <= Z.lor perm 1 < 1024)%Z ->
  pte_set_ad (uvm_pte perm r) a d
  = mk_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44)
      (uvm_flags perm a d).
Proof.
  intros Hf. rewrite uvm_pte_mk. unfold mk_pte, uvm_flags.
  apply (pte_set_ad_zext_concat _ (Z.lor perm 1) a d). exact Hf.
Qed.

Lemma uvm_variant_flags (perm : Z) (r : mword 64) (a d : mword 1) :
  (0 <= perm < 1024)%Z ->
  subrange_vec_dec (pte_set_ad (uvm_pte perm r) a d) 7 0
  = (mword_of_int (uvm_flags perm a d) : mword 8).
Proof.
  intros Hp. rewrite (uvm_variant_mk perm r a d (pb_lor1_range perm Hp)).
  apply mk_pte_flags1024. exact (uvm_flags_bound perm a d Hp).
Qed.

Lemma uvm_variant_ext (perm : Z) (r : mword 64) (a d : mword 1) :
  (0 <= perm < 1024)%Z ->
  ext_bits_of_PTE (pte_set_ad (uvm_pte perm r) a d) = Mk_PTE_Ext (mword_of_int 0).
Proof.
  intros Hp. rewrite pte_set_ad_ext. rewrite uvm_pte_mk.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity | exact (pb_lor1_range perm Hp)].
Qed.

(* THE PERMISSION CONTRACT.  Everything the user-table invariant asks of a
   leaf built at [perm], for every page and every A/D variant. *)
Definition uvm_perm_ok (perm : Z) : Prop :=
  mappages_perm_ok perm /\
  (forall (r : mword 64) (a d : mword 1),
     pte_valid (pte_set_ad (uvm_pte perm r) a d) /\
     pte_leaf (pte_set_ad (uvm_pte perm r) a d) /\
     pte_no_napot (pte_set_ad (uvm_pte perm r) a d) /\
     pte_pbmt0 (pte_set_ad (uvm_pte perm r) a d)) /\
  (forall (r : mword 64) (acc : MemoryAccessType mem_payload),
     u_acc acc -> uleaf_ok acc (uvm_pte perm r) \/ uleaf_denied acc (uvm_pte perm r)).

(* At a CONCRETE permission every obligation is closed by computation; the
   only symbolic data left are the ppn (carried through [mk_pte]) and, in
   the access clause, [mxr]/[do_sum]/the AMO op.  [Hp] is the permission's
   range fact, asserted once per instance so the two rewrites never carry an
   inline [ltac:] premise (the optimization.md rule). *)
Local Ltac uvm_ad_cases a d :=
  destruct (mword1_cases a) as [-> | ->];
  destruct (mword1_cases d) as [-> | ->].

Local Ltac uvm_leaf_tac Hp :=
  intros r a d; repeat split;
  [ intros s; unfold Mk_PTE_Flags;
    rewrite (uvm_variant_flags _ r a d Hp); rewrite (uvm_variant_ext _ r a d Hp);
    uvm_ad_cases a d; vm_compute; reflexivity
  | unfold pte_leaf, Mk_PTE_Flags;
    rewrite (uvm_variant_flags _ r a d Hp);
    uvm_ad_cases a d; vm_compute; reflexivity
  | unfold pte_no_napot; rewrite (uvm_variant_ext _ r a d Hp); apply kpt_extN_red
  | unfold pte_pbmt0; rewrite (uvm_variant_ext _ r a d Hp);
    vm_compute; reflexivity ].

Local Ltac uvm_acc_one Hp :=
  intros a d mxr do_sum s; unfold Mk_PTE_Flags;
  rewrite (uvm_variant_flags _ _ a d Hp); rewrite (uvm_variant_ext _ _ a d Hp);
  uvm_ad_cases a d; vm_compute; reflexivity.

Local Ltac uvm_perm_tac p :=
  assert (Hp : (0 <= p < 1024)%Z) by lia;
  split; [ unfold mappages_perm_ok; split; [lia|];
           split; [intro s; vm_compute; reflexivity|];
           split; [vm_compute; reflexivity|];
           split; [vm_compute; reflexivity | vm_compute; reflexivity]
         | split; [ uvm_leaf_tac Hp
                  | intros r acc [-> | [-> | [-> | [-> | [-> | (op & ->)]]]]];
                    first [ left; uvm_acc_one Hp | right; uvm_acc_one Hp ] ] ].

(* PTE_R|PTE_U -- exec's read-only segments *)
Lemma uvm_perm_ok_18 : uvm_perm_ok 18.
Proof. uvm_perm_tac 18. Qed.

(* PTE_R|PTE_W|PTE_U -- vmfault, sbrk/growproc *)
Lemma uvm_perm_ok_22 : uvm_perm_ok 22.
Proof. uvm_perm_tac 22. Qed.

(* PTE_R|PTE_X|PTE_U -- exec's text *)
Lemma uvm_perm_ok_26 : uvm_perm_ok 26.
Proof. uvm_perm_tac 26. Qed.

(* PTE_R|PTE_W|PTE_X|PTE_U *)
Lemma uvm_perm_ok_30 : uvm_perm_ok 30.
Proof. uvm_perm_tac 30. Qed.

(* ---- the vmfault instance, as the tree already names it -------------- *)

Lemma vmf_perm_ok22 : mappages_perm_ok 22.
Proof. exact (proj1 uvm_perm_ok_22). Qed.

Lemma vmfault_pte_mk (r : mword 64) :
  vmfault_pte r
  = mk_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) 23.
Proof. unfold vmfault_pte. rewrite uvm_pte_mk. reflexivity. Qed.

Lemma vmfault_variant (r : mword 64) (a d : mword 1) :
  pte_valid (pte_set_ad (vmfault_pte r) a d) /\
  pte_leaf (pte_set_ad (vmfault_pte r) a d) /\
  pte_no_napot (pte_set_ad (vmfault_pte r) a d) /\
  pte_pbmt0 (pte_set_ad (vmfault_pte r) a d).
Proof. exact (proj1 (proj2 uvm_perm_ok_22) r a d). Qed.

Lemma vmfault_uleaf (r : mword 64) (acc : MemoryAccessType mem_payload) :
  u_acc acc -> uleaf_ok acc (vmfault_pte r) \/ uleaf_denied acc (vmfault_pte r).
Proof. exact (proj2 (proj2 uvm_perm_ok_22) r acc). Qed.

(* ---- the geometry roundtrips --------------------------------------- *)

Lemma pte_ppn_mk_pte (ppn : mword 44) (f : Z) :
  0 <= f < 1024 -> pte_ppn (mk_pte ppn f) = ppn.
Proof.
  intros Hf. unfold pte_ppn. rewrite !autocast_id.
  unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id. apply mk_pte_ppn_field. exact Hf.
Qed.

Lemma pte_ppn_uvm (perm : Z) (r : mword 64) :
  (0 <= Z.lor perm 1 < 1024)%Z ->
  pte_ppn (uvm_pte perm r) = autocast (T := mword) (subrange_vec_dec r 55 12).
Proof. intros Hf. rewrite uvm_pte_mk. apply pte_ppn_mk_pte. exact Hf. Qed.

Lemma pte_ppn_vmfault (r : mword 64) :
  pte_ppn (vmfault_pte r) = autocast (T := mword) (subrange_vec_dec r 55 12).
Proof. rewrite vmfault_pte_mk. apply pte_ppn_mk_pte. lia. Qed.

Local Lemma z_lt_4096_mul (x : Z) : x < 72057594037927936 -> x < 4096 * 17592186044416.
Proof. lia. Qed.

(* bits 55:12 of a below-2^56 word ARE its page number: one instance of
   [RiscvExtras.subrange_dec_unsigned] plus the observation that the [mod]
   is vacuous in range. *)
Local Lemma ppo_subrange_55_12 (a : mword 64) :
  bv_unsigned (subrange_vec_dec a 55 12 : mword 44)
  = bv_unsigned a / 4096 mod 17592186044416.
Proof.
  apply (subrange_dec_unsigned a 55 12 _ _);
    [lia | lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Local Lemma ppo_subrange_55_12_unsigned (a : mword 64) :
  bv_unsigned a < 72057594037927936 ->
  bv_unsigned (autocast (T := mword) (subrange_vec_dec a 55 12) : mword 44)
  = bv_unsigned a / 4096.
Proof.
  intros Hlt.
  rewrite autocast_id. rewrite ppo_subrange_55_12.
  apply Z.mod_small.
  split.
  - apply Z.div_pos; [exact (proj1 (bv_unsigned_in_range _ a)) | reflexivity].
  - apply Z.div_lt_upper_bound; [reflexivity | exact (z_lt_4096_mul _ Hlt)].
Qed.

(* the mword-free arithmetic (the zify-hook rule: no [bv_unsigned] in a goal
   [lia] has to see) *)
Local Lemma z_page_base_roundtrip (x : Z) : x mod 4096 = 0 -> x / 4096 * 4096 = x.
Proof. intros H. pose proof (Z_div_mod_eq_full x 4096). lia. Qed.

Local Lemma z_lt_2_56 (x : Z) : x < 2281701376 -> x < 72057594037927936.
Proof. lia. Qed.

Lemma page_base_of_valid (r : mword 64) :
  page_valid r ->
  page_base (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) = r.
Proof.
  intros [Hal Hrng].
  unfold page_aligned, PGSIZE in Hal.
  unfold page_in_range, kmem_hi in Hrng.
  rewrite uint_unsigned in Hal. rewrite uint_unsigned in Hrng.
  apply bv_eq.
  rewrite page_base_ppn_unsigned.
  rewrite (ppo_subrange_55_12_unsigned r (z_lt_2_56 _ (proj2 Hrng))).
  exact (z_page_base_roundtrip _ Hal).
Qed.

(* ---- PGROUNDDOWN: [and_vec va (mword_of_int (-4096))] --------------- *)

Local Lemma ppo_and_vec_unsigned (a b : mword 64) :
  bv_unsigned (and_vec a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof. exact (and_vec64_unsigned a b). Qed.

Local Lemma z_bits_high_64 (x j : Z) :
  0 <= x < 18446744073709551616 -> 64 <= j -> Z.testbit x j = false.
Proof.
  intros Hx Hj. apply Z.bits_above_log2; [lia |].
  assert (Hl : Z.log2 x < 64).
  { destruct (Z.eq_dec x 0) as [-> | Hnz]; [vm_compute; reflexivity |].
    apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))).
    change (2 ^ 64) with 18446744073709551616. lia. }
  lia.
Qed.

(* masking off the low 12 bits of a 64-bit value IS the truncation *)
Local Lemma z_pgd_land (x : Z) :
  0 <= x < 18446744073709551616 ->
  Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (Hm : 18446744073709547520 = Z.shiftl (Z.ones 52) 12)
    by (vm_compute; reflexivity).
  assert (Hd : x - x mod 4096 = Z.shiftl (Z.shiftr x 12) 12).
  { rewrite Z.shiftr_div_pow2; [| lia].
    rewrite Z.shiftl_mul_pow2; [| lia]. change (2 ^ 12) with 4096.
    pose proof (Z_div_mod_eq_full x 4096). lia. }
  rewrite Hm Hd.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  rewrite (Z.shiftl_spec (Z.ones 52) 12 k Hk).
  rewrite (Z.shiftl_spec (Z.shiftr x 12) 12 k Hk).
  destruct (Z_lt_le_dec k 12) as [Hlt | Hge].
  - rewrite (Z.testbit_neg_r (Z.ones 52) (k - 12)); [| lia].
    rewrite (Z.testbit_neg_r (Z.shiftr x 12) (k - 12)); [| lia].
    apply andb_false_r.
  - rewrite (Z.shiftr_spec x 12 (k - 12)); [| lia].
    replace (k - 12 + 12) with k by lia.
    destruct (Z_lt_le_dec k 64) as [Hlt64 | Hge64].
    + rewrite Z.testbit_ones; [| lia].
      replace ((0 <=? k - 12) && (k - 12 <? 52)) with true;
        [ apply andb_true_r
        | symmetry; apply andb_true_iff; split;
            [ apply Z.leb_le; lia | apply Z.ltb_lt; lia ] ].
    + rewrite (z_bits_high_64 x k Hx ltac:(lia)). reflexivity.
Qed.

Lemma pgd_unsigned (va : mword 64) :
  bv_unsigned (and_vec va (mword_of_int (-4096) : mword 64))
  = bv_unsigned va - bv_unsigned va mod 4096.
Proof.
  rewrite ppo_and_vec_unsigned.
  replace (bv_unsigned (mword_of_int (-4096) : mword 64)) with 18446744073709547520
    by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ va) as Hr.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr.
  exact (z_pgd_land _ Hr).
Qed.

Local Lemma ppo_subrange_11_0_unsigned (a : mword 64) :
  bv_unsigned (subrange_vec_dec a 11 0 : mword 12) = bv_unsigned a mod 4096.
Proof. apply (subrange_dec_unsigned_lo0 a 11 4096); [lia | reflexivity]. Qed.

(* a PGROUNDDOWNed value is a multiple of the page size.  Not [Local]: both
   copy loops need it to see that re-masking an already-masked va is the
   identity ([pgd_idem] below), which is what lets them match vmfault's
   postcondition (stated at the RE-masked value). *)
Lemma z_pgd_mod (x : Z) : (x - x mod 4096) mod 4096 = 0.
Proof.
  pose proof (Z_div_mod_eq_full x 4096) as H.
  replace (x - x mod 4096) with (x / 4096 * 4096) by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma pgrounddown_low12 (va : mword 64) :
  subrange_vec_dec (and_vec va (mword_of_int (-4096))) 11 0 = (zeros' 12 : mword 12).
Proof.
  apply bv_eq.
  rewrite ppo_subrange_11_0_unsigned.
  rewrite pgd_unsigned.
  rewrite z_pgd_mod.
  vm_compute (bv_unsigned (zeros' 12 : mword 12)). reflexivity.
Qed.

Local Lemma z_pgd_bound (x : Z) :
  0 <= x -> x < 274877906944 -> x - x mod 4096 + 4096 <= 274877906944.
Proof.
  intros H0 H1.
  pose proof (Z_div_mod_eq_full x 4096) as H.
  pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as Hb.
  lia.
Qed.

Lemma pgrounddown_bound (va : mword 64) :
  (uint va < 2 ^ 38)%Z ->
  (uint (and_vec va (mword_of_int (-4096))) + 4096 <= 2 ^ 38)%Z.
Proof.
  intros Hlt.
  change (2 ^ 38) with 274877906944 in Hlt |- *.
  rewrite uint_unsigned in Hlt. rewrite uint_unsigned.
  rewrite pgd_unsigned.
  exact (z_pgd_bound _ (proj1 (bv_unsigned_in_range _ va)) Hlt).
Qed.

(* ---- the vpn of a PGROUNDDOWNed va, and its MAXVA bound ------------- *)

Local Lemma ppo_subrange_38_0_unsigned (a : mword 64) :
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = bv_unsigned a mod 549755813888.
Proof.
  apply (subrange_dec_unsigned_lo0 a (Z.sub 39 1) 549755813888);
    [lia | vm_compute; reflexivity].
Qed.

Local Lemma z_wrap39_shift (x : Z) :
  ((x mod 549755813888) / 4096) mod 134217728 = (x / 4096) mod 134217728.
Proof.
  pose proof (Z_div_mod_eq_full x 549755813888) as Hdm.
  assert (Hr : x mod 549755813888
             = x + (- (x / 549755813888) * 134217728) * 4096) by lia.
  rewrite Hr.
  rewrite Z.div_add; [| lia].
  apply Z.mod_add. lia.
Qed.

(* the UNCONDITIONAL value of [svpn_of] (bits 38:12), which the bounded
   [RiscvExtras.svpn_of_unsigned_lo] does not give *)
Lemma svpn_of_unsigned_gen (a : mword 64) :
  bv_unsigned (svpn_of a) = (bv_unsigned a / 4096) mod 134217728.
Proof.
  unfold svpn_of. cbn [bits_of_virtaddr]. rewrite autocast_id.
  unfold subrange_vec_dec at 1. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx pagesize_bits) with 12%N.
  rewrite bv_extract_unsigned.
  fold (subrange_vec_dec a (Z.sub 39 1) 0).
  rewrite ppo_subrange_38_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - pagesize_bits + 1)) with 27%N.
  unfold bv_wrap. change (bv_modulus 27) with 134217728.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  apply z_wrap39_shift.
Qed.

Local Lemma z_pgd_div (x : Z) : (x - x mod 4096) / 4096 = x / 4096.
Proof.
  pose proof (Z_div_mod_eq_full x 4096) as H.
  replace (x - x mod 4096) with (x / 4096 * 4096) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma svpn_of_pgrounddown (va : mword 64) :
  svpn_of (and_vec va (mword_of_int (-4096))) = svpn_of va.
Proof.
  apply bv_eq.
  rewrite !svpn_of_unsigned_gen.
  rewrite pgd_unsigned.
  rewrite z_pgd_div. reflexivity.
Qed.

(* ---- the three PGROUNDDOWN facts a chunked copy loop lives on ------- *)

(* PGROUNDDOWN is IDEMPOTENT.  vmfault re-masks the already-masked va it is
   handed and states its postcondition at THAT re-masked value, so both copy
   loops must see the two as the same address. *)
Lemma pgd_idem (va : mword 64) :
  and_vec (and_vec va (mword_of_int (-4096))) (mword_of_int (-4096))
  = and_vec va (mword_of_int (-4096)).
Proof.
  apply bv_eq. rewrite !pgd_unsigned. rewrite (z_pgd_mod (bv_unsigned va)).
  apply Z.sub_0_r.
Qed.

(* [sub rd,va,va0]: the OFFSET of the cursor inside its page (copyin's
   +0x38, copyout's +0x32). *)
Lemma pgd_off (va : mword 64) :
  sub_vec va (and_vec va (mword_of_int (-4096)))
  = (mword_of_int (bv_unsigned va mod 4096) : mword 64).
Proof.
  apply bv_eq. rewrite bc_sub_vec_unsigned !bc_moi_unsigned pgd_unsigned.
  f_equal. ring.
Qed.

(* [sub rd,va0,va] then [add rd,rd,PGSIZE]: the bytes left in that page
   above the cursor (copyin's +0x2c, copyout's +0x82). *)
Lemma pgd_room (va : mword 64) :
  add_vec (sub_vec (and_vec va (mword_of_int (-4096))) va) (mword_of_int 4096)
  = (mword_of_int (4096 - bv_unsigned va mod 4096) : mword 64).
Proof.
  apply bv_eq.
  rewrite bc_add_vec_unsigned bc_sub_vec_unsigned !bc_moi_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r.
  rewrite pgd_unsigned. f_equal. ring.
Qed.

(* ---- PGROUNDUP, and the two run lengths the uvm* specs quantify over -- *)
(*                                                                         *)
(*   [uvm_maxsz] is TRAPFRAME = MAXVA - 2*PGSIZE, the first va ABOVE the    *)
(*   user region.  A page starting at [a] belongs in a user map exactly     *)
(*   when [uint a + 4096 <= uvm_maxsz] -- that is what puts its vpn         *)
(*   strictly below [tf_vpn] ([upt_map_wf]'s clause), so it is the bound    *)
(*   every uvm* spec carries about its size arguments.                      *)

Definition uvm_maxsz : Z := 2 ^ 38 - 8192.

Definition pgroundup (x : mword 64) : mword 64 :=
  and_vec (add_vec x (mword_of_int 4095)) (mword_of_int (-4096)).

(* how many pages uvmalloc's loop maps, and uvmdealloc's unmaps.  Both are
   [Z.to_nat] of a quotient that goes NEGATIVE exactly on the arms where the
   C code does nothing, so both are 0 there and no case split is needed in
   the specs. *)
Definition uvma_np (oldsz newsz : mword 64) : nat :=
  Z.to_nat ((bv_unsigned newsz - bv_unsigned (pgroundup oldsz) + 4095) / 4096).

Definition uvmd_np (oldsz newsz : mword 64) : nat :=
  Z.to_nat ((bv_unsigned (pgroundup oldsz) - bv_unsigned (pgroundup newsz)) / 4096).

(* the arithmetic lifted OUT of any goal mentioning [bv_unsigned] -- the
   zify-hook rule in claude-notes/durable-notes.md *)
Local Lemma z_pgu_small (v : Z) :
  (0 <= v)%Z -> (v + 4095 < 18446744073709551616)%Z ->
  (0 <= v + 4095 < 18446744073709551616)%Z.
Proof. lia. Qed.

Lemma pgroundup_unsigned (x : mword 64) :
  (bv_unsigned x + 4095 < 2 ^ 64)%Z ->
  bv_unsigned (pgroundup x)
  = ((bv_unsigned x + 4095) - (bv_unsigned x + 4095) mod 4096)%Z.
Proof.
  intros Hlt.
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z)
    by (vm_compute; reflexivity).
  change (2 ^ 64)%Z with 18446744073709551616%Z in Hlt.
  assert (Hsum : bv_unsigned (add_vec x (mword_of_int 4095))
                 = (bv_unsigned x + 4095)%Z).
  { rewrite add_vec64_unsigned moi64_unsigned.
    rewrite (bv_wrap_small 64 4095); [| rewrite Hm; vm_compute; intuition congruence].
    apply bv_wrap_small. rewrite Hm.
    exact (z_pgu_small _ (proj1 (bv_unsigned_in_range 64 x)) Hlt). }
  unfold pgroundup. rewrite pgd_unsigned Hsum. reflexivity.
Qed.

Lemma pgroundup_low12 (x : mword 64) :
  subrange_vec_dec (pgroundup x) 11 0 = (zeros' 12 : mword 12).
Proof. unfold pgroundup. apply pgrounddown_low12. Qed.

Local Lemma z_svpn_lt_maxva (x : Z) :
  0 <= x -> x < 274877906944 -> (x / 4096) mod 134217728 < 67108864.
Proof.
  intros H0 H1.
  assert (Hq : 0 <= x / 4096 < 67108864)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (x / 4096) 134217728); lia.
Qed.

(* below MAXVA = 2^38 a va's vpn is below 2^26 -- the bound
   [upt_map_wf_insert_vmfault] needs (TRAMPOLINE's vpn is 2^26-1) *)
Lemma svpn_of_lt_maxva (a : mword 64) :
  (uint a < 2 ^ 38)%Z -> (bv_unsigned (svpn_of a) < 67108864)%Z.
Proof.
  intros Hlt.
  change (2 ^ 38) with 274877906944 in Hlt.
  rewrite uint_unsigned in Hlt.
  rewrite svpn_of_unsigned_gen.
  exact (z_svpn_lt_maxva _ (proj1 (bv_unsigned_in_range _ a)) Hlt).
Qed.

(* ===================================================================== *)
(* §2f WHICH PAGE A WALKADDR VERDICT NAMES.                                *)
(*                                                                         *)
(*     copyin/copyout do not walk the table themselves: they call          *)
(*     walkaddr, which returns the base of the page a va reaches, and      *)
(*     then memmove into or out of that page.  What walkaddr actually      *)
(*     tests is [pte_vu] -- V and U both set -- on the EXACT (A/D-bearing) *)
(*     word its walk read, i.e. on [m_ad], not on the canonical user map.  *)
(*     To hand the caller a page of [proc_pt] we must get back from that   *)
(*     word to an entry of [ud_um]; these three lemmas are that step.      *)
(*                                                                         *)
(*     The A/D bits cannot change which page a leaf names                  *)
(*     ([pte_ppn_set_ad]), and the two non-user leaves of a user table --  *)
(*     the trampoline and the trapframe -- both have U = 0, so no A/D      *)
(*     variant of either can pass walkaddr's test.  That leaves exactly    *)
(*     the [um] case, at the same ppn.                                     *)
(* ===================================================================== *)

Lemma pte_ppn_set_ad (w : mword 64) (a d : mword 1) :
  pte_ppn (pte_set_ad w a d) = pte_ppn w.
Proof.
  unfold pte_ppn. rewrite !autocast_id. apply pte_set_ad_ppn.
Qed.

Lemma pte_vu_not_tramp (a d : mword 1) : ~ pte_vu (pte_set_ad pte_tramp a d).
Proof.
  intros (_ & HU). unfold Mk_PTE_Flags in HU.
  rewrite tramp_variant_flags in HU.
  apply (f_equal bv_unsigned) in HU.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute in HU; discriminate.
Qed.

Lemma pte_vu_not_tf (tfp : mword 44) (a d : mword 1) :
  ~ pte_vu (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros (_ & HU). unfold Mk_PTE_Flags in HU.
  rewrite tf_variant_flags in HU.
  apply (f_equal bv_unsigned) in HU.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute in HU; discriminate.
Qed.

(* the step itself: a V|U word of the exact map comes from the user map,
   and names the same page *)
Lemma upt_ad_view_vu (tfp : mword 44) (um m_ad : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_ad_view tfp um m_ad -> m_ad !! vpn = Some w -> pte_vu w ->
  exists w0, um !! vpn = Some w0 /\ pte_ppn w0 = pte_ppn w.
Proof.
  intros (_ & Hview) Hl Hvu.
  destruct (Hview vpn w Hl) as (w0 & a & d & Hleaf & ->).
  destruct Hleaf as [(_ & ->) | [(_ & ->) | Hl0]].
  - destruct (pte_vu_not_tramp a d Hvu).
  - destruct (pte_vu_not_tf tfp a d Hvu).
  - exists w0. split; [exact Hl0 | symmetry; apply pte_ppn_set_ad].
Qed.

(* ===================================================================== *)
(* §3 VALIDITY.  One predicate, over the existing pure pieces plus the    *)
(*    kalloc-page conjunct.                                              *)
(* ===================================================================== *)

(* every page the table hands the process is a kalloc page: 4KB-aligned and
   inside the kernel free-page range.  See design decision (3) at the top. *)
Definition um_pages_valid (um : gmap (mword 27) (mword 64)) : Prop :=
  forall ppn, ppn ∈ um_ppns um -> page_valid (page_base ppn).

(* NO ALIASING: distinct user vpns name distinct pages.
   [upt_pages_own] is a big-op over the SET of ppns, so without this a table
   mapping one page at two vpns would carry ONE [phys_page_own] for two
   entries -- and uvmunmap, which frees the page of every mapped vpn in its
   range, would then have to free it twice.  So the invariant has to say it.
   It is never a proof obligation on a caller: an insert re-establishes it
   from the OWNERSHIP of the page being added ([upt_pages_own_fresh]), which
   is the same argument that already gave [proc_pt_grow] its freshness. *)
Definition um_inj (um : gmap (mword 27) (mword 64)) : Prop :=
  forall v1 v2 w1 w2, um !! v1 = Some w1 -> um !! v2 = Some w2 ->
    pte_ppn w1 = pte_ppn w2 -> v1 = v2.

Definition proc_pt_wf (P : uptd) : Prop :=
  upt_map_wf P.(ud_um) /\           (* below TRAPFRAME, a proper 4K leaf   *)
  upt_acc_wf P.(ud_um) /\           (* each leaf User-ok or User-denied    *)
  um_pages_valid P.(ud_um) /\       (* every user page is a kalloc page    *)
  um_inj P.(ud_um) /\               (* distinct vpns, distinct pages       *)
  page_valid (page_base P.(ud_tfp)).
  (* ... and so is the trapframe page *)

Lemma um_inj_empty : um_inj (∅ : gmap (mword 27) (mword 64)).
Proof. intros v1 v2 w1 w2 Hl. rewrite lookup_empty in Hl. discriminate. Qed.

Lemma um_inj_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  um_inj um -> um_inj (delete vpn um).
Proof.
  intros Hinj v1 v2 w1 w2 Hl1 Hl2 Hq.
  apply lookup_delete_Some in Hl1. apply lookup_delete_Some in Hl2.
  exact (Hinj v1 v2 w1 w2 (proj2 Hl1) (proj2 Hl2) Hq).
Qed.

(* the insert case: the new page is not one of the pages already named *)
Lemma um_inj_insert (um : gmap (mword 27) (mword 64)) (vpn : mword 27)
    (w : mword 64) :
  um_inj um -> pte_ppn w ∉ um_ppns um -> um_inj (<[vpn := w]> um).
Proof.
  intros Hinj Hfresh v1 v2 w1 w2 Hl1 Hl2 Hq.
  assert (Hin : forall v x, um !! v = Some x -> pte_ppn x ∈ um_ppns um).
  { intros v x Hl. apply elem_of_um_ppns. exists v, x.
    split; [exact Hl | reflexivity]. }
  apply lookup_insert_Some in Hl1. apply lookup_insert_Some in Hl2.
  destruct Hl1 as [(Hv1 & Hw1) | (_ & Hl1)];
    destruct Hl2 as [(Hv2 & Hw2) | (_ & Hl2)].
  - congruence.
  - exfalso. apply Hfresh. rewrite Hw1 Hq. exact (Hin v2 w2 Hl2).
  - exfalso. apply Hfresh. rewrite Hw2. rewrite <- Hq. exact (Hin v1 w1 Hl1).
  - exact (Hinj v1 v2 w1 w2 Hl1 Hl2 Hq).
Qed.

(* the step from "the map has a leaf here" to "the page it names is a kalloc
   page": [elem_of_um_ppns] then the [um_pages_valid] conjunct.  Used by the
   page accessor (§6) and by every caller that must decide a [bnez] on a page
   pointer ([KallocInv.page_valid_neq_zero]). *)
Lemma um_page_valid (P : uptd) (vpn : mword 27) (w : mword 64) :
  proc_pt_wf P -> P.(ud_um) !! vpn = Some w -> page_valid (page_base (pte_ppn w)).
Proof.
  intros (_ & _ & Hpv & _ & _) Hl. apply Hpv.
  apply elem_of_um_ppns. exists vpn, w. split; [exact Hl | reflexivity].
Qed.

(* A kalloc page's bytes are kernel data bytes, hence statically claimed at
   KP_rw -- this is what makes the [↦ₚ ⇄ ↦ₘ] tier bridge available on every
   byte of every page the process owns (§5). *)
Lemma page_valid_kdata (ppn : mword 44) (j : nat) :
  page_valid (page_base ppn) -> (j < 4096)%nat ->
  addr_is_kdata (pa_add (page_base ppn) j).
Proof. intros Hv Hj. exact (page_in_range_addr_is_kdata (page_base ppn) j Hv Hj). Qed.

Lemma page_valid_kmap_static (ppn : mword 44) (j : nat) :
  page_valid (page_base ppn) -> (j < 4096)%nat ->
  kmap_static (svpn_of (pa_add (page_base ppn) j)) KP_rw.
Proof. intros Hv Hj. exact (kdata_svpn_class _ (page_valid_kdata ppn j Hv Hj)). Qed.

Lemma page_valid_ram (ppn : mword 44) (j : nat) :
  page_valid (page_base ppn) -> (j < 4096)%nat ->
  addr_is_ram (pa_add (page_base ppn) j).
Proof. intros Hv Hj. exact (addr_is_kdata_ram _ (page_valid_kdata ppn j Hv Hj)). Qed.

(* Sv39 canonicality of every byte of a kalloc page: the DRAM bank tops out
   at 0x88000000, well below 2^38. *)
Local Lemma z_ram_canon (x : Z) :
  ram_base <= x < ram_base + ram_size -> x < 274877906944.
Proof. unfold ram_base, ram_size. lia. Qed.

Lemma page_valid_canon (ppn : mword 44) (j : nat) :
  page_valid (page_base ppn) -> (j < 4096)%nat ->
  (uint (pa_add (page_base ppn) j) < 274877906944)%Z.
Proof. intros Hv Hj. exact (z_ram_canon _ (page_valid_ram ppn j Hv Hj)). Qed.

Lemma um_pages_kmap_static (um : gmap (mword 27) (mword 64))
    (ppn : mword 44) (j : nat) :
  um_pages_valid um -> ppn ∈ um_ppns um -> (j < 4096)%nat ->
  kmap_static (svpn_of (pa_add (page_base ppn) j)) KP_rw.
Proof. intros Hv Hppn Hj. exact (page_valid_kmap_static ppn j (Hv ppn Hppn) Hj). Qed.

(* the empty user map is valid and User-classified vacuously *)
Lemma um_pages_valid_empty : um_pages_valid (∅ : gmap (mword 27) (mword 64)).
Proof.
  intros ppn Hin. exfalso. exact (not_elem_of_um_ppns_empty ppn Hin).
Qed.

Lemma upt_acc_wf_empty : upt_acc_wf (∅ : gmap (mword 27) (mword 64)).
Proof. intros vpn w Hl. rewrite lookup_empty in Hl. discriminate. Qed.

(* ===================================================================== *)
(* §3b THE VMFAULT INSERT preserves each conjunct of [proc_pt_wf].         *)
(*                                                                        *)
(*     NOTE the bound in [upt_map_wf_insert_vmfault]: xv6's MAXVA is       *)
(*     1 << 38, so TRAMPOLINE's vpn is 2^26-1 and TRAPFRAME's is 2^26-2 -- *)
(*     a 27-bit vpn being different from BOTH does not put it below the    *)
(*     trapframe.  What does is [va < MAXVA], i.e. vpn < 2^26              *)
(*     ([svpn_of_lt_maxva]).                                              *)
(* ===================================================================== *)

(* peel the head of a [seq] with the LENGTH ABSTRACT: doing it by
   [replace (seq 0 4096) with (0 :: seq 1 4095) by reflexivity] instead costs
   ~6 s (the 4096-deep nat literal is converted, and the proof term is
   re-checked at [Qed]). *)
Local Lemma ppo_seq_cons (a b : nat) : seq a (S b) = a :: seq (S a) b.
Proof. reflexivity. Qed.

Local Lemma z_vpn_lt_tf (v : Z) :
  v < 67108864 -> v <> 67108863 -> v <> 67108862 -> v < 67108862.
Proof. lia. Qed.

Lemma upt_map_wf_insert_uvm (um : gmap (mword 27) (mword 64)) (perm : Z)
    (vpn : mword 27) (r : mword 64) :
  uvm_perm_ok perm ->
  upt_map_wf um -> vpn <> tramp_vpn -> vpn <> tf_vpn ->
  (bv_unsigned vpn < 67108864)%Z ->
  upt_map_wf (<[vpn := uvm_pte perm r]> um).
Proof.
  intros (_ & Hleaf & _) Hwf Hnt Hntf Hlt v w Hl.
  apply lookup_insert_Some in Hl. destruct Hl as [(Hv & Hw) | (_ & Hl)].
  - subst v. subst w. split.
    + rewrite tf_vpn_unsigned.
      apply z_vpn_lt_tf; [exact Hlt | ..].
      * intro He. apply Hnt. apply bv_eq. rewrite tramp_vpn_unsigned. exact He.
      * intro He. apply Hntf. apply bv_eq. rewrite tf_vpn_unsigned. exact He.
    + intros a d. exact (Hleaf r a d).
  - exact (Hwf v w Hl).
Qed.

Lemma upt_acc_wf_insert_uvm (um : gmap (mword 27) (mword 64)) (perm : Z)
    (vpn : mword 27) (r : mword 64) :
  uvm_perm_ok perm ->
  upt_acc_wf um -> upt_acc_wf (<[vpn := uvm_pte perm r]> um).
Proof.
  intros (_ & _ & Hacc0) Hwf v w Hl acc Hacc.
  apply lookup_insert_Some in Hl. destruct Hl as [(_ & Hw) | (_ & Hl)].
  - subst w. exact (Hacc0 r acc Hacc).
  - exact (Hwf v w Hl acc Hacc).
Qed.

Lemma um_pages_valid_insert_uvm (um : gmap (mword 27) (mword 64)) (perm : Z)
    (vpn : mword 27) (r : mword 64) :
  uvm_perm_ok perm ->
  um_pages_valid um -> page_valid r ->
  um_pages_valid (<[vpn := uvm_pte perm r]> um).
Proof.
  intros (Hpk & _ & _) Hv Hpv q Hq.
  apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hl & Hq).
  apply lookup_insert_Some in Hl. destruct Hl as [(_ & Hw) | (_ & Hl)].
  - subst x. rewrite <- Hq. rewrite (pte_ppn_uvm perm r (pb_lor1_range perm (proj1 Hpk))).
    rewrite (page_base_of_valid r Hpv). exact Hpv.
  - apply Hv. apply elem_of_um_ppns. exists v, x. split; [exact Hl | exact Hq].
Qed.

(* the vmfault instances, as ProofVmfault names them *)
Lemma upt_map_wf_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  upt_map_wf um -> vpn <> tramp_vpn -> vpn <> tf_vpn ->
  (bv_unsigned vpn < 67108864)%Z ->
  upt_map_wf (<[vpn := vmfault_pte r]> um).
Proof. exact (upt_map_wf_insert_uvm um 22 vpn r uvm_perm_ok_22). Qed.

Lemma upt_acc_wf_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  upt_acc_wf um -> upt_acc_wf (<[vpn := vmfault_pte r]> um).
Proof. exact (upt_acc_wf_insert_uvm um 22 vpn r uvm_perm_ok_22). Qed.

Lemma um_pages_valid_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  um_pages_valid um -> page_valid r ->
  um_pages_valid (<[vpn := vmfault_pte r]> um).
Proof. exact (um_pages_valid_insert_uvm um 22 vpn r uvm_perm_ok_22). Qed.

(* ---- §3c THE UNMAP STEP: deleting one user vpn ---------------------- *)
(* Each conjunct of [proc_pt_wf] is a per-entry property, so all four
   survive a [delete] with no side condition at all. *)

Lemma upt_map_wf_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  upt_map_wf um -> upt_map_wf (delete vpn um).
Proof.
  intros Hwf v w Hl. apply lookup_delete_Some in Hl. exact (Hwf v w (proj2 Hl)).
Qed.

Lemma upt_acc_wf_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  upt_acc_wf um -> upt_acc_wf (delete vpn um).
Proof.
  intros Hwf v w Hl. apply lookup_delete_Some in Hl. exact (Hwf v w (proj2 Hl)).
Qed.

Lemma um_pages_valid_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  um_pages_valid um -> um_pages_valid (delete vpn um).
Proof.
  intros Hv q Hq. apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hl & Hq).
  apply lookup_delete_Some in Hl.
  apply Hv. apply elem_of_um_ppns. exists v, x. split; [exact (proj2 Hl) | exact Hq].
Qed.

(* THE FOOTPRINT SHRINKS BY EXACTLY ONE PAGE.  This is what [um_inj] buys:
   without it the deleted vpn's ppn could still be named by another entry
   and the page could not be handed to kfree. *)
Lemma um_ppns_delete (um : gmap (mword 27) (mword 64)) (vpn : mword 27)
    (w : mword 64) :
  um_inj um -> um !! vpn = Some w ->
  um_ppns (delete vpn um) = um_ppns um ∖ {[pte_ppn w]}.
Proof.
  intros Hinj Hl. apply set_eq. intros q. split.
  - intros Hq. apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hlv & Hq).
    apply lookup_delete_Some in Hlv. destruct Hlv as (Hne & Hlv).
    apply elem_of_difference. split.
    + apply elem_of_um_ppns. exists v, x. split; [exact Hlv | exact Hq].
    + intros Hin. apply elem_of_singleton in Hin.
      apply Hne. exact (eq_sym (Hinj v vpn x w Hlv Hl (eq_trans Hq Hin))).
  - intros Hq. apply elem_of_difference in Hq. destruct Hq as (Hin & Hnin).
    apply elem_of_um_ppns in Hin. destruct Hin as (v & x & Hlv & Hq).
    apply elem_of_um_ppns. exists v, x.
    split; [| exact Hq].
    apply lookup_delete_Some. split; [| exact Hlv].
    intros ->. apply Hnin. apply elem_of_singleton.
    rewrite <- Hq. f_equal. congruence.
Qed.

(* ---- §3d THE RUN: what uvmunmap does to the descriptor --------------- *)
(* uvmunmap walks [npages] consecutive vpns and clears each.  Both views --
   the exact [pt_rep0] map and the canonical [ud_um] -- move by the same
   fold, so ONE definition serves both, and its recursion is written to
   match the LOOP: [um_del_run _ _ (S k)] deletes the k-th vpn LAST, so the
   loop invariant after [i] iterations is [um_del_run um vpn0 i]. *)
Fixpoint um_del_run (um : gmap (mword 27) (mword 64)) (vpn0 : mword 27)
    (k : nat) : gmap (mword 27) (mword 64) :=
  match k with
  | O => um
  | S k' => delete (vpn_at vpn0 k') (um_del_run um vpn0 k')
  end.

Definition vpn_run (vpn0 : mword 27) (k : nat) : gset (mword 27) :=
  list_to_set (vpn_at vpn0 <$> seq 0 k).

Definition uptd_delete (P : uptd) (vpn : mword 27) : uptd :=
  UPTD P.(ud_root) P.(ud_tfp) (delete vpn P.(ud_um))
       (um_pas (delete vpn P.(ud_um))).

Definition uptd_del_run (P : uptd) (vpn0 : mword 27) (k : nat) : uptd :=
  UPTD P.(ud_root) P.(ud_tfp) (um_del_run P.(ud_um) vpn0 k)
       (um_pas (um_del_run P.(ud_um) vpn0 k)).

(* the loop step, as the invariant uses it *)
Lemma uptd_del_run_S (P : uptd) (vpn0 : mword 27) (k : nat) :
  uptd_del_run P vpn0 (S k) = uptd_delete (uptd_del_run P vpn0 k) (vpn_at vpn0 k).
Proof. reflexivity. Qed.

Lemma uptd_del_run_0 (P : uptd) (vpn0 : mword 27) :
  uptd_del_run P vpn0 0 = UPTD P.(ud_root) P.(ud_tfp) P.(ud_um) (um_pas P.(ud_um)).
Proof. reflexivity. Qed.

Lemma um_del_run_0 (um : gmap (mword 27) (mword 64)) (vpn0 : mword 27) :
  um_del_run um vpn0 0 = um.
Proof. reflexivity. Qed.

Lemma elem_of_vpn_run (vpn0 : mword 27) (k : nat) (v : mword 27) :
  v ∈ vpn_run vpn0 k <-> exists i, (i < k)%nat /\ v = vpn_at vpn0 i.
Proof.
  unfold vpn_run. rewrite elem_of_list_to_set elem_of_list_fmap. split.
  - intros (i & Hv & Hi). apply elem_of_seq in Hi.
    exists i. split; [lia | exact Hv].
  - intros (i & Hi & Hv). exists i. split; [exact Hv |].
    apply elem_of_seq. lia.
Qed.

(* inside the run: gone.  Outside it: untouched. *)
Lemma um_del_run_in (um : gmap (mword 27) (mword 64)) (vpn0 : mword 27)
    (k : nat) (v : mword 27) :
  v ∈ vpn_run vpn0 k -> um_del_run um vpn0 k !! v = None.
Proof.
  induction k as [| k IH]; intros Hin.
  { apply elem_of_vpn_run in Hin. destruct Hin as (i & Hi & _). lia. }
  cbn [um_del_run].
  destruct (decide (v = vpn_at vpn0 k)) as [-> | Hne].
  { apply lookup_delete. }
  rewrite (lookup_delete_ne _ _ _ (not_eq_sym Hne)).
  apply IH. apply elem_of_vpn_run.
  apply elem_of_vpn_run in Hin. destruct Hin as (i & Hi & Hv).
  destruct (decide (i = k)) as [-> | Hik]; [exfalso; exact (Hne Hv) |].
  exists i. split; [lia | exact Hv].
Qed.

Lemma um_del_run_out (um : gmap (mword 27) (mword 64)) (vpn0 : mword 27)
    (k : nat) (v : mword 27) :
  v ∉ vpn_run vpn0 k -> um_del_run um vpn0 k !! v = um !! v.
Proof.
  induction k as [| k IH]; intros Hnin; [reflexivity |].
  cbn [um_del_run].
  assert (Hne : v <> vpn_at vpn0 k).
  { intros ->. apply Hnin. apply elem_of_vpn_run. exists k. split; [lia | reflexivity]. }
  rewrite (lookup_delete_ne _ _ _ (not_eq_sym Hne)).
  apply IH. intros Hin. apply Hnin. apply elem_of_vpn_run.
  apply elem_of_vpn_run in Hin. destruct Hin as (i & Hi & Hv).
  exists i. split; [lia | exact Hv].
Qed.

(* THE RESTORE LAW -- what makes uvmalloc's failure arm give back exactly
   the descriptor it was called with.  uvmalloc extends [um] over the run
   (each vpn fresh), then uvmdealloc deletes precisely that run. *)
Lemma um_del_run_restore (um um' : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (k : nat) :
  um ⊆ um' ->
  dom um' = dom um ∪ vpn_run vpn0 k ->
  (forall i, (i < k)%nat -> um !! vpn_at vpn0 i = None) ->
  um_del_run um' vpn0 k = um.
Proof.
  intros Hsub Hdom Hfresh. apply map_eq. intros v.
  destruct (decide (v ∈ vpn_run vpn0 k)) as [Hin | Hnin].
  - rewrite (um_del_run_in um' vpn0 k v Hin).
    apply elem_of_vpn_run in Hin. destruct Hin as (i & Hi & ->).
    exact (eq_sym (Hfresh i Hi)).
  - rewrite (um_del_run_out um' vpn0 k v Hnin).
    destruct (um !! v) as [w |] eqn:Hl.
    + exact (lookup_weaken um um' v w Hl Hsub).
    + apply not_elem_of_dom. rewrite Hdom.
      intros Hin. apply elem_of_union in Hin. destruct Hin as [Hin | Hin].
      * apply (not_elem_of_dom (D := gset (mword 27)) um v) in Hl.
        exact (Hl Hin).
      * exact (Hnin Hin).
Qed.

(* the wf conjuncts ride across the whole run *)
Lemma proc_pt_wf_del_run (P : uptd) (vpn0 : mword 27) (k : nat) :
  proc_pt_wf P -> proc_pt_wf (uptd_del_run P vpn0 k).
Proof.
  intros (Hm & Ha & Hp & Hi & Ht).
  unfold uptd_del_run, proc_pt_wf. cbn [ud_root ud_tfp ud_um].
  induction k as [| k IH]; [cbn [um_del_run]; split_and!; assumption |].
  destruct IH as (Hm' & Ha' & Hp' & Hi' & _).
  cbn [um_del_run]. split_and!.
  - exact (upt_map_wf_delete _ _ Hm').
  - exact (upt_acc_wf_delete _ _ Ha').
  - exact (um_pages_valid_delete _ _ Hp').
  - exact (um_inj_delete _ _ Hi').
  - exact Ht.
Qed.

(* ===================================================================== *)
(* §4 The coverage side condition, as a theorem.                          *)
(* ===================================================================== *)

(* a leaf's translate output lies in that leaf's page -- the fact that ties
   the tree layer's pa formula to page-granular ownership *)
(* the [bv_unsigned]-free arithmetic, so [lia] is not looking at a goal
   mentioning [bv_unsigned] (see the zify-hook gotcha in the durable notes) *)
Local Lemma to_nat_lt_4096 (x : Z) : 0 <= x < 4096 -> (Z.to_nat x < 4096)%nat.
Proof. lia. Qed.

Lemma u_walk_pa_in_page (w va : mword 64) :
  u_walk_pa w va ∈ page_pas (pte_ppn w).
Proof.
  pose proof (bv_unsigned_in_range _
    (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) 11 0)) as Hoff.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 12) = 4096)
    by (vm_compute; reflexivity).
  rewrite Hm in Hoff.
  apply elem_of_page_pas.
  exists (Z.to_nat (bv_unsigned
    (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) 11 0))).
  split; [exact (to_nat_lt_4096 _ Hoff) |].
  apply bv_eq.
  rewrite (pa_add_page_unsigned (pte_ppn w) _ (to_nat_lt_4096 _ Hoff)).
  rewrite (Z2Nat.id _ (proj1 Hoff)).
  unfold u_walk_pa, pte_ppn.
  change (Z.sub pagesize_bits 1) with 11.
  apply zext64_concat44_12_unsigned.
Qed.

Lemma um_pas_cov (um : gmap (mword 27) (mword 64)) : udata_cov um (um_pas um).
Proof.
  intros vpn w va Hl.
  apply elem_of_um_pas.
  exists (pte_ppn w).
  split; [| exact (u_walk_pa_in_page w va)].
  apply elem_of_um_ppns. exists vpn, w. split; [exact Hl | reflexivity].
Qed.

Lemma ud_pas_cov (P : uptd) : udata_cov P.(ud_um) (ud_pas P).
Proof. apply um_pas_cov. Qed.

(* ===================================================================== *)
(* §5 THE OWNERSHIP, and THE PREDICATE.                                   *)
(* ===================================================================== *)

Section ProcPt.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* one physical byte, contents existential (the [↦ₚ] analogue of
     KallocInv's [byte_any]) *)
  Definition phys_byte_any (a : Arch.pa) : iProp Σ := (∃ b : bv 8, a ↦ₚ b)%I.

  (* a whole physical page.  Tier-neutral by construction: no va inside. *)
  Definition phys_page_own (ppn : mword 44) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4096, phys_byte_any (pa_add (page_base ppn) j))%I.

  (* the user pages the table hands the process *)
  Definition upt_pages_own (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    ([∗ set] ppn ∈ um_ppns um, phys_page_own ppn)%I.

  (* the trapframe page.  Deliberately its own conjunct so it can later
     gain structure -- see the header. *)
  (* everything the table OWNS.  Identical in the parked and the installed
     form -- the pages do not change hands at the satp switch. *)
  Definition proc_pt_own (P : uptd) : iProp Σ :=
    upt_pages_own P.(ud_um).

  Typeclasses Opaque phys_page_own upt_pages_own.

  (* ------------------------------------------------------------------ *)
  (* THE SHAPE BRIDGE.  [UserPtTree.udata_own] -- the aggregated byte map *)
  (* user-mode execution reads and writes -- is the SAME resource as a    *)
  (* set of existential physical bytes.  With this, dropping the          *)
  (* [uptd]'s [ud_data] field costs the user-execution engines nothing:   *)
  (* they keep consuming [udata_own], now at the DERIVED footprint        *)
  (* [ud_pas], whose coverage side condition is [ud_pas_cov] above.       *)
  (* ------------------------------------------------------------------ *)
  Lemma phys_bytes_udata (S : gset Arch.pa) :
    ([∗ set] a ∈ S, phys_byte_any a) ⊣⊢ udata_own S.
  Proof.
    iSplit.
    - iIntros "H".
      iInduction S as [| a S' Hnin] "IH" using set_ind_L.
      + iExists ∅. rewrite big_sepM_empty dom_empty_L.
        iSplit; [done | done].
      + rewrite big_sepS_insert; [| exact Hnin].
        iDestruct "H" as "[Ha HS]".
        iDestruct ("IH" with "HS") as (dm) "[%Hdom Hdm]".
        rewrite /phys_byte_any. iDestruct "Ha" as (b) "Ha".
        assert (Hnone : dm !! a = None).
        { apply not_elem_of_dom. rewrite Hdom. exact Hnin. }
        iExists (<[a := b]> dm).
        rewrite big_sepM_insert; [| exact Hnone].
        iFrame "Ha Hdm". iPureIntro.
        rewrite dom_insert_L Hdom. reflexivity.
    - iIntros "H". iDestruct "H" as (dm) "[%Hdom Hdm]".
      rewrite <- Hdom.
      rewrite <- (big_sepM_dom (fun a => phys_byte_any a) dm).
      iApply (big_sepM_impl with "Hdm").
      iIntros "!>" (a b _) "Hb". iExists b. iExact "Hb".
  Qed.

  (* one page's bytes, as a byte SET (the [list_to_set] does not collapse:
     [page_pa_inj] gives the 4096 addresses NoDup) *)
  Lemma phys_page_own_set (ppn : mword 44) :
    phys_page_own ppn ⊣⊢ ([∗ set] a ∈ page_pas ppn, phys_byte_any a).
  Proof.
    rewrite /phys_page_own /page_pas.
    rewrite big_sepS_list_to_set.
    - rewrite big_sepL_fmap. reflexivity.
    - apply NoDup_fmap_2_strong; [| apply NoDup_seq].
      intros j k Hj Hk Heq.
      apply elem_of_seq in Hj. apply elem_of_seq in Hk.
      exact (page_pa_inj ppn j k ltac:(lia) ltac:(lia) Heq).
  Qed.

  (* a SET of pages, likewise -- the union splits because distinct pages are
     disjoint blocks ([page_pas_disjoint_pages]) *)
  Lemma phys_pages_own_set (T : gset (mword 44)) :
    ([∗ set] ppn ∈ T, phys_page_own ppn)
    ⊣⊢ ([∗ set] a ∈ pages_pas T, phys_byte_any a).
  Proof.
    induction T as [| ppn T Hnin IH] using set_ind_L.
    - rewrite pages_pas_empty !big_sepS_empty. reflexivity.
    - rewrite pages_pas_insert.
      rewrite big_sepS_insert; [| exact Hnin].
      rewrite big_sepS_union; [| exact (page_pas_disjoint_pages ppn T Hnin)].
      rewrite phys_page_own_set IH. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE OWNERSHIP BRIDGE.  The kernel's page-indexed view of a process's *)
  (* user pages IS [udata_own] at the derived footprint -- so the satp    *)
  (* switch converts NOTHING, and user execution keeps its aggregated     *)
  (* byte map unchanged.                                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma upt_pages_udata (um : gmap (mword 27) (mword 64)) :
    upt_pages_own um ⊣⊢ udata_own (um_pas um).
  Proof.
    rewrite /upt_pages_own /um_pas.
    rewrite phys_pages_own_set. apply phys_bytes_udata.
  Qed.

  Lemma proc_pt_own_udata (P : uptd) :
    proc_pt_own P ⊣⊢ udata_own (ud_pas P).
  Proof. rewrite /proc_pt_own /ud_pas upt_pages_udata. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE KALLOC/KFREE BOUNDARY.  [KallocInv.page_own] -- the [↦ₘ] page    *)
  (* kalloc hands out and kfree takes back -- converts to and from the    *)
  (* tier-neutral [phys_page_own] for any kalloc page.  This is the ONE   *)
  (* place a process page table's pages change tier: on the way in        *)
  (* (uvmalloc / proc_pagetable) and on the way out (uvmunmap / freewalk).*)
  (* Generalizes [KMap.mem_page_to_phys], which is stated only for a      *)
  (* single constant byte value across the page and so does not fit       *)
  (* [page_own]'s per-byte existential contents.                          *)
  (* ------------------------------------------------------------------ *)
  Lemma page_own_to_phys (ppn : mword 44) :
    page_valid (page_base ppn) ->
    kmap_static_claims -∗ page_own (page_base ppn) -∗ phys_page_own ppn.
  Proof.
    intros Hv. iIntros "#Hb Hp".
    rewrite /page_own /phys_page_own.
    iApply (big_sepL_impl with "Hp").
    iIntros "!>" (k j Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    rewrite /byte_any /phys_byte_any. iDestruct "H" as (b) "H".
    iExists b.
    iApply (mem_ident_phys (pa_add (page_base ppn) (0 + k)%nat) (DfracOwn 1) b
              (page_valid_kmap_static ppn (0 + k)%nat Hv ltac:(lia)) with "Hb H").
  Qed.

  Lemma phys_to_page_own (ppn : mword 44) :
    page_valid (page_base ppn) ->
    kmap_static_claims -∗ phys_page_own ppn -∗ page_own (page_base ppn).
  Proof.
    intros Hv. iIntros "#Hb Hp".
    rewrite /page_own /phys_page_own.
    iApply (big_sepL_impl with "Hp").
    iIntros "!>" (k j Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    rewrite /byte_any /phys_byte_any. iDestruct "H" as (b) "H".
    iExists b.
    iApply (phys_ident_mem (pa_add (page_base ppn) (0 + k)%nat) (DfracOwn 1) b
              (page_valid_kmap_static ppn (0 + k)%nat Hv ltac:(lia))
              (page_valid_ram ppn (0 + k)%nat Hv ltac:(lia))
              (page_valid_canon ppn (0 + k)%nat Hv ltac:(lia)) with "Hb H").
  Qed.

  Typeclasses Opaque phys_byte_any.

  (* ------------------------------------------------------------------ *)
  (* FRESHNESS IS BY OWNERSHIP.  A page cannot be owned twice at         *)
  (* fraction 1, so the vmfault page is automatically distinct from      *)
  (* every page the table already maps -- no pure side condition.        *)
  (* ------------------------------------------------------------------ *)
  Lemma phys_page_own_dup (ppn : mword 44) :
    phys_page_own ppn -∗ phys_page_own ppn -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite /phys_page_own.
    rewrite (ppo_seq_cons 0 4095).
    iDestruct "H1" as "[Hb1 _]".
    iDestruct "H2" as "[Hb2 _]".
    rewrite /phys_byte_any.
    iDestruct "Hb1" as (b1) "Hb1". iDestruct "Hb2" as (b2) "Hb2".
    rewrite /phys_pointsto.
    iDestruct "Hb1" as "[Hp1 _]". iDestruct "Hb2" as "[Hp2 _]".
    iDestruct (pointsto_ne with "Hp1 Hp2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  (* FRESHNESS, EXTRACTED.  Owning a page the table already maps would be
     owning it twice -- so the pure "this ppn is new" fact that [um_inj]'s
     insert law wants is a CONSEQUENCE of the resources, never a caller
     obligation. *)
  Lemma upt_pages_own_fresh (um : gmap (mword 27) (mword 64)) (ppn : mword 44) :
    phys_page_own ppn -∗ upt_pages_own um -∗ ⌜ppn ∉ um_ppns um⌝.
  Proof.
    iIntros "Hp Hum".
    destruct (decide (ppn ∈ um_ppns um)) as [Hin | Hnin]; [| by iPureIntro].
    iEval (rewrite /upt_pages_own
             (big_sepS_delete (fun q => phys_page_own q) (um_ppns um) ppn Hin)) in "Hum".
    iDestruct "Hum" as "[Hq _]".
    iDestruct (phys_page_own_dup ppn with "Hp Hq") as %[].
  Qed.

  (* one page joins the footprint.  If its ppn were already there, the
     [big_sepS] would hand us a second full copy -- refuted above. *)
  Lemma upt_pages_own_insert (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w : mword 64) :
    um !! vpn = None ->
    phys_page_own (pte_ppn w) -∗ upt_pages_own um -∗ upt_pages_own (<[vpn := w]> um).
  Proof.
    intros Hn. iIntros "Hp Hum".
    iDestruct (upt_pages_own_fresh um (pte_ppn w) with "Hp Hum") as %Hnin.
    rewrite /upt_pages_own.
    rewrite (um_ppns_insert um vpn w Hn).
    rewrite big_sepS_insert; [| exact Hnin].
    iFrame "Hp Hum".
  Qed.

  (* ...and one page LEAVES it.  The mirror of [upt_pages_own_insert]: what
     [um_inj] makes possible ([um_ppns_delete]) is handing the page to
     kfree while the rest of the footprint stays intact. *)
  Lemma upt_pages_own_take (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w : mword 64) :
    um_inj um -> um !! vpn = Some w ->
    upt_pages_own um ⊢ phys_page_own (pte_ppn w) ∗ upt_pages_own (delete vpn um).
  Proof.
    intros Hinj Hl.
    assert (Hin : pte_ppn w ∈ um_ppns um).
    { apply elem_of_um_ppns. exists vpn, w. split; [exact Hl | reflexivity]. }
    iIntros "Hum".
    iEval (rewrite /upt_pages_own
             (big_sepS_delete (fun q => phys_page_own q) (um_ppns um)
                (pte_ppn w) Hin)) in "Hum".
    iDestruct "Hum" as "[Hp Hrest]".
    rewrite /upt_pages_own (um_ppns_delete um vpn w Hinj Hl).
    iFrame "Hp Hrest".
  Qed.

  (* kalloc's page, at the ppn the vmfault leaf names *)
  Lemma page_own_to_phys_vmfault (r : mword 64) :
    page_valid r ->
    kmap_static_claims -∗ page_own r -∗ phys_page_own (pte_ppn (vmfault_pte r)).
  Proof.
    intros Hval.
    pose proof (page_base_of_valid r Hval) as Hpb.
    assert (Hv' : page_valid (page_base
             (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44)))
      by (rewrite Hpb; exact Hval).
    iIntros "#Hb Hp".
    rewrite pte_ppn_vmfault.
    iApply (page_own_to_phys _ Hv' with "Hb").
    rewrite Hpb. iExact "Hp".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PREDICATE: a valid process page table, PARKED -- the form the   *)
  (* kernel holds while the process is not running on this hart.  Its    *)
  (* installed counterpart is [UserPtTree.user_pt_inv] (same wf, same    *)
  (* [proc_pt_own], [utlb_inv_pt] in place of [pt_frame]); the two are   *)
  (* converted by the satp-switch window (TransPt.v's                    *)
  (* [tlb_inv_pt2_enter] / [_exit]), which touches only the tree         *)
  (* conjunct.                                                           *)
  (* ------------------------------------------------------------------ *)
  Definition proc_pt (P : uptd) : iProp Σ :=
    (⌜proc_pt_wf P⌝ ∗
     pt_frame (upt_tree_spec P.(ud_root) P.(ud_tfp) P.(ud_um)) ∗
     proc_pt_own P)%I.

  (* ... tied to the two [struct proc] cells.  Both hold a page's identity
     kernel va, which is [page_base] of the ppn the table is described by:
     [p->pagetable] the root, [p->trapframe] the trapframe page. *)
  Definition proc_pt_at (pa : mword 64) (P : uptd) : iProp Σ :=
    (p_pagetable pa ↦₈ page_base P.(ud_root) ∗
     p_trapframe pa ↦₈ page_base P.(ud_tfp) ∗
     proc_pt P)%I.

  (* [iFrame] must NOT search inside these.  [proc_pt] contains [pt_frame]
     and a big-op over the page footprint; letting the Frame instances unfold
     it turns a one-line projection into minutes and gigabytes (measured: a
     [proc_priv] projection went 2 s -> 300 s / 15.7 GB without this).  Same
     reason [phys_page_own]/[upt_pages_own] are already opaque above. *)
  Typeclasses Opaque proc_pt proc_pt_at.

  (* ------------------------------------------------------------------ *)
  (* INTRO AT THE EMPTY MAP -- the join with the CONSTRUCTION side.       *)
  (* [wp_proc_pagetable] (SpecProcPagetable.v) delivers                   *)
  (* [ptree_own 2 1 t] + [⌜pt_rep0 t (ppt_map tfp)⌝], and                 *)
  (* [ProcPt.ppt_bridge] carries that to                                  *)
  (* [upt_tree_spec (pt_base t) tfp ∅ t] -- exactly [proc_pt]'s tree      *)
  (* conjunct.  What the caller must ADD is the ownership proc_pagetable   *)
  (* deliberately does not touch (its precondition on the process is only  *)
  (* that [p->trapframe] holds a page-aligned address): the trapframe      *)
  (* page, and kalloc's [page_valid] guarantee for it.                    *)
  (* ------------------------------------------------------------------ *)
  Definition upt_desc (root tfp : mword 44) : uptd :=
    (* the [ud_data] argument is the DERIVED footprint -- it disappears
       when the field does (see claude-notes/projects/
       proc-pagetable-ownership.md, step 3). *)
    UPTD root tfp ∅ (um_pas ∅).

  (* the general form: any table whose spec holds at the EMPTY user map.
     NOTE the tactic discipline -- [rewrite /…] only, never a bare [simpl]
     or [/=]: [simpl] on this goal tries to normalize [um_pas ∅],
     [page_base] and the big-op bodies and does not come back (the
     large-pure-term landmine in claude-notes/durable-notes.md).  The
     record projections are reduced by a TARGETED [cbn]. *)
  Lemma proc_pt_intro_empty (root tfp : mword 44) (t : ptree) :
    upt_tree_spec root tfp ∅ t ->
    page_valid (page_base tfp) ->
    ptree_own 2 (DfracOwn 1) t -∗ proc_pt (upt_desc root tfp).
  Proof.
    intros Hspec Hvtf. iIntros "Ht".
    rewrite /proc_pt /proc_pt_own /upt_desc.
    cbn [ud_root ud_tfp ud_um].
    iSplitR.
    { iPureIntro. split; [exact upt_map_wf_empty |].
      split; [exact upt_acc_wf_empty |].
      split; [exact um_pages_valid_empty |].
      split; [exact um_inj_empty | exact Hvtf]. }
    iSplitL "Ht".
    { iExists t. iFrame "Ht". iPureIntro. exact Hspec. }
    rewrite /upt_pages_own um_ppns_empty big_sepS_empty. done.
  Qed.

  (* the instance at proc_pagetable's post, through [ProcPt.ppt_bridge] *)
  Lemma proc_pt_intro_ppt (t : ptree) (tfp : mword 44) :
    pt_rep0 t (ppt_map tfp) ->
    page_valid (page_base tfp) ->
    ptree_own 2 (DfracOwn 1) t -∗ proc_pt (upt_desc (pt_base t) tfp).
  Proof.
    intros Hrep Hvtf.
    exact (proc_pt_intro_empty (pt_base t) tfp t (ppt_bridge t tfp Hrep) Hvtf).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE DOVETAIL WITH walk / mappages (claude-notes/completed/vmfault.md) *)
  (*                                                                     *)
  (* [proc_pt] carries the modulo-A/D mapping SPEC; walk and mappages     *)
  (* consume the EXACT vpn -> word map [pt_rep0].  These three lemmas are *)
  (* the whole conversion, so ProofVmfault never opens [upt_tree_spec]:   *)
  (*   OPEN    at the ismapped/mappages call        [proc_pt_acc_rep0]    *)
  (*   CLOSE   unchanged (every failure arm)        [proc_pt_rebuild]     *)
  (*   CLOSE   grown by one page (success arm)      [proc_pt_grow]        *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_acc_rep0 (P : uptd) :
    proc_pt P ⊢ ∃ t m_ad, ⌜pt_rep0 t m_ad⌝ ∗ ⌜upt_ad_view P.(ud_tfp) P.(ud_um) m_ad⌝ ∗
      ⌜pt_base t = P.(ud_root)⌝ ∗ ⌜proc_pt_wf P⌝ ∗
      ptree_own 2 (DfracOwn 1) t ∗ proc_pt_own P.
  Proof.
    iIntros "H". rewrite /proc_pt /pt_frame.
    iDestruct "H" as "(%Hwf & Ht & Hown)".
    iDestruct "Ht" as (t) "(%Hspec & Ht)".
    destruct (upt_spec_rep0 P.(ud_root) P.(ud_tfp) P.(ud_um) t Hspec)
      as (m_ad & Hrep & Hview).
    iExists t, m_ad.
    iSplitR; [iPureIntro; exact Hrep |].
    iSplitR; [iPureIntro; exact Hview |].
    iSplitR; [iPureIntro; exact (proj1 Hspec) |].
    iSplitR; [iPureIntro; exact Hwf |].
    iFrame "Ht Hown".
  Qed.

  Lemma proc_pt_rebuild (P : uptd) (t' : ptree) (m_ad : gmap (mword 27) (mword 64)) :
    proc_pt_wf P -> upt_ad_view P.(ud_tfp) P.(ud_um) m_ad ->
    pt_rep0 t' m_ad -> pt_base t' = P.(ud_root) ->
    ptree_own 2 (DfracOwn 1) t' -∗ proc_pt_own P -∗ proc_pt P.
  Proof.
    intros Hwf Hview Hrep Hbase. iIntros "Ht Hown".
    rewrite /proc_pt.
    iSplitR; [iPureIntro; exact Hwf |].
    iSplitL "Ht"; [| iFrame "Hown"].
    rewrite /pt_frame. iExists t'. iFrame "Ht". iPureIntro.
    exact (upt_spec_of_rep0 P.(ud_root) P.(ud_tfp) P.(ud_um) m_ad t'
             (proj1 Hwf) Hview Hrep Hbase).
  Qed.

  (* the success arm.  [m_ad !! vpn = None] gives, through the view, both
     [vpn <> tramp/tf] and [ud_um !! vpn = None] -- so freshness in the
     user map is not a separate premise; and the page's OWNERSHIP is what
     makes it distinct from the pages already mapped.  The MAXVA bound is
     genuinely needed (see §3b). *)
  Lemma proc_pt_grow_uvm (P : uptd) (perm : Z) (vpn : mword 27) (r : mword 64)
      (t' : ptree) (m_ad : gmap (mword 27) (mword 64)) :
    uvm_perm_ok perm ->
    proc_pt_wf P -> upt_ad_view P.(ud_tfp) P.(ud_um) m_ad ->
    m_ad !! vpn = None ->
    (bv_unsigned vpn < 67108864)%Z ->
    pt_rep0 t' (<[vpn := uvm_pte perm r]> m_ad) -> pt_base t' = P.(ud_root) ->
    page_valid r ->
    kmap_static_claims -∗ ptree_own 2 (DfracOwn 1) t' -∗
    page_own r -∗ proc_pt_own P -∗
    proc_pt (uptd_insert_perm P perm vpn r).
  Proof.
    intros Hperm (Hmwf & Hawf & Hpwf & Hinj & Htfv) Hview Hnone Hlt Hrep Hbase Hval.
    destruct (proj1 (proj1 Hview vpn) Hnone) as (Hnt & Hntf & Hunone).
    pose proof (upt_map_wf_insert_uvm P.(ud_um) perm vpn r Hperm Hmwf Hnt Hntf Hlt)
      as Hmwf'.
    assert (Hppn : pte_ppn (uvm_pte perm r) = autocast (T := mword)
                     (subrange_vec_dec r 55 12))
      by exact (pte_ppn_uvm perm r (pb_lor1_range perm (proj1 (proj1 Hperm)))).
    assert (Hpb : page_base (pte_ppn (uvm_pte perm r)) = r)
      by (rewrite Hppn; exact (page_base_of_valid r Hval)).
    iIntros "#Hb Ht Hpg Hown".
    (* the page moves tier FIRST: its ownership is what re-establishes
       [um_inj], so the pure part cannot be split off before it. *)
    iAssert (phys_page_own (pte_ppn (uvm_pte perm r))) with "[Hpg]" as "Hph".
    { assert (Hv' : page_valid (page_base (pte_ppn (uvm_pte perm r))))
        by (rewrite Hpb; exact Hval).
      iApply (page_own_to_phys _ Hv' with "Hb"). rewrite Hpb. iExact "Hpg". }
    iDestruct (upt_pages_own_fresh P.(ud_um) (pte_ppn (uvm_pte perm r))
                 with "Hph Hown") as %Hfresh.
    rewrite /proc_pt /proc_pt_own /uptd_insert_perm.
    cbn [ud_root ud_tfp ud_um].
    iSplitR.
    { iPureIntro. unfold proc_pt_wf. cbn [ud_root ud_tfp ud_um].
      split_and!.
      - exact Hmwf'.
      - exact (upt_acc_wf_insert_uvm P.(ud_um) perm vpn r Hperm Hawf).
      - exact (um_pages_valid_insert_uvm P.(ud_um) perm vpn r Hperm Hpwf Hval).
      - exact (um_inj_insert P.(ud_um) vpn (uvm_pte perm r) Hinj Hfresh).
      - exact Htfv. }
    iSplitL "Ht".
    { rewrite /pt_frame. iExists t'. iFrame "Ht". iPureIntro.
      exact (upt_spec_of_rep0 P.(ud_root) P.(ud_tfp)
               (<[vpn := uvm_pte perm r]> P.(ud_um))
               (<[vpn := uvm_pte perm r]> m_ad) t' Hmwf'
               (upt_ad_view_insert P.(ud_tfp) P.(ud_um) m_ad vpn (uvm_pte perm r)
                  Hview Hnone)
               Hrep Hbase). }
    iApply (upt_pages_own_insert P.(ud_um) vpn (uvm_pte perm r) Hunone
              with "Hph Hown").
  Qed.

  Lemma proc_pt_grow (P : uptd) (vpn : mword 27) (r : mword 64)
      (t' : ptree) (m_ad : gmap (mword 27) (mword 64)) :
    proc_pt_wf P -> upt_ad_view P.(ud_tfp) P.(ud_um) m_ad ->
    m_ad !! vpn = None ->
    (bv_unsigned vpn < 67108864)%Z ->
    pt_rep0 t' (<[vpn := vmfault_pte r]> m_ad) -> pt_base t' = P.(ud_root) ->
    page_valid r ->
    kmap_static_claims -∗ ptree_own 2 (DfracOwn 1) t' -∗
    page_own r -∗ proc_pt_own P -∗
    proc_pt (uptd_insert P vpn r).
  Proof. exact (proc_pt_grow_uvm P 22 vpn r t' m_ad uvm_perm_ok_22). Qed.

  (* ------------------------------------------------------------------ *)
  (* THE UNMAP STEP -- the inverse of [proc_pt_grow].  uvmunmap clears one *)
  (* leaf and frees its page, so this is the ONE lemma that takes a page   *)
  (* OUT of the invariant: [ptree_own] comes back over the cleared tree,   *)
  (* [proc_pt_own] over the shrunk map, and the page is handed over at     *)
  (* kfree's [↦ₘ] tier together with the [page_valid] kfree also wants.    *)
  (* Stated at [proc_pt_own] (not [proc_pt]) because uvmunmap's loop keeps *)
  (* the tree OPEN across iterations -- walk needs [ptree_own].            *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_own_shrink (P : uptd) (vpn : mword 27) (w : mword 64) :
    proc_pt_wf P -> P.(ud_um) !! vpn = Some w ->
    kmap_static_claims -∗ proc_pt_own P -∗
      page_own (page_base (pte_ppn w)) ∗ proc_pt_own (uptd_delete P vpn).
  Proof.
    intros Hwf Hl.
    pose proof (um_page_valid P vpn w Hwf Hl) as Hval.
    destruct Hwf as (_ & _ & _ & Hinj & _).
    iIntros "#Hb Hown".
    iEval (rewrite /proc_pt_own (upt_pages_own_take P.(ud_um) vpn w Hinj Hl)) in "Hown".
    iDestruct "Hown" as "[Hp Hrest]".
    iSplitL "Hp".
    { iApply (phys_to_page_own (pte_ppn w) Hval with "Hb Hp"). }
    rewrite /proc_pt_own /uptd_delete. cbn [ud_um]. iExact "Hrest".
  Qed.

  (* the vpn was NOT mapped (walk found no leaf, or the slot is invalid):
     nothing changes, but the descriptor still steps.  Together with
     [proc_pt_own_shrink] these are the loop body's two arms. *)
  Lemma proc_pt_own_skip (P : uptd) (vpn : mword 27) :
    P.(ud_um) !! vpn = None ->
    proc_pt_own P ⊢ proc_pt_own (uptd_delete P vpn).
  Proof.
    intros Hl. rewrite /proc_pt_own /uptd_delete. cbn [ud_um].
    rewrite (delete_notin _ _ Hl). reflexivity.
  Qed.

  Lemma proc_pt_wf_delete (P : uptd) (vpn : mword 27) :
    proc_pt_wf P -> proc_pt_wf (uptd_delete P vpn).
  Proof.
    intros (Hm & Ha & Hp & Hi & Ht).
    unfold uptd_delete, proc_pt_wf. cbn [ud_root ud_tfp ud_um]. split_and!.
    - exact (upt_map_wf_delete _ _ Hm).
    - exact (upt_acc_wf_delete _ _ Ha).
    - exact (um_pages_valid_delete _ _ Hp).
    - exact (um_inj_delete _ _ Hi).
    - exact Ht.
  Qed.

  (* [proc_pt] does not read [ud_data] (a derived footprint, slated for
     retirement -- see claude-notes/projects/proc-pagetable-ownership.md
     step 3), so two descriptors agreeing on the three real fields carry
     the same predicate.  This is what lets uvmalloc's failure arm hand
     back [proc_pt P] itself after uvmdealloc deleted its way back to
     [P]'s map. *)
  Lemma proc_pt_data_irrel (P Q : uptd) :
    P.(ud_root) = Q.(ud_root) -> P.(ud_tfp) = Q.(ud_tfp) ->
    P.(ud_um) = Q.(ud_um) ->
    proc_pt P ⊣⊢ proc_pt Q.
  Proof.
    intros Hr Ht Hu. rewrite /proc_pt /proc_pt_own /proc_pt_wf.
    rewrite Hr Ht Hu. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE USER PAGE, BORROWED.  copyin and copyout do not change the       *)
  (* table at all -- they memmove into or out of a single page walkaddr   *)
  (* handed them.  So what they need from [proc_pt] is not an open/close  *)
  (* of the tree but an ACCESSOR: take the page out at the [↦ₘ] tier the  *)
  (* memmove spec speaks (KallocInv's [page_own]), give it back, and the  *)
  (* invariant is exactly as it was.  Nothing about the map or the tree   *)
  (* moves, so the closing wand needs no pure premise -- only             *)
  (* [kmap_static_claims], which is persistent and so is captured.        *)
  (* ------------------------------------------------------------------ *)
  Lemma proc_pt_page_acc (P : uptd) (vpn : mword 27) (w : mword 64) :
    P.(ud_um) !! vpn = Some w ->
    kmap_static_claims -∗ proc_pt P -∗
      page_own (page_base (pte_ppn w)) ∗
      (page_own (page_base (pte_ppn w)) -∗ proc_pt P).
  Proof.
    intros Hl.
    assert (Hin : pte_ppn w ∈ um_ppns P.(ud_um)).
    { apply elem_of_um_ppns. exists vpn, w. split; [exact Hl | reflexivity]. }
    iIntros "#Hb H".
    iEval (rewrite /proc_pt /proc_pt_own /upt_pages_own
             (big_sepS_delete (fun q => phys_page_own q)
                (um_ppns P.(ud_um)) (pte_ppn w) Hin)) in "H".
    iDestruct "H" as "(%Hwf & Ht & Hp & Hrest)".
    pose proof (um_page_valid P vpn w Hwf Hl) as Hval.
    iDestruct (phys_to_page_own (pte_ppn w) Hval with "Hb Hp") as "Hpg".
    iSplitL "Hpg"; [iExact "Hpg" |].
    iIntros "Hpg".
    iDestruct (page_own_to_phys (pte_ppn w) Hval with "Hb Hpg") as "Hp".
    rewrite /proc_pt /proc_pt_own /upt_pages_own.
    rewrite (big_sepS_delete (fun q => phys_page_own q)
               (um_ppns P.(ud_um)) (pte_ppn w) Hin).
    iSplitR; [iPureIntro; exact Hwf |].
    iFrame "Ht Hp Hrest".
  Qed.

  (* the instance the vmfault-success arm hands on: the page just faulted
     in is [r] itself, since [page_base] of the leaf's ppn roundtrips
     through [page_valid]. *)
  Lemma proc_pt_page_acc_vmfault (P : uptd) (vpn : mword 27) (r : mword 64) :
    page_valid r ->
    kmap_static_claims -∗ proc_pt (uptd_insert P vpn r) -∗
      page_own r ∗ (page_own r -∗ proc_pt (uptd_insert P vpn r)).
  Proof.
    intros Hval.
    assert (Hl : (uptd_insert P vpn r).(ud_um) !! vpn = Some (vmfault_pte r)).
    { unfold uptd_insert. cbn [ud_um]. apply lookup_insert. }
    assert (Hpb : page_base (pte_ppn (vmfault_pte r)) = r).
    { rewrite pte_ppn_vmfault. exact (page_base_of_valid r Hval). }
    (* rewrite FORWARD in the instance -- [rewrite <- Hpb] in the goal would
       also hit the [r] inside [uptd_insert]. *)
    pose proof (proc_pt_page_acc (uptd_insert P vpn r) vpn (vmfault_pte r) Hl)
      as Hacc.
    rewrite Hpb in Hacc. exact Hacc.
  Qed.

  (* the root page itself is owned inside [pt_frame] (every node of
     [ptree_own 2 1 t] carries its page's 512 slots and its own identity
     claim, [PtTree.pt_page_own]) -- so [proc_pt] owns the root, the
     interior nodes, the trapframe page and the user pages, each exactly
     once. *)

End ProcPt.
