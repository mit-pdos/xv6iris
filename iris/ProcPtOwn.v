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
Require Import UptTree.
Require Import UserPtTree.
Require Import ProcPt.
Require Import KallocInv.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d.
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
(* §2b The vmfault step: the leaf the lazy-allocation fault handler       *)
(*     installs, and the descriptor after one page joins the map.         *)
(*     [vmfault_pte r] is spelled EXACTLY as SpecMappages' [ppn0]/post at  *)
(*     [perm := 22] (PTE_W|PTE_U|PTE_R), [npages := 1], so ProofVmfault    *)
(*     meets mappages' postcondition syntactically.                       *)
(* ===================================================================== *)

Definition vmfault_pte (r : mword 64) : mword 64 :=
  mappages_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) 22 0.

Definition uptd_insert (P : uptd) (vpn : mword 27) (r : mword 64) : uptd :=
  UPTD P.(ud_root) P.(ud_tfp) (<[vpn := vmfault_pte r]> P.(ud_um))
       (um_pas (<[vpn := vmfault_pte r]> P.(ud_um))).

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

(* ===================================================================== *)
(* §2c THE VMFAULT LEAF, CLASSIFIED.  [vmfault_pte r] is [mk_pte] of the   *)
(*     ppn of [r] at flag byte 23 = V|R|W|U; the A/D variants add bit 6    *)
(*     and bit 7.  Every variant is a proper 4K leaf; a user LOAD/STORE/   *)
(*     LR/SC/AMO passes its permission check and a user FETCH is denied    *)
(*     (X = 0).  Then the two geometry roundtrips (the ppn of the leaf,    *)
(*     the base of that ppn) and the PGROUNDDOWN bit facts.                *)
(*                                                                        *)
(*     The dispatch recipe is UptTree §1's: [pte_set_ad_zext_concat] turns *)
(*     a variant back into a [mk_pte] at an ADJUSTED flag constant, then   *)
(*     the flag byte / ext field are read off symbolically in the ppn      *)
(*     ([mk_pte_flags] / [mk_pte_ext]) and every predicate is one          *)
(*     [vm_compute] per A/D case.                                          *)
(* ===================================================================== *)

(* mappages' own precondition at [PTE_W|PTE_U|PTE_R] *)
Lemma vmf_perm_ok22 : mappages_perm_ok 22.
Proof.
  unfold mappages_perm_ok. split; [lia|].
  split; [intro s; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* the leaf in [mk_pte] shape: [Z.lor 22 1 = 23] *)
Lemma vmfault_pte_mk (r : mword 64) :
  vmfault_pte r
  = mk_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) 23.
Proof. unfold vmfault_pte. rewrite mappages_pte_0. reflexivity. Qed.

Lemma vmfault_variant_mk (r : mword 64) (a d : mword 1) :
  pte_set_ad (vmfault_pte r) a d
  = mk_pte (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44)
      (Z.lor (Z.land 23 831)
         (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7))).
Proof.
  rewrite vmfault_pte_mk. unfold mk_pte.
  apply (pte_set_ad_zext_concat _ 23 a d). lia.
Qed.

Lemma vmfault_variant_flags (r : mword 64) (a d : mword 1) :
  subrange_vec_dec (pte_set_ad (vmfault_pte r) a d) 7 0
  = (mword_of_int (Z.lor (Z.land 23 831)
       (Z.lor (Z.shiftl (bv_unsigned a) 6)
              (Z.shiftl (bv_unsigned d) 7))) : mword 8).
Proof.
  rewrite vmfault_variant_mk.
  apply mk_pte_flags.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; intuition congruence.
Qed.

Lemma vmfault_variant_ext (r : mword 64) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad (vmfault_pte r) a d) = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite pte_set_ad_ext. rewrite vmfault_pte_mk.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity | lia].
Qed.

(* the 4K-leaf classification, on every A/D variant *)
Lemma vmfault_variant (r : mword 64) (a d : mword 1) :
  pte_valid (pte_set_ad (vmfault_pte r) a d) /\
  pte_leaf (pte_set_ad (vmfault_pte r) a d) /\
  pte_no_napot (pte_set_ad (vmfault_pte r) a d) /\
  pte_pbmt0 (pte_set_ad (vmfault_pte r) a d).
Proof.
  repeat split.
  - intros s. unfold Mk_PTE_Flags.
    rewrite vmfault_variant_flags. rewrite vmfault_variant_ext.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_leaf, Mk_PTE_Flags.
    rewrite vmfault_variant_flags.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_no_napot.
    rewrite vmfault_variant_ext.
    apply kpt_extN_red.
  - unfold pte_pbmt0.
    rewrite vmfault_variant_ext.
    vm_compute. reflexivity.
Qed.

(* the User-access classification [upt_acc_wf] wants: the leaf is R|W|U with
   X = 0, so data accesses pass and a fetch is denied.  [mxr]/[do_sum] stay
   SYMBOLIC (at User [do_sum] is never consulted, and [pte_X = 0] kills the
   [mxr] disjunct), so the dispatch is 4 A/D cases per access, not 16. *)
Local Ltac vmf_check_tac :=
  intros a d mxr do_sum s; unfold Mk_PTE_Flags;
  rewrite vmfault_variant_flags; rewrite vmfault_variant_ext;
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
  vm_compute; reflexivity.

Lemma vmfault_uleaf (r : mword 64) (acc : MemoryAccessType mem_payload) :
  u_acc acc -> uleaf_ok acc (vmfault_pte r) \/ uleaf_denied acc (vmfault_pte r).
Proof.
  intros [-> | [-> | [-> | [-> | [-> | (op & ->)]]]]].
  - right. vmf_check_tac.        (* InstructionFetch: X = 0 *)
  - left. vmf_check_tac.         (* Load Data *)
  - left. vmf_check_tac.         (* Store Data *)
  - left. vmf_check_tac.         (* LoadReserved Data *)
  - left. vmf_check_tac.         (* StoreConditional Data *)
  - left. vmf_check_tac.         (* Atomic (op, Data, Data), op symbolic *)
Qed.

(* ---- the geometry roundtrips --------------------------------------- *)

Lemma pte_ppn_mk_pte (ppn : mword 44) (f : Z) :
  0 <= f < 1024 -> pte_ppn (mk_pte ppn f) = ppn.
Proof.
  intros Hf. unfold pte_ppn. rewrite !autocast_id.
  unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id. apply mk_pte_ppn_field. exact Hf.
Qed.

Lemma pte_ppn_vmfault (r : mword 64) :
  pte_ppn (vmfault_pte r) = autocast (T := mword) (subrange_vec_dec r 55 12).
Proof. rewrite vmfault_pte_mk. apply pte_ppn_mk_pte. lia. Qed.

Local Lemma z_lt_4096_mul (x : Z) : x < 72057594037927936 -> x < 4096 * 17592186044416.
Proof. lia. Qed.

(* [PtBuild.pb_subrange_55_12_unsigned] is [Local] there; same one-liner. *)
Local Lemma ppo_subrange_55_12_unsigned (a : mword 64) :
  bv_unsigned a < 72057594037927936 ->
  bv_unsigned (autocast (T := mword) (subrange_vec_dec a 55 12) : mword 44)
  = bv_unsigned a / 4096.
Proof.
  intros Hlt.
  rewrite autocast_id.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  change (MachineWord.MachineWord.Z_idx (55 - 12 + 1)) with 44%N.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  apply bv_wrap_small.
  unfold bv_modulus.
  change (2 ^ Z.of_N 44) with 17592186044416.
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
Proof.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.and. apply bv_and_unsigned.
Qed.

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
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (11 - 0 + 1)) with 12%N.
  unfold bv_wrap. change (bv_modulus 12) with 4096. reflexivity.
Qed.

Local Lemma z_pgd_mod (x : Z) : (x - x mod 4096) mod 4096 = 0.
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
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - 0 + 1)) with 39%N.
  unfold bv_wrap. change (bv_modulus 39) with 549755813888. reflexivity.
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
(* §3 VALIDITY.  One predicate, over the existing pure pieces plus the    *)
(*    kalloc-page conjunct.                                              *)
(* ===================================================================== *)

(* every page the table hands the process is a kalloc page: 4KB-aligned and
   inside the kernel free-page range.  See design decision (3) at the top. *)
Definition um_pages_valid (um : gmap (mword 27) (mword 64)) : Prop :=
  forall ppn, ppn ∈ um_ppns um -> page_valid (page_base ppn).

Definition proc_pt_wf (P : uptd) : Prop :=
  upt_map_wf P.(ud_um) /\           (* below TRAPFRAME, a proper 4K leaf   *)
  upt_acc_wf P.(ud_um) /\           (* each leaf User-ok or User-denied    *)
  um_pages_valid P.(ud_um) /\       (* every user page is a kalloc page    *)
  page_valid (page_base P.(ud_tfp)).
  (* ... and so is the trapframe page *)

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

Lemma upt_map_wf_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  upt_map_wf um -> vpn <> tramp_vpn -> vpn <> tf_vpn ->
  (bv_unsigned vpn < 67108864)%Z ->
  upt_map_wf (<[vpn := vmfault_pte r]> um).
Proof.
  intros Hwf Hnt Hntf Hlt v w Hl.
  apply lookup_insert_Some in Hl. destruct Hl as [(Hv & Hw) | (_ & Hl)].
  - subst v. subst w. split.
    + rewrite tf_vpn_unsigned.
      apply z_vpn_lt_tf; [exact Hlt | ..].
      * intro He. apply Hnt. apply bv_eq. rewrite tramp_vpn_unsigned. exact He.
      * intro He. apply Hntf. apply bv_eq. rewrite tf_vpn_unsigned. exact He.
    + intros a d. exact (vmfault_variant r a d).
  - exact (Hwf v w Hl).
Qed.

Lemma upt_acc_wf_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  upt_acc_wf um -> upt_acc_wf (<[vpn := vmfault_pte r]> um).
Proof.
  intros Hwf v w Hl acc Hacc.
  apply lookup_insert_Some in Hl. destruct Hl as [(_ & Hw) | (_ & Hl)].
  - subst w. exact (vmfault_uleaf r acc Hacc).
  - exact (Hwf v w Hl acc Hacc).
Qed.

Lemma um_pages_valid_insert_vmfault (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (r : mword 64) :
  um_pages_valid um -> page_valid r ->
  um_pages_valid (<[vpn := vmfault_pte r]> um).
Proof.
  intros Hv Hpv q Hq.
  apply elem_of_um_ppns in Hq. destruct Hq as (v & x & Hl & Hq).
  apply lookup_insert_Some in Hl. destruct Hl as [(_ & Hw) | (_ & Hl)].
  - subst x. rewrite <- Hq. rewrite pte_ppn_vmfault.
    rewrite (page_base_of_valid r Hpv). exact Hpv.
  - apply Hv. apply elem_of_um_ppns. exists v, x. split; [exact Hl | exact Hq].
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

  (* one page joins the footprint.  If its ppn were already there, the
     [big_sepS] would hand us a second full copy -- refuted above. *)
  Lemma upt_pages_own_insert (um : gmap (mword 27) (mword 64))
      (vpn : mword 27) (w : mword 64) :
    um !! vpn = None ->
    phys_page_own (pte_ppn w) -∗ upt_pages_own um -∗ upt_pages_own (<[vpn := w]> um).
  Proof.
    intros Hn. iIntros "Hp Hum".
    rewrite /upt_pages_own.
    rewrite (um_ppns_insert um vpn w Hn).
    destruct (decide (pte_ppn w ∈ um_ppns um)) as [Hin | Hnin].
    - rewrite (big_sepS_delete (fun q => phys_page_own q) (um_ppns um) (pte_ppn w) Hin).
      iDestruct "Hum" as "[Hq _]".
      iDestruct (phys_page_own_dup (pte_ppn w) with "Hp Hq") as %[].
    - rewrite big_sepS_insert; [| exact Hnin].
      iFrame "Hp Hum".
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
      split; [exact um_pages_valid_empty | exact Hvtf]. }
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
  (* THE DOVETAIL WITH walk / mappages (claude-notes/projects/vmfault.md) *)
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
  Proof.
    intros (Hmwf & Hawf & Hpwf & Htfv) Hview Hnone Hlt Hrep Hbase Hval.
    destruct (proj1 (proj1 Hview vpn) Hnone) as (Hnt & Hntf & Hunone).
    pose proof (upt_map_wf_insert_vmfault P.(ud_um) vpn r Hmwf Hnt Hntf Hlt) as Hmwf'.
    iIntros "#Hb Ht Hpg Hown".
    rewrite /proc_pt /proc_pt_own /uptd_insert.
    cbn [ud_root ud_tfp ud_um].
    iSplitR.
    { iPureIntro. unfold proc_pt_wf. cbn [ud_root ud_tfp ud_um].
      split_and!.
      - exact Hmwf'.
      - exact (upt_acc_wf_insert_vmfault P.(ud_um) vpn r Hawf).
      - exact (um_pages_valid_insert_vmfault P.(ud_um) vpn r Hpwf Hval).
      - exact Htfv. }
    iSplitL "Ht".
    { rewrite /pt_frame. iExists t'. iFrame "Ht". iPureIntro.
      exact (upt_spec_of_rep0 P.(ud_root) P.(ud_tfp)
               (<[vpn := vmfault_pte r]> P.(ud_um))
               (<[vpn := vmfault_pte r]> m_ad) t' Hmwf'
               (upt_ad_view_insert P.(ud_tfp) P.(ud_um) m_ad vpn (vmfault_pte r)
                  Hview Hnone)
               Hrep Hbase). }
    iApply (upt_pages_own_insert P.(ud_um) vpn (vmfault_pte r) Hunone with "[Hpg] Hown").
    iApply (page_own_to_phys_vmfault r Hval with "Hb Hpg").
  Qed.

  (* the root page itself is owned inside [pt_frame] (every node of
     [ptree_own 2 1 t] carries its page's 512 slots and its own identity
     claim, [PtTree.pt_page_own]) -- so [proc_pt] owns the root, the
     interior nodes, the trapframe page and the user pages, each exactly
     once. *)

End ProcPt.
