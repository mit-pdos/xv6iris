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
Require Import TrampPt.
Require Import PtBuild.
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

  (* the root page itself is owned inside [pt_frame] (every node of
     [ptree_own 2 1 t] carries its page's 512 slots and its own identity
     claim, [PtTree.pt_page_own]) -- so [proc_pt] owns the root, the
     interior nodes, the trapframe page and the user pages, each exactly
     once. *)

End ProcPt.
