(* UmCovered.v -- THE DUAL OF [ProcPtOwn.um_below], and the counting argument
   that makes it worth having: a user page table whose every page below [sz]
   is mapped cannot have [sz] larger than physical memory.

   ---- WHY THIS FILE EXISTS -------------------------------------------------

   [SpecUvmalloc] demands [uint newsz <= uvm_maxsz] ([uvm_maxsz = TRAPFRAME]).
   That premise is not decoration: it is what refutes [panic("mappages:
   remap")] at TRAPFRAME and [panic("walk")] above MAXVA, and it is why
   [SpecMappages] may demand its target run be unmapped.

   Every caller could pay it by testing -- growproc does ([sz + n > TRAPFRAME]
   returns -1) -- except kexec, which hands uvmalloc [ph.vaddr + ph.memsz]
   read straight out of an untrusted file and tests only that [memsz >=
   filesz], that the sum does not wrap, and that [vaddr] is page-aligned.  So
   the premise is unpayable there, and it cannot be moved into kexec's
   contract either: that contract takes a PATH, so the file's program headers
   live behind phase A's existential and are not nameable in the statement.

   THE CODE IS NEVERTHELESS SAFE, and the reason is a counting argument
   rather than a test.  For uvmalloc to reach TRAPFRAME it must first map
   EVERY page below it -- its loop is [for (a = PGROUNDUP(oldsz); a < newsz;
   a += PGSIZE)] with a kalloc per iteration -- and that is 2^26 pages, far
   more than [end .. PHYSTOP) holds.  kalloc returns 0 long first, uvmdealloc
   rolls back, and uvmalloc returns 0.  The malformed executable takes
   [bad:]; nothing panics.

   THIS FILE IS THAT ARGUMENT, as a pure fact about the map:

     every page below [z] is mapped                       ([um_covered_z])
     + distinct vpns name distinct pages                  ([um_inj])
     + every page named is a kalloc page                  ([um_pages_valid])
     ------------------------------------------------------------------
     z <= 4096 * kmem_maxppn = 0x88000000                 ([um_covered_bound])

   and [0x88000000] is PHYSTOP, which is 120x below [uvm_maxsz].  So a caller
   that can show its table is COVERED gets uvmalloc's size premise for free,
   and does not have to test for it.

   Note the argument needs BOTH halves of the no-aliasing story.  Without
   [um_inj] a table could map one page at every vpn and cover any [z] at all;
   without [um_pages_valid] the pages it names need not be finitely many.
   Both are already conjuncts of [ProcPtOwn.proc_pt_wf], so a holder of
   [proc_pt] pays nothing for them -- see [proc_pt_covered_maxsz], which is
   the form callers actually use.

   PURE: no proofmode, no Iris resources, in the style of [ElfEnc.v] /
   [BlockWords.v].  It sits between [ProcPtOwn.v] and [SpecUvmalloc.v] rather
   than inside [ProcPtOwn.v] so that adding it does not recompile the whole
   mid-tree. *)
(* NB: no [From Stdlib Require List] -- its [NoDup_cons] shadows stdpp's
   (which is the iff), and the shadowing shows up as "Cannot find a
   homogeneous relation to rewrite", not as a name clash. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap list sets fin_sets bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import PageGeom.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  A PIGEONHOLE FOR FINITE SETS.                                         *)
(* ===================================================================== *)
(* stdpp has [subseteq_size] but no "an injection bounds the cardinality",
   and no locally-injective [NoDup_fmap] (its [NoDup_fmap_2] wants a GLOBAL
   [Inj] instance, which neither of this file's two maps has -- both are
   injective only on the set they are applied to).  Both are three lines. *)

(* [base.NoDup] EXPLICITLY: something in this file's Require chain re-imports
   Stdlib's [List], whose [NoDup] then shadows stdpp's -- and the mismatch
   surfaces only where the two meet, as "expected base.NoDup (?x :: ?l)". *)
Lemma NoDup_fmap_strong {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, x ∈ l -> y ∈ l -> f x = f y -> x = y) ->
  base.NoDup l -> base.NoDup (f <$> l).
Proof.
  induction l as [| a l IH]; intros Hinj Hnd; [ constructor |].
  rewrite fmap_cons.
  pose proof (NoDup_cons_1_1 _ _ Hnd) as Hnin.
  pose proof (NoDup_cons_1_2 _ _ Hnd) as Hnd'.
  apply NoDup_cons_2.
  - intros Hin. apply elem_of_list_fmap in Hin as (y & Hfy & Hy).
    apply Hnin.
    assert (Hay : a = y).
    { apply Hinj; [ apply elem_of_cons; left; reflexivity
                  | apply elem_of_cons; right; exact Hy
                  | exact Hfy ]. }
    rewrite Hay. exact Hy.
  - apply IH; [| exact Hnd'].
    intros x y Hx Hy Hf.
    apply Hinj; [ apply elem_of_cons; right; exact Hx
                | apply elem_of_cons; right; exact Hy
                | exact Hf ].
Qed.

Lemma set_card_inj `{FinSet A C} `{FinSet B D} (f : A -> B) (X : C) (Y : D) :
  (forall x1 x2, x1 ∈ X -> x2 ∈ X -> f x1 = f x2 -> x1 = x2) ->
  (forall x, x ∈ X -> f x ∈ Y) ->
  (size X <= size Y)%nat.
Proof.
  intros Hinj Hmap.
  assert (Hsz : size (set_map (D := D) f X) = size X).
  { unfold set_map. rewrite size_list_to_set.
    - rewrite length_fmap. reflexivity.
    - apply NoDup_fmap_strong; [| apply NoDup_elements].
      intros x y Hx Hy Hf.
      apply Hinj; [ by apply elem_of_elements | by apply elem_of_elements
                  | exact Hf ]. }
  rewrite <- Hsz. apply subseteq_size.
  intros y Hy. apply elem_of_map in Hy as (x & -> & Hx). exact (Hmap x Hx).
Qed.

(* ===================================================================== *)
(*  THE PAGE SUPPLY.                                                      *)
(* ===================================================================== *)
(* An upper bound on how many distinct pages a [page_valid] address can
   name.  [page_valid] is [kmem_lo <= uint p < kmem_hi] plus 4K-alignment
   ([PageGeom.v]), so [uint p / 4096 < kmem_hi / 4096]; the [kmem_lo] end is
   deliberately NOT subtracted, because the bound is 120x looser than it
   needs to be either way and this keeps it a literal that [lia] can see.
   [kmem_hi] is PHYSTOP = 0x88000000. *)
(* [Z.to_nat] of a Z literal, never the [nat] literal itself: a [nat]
   equation whose RHS is past Rocq's abstraction threshold elaborates to an
   opaque [Nat.of_num_uint] application that [lia] cannot relate to a
   computed product (durable-notes.md).  Everything downstream goes through
   [kmem_maxppn_Z] rather than [unfold]. *)
Definition kmem_maxppn : nat := Z.to_nat 557056.   (* 0x88000 = kmem_hi/4096 *)

Lemma kmem_maxppn_Z : Z.of_nat kmem_maxppn = 557056%Z.
Proof. unfold kmem_maxppn. rewrite Z2Nat.id; [reflexivity | lia]. Qed.

Lemma kmem_maxppn_val : (4096 * Z.of_nat kmem_maxppn = 2281701376)%Z.
Proof. rewrite kmem_maxppn_Z. lia. Qed.

(* ...and it is far below the user region's top, which is the whole point. *)
Lemma kmem_maxppn_uvm : (4096 * Z.of_nat kmem_maxppn <= uvm_maxsz)%Z.
Proof. rewrite kmem_maxppn_val, uvm_maxsz_val. lia. Qed.

Lemma page_valid_ppn_lt (ppn : mword 44) :
  page_valid (page_base ppn) -> (bv_unsigned ppn < Z.of_nat kmem_maxppn)%Z.
Proof.
  intros [_ [_ Hhi]].
  rewrite uint_unsigned, page_base_ppn_unsigned in Hhi.
  unfold kmem_hi in Hhi. rewrite kmem_maxppn_Z. lia.
Qed.

(* ===================================================================== *)
(*  COVERAGE.                                                             *)
(* ===================================================================== *)
(* [ProcPtOwn.um_below]'s dual.  Note it says only that the entry EXISTS --
   not that it is a valid user leaf.  That is deliberate and load-bearing:
   uvmalloc's postcondition pins the resulting map's DOMAIN and nothing about
   the words in it, so a coverage predicate carrying a [pte_vu] conjunct
   would not be inductive across the very call the invariant exists for. *)
Definition um_covered_z (z : Z) (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn : mword 27, (bv_unsigned vpn * 4096 < z)%Z -> is_Some (um !! vpn).

Definition um_covered (szv : mword 64) (um : gmap (mword 27) (mword 64)) : Prop :=
  um_covered_z (bv_unsigned szv) um.

Lemma um_covered_z_mono (z z' : Z) (um : gmap (mword 27) (mword 64)) :
  (z' <= z)%Z -> um_covered_z z um -> um_covered_z z' um.
Proof. intros Hle Hc vpn Hlt. apply Hc. lia. Qed.

Lemma um_covered_zero (um : gmap (mword 27) (mword 64)) :
  um_covered (mword_of_int 0 : mword 64) um.
Proof.
  intros vpn Hlt. exfalso.
  pose proof (bv_unsigned_in_range _ vpn) as [Hlo _].
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 64) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz in Hlt. lia.
Qed.

Lemma um_covered_z_subseteq (z : Z) (um um' : gmap (mword 27) (mword 64)) :
  dom um ⊆ dom um' -> um_covered_z z um -> um_covered_z z um'.
Proof.
  intros Hsub Hc vpn Hlt.
  apply elem_of_dom. apply Hsub. apply elem_of_dom. exact (Hc vpn Hlt).
Qed.

(* ===================================================================== *)
(*  THE COUNTING ARGUMENT.                                                *)
(* ===================================================================== *)

(* (1) a table with no aliasing maps no more pages than there are pages. *)
Lemma um_dom_card (um : gmap (mword 27) (mword 64)) :
  um_pages_valid um -> um_inj um -> (size (dom um) <= kmem_maxppn)%nat.
Proof.
  intros Hpv Hinj.
  pose (f := fun vpn : mword 27 =>
               match um !! vpn with
               | Some w => Z.to_nat (bv_unsigned (pte_ppn w))
               | None => 0%nat
               end).
  assert (Hval : forall vpn w, um !! vpn = Some w ->
                   (bv_unsigned (pte_ppn w) < Z.of_nat kmem_maxppn)%Z).
  { intros vpn w Hl. apply page_valid_ppn_lt. apply Hpv.
    apply elem_of_um_ppns. exists vpn, w. split; [exact Hl | reflexivity]. }
  rewrite <- (size_set_seq (C := gset nat) 0 kmem_maxppn).
  apply (set_card_inj f).
  - intros v1 v2 Hv1 Hv2 Hf.
    apply elem_of_dom in Hv1 as [w1 Hw1]. apply elem_of_dom in Hv2 as [w2 Hw2].
    unfold f in Hf. rewrite Hw1, Hw2 in Hf.
    pose proof (bv_unsigned_in_range _ (pte_ppn w1)) as [Hp1 _].
    pose proof (bv_unsigned_in_range _ (pte_ppn w2)) as [Hp2 _].
    assert (Hq : bv_unsigned (pte_ppn w1) = bv_unsigned (pte_ppn w2)) by lia.
    refine (Hinj v1 v2 w1 w2 Hw1 Hw2 _). apply bv_eq. exact Hq.
  - intros vpn Hvpn.
    apply elem_of_dom in Hvpn as [w Hw].
    apply elem_of_set_seq. unfold f. rewrite Hw.
    pose proof (bv_unsigned_in_range _ (pte_ppn w)) as [Hp0 _].
    pose proof (Hval vpn w Hw). pose proof kmem_maxppn_Z. lia.
Qed.

(* (2) a COVERED table maps at least as many pages as [z] spans. *)
Lemma um_covered_bound (z : Z) (um : gmap (mword 27) (mword 64)) :
  um_pages_valid um -> um_inj um -> um_covered_z z um ->
  (z <= 4096 * Z.of_nat kmem_maxppn)%Z.
Proof.
  intros Hpv Hinj Hc.
  pose proof kmem_maxppn_Z as HN.
  destruct (Z_le_gt_dec z (4096 * Z.of_nat kmem_maxppn)) as [Hle | Hgt];
    [exact Hle | exfalso].
  (* [kmem_maxppn + 1] distinct vpns, all covered, all in [dom um] *)
  pose (g := fun k : nat => (Z_to_bv 27 (Z.of_nat k) : mword 27)).
  assert (Hgu : forall k : nat, (k <= kmem_maxppn)%nat ->
                  bv_unsigned (g k) = Z.of_nat k).
  { intros k Hk. unfold g. apply Z_to_bv_small.
    assert (Hbm : bv_modulus 27 = 134217728%Z) by (vm_compute; reflexivity).
    rewrite Hbm.
    assert (HkZ : (Z.of_nat k <= Z.of_nat kmem_maxppn)%Z) by lia. lia. }
  assert (Hcard : (S kmem_maxppn <= size (dom um))%nat).
  { rewrite <- (size_set_seq (C := gset nat) 0 (S kmem_maxppn)).
    apply (set_card_inj g).
    - intros k1 k2 Hk1 Hk2 Hf.
      apply elem_of_set_seq in Hk1. apply elem_of_set_seq in Hk2.
      assert (Hu : bv_unsigned (g k1) = bv_unsigned (g k2)) by (by rewrite Hf).
      rewrite (Hgu k1 ltac:(lia)), (Hgu k2 ltac:(lia)) in Hu. lia.
    - intros k Hk. apply elem_of_set_seq in Hk.
      apply elem_of_dom. apply Hc.
      rewrite (Hgu k ltac:(lia)).
      assert (Z.of_nat k <= Z.of_nat kmem_maxppn)%Z by lia. lia. }
  pose proof (um_dom_card um Hpv Hinj). lia.
Qed.

(* (3) the form callers use: [proc_pt]'s own well-formedness supplies both
   halves, so a covered descriptor's size is bounded by nothing but the
   machine's memory -- and hence is far below [uvm_maxsz]. *)
Lemma proc_pt_covered_bound (P : uptd) (z : Z) :
  proc_pt_wf P -> um_covered_z z P.(ud_um) -> (z <= uvm_maxsz)%Z.
Proof.
  intros (_ & _ & Hpv & Hinj & _) Hc.
  pose proof (um_covered_bound z P.(ud_um) Hpv Hinj Hc).
  pose proof kmem_maxppn_uvm. lia.
Qed.

Lemma proc_pt_covered_maxsz (P : uptd) (szv : mword 64) :
  proc_pt_wf P -> um_covered szv P.(ud_um) ->
  (bv_unsigned szv <= uvm_maxsz)%Z.
Proof. intros Hwf Hc. exact (proc_pt_covered_bound P _ Hwf Hc). Qed.

(* ===================================================================== *)
(*  COVERAGE ACROSS A uvmalloc RUN.                                        *)
(* ===================================================================== *)
(* uvmalloc maps the run [PGROUNDUP(oldsz) .. ) one page at a time, so after
   [j] iterations everything below [PGROUNDUP(oldsz) + 4096*j] is mapped: the
   caller's coverage handles [0 .. oldsz), and the run itself handles
   [PGROUNDUP(oldsz) .. ) -- the two ABUT, because a page-aligned address at
   or above [oldsz] is at or above [PGROUNDUP(oldsz)], which is what makes
   the gap [oldsz .. PGROUNDUP(oldsz)) contain no page BASE at all. *)
Lemma um_covered_run (oldsz : mword 64) (um umj : gmap (mword 27) (mword 64))
    (j : nat) :
  (bv_unsigned oldsz <= uvm_maxsz)%Z ->
  um_covered oldsz um ->
  dom umj = dom um ∪ vpn_run (svpn_of (pgroundup oldsz)) j ->
  um_covered_z (bv_unsigned (pgroundup oldsz) + 4096 * Z.of_nat j) umj.
Proof.
  intros Hob Hc Hdom vpn Hlt.
  destruct (pgroundup_maxsz oldsz Hob) as [[Hge Hle] Hmod].
  pose proof (bv_unsigned_in_range _ (pgroundup oldsz)) as [Hpu0 _].
  pose proof (bv_unsigned_in_range _ vpn) as [Hv0 Hvhi].
  assert (Hbm27 : bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728%Z)
    by (vm_compute; reflexivity).
  rewrite Hbm27 in Hvhi.
  pose proof Hob as Hob'. rewrite uvm_maxsz_val in Hob', Hle.
  (* [PGROUNDUP] never overshoots by a whole page *)
  assert (Hnw64 : (bv_unsigned oldsz + 4095 < 2 ^ 64)%Z).
  { change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  assert (Hpule : (bv_unsigned (pgroundup oldsz) <= bv_unsigned oldsz + 4095)%Z).
  { rewrite (pgroundup_unsigned oldsz Hnw64).
    pose proof (Z.mod_pos_bound (bv_unsigned oldsz + 4095) 4096 ltac:(lia)).
    lia. }
  (* a vpn's base address is a multiple of the page size *)
  assert (Hvmul : ((bv_unsigned vpn * 4096) mod 4096 = 0)%Z)
    by (apply Z_mod_mult).
  apply elem_of_dom. rewrite Hdom.
  destruct (Z_lt_ge_dec (bv_unsigned vpn * 4096) (bv_unsigned oldsz))
    as [Hlo | Hhi].
  - (* below [oldsz]: the caller's coverage *)
    apply elem_of_union_l. apply elem_of_dom. exact (Hc vpn Hlo).
  - (* at or above [oldsz]: a page BASE, hence at or above PGROUNDUP(oldsz) --
       the gap [oldsz .. PGROUNDUP(oldsz)) is shorter than a page, so it
       contains no multiple of 4096 at all. *)
    apply elem_of_union_r. apply elem_of_vpn_run.
    assert (Hpuv : (bv_unsigned (pgroundup oldsz) <= bv_unsigned vpn * 4096)%Z).
    { destruct (Z_lt_ge_dec (bv_unsigned vpn * 4096)
                            (bv_unsigned (pgroundup oldsz))) as [Hc2 | Hc3];
        [| lia].
      exfalso.
      assert (Hdm : ((bv_unsigned (pgroundup oldsz) - bv_unsigned vpn * 4096)
                       mod 4096 = 0)%Z).
      { rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hmod, Hvmul.
        reflexivity. }
      assert (Hd : (0 <= bv_unsigned (pgroundup oldsz)
                         - bv_unsigned vpn * 4096 < 4096)%Z) by lia.
      rewrite (Z.mod_small _ 4096 Hd) in Hdm. lia. }
    pose (i := Z.to_nat ((bv_unsigned vpn * 4096
                          - bv_unsigned (pgroundup oldsz)) / 4096)).
    assert (Hi0 : (0 <= (bv_unsigned vpn * 4096
                         - bv_unsigned (pgroundup oldsz)) / 4096)%Z)
      by (apply Z.div_pos; lia).
    assert (Hdiv : ((bv_unsigned vpn * 4096
                     - bv_unsigned (pgroundup oldsz)) / 4096 * 4096
                    = bv_unsigned vpn * 4096 - bv_unsigned (pgroundup oldsz))%Z).
    { assert (Hm : ((bv_unsigned vpn * 4096
                     - bv_unsigned (pgroundup oldsz)) mod 4096 = 0)%Z).
      { rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hmod, Hvmul.
        reflexivity. }
      pose proof (Z_div_mod_eq_full
                    (bv_unsigned vpn * 4096
                     - bv_unsigned (pgroundup oldsz)) 4096). lia. }
    assert (HiZ : Z.of_nat i = ((bv_unsigned vpn * 4096
                                 - bv_unsigned (pgroundup oldsz)) / 4096)%Z)
      by (unfold i; rewrite Z2Nat.id; [reflexivity | exact Hi0]).
    exists i. split.
    + apply Nat2Z.inj_lt. rewrite HiZ. lia.
    + assert (Hvp0 : bv_unsigned (svpn_of (pgroundup oldsz))
                     = (bv_unsigned (pgroundup oldsz) / 4096)%Z).
      { apply svpn_of_unsigned_small. rewrite uvm_maxsz_val. lia. }
      assert (Hpq : (bv_unsigned (pgroundup oldsz) / 4096 * 4096
                     = bv_unsigned (pgroundup oldsz))%Z).
      { pose proof (Z_div_mod_eq_full (bv_unsigned (pgroundup oldsz)) 4096).
        lia. }
      assert (Hnw : (bv_unsigned (svpn_of (pgroundup oldsz)) + Z.of_nat i
                     < 134217728)%Z) by (rewrite Hvp0, HiZ; lia).
      apply bv_eq. rewrite (vpn_at_unsigned _ _ Hnw), Hvp0, HiZ. lia.
Qed.

(* THE ONE LEMMA uvmalloc's LOOP NEEDS: at step [j] the address it is about
   to map is inside the physical page window, and hence far below MAXVA.
   Everything else in this file exists to make this one line available. *)
Lemma uvma_addr_bound (P Pj : uptd) (oldsz : mword 64) (j : nat) :
  (bv_unsigned oldsz <= uvm_maxsz)%Z ->
  proc_pt_wf Pj ->
  um_covered oldsz P.(ud_um) ->
  dom Pj.(ud_um) = dom P.(ud_um) ∪ vpn_run (svpn_of (pgroundup oldsz)) j ->
  (bv_unsigned (pgroundup oldsz) + 4096 * Z.of_nat j
   <= 4096 * Z.of_nat kmem_maxppn)%Z.
Proof.
  intros Hob (_ & _ & Hpv & Hinj & _) Hc Hdom.
  apply (um_covered_bound _ Pj.(ud_um) Hpv Hinj).
  exact (um_covered_run oldsz P.(ud_um) Pj.(ud_um) j Hob Hc Hdom).
Qed.

(* ...and the form a CALLER uses to keep coverage inductive across the call:
   uvmalloc's postcondition pins the new map's domain, and
   [PGROUNDUP(oldsz) + 4096 * uvma_np oldsz newsz] is at or above [newsz] by
   construction, so the run reaches the new size. *)
Lemma um_covered_after (oldsz newsz : mword 64)
    (um um' : gmap (mword 27) (mword 64)) :
  (bv_unsigned oldsz <= uvm_maxsz)%Z ->
  (bv_unsigned oldsz <= bv_unsigned newsz)%Z ->
  um_covered oldsz um ->
  dom um' = dom um ∪ vpn_run (svpn_of (pgroundup oldsz)) (uvma_np oldsz newsz) ->
  um_covered newsz um'.
Proof.
  intros Hob Hle Hc Hdom.
  pose proof (um_covered_run oldsz um um' (uvma_np oldsz newsz) Hob Hc Hdom)
    as Hrun.
  (* [PGROUNDUP(oldsz) + 4096 * ceil((newsz - PGROUNDUP oldsz)/4096) >= newsz] *)
  destruct (pgroundup_maxsz oldsz Hob) as [[Hge Hple] Hmod].
  rewrite uvm_maxsz_val in Hob, Hple.
  assert (Hnw64 : (bv_unsigned oldsz + 4095 < 2 ^ 64)%Z).
  { pose proof (bv_unsigned_in_range _ oldsz) as [Ho0 _].
    change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  assert (Hpule : (bv_unsigned (pgroundup oldsz) <= bv_unsigned oldsz + 4095)%Z).
  { rewrite (pgroundup_unsigned oldsz Hnw64).
    pose proof (Z.mod_pos_bound (bv_unsigned oldsz + 4095) 4096 ltac:(lia)).
    lia. }
  assert (Hreach : (bv_unsigned newsz
                    <= bv_unsigned (pgroundup oldsz)
                       + 4096 * Z.of_nat (uvma_np oldsz newsz))%Z).
  { unfold uvma_np. rewrite Z2Nat.id.
    - pose proof (Z_div_mod_eq_full
                    (bv_unsigned newsz - bv_unsigned (pgroundup oldsz) + 4095)
                    4096) as Hd.
      pose proof (Z.mod_pos_bound
                    (bv_unsigned newsz - bv_unsigned (pgroundup oldsz) + 4095)
                    4096 ltac:(lia)) as Hm.
      lia.
    - apply Z.div_pos; lia. }
  exact (um_covered_z_mono _ _ _ Hreach Hrun).
Qed.
