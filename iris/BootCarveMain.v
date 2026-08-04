(* ====================================================================== *)
(* BootCarveMain.v -- the boot-image carve at MAIN's altitude.              *)
(*                                                                         *)
(* BootCarve.v deliberately stays BELOW the WP tower: it knows the raw      *)
(* memory conjunct, the rwx split at [text_end], the ADDRESS-RANGE          *)
(* vocabulary ([boot_raw_ran] / [boot_ran_split] / [boot_ran_bytes]),       *)
(* words, and the physical boot stack.  The bundles                         *)
(* [SpecMain.wp_main_boot_sconf_body] asks for are stated in the vocabulary *)
(* of the files main's CALLEES own ([KallocInv.page_own],                    *)
(* [SpecFreerange.prun], and -- for slice 2 -- ProcGeom / FdSlots /         *)
(* BcacheInv / DiskInv), so they are carved here, out of those ranges.      *)
(*                                                                         *)
(* THIS FILE HOLDS SLICE 3: kinit's free-page run.  [freerange]'s contract  *)
(* is stated over a LIST of pages [ps] with the pure shape                   *)
(* [prun phystop s1entry ps] plus [[∗ list] p ∈ ps, page_own p], so both     *)
(* halves are produced here from one range, and the list is spelled the way *)
(* [prun] RECURSES ([pg_run]) so that the pure half is a structural          *)
(* induction with no list surgery.                                          *)
(*                                                                         *)
(* NB ALL ARITHMETIC GOES THROUGH THE [uint] BRIDGES BELOW, and the two     *)
(* mword facts are not re-proved here: [add_vec s1 negPGSIZEv] IS           *)
(* [pa_stk s1 512] and [add_vec s1 PGSIZEv] IS [pa_add s1 4096], so         *)
(* [StackOwn.uint_pa_stk] and [PageGeom.kalloc_uint_pa_add] already say     *)
(* what their unsigned values are.                                          *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import RiscvExtras PowerBoot StackOwn.
Require Import KptPt KMap.
Require Import KernelText.
Require Import BootCarve.
Require Import PageGeom KallocInv.
Require Import SpecFreerange.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. The page arithmetic, over plain [Z].                                 *)
(*                                                                        *)
(* This file's Require chain reaches [bitvector.tactics], whose zify hook   *)
(* makes [lia] answer "Cannot find witness" on goals mentioning            *)
(* [bv_unsigned] (durable-notes), so the modular arithmetic is packaged as  *)
(* closed plain-[Z] facts and applied.                                     *)
(* ---------------------------------------------------------------------- *)

Lemma z_mod4096_sub (u : Z) : u mod 4096 = 0 -> (u - 4096) mod 4096 = 0.
Proof. intro H. rewrite Zminus_mod H Z_mod_same_full. reflexivity. Qed.

Lemma z_mod4096_add (u : Z) : u mod 4096 = 0 -> (u + 4096) mod 4096 = 0.
Proof. intro H. rewrite Zplus_mod H Z_mod_same_full. reflexivity. Qed.

(* The cursor equation, in its five uses.  Every literal that appears here is
   a BOUND VARIABLE at the call site ([kmem_lo], [ram_hi], ...) or lives
   inside the helper's own statement, which is what keeps [lia] usable. *)
Lemma z_run_base (u pt : Z) : u + 0 = pt + 4096 -> pt < u.
Proof. lia. Qed.
Lemma z_run_le (u pt k : Z) :
  0 <= k -> u + 4096 * Z.succ k = pt + 4096 -> u <= pt.
Proof. lia. Qed.
Lemma z_run_next (u pt k : Z) :
  u + 4096 * Z.succ k = pt + 4096 -> u + 4096 + 4096 * k = pt + 4096.
Proof. lia. Qed.
Lemma z_run_end (u pt m : Z) :
  u + 4096 * m = pt + 4096 -> u - 4096 + 4096 * m = pt.
Proof. lia. Qed.
Lemma z_run_page (klo u pt khi : Z) :
  klo + 4096 <= u -> u <= pt -> pt <= khi -> klo <= u - 4096 < khi.
Proof. lia. Qed.

(* offset bookkeeping *)
Lemma z_shift_le (a u : Z) : a <= u -> a <= u + 4096.
Proof. lia. Qed.
Lemma z_drop_base (t d u : Z) : 0 <= t -> t + d <= u -> d <= u.
Proof. lia. Qed.
Lemma z_le_self (x : Z) : x - 4096 <= x - 4096 + 4096.
Proof. lia. Qed.
Lemma z_le_succ (x k : Z) :
  0 <= k -> x - 4096 + 4096 <= x - 4096 + 4096 * Z.succ k.
Proof. lia. Qed.
Lemma z_sub_le (t u : Z) : t + 4096 <= u -> t <= u - 4096.
Proof. lia. Qed.
Lemma z_first_page (x k r : Z) :
  0 <= k -> x - 4096 + 4096 * Z.succ k <= r -> x - 4096 + 4096 <= r.
Proof. lia. Qed.
Lemma z_nowrap_le (u pt : Z) :
  u <= pt -> pt + 4096 < 18446744073709551616 ->
  u + 4096 < 18446744073709551616.
Proof. lia. Qed.
Lemma z_nowrap (x k r : Z) :
  0 <= k -> x - 4096 + 4096 * Z.succ k <= r ->
  r + 4096 < 18446744073709551616 -> x + 4096 < 18446744073709551616.
Proof. lia. Qed.
Lemma z_ihi (x k r : Z) :
  x - 4096 + 4096 * Z.succ k <= r -> x + 4096 - 4096 + 4096 * k <= r.
Proof. lia. Qed.
Lemma z_erlo (x : Z) : x - 4096 + 4096 = x + 4096 - 4096.
Proof. lia. Qed.
Lemma z_erhi (x k : Z) :
  x - 4096 + 4096 * Z.succ k = x + 4096 - 4096 + 4096 * k.
Proof. lia. Qed.
Lemma z_le_trans_eq (x pt khi : Z) : x = pt -> pt <= khi -> x <= khi.
Proof. lia. Qed.

(* the closed facts about the layout constants (order goals on literals need
   no [lia] at all: [Z.le] is [(x ?= y) <> Gt], [Z.lt] is [= Lt]) *)
Lemma z_kmem_lo_pos : 0 <= kmem_lo.
Proof. unfold kmem_lo. discriminate. Qed.
Lemma z_text_end_pos : 0 <= text_end.
Proof. unfold text_end. discriminate. Qed.
Lemma z_ram_hi_nowrap : ram_hi + 4096 < 18446744073709551616.
Proof. unfold ram_hi. reflexivity. Qed.
Lemma z_kmem_hi_ram_hi : kmem_hi = ram_hi.
Proof. reflexivity. Qed.
Lemma z_of_nat_4096 : Z.of_nat 4096%nat = 4096.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The page list, spelled the way [prun] recurses.                      *)
(* ---------------------------------------------------------------------- *)

(* [prun pa_end s1 (p :: rest)] wants [p = s1 - PGSIZE] and then the run
   from [s1 + PGSIZE], so THIS is the shape that makes the pure half a
   structural induction.  (freerange's own loop cursor is [s1]: it frees the
   page BELOW the cursor and stops when the cursor passes [pa_end].) *)
Fixpoint pg_run (s1 : mword 64) (n : nat) : list (mword 64) :=
  match n with
  | O => []
  | S k => add_vec s1 negPGSIZEv :: pg_run (add_vec s1 PGSIZEv) k
  end.

Lemma pg_run_length (s1 : mword 64) (n : nat) : length (pg_run s1 n) = n.
Proof.
  revert s1. induction n as [|k IH]; intro s1; [reflexivity |].
  cbn [pg_run length]. f_equal. apply IH.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The two mword bridges: what the cursor's neighbours ARE.             *)
(* ---------------------------------------------------------------------- *)

Lemma pg_below_uint (s1 : mword 64) :
  4096 <= uint s1 -> uint (add_vec s1 negPGSIZEv) = uint s1 - 4096.
Proof.
  intro H.
  assert (Ez : (-4096)%Z = - (8 * Z.of_nat 512%nat)) by (vm_compute; reflexivity).
  assert (E4 : 8 * Z.of_nat 512%nat = 4096) by (vm_compute; reflexivity).
  assert (E : add_vec s1 negPGSIZEv = pa_stk s1 512%nat).
  { unfold pa_stk, add_vec_int, negPGSIZEv. rewrite Ez. reflexivity. }
  assert (Hu : 8 * Z.of_nat 512%nat <= uint s1) by (rewrite E4; exact H).
  rewrite E (uint_pa_stk s1 512%nat Hu) E4. reflexivity.
Qed.

Lemma pg_below (s1 : mword 64) :
  4096 <= uint s1 -> add_vec s1 negPGSIZEv = pa_of_z (uint s1 - 4096).
Proof.
  intro H. rewrite <- (pg_below_uint s1 H). symmetry. apply pa_of_z_uint.
Qed.

Lemma pg_above_uint (s1 : mword 64) :
  uint s1 + 4096 < 18446744073709551616 ->
  uint (add_vec s1 PGSIZEv) = uint s1 + 4096.
Proof.
  intro H.
  assert (E4 : Z.of_nat 4096%nat = 4096) by (vm_compute; reflexivity).
  assert (E : add_vec s1 PGSIZEv = pa_add s1 4096%nat).
  { unfold pa_add, add_vec_int, PGSIZEv. rewrite E4. reflexivity. }
  assert (Hnw : uint s1 + Z.of_nat 4096%nat < 18446744073709551616)
    by (rewrite E4; exact H).
  rewrite E (PageGeom.kalloc_uint_pa_add s1 4096%nat Hnw) E4. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The PURE half: [prun].                                               *)
(* ---------------------------------------------------------------------- *)

(* The run is pinned by ONE equation -- the cursor ends exactly one page
   past [phystop] -- which is what makes both of [prun]'s comparisons
   ([<u] false at every step, true at the end) come out of the same fact. *)
Lemma prun_pg_run (phystop s1 : mword 64) (n : nat) :
  uint s1 + 4096 * Z.of_nat n = uint phystop + 4096 ->
  kmem_lo + 4096 <= uint s1 ->
  uint s1 mod 4096 = 0 ->
  uint phystop <= kmem_hi ->
  uint phystop + 4096 < 18446744073709551616 ->
  prun phystop s1 (pg_run s1 n).
Proof.
  revert s1. induction n as [|k IH]; intros s1 Heq Hlo Hal Hpt Hnw.
  - cbn [pg_run prun]. unfold zopz0zI_u.
    apply (proj2 (Z.ltb_lt _ _)). rewrite Z.mul_0_r in Heq.
    exact (z_run_base _ _ Heq).
  - assert (Hk0 : 0 <= Z.of_nat k) by apply Nat2Z.is_nonneg.
    rewrite Nat2Z.inj_succ in Heq.
    assert (Hle : uint s1 <= uint phystop) by exact (z_run_le _ _ _ Hk0 Heq).
    assert (H4 : 4096 <= uint s1)
      by exact (z_drop_base _ _ _ z_kmem_lo_pos Hlo).
    assert (Hupd : uint (add_vec s1 PGSIZEv) = uint s1 + 4096)
      by exact (pg_above_uint s1 (z_nowrap_le _ _ Hle Hnw)).
    cbn [pg_run prun].
    split; [unfold zopz0zI_u; apply (proj2 (Z.ltb_ge _ _)); exact Hle |].
    split; [reflexivity |].
    split.
    + split.
      * unfold page_aligned, PGSIZE. rewrite (pg_below_uint s1 H4).
        exact (z_mod4096_sub _ Hal).
      * unfold page_in_range. rewrite (pg_below_uint s1 H4).
        exact (z_run_page _ _ _ _ Hlo Hle Hpt).
    + apply IH.
      * rewrite Hupd. exact (z_run_next _ _ _ Heq).
      * rewrite Hupd. exact (z_shift_le _ _ Hlo).
      * rewrite Hupd. exact (z_mod4096_add _ Hal).
      * exact Hpt.
      * exact Hnw.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The RESOURCE half: the pages themselves.                             *)
(* ---------------------------------------------------------------------- *)

Section BootCarveMain.
  Context `{!riscvGS Σ}.

  (* one page, out of its own 4096-byte range: [BootCarve.boot_ran_mem_run]
     hands out the bytes already indexed by [pa_add], and [page_own] is that
     run with the contents forgotten. *)
  Lemma boot_page_own (g : gstate) (lo : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= lo -> lo + 4096 <= ram_hi ->
    kmap_static_claims -∗ boot_raw_ran g lo (lo + 4096)
    -∗ page_own (pa_of_z lo).
  Proof.
    intros Hmem Hlo Hhi. iIntros "#Hcl H".
    assert (E : lo + 4096 = lo + Z.of_nat 4096%nat)
      by (rewrite z_of_nat_4096; reflexivity).
    assert (Hhi' : lo + Z.of_nat 4096%nat <= ram_hi)
      by (rewrite z_of_nat_4096; exact Hhi).
    iDestruct (boot_ran_eq g lo (lo + 4096) lo (lo + Z.of_nat 4096%nat)
                 eq_refl E with "H") as "H".
    iDestruct (boot_ran_mem_run g lo 4096%nat Hmem Hlo Hhi' with "Hcl H") as "Hbs".
    rewrite /page_own. iApply (big_sepL_mono with "Hbs").
    iIntros (j x _) "Hb". rewrite /byte_any. iExists _. iExact "Hb".
  Qed.

  (* ...and the whole run, by the same downward induction as §9's stack:
     ONE cut per page, the cursor moving up. *)
  Lemma boot_pg_run_own (g : gstate) (s1 : mword 64) (n : nat) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end + 4096 <= uint s1 ->
    uint s1 - 4096 + 4096 * Z.of_nat n <= ram_hi ->
    kmap_static_claims -∗
    boot_raw_ran g (uint s1 - 4096) (uint s1 - 4096 + 4096 * Z.of_nat n)
    -∗ ([∗ list] p ∈ pg_run s1 n, page_own p).
  Proof.
    intro Hmem. revert s1. induction n as [|k IH]; intros s1 Hlo Hhi.
    - iIntros "_ _". done.
    - assert (Hk0 : 0 <= Z.of_nat k) by apply Nat2Z.is_nonneg.
      rewrite Nat2Z.inj_succ in Hhi |- *.
      assert (H4 : 4096 <= uint s1)
        by exact (z_drop_base _ _ _ z_text_end_pos Hlo).
      assert (Hd1 : uint s1 - 4096 <= uint s1 - 4096 + 4096)
        by exact (z_le_self _).
      assert (Hd2 : uint s1 - 4096 + 4096
                    <= uint s1 - 4096 + 4096 * Z.succ (Z.of_nat k))
        by exact (z_le_succ _ _ Hk0).
      assert (Hplo : text_end <= uint s1 - 4096) by exact (z_sub_le _ _ Hlo).
      assert (Hphi : uint s1 - 4096 + 4096 <= ram_hi)
        by exact (z_first_page _ _ _ Hk0 Hhi).
      assert (Hupd : uint (add_vec s1 PGSIZEv) = uint s1 + 4096)
        by exact (pg_above_uint s1 (z_nowrap _ _ _ Hk0 Hhi z_ram_hi_nowrap)).
      iIntros "#Hcl H".
      iDestruct (boot_ran_split g _ (uint s1 - 4096 + 4096)
                   (uint s1 - 4096 + 4096 * Z.succ (Z.of_nat k)) Hd1 Hd2
                   with "H") as "[Hp Hrest]".
      iDestruct (boot_page_own g (uint s1 - 4096) Hmem Hplo Hphi with "Hcl Hp")
        as "Hp".
      assert (Hilo : text_end + 4096 <= uint (add_vec s1 PGSIZEv))
        by (rewrite Hupd; exact (z_shift_le _ _ Hlo)).
      assert (Hihi : uint (add_vec s1 PGSIZEv) - 4096
                     + 4096 * Z.of_nat k <= ram_hi)
        by (rewrite Hupd; exact (z_ihi _ _ _ Hhi)).
      assert (Erlo : uint s1 - 4096 + 4096
                     = uint (add_vec s1 PGSIZEv) - 4096)
        by (rewrite Hupd; exact (z_erlo _)).
      assert (Erhi : uint s1 - 4096 + 4096 * Z.succ (Z.of_nat k)
                     = uint (add_vec s1 PGSIZEv) - 4096 + 4096 * Z.of_nat k)
        by (rewrite Hupd; exact (z_erhi _ _)).
      cbn [pg_run]. iSplitL "Hp".
      + rewrite (pg_below s1 H4). iExact "Hp".
      + iDestruct (boot_ran_eq g _ _ _ _ Erlo Erhi with "Hrest") as "Hrest".
        iApply (IH (add_vec s1 PGSIZEv) Hilo Hihi with "Hcl Hrest").
  Qed.

  (* ---- the slice-3 deliverable, both halves at one list ---- *)

  (* kinit's free-page run, exactly as [SpecMain.wp_main_boot_sconf_body] asks
     for it: a page list [ps] with [prun phystop s1entry ps], the pages
     themselves, and its LENGTH (which is what main's budget premise
     [K_kvmmake + 64 + 3 < length ps] is about).  The cursor equation
     [uint s1 + 4096*n = uint phystop + 4096] is what pins the run: the
     cursor ends exactly one page past PHYSTOP. *)
  Lemma boot_kinit_run (g : gstate) (phystop s1 : mword 64) (n : nat) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    uint s1 + 4096 * Z.of_nat n = uint phystop + 4096 ->
    text_end + 4096 <= uint s1 ->
    kmem_lo + 4096 <= uint s1 ->
    uint s1 mod 4096 = 0 ->
    uint phystop <= kmem_hi ->
    uint phystop + 4096 < 18446744073709551616 ->
    kmap_static_claims -∗
    boot_raw_ran g (uint s1 - 4096) (uint phystop)
    -∗ ⌜prun phystop s1 (pg_run s1 n)⌝ ∗
       ⌜length (pg_run s1 n) = n⌝ ∗
       ([∗ list] p ∈ pg_run s1 n, page_own p).
  Proof.
    intros Hmem Heq Hlo Hklo Hal Hpt Hnw. iIntros "#Hcl H".
    assert (Hend : uint s1 - 4096 + 4096 * Z.of_nat n = uint phystop)
      by exact (z_run_end _ _ _ Heq).
    rewrite z_kmem_hi_ram_hi in Hpt.
    assert (Hhi : uint s1 - 4096 + 4096 * Z.of_nat n <= ram_hi)
      by exact (z_le_trans_eq _ _ _ Hend Hpt).
    iSplitR; [iPureIntro; exact (prun_pg_run phystop s1 n Heq Hklo Hal Hpt Hnw) |].
    iSplitR; [iPureIntro; exact (pg_run_length s1 n) |].
    iDestruct (boot_ran_eq g _ _ _ _ eq_refl (eq_sym Hend) with "H") as "H".
    iApply (boot_pg_run_own g s1 n Hmem Hlo Hhi with "Hcl H").
  Qed.

End BootCarveMain.
