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
Require Import WpLock SpecProcinit.
(* the vocabulary of the STRUCTURED conjuncts (slice 2b).  [Import] is not
   transitive, so each file whose predicate is named below has to be imported
   here even though [SpecMain] already requires all of them. *)
Require Import ProcGeom UserPtTree ProcInv SwtchCtx SchedCtx.
Require Import SleepLock BcacheInv SpecIinit.
Require Import DiskInv SpecVirtioDiskInit.
Require Import SpecMain.
Local Open Scope Z_scope.

(* --- the alignment arithmetic the structured carves need, over plain [Z] --- *)
(* Divisor-generic, because the shapes mix [↦₈] and [↦₄] cells: an OFFSET into
   a record, and the base of the [i]th element of a stride family. *)
Lemma z_mod_addo (d A o : Z) : A mod d = 0 -> o mod d = 0 -> (A + o) mod d = 0.
Proof. intros H1 H2. rewrite Zplus_mod H1 H2. reflexivity. Qed.

Lemma z_mod_mul (d b s : Z) (i : nat) :
  b mod d = 0 -> s mod d = 0 -> (b + s * Z.of_nat i) mod d = 0.
Proof.
  intros H1 H2. rewrite Zplus_mod H1 Zmult_mod H2 Z.mul_0_l. reflexivity.
Qed.

Lemma z_mod8_addo (A o : Z) :
  A mod 8 = 0 -> o mod 8 = 0 -> (A + o) mod 8 = 0.
Proof. exact (z_mod_addo 8 A o). Qed.

Lemma z_mod8_mod4 (A : Z) : A mod 8 = 0 -> A mod 4 = 0.
Proof.
  intro H. apply Z.mod_divide in H; [| lia]. apply Z.mod_divide; [lia |].
  apply (Z.divide_trans 4 8); [exists 2; reflexivity | exact H].
Qed.

(* the two window-bookkeeping steps a stride family's per-element carve needs,
   over VARIABLES (so no layout literal ever reaches the zify hook): the
   element is at or above the base, and its own record fits inside the array's
   upper bound.  [stride * N] is one atom on both sides, which is what keeps
   these linear. *)
Lemma z_lo_trans (t base A : Z) : t <= base -> base <= A -> t <= A.
Proof. lia. Qed.

Lemma z_win_hi (A base stride N w hi : Z) :
  A + stride <= base + stride * N -> base + stride * N <= hi -> w <= stride ->
  A + w <= hi.
Proof. lia. Qed.

(* THE side-condition lemma every stride family's per-element carve is applied
   through: out of the element's index and the family's four CLOSED facts (the
   base is above [lo], the array's top is below [hi], the record fits in the
   stride, base and stride are 8-aligned) it produces exactly the three
   premises a cell carve takes.  Written once, over variables: the caller's
   whole obligation per family is four [vm_compute]s. *)
Lemma z_stride_side (base stride : Z) (N : nat) (w lo hi : Z) (i : nat) (A : Z) :
  (i < N)%nat -> A = base + stride * Z.of_nat i ->
  0 <= w <= stride -> lo <= base -> base + stride * Z.of_nat N <= hi ->
  base mod 8 = 0 -> stride mod 8 = 0 ->
  lo <= A /\ A + w <= hi /\ A mod 8 = 0.
Proof.
  intros Hi HA Hw Hlo Hhi Hb8 Hs8.
  assert (Hst : 0 <= stride) by lia.
  assert (Hi0 : 0 <= Z.of_nat i) by apply Nat2Z.is_nonneg.
  assert (H1 : 0 <= stride * Z.of_nat i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (H2 : stride * (Z.of_nat i + 1) <= stride * Z.of_nat N).
  { apply Z.mul_le_mono_nonneg_l; [exact Hst |].
    assert (Hle : Z.of_nat (S i) <= Z.of_nat N) by (apply inj_le; lia).
    rewrite Nat2Z.inj_succ in Hle. lia. }
  split_and!; [lia | rewrite HA; lia | rewrite HA; exact (z_mod_mul 8 base stride i Hb8 Hs8)].
Qed.

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
(* 0b. The [struct disk] cell addresses, in [pa_of_z] spelling.            *)
(*                                                                        *)
(* [DiskInv]'s geometry is [pa_add disk_base <nat offset>] rather than the *)
(* [add_vec _ (mword_of_int _)] every other struct field uses, so the      *)
(* bridge is [BootCarve.pa_add_of_z] and the whole content is pushing      *)
(* [Z.of_nat] through the offset.  [disk_lock] is the one address of the   *)
(* eleven main locks that needs a bridge at all (the other ten ARE         *)
(* [mword_of_int <symbol>]).                                              *)
(* ---------------------------------------------------------------------- *)

Lemma d_info_b_of_z (i : nat) :
  d_info_b i = pa_of_z (KernelSyms.disk + 40 + 16 * Z.of_nat i).
Proof. unfold d_info_b. rewrite pa_add_of_z. f_equal. lia. Qed.

Lemma d_info_status_of_z (i : nat) :
  d_info_status i
  = pa_add (pa_of_z (KernelSyms.disk + 40 + 16 * Z.of_nat i)) 8%nat.
Proof. unfold d_info_status. rewrite !pa_add_of_z. f_equal. lia. Qed.

Lemma d_ops_of_z (i : nat) :
  d_ops i = pa_of_z (KernelSyms.disk + 168 + 16 * Z.of_nat i).
Proof. unfold d_ops. rewrite pa_add_of_z. f_equal. lia. Qed.

Lemma d_ops_res_of_z (i : nat) :
  pa_add disk_base (168 + 16 * i + 4)%nat
  = pa_add (pa_of_z (KernelSyms.disk + 168 + 16 * Z.of_nat i)) 4%nat.
Proof. rewrite !pa_add_of_z. f_equal. lia. Qed.

Lemma d_ops_sec_of_z (i : nat) :
  pa_add disk_base (168 + 16 * i + 8)%nat
  = pa_add (pa_of_z (KernelSyms.disk + 168 + 16 * Z.of_nat i)) 8%nat.
Proof. rewrite !pa_add_of_z. f_equal. lia. Qed.

(* The three index families' addresses, in the family carve's own spelling.
   All three hold BY DEFINITION -- [ArrCursor.acur base stride i] IS
   [pa_of_z (base + stride * i)] -- and [proc_addr] is that same term up to
   one [add_vec] normalisation ([SpecProcinit.proc_addr_acur]). *)
Lemma bnode_of_z (k : nat) :
  bnode k = pa_of_z (buf_base + buf_stride * Z.of_nat k).
Proof. reflexivity. Qed.

Lemma inode_lock_of_z (i : nat) :
  inode_lock i = pa_of_z (inode_lock_base + inode_stride * Z.of_nat i).
Proof. reflexivity. Qed.

Lemma proc_addr_of_z (i : nat) :
  proc_addr i = pa_of_z (KernelSyms.proc + proc_size * Z.of_nat i).
Proof. rewrite proc_addr_acur. reflexivity. Qed.

Lemma disk_lock_of_z : disk_lock = pa_of_z (KernelSyms.disk + 296).
Proof.
  assert (E : (sign_extend' 64 (mword_of_int 0x128 : mword 12) : mword 64)
              = mword_of_int 296) by (apply bv_eq; vm_compute; reflexivity).
  unfold disk_lock. rewrite E. apply off_of_z.
Qed.

(* the eleven [struct spinlock] windows [main_locks_raw] enumerates, IN
   ADDRESS ORDER and pairwise disjoint -- which is what lets a client cut all
   eleven out of the one .bss range with [boot_ran_split] alone.  Every step
   is [x + 24 <= y] on two literals, so the whole check is one [vm_compute]
   per conjunct.  (The full .bss decomposition -- which of these gaps holds
   which other bundle -- is tabulated in claude-notes/projects/crash.md.) *)
Lemma main_lock_windows :
  img_end <= KernelSyms.cons /\
  KernelSyms.cons + 24 <= KernelSyms.pr /\
  KernelSyms.pr + 24 <= KernelSyms.tx_lock /\
  KernelSyms.tx_lock + 24 <= KernelSyms.kmem /\
  KernelSyms.kmem + 24 <= KernelSyms.pid_lock /\
  KernelSyms.pid_lock + 24 <= KernelSyms.wait_lock /\
  KernelSyms.wait_lock + 24 <= KernelSyms.tickslock /\
  KernelSyms.tickslock + 24 <= KernelSyms.bcache /\
  KernelSyms.bcache + 24 <= KernelSyms.itable /\
  KernelSyms.itable + 24 <= KernelSyms.ftable /\
  KernelSyms.ftable + 24 <= KernelSyms.disk + 296 /\
  KernelSyms.disk + 296 + 24 <= ram_hi.
Proof. split_and!; vm_compute; discriminate. Qed.

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
  Context `{!riscvGS Σ, !lockG Σ}.

  (* ------------------------------------------------------------------ *)
  (* The LOCK TRIPLE, out of a [struct spinlock]'s own 24 bytes.         *)
  (*                                                                    *)
  (* [SpecProcinit.lk_raw] is the shape EVERY uninitialised lock in the  *)
  (* kernel is handed over at -- [main_locks_raw]'s eleven, the 64 proc  *)
  (* locks inside [proc_raw], and the inner spinlock of every sleeplock  *)
  (* -- so it is carved once here.  The footprint is [lock ↦₄] at +0,    *)
  (* [name ↦₈] at +8 and [cpu ↦₈] at +16; +4..+8 is padding and is       *)
  (* dropped.  Both field addresses go through [BootCarve.off_of_z]      *)
  (* after their [sign_extend']-ed 12-bit literal offsets reduce by      *)
  (* [vm_compute].                                                      *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_lk_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 24 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 24) -∗ lk_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                 = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
    assert (E16 : (sign_extend' 64 (mword_of_int 0x10 : mword 12) : mword 64)
                  = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hal8 : (A + 8) mod 8 = 0)
      by (apply z_mod8_addo; [exact Hal | reflexivity]).
    assert (Hal16 : (A + 16) mod 8 = 0)
      by (apply z_mod8_addo; [exact Hal | reflexivity]).
    (* three field ranges out of the record's 24 bytes *)
    iDestruct (boot_ran_split g A (A + 8) (A + 24) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H2]".
    iDestruct (boot_ran_split g A (A + 4) (A + 8) ltac:(lia) ltac:(lia)
                 with "H0") as "[H0 _]".
    iDestruct (boot_ran_split g (A + 8) (A + 16) (A + 24) ltac:(lia) ltac:(lia)
                 with "H2") as "[H1 H2]".
    iDestruct (boot_ran_cell4 g A Hmem Hlo ltac:(lia)
                 (z_mod8_mod4 A Hal) with "Hcl H0") as (vlock) "H0".
    iDestruct (boot_ran_eq g (A + 8) (A + 16) (A + 8) (A + 8 + 8)
                 eq_refl ltac:(lia) with "H1") as "H1".
    iDestruct (boot_ran_cell8 g (A + 8) Hmem ltac:(lia) ltac:(lia) Hal8
                 with "Hcl H1") as (vname) "H1".
    iDestruct (boot_ran_eq g (A + 16) (A + 24) (A + 16) (A + 16 + 8)
                 eq_refl ltac:(lia) with "H2") as "H2".
    iDestruct (boot_ran_cell8 g (A + 16) Hmem ltac:(lia) ltac:(lia) Hal16
                 with "Hcl H2") as (vcpu) "H2".
    rewrite /lk_raw /lock_name_field /lk_cpu E8 E16 !off_of_z.
    iExists vlock, vname, vcpu. iFrame "H0 H1 H2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE OTHER THREE FLAT SHAPES -- each [boot_lk_raw]'s pattern at its   *)
  (* own offsets.  The residue between two cells (a record's padding, or  *)
  (* a field no bundle claims) is DROPPED: [boot_raw_ran] is affine.      *)
  (* Every cut is taken in ADDRESS ORDER, and a window is re-anchored by  *)
  (* an EMPTY split rather than by [boot_ran_eq] -- [boot_ran_split g lo   *)
  (* mid hi] with [lo = mid] pointwise but not syntactically is what      *)
  (* makes the next window's [lo] literally the [A + off] the cell lemma  *)
  (* asks for.                                                          *)
  (* ------------------------------------------------------------------ *)

  (* [SleepLock.sl_raw]: six cells out of a [struct sleeplock]'s 44 bytes --
     [locked ↦₄] at +0, the inner spinlock's three ([lk ↦₄] at +8,
     [lk.name ↦₈] at +16, [lk.cpu ↦₈] at +24), then [name ↦₈] at +32 and
     [pid ↦₄] at +40.  Serves every sleeplock in the image: the NBUF buffer
     locks and the NINODE inode locks. *)
  Lemma boot_sl_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 44 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 44) -∗ sl_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                 = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
    assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                  = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
    assert (E32 : (sign_extend' 64 (mword_of_int 32 : mword 12) : mword 64)
                  = mword_of_int 32) by (apply bv_eq; vm_compute; reflexivity).
    assert (E40 : (sign_extend' 64 (mword_of_int 40 : mword 12) : mword 64)
                  = mword_of_int 40) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hal4 : A mod 4 = 0) by exact (z_mod8_mod4 A Hal).
    assert (En16 : A + 8 + 8 = A + 16) by lia.
    assert (En24 : A + 8 + 16 = A + 24) by lia.
    (* +0: locked *)
    iDestruct (boot_ran_split g A (A + 4) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H]".
    iDestruct (boot_ran_cell4 g A Hmem Hlo ltac:(lia) Hal4 with "Hcl H0")
      as (vlocked) "H0".
    (* +8: the inner spinlock's own word *)
    iDestruct (boot_ran_split g (A + 4) (A + 8) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 8) (A + 8 + 4) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H1 H]".
    iDestruct (boot_ran_cell4 g (A + 8) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 8 Hal4 eq_refl)) with "Hcl H1")
      as (vlk) "H1".
    (* +16: the inner spinlock's name field *)
    iDestruct (boot_ran_split g (A + 8 + 4) (A + 16) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 16) (A + 16 + 8) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H2 H]".
    iDestruct (boot_ran_cell8 g (A + 16) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 16 Hal eq_refl)) with "Hcl H2")
      as (vlkname) "H2".
    (* +24: the inner spinlock's cpu field *)
    iDestruct (boot_ran_split g (A + 16 + 8) (A + 24) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 24) (A + 24 + 8) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H3 H]".
    iDestruct (boot_ran_cell8 g (A + 24) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 24 Hal eq_refl)) with "Hcl H3")
      as (vcpu) "H3".
    (* +32: the sleeplock's own name field *)
    iDestruct (boot_ran_split g (A + 24 + 8) (A + 32) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 32) (A + 32 + 8) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H4 H]".
    iDestruct (boot_ran_cell8 g (A + 32) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 32 Hal eq_refl)) with "Hcl H4")
      as (vname) "H4".
    (* +40: pid *)
    iDestruct (boot_ran_split g (A + 32 + 8) (A + 40) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 40) (A + 40 + 4) (A + 44) ltac:(lia) ltac:(lia)
                 with "H") as "[H5 _]".
    iDestruct (boot_ran_cell4 g (A + 40) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 40 Hal4 eq_refl)) with "Hcl H5")
      as (vpid) "H5".
    rewrite /sl_raw /sl_lkcpu /sl_name_field /sl_pid /lock_name_field /sl_lk
            E8 E16 E32 E40 !off_of_z En16 En24.
    iExists vlocked, vlk, vpid, vlkname, vcpu, vname.
    iFrame "H0 H1 H2 H3 H4 H5".
  Qed.

  (* [BcacheInv.blink_raw]: the LRU link pair, [prev ↦₈] at +72 and
     [next ↦₈] at +80 of a [struct buf]. *)
  Lemma boot_blink_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 88 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g (A + 72) (A + 88)
    -∗ blink_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (E72 : (sign_extend' 64 (mword_of_int 72 : mword 12) : mword 64)
                  = mword_of_int 72) by (apply bv_eq; vm_compute; reflexivity).
    assert (E80 : (sign_extend' 64 (mword_of_int 80 : mword 12) : mword 64)
                  = mword_of_int 80) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct (boot_ran_split g (A + 72) (A + 72 + 8) (A + 88)
                 ltac:(lia) ltac:(lia) with "H") as "[H0 H]".
    iDestruct (boot_ran_cell8 g (A + 72) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 72 Hal eq_refl)) with "Hcl H0")
      as (vprev) "H0".
    iDestruct (boot_ran_split g (A + 72 + 8) (A + 80) (A + 88)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 80) (A + 80 + 8) (A + 88)
                 ltac:(lia) ltac:(lia) with "H") as "[H1 _]".
    iDestruct (boot_ran_cell8 g (A + 80) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 80 Hal eq_refl)) with "Hcl H1")
      as (vnext) "H1".
    rewrite /blink_raw /bprev /bnext E72 E80 !off_of_z.
    iSplitL "H0"; [iExists vprev; iExact "H0" | iExists vnext; iExact "H1"].
  Qed.

  (* [DiskInv.disk_slot_raw i] is NOT contiguous: it is slot [i]'s 16-byte
     [ops[i]] header at [disk+168+16i] plus its [info[i]] pair at
     [disk+40+16i].  So it comes out of TWO stride families over the same
     index, merged by [big_sepL_sep] -- which is also why the halves get
     names: the family's [Φ] is a function of the ADDRESS, so each half has
     to be a predicate on one. *)
  Local Definition dinfo_raw (a : Arch.pa) : iProp Σ :=
    ((∃ w : SailStdpp.Values.mword 64, a ↦₈ w) ∗
     (∃ sb : bv 8, (pa_add a 8%nat) ↦ₘ sb))%I.

  Local Definition dops_raw (a : Arch.pa) : iProp Σ :=
    (∃ (t r : SailStdpp.Values.mword 32) (s : SailStdpp.Values.mword 64),
       a ↦₄ t ∗ (pa_add a 4%nat) ↦₄ r ∗ (pa_add a 8%nat) ↦₈ s)%I.

  Lemma boot_dinfo_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 16 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 16) -∗ dinfo_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    iDestruct (boot_ran_split g A (A + 8) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H]".
    iDestruct (boot_ran_cell8 g A Hmem Hlo ltac:(lia) Hal with "Hcl H0")
      as (w) "H0".
    iDestruct (boot_ran_split g (A + 8) (A + 8 + 1) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[H1 _]".
    iDestruct (boot_ran_byte g (A + 8) Hmem ltac:(lia) ltac:(lia) with "Hcl H1")
      as "H1".
    rewrite /dinfo_raw pa_add_of_z (_ : A + Z.of_nat 8%nat = A + 8);
      [| lia ].
    iSplitL "H0"; [iExists w; iExact "H0" | iExists (boot_byte (A + 8)); iExact "H1"].
  Qed.

  Lemma boot_dops_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 16 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 16) -∗ dops_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (Hal4 : A mod 4 = 0) by exact (z_mod8_mod4 A Hal).
    iDestruct (boot_ran_split g A (A + 4) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H]".
    iDestruct (boot_ran_cell4 g A Hmem Hlo ltac:(lia) Hal4 with "Hcl H0")
      as (t) "H0".
    iDestruct (boot_ran_split g (A + 4) (A + 4 + 4) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[H1 H]".
    iDestruct (boot_ran_cell4 g (A + 4) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 4 Hal4 eq_refl)) with "Hcl H1")
      as (r) "H1".
    iDestruct (boot_ran_split g (A + 4 + 4) (A + 8) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 8) (A + 8 + 8) (A + 16) ltac:(lia) ltac:(lia)
                 with "H") as "[H _]".
    iDestruct (boot_ran_cell8 g (A + 8) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 8 Hal eq_refl)) with "Hcl H")
      as (s) "H".
    rewrite /dops_raw !pa_add_of_z (_ : A + Z.of_nat 4%nat = A + 4);
      [| lia ].
    rewrite (_ : A + Z.of_nat 8%nat = A + 8); [| lia ].
    iExists t, r, s. iFrame "H0 H1 H".
  Qed.

  (* the eight slots, out of the two ranges. *)
  Lemma boot_disk_slots (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g (KernelSyms.disk + 40)
                   (KernelSyms.disk + 40 + 16 * Z.of_nat 8%nat) -∗
    boot_raw_ran g (KernelSyms.disk + 168)
                   (KernelSyms.disk + 168 + 16 * Z.of_nat 8%nat)
    -∗ ([∗ list] i ∈ seq 0 8, disk_slot_raw i).
  Proof.
    intro Hmem. iIntros "#Hcl Hi Ho".
    iDestruct (boot_stride_family_seq g dinfo_raw (KernelSyms.disk + 40) 16 8%nat
                 ltac:(lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side (KernelSyms.disk + 40) 16 8%nat 16
                                   text_end ram_hi i A Hi HA
                                   ltac:(lia) ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       iApply (boot_dinfo_raw g A Hmem Q1 Q2 Q3))
                 with "Hcl Hi") as "Hi".
    iDestruct (boot_stride_family_seq g dops_raw (KernelSyms.disk + 168) 16 8%nat
                 ltac:(lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side (KernelSyms.disk + 168) 16 8%nat 16
                                   text_end ram_hi i A Hi HA
                                   ltac:(lia) ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       iApply (boot_dops_raw g A Hmem Q1 Q2 Q3))
                 with "Hcl Ho") as "Ho".
    iAssert ([∗ list] i ∈ seq 0 8,
               (dinfo_raw (pa_of_z (KernelSyms.disk + 40 + 16 * Z.of_nat i)) ∗
                dops_raw (pa_of_z (KernelSyms.disk + 168 + 16 * Z.of_nat i))))%I
      with "[Hi Ho]" as "H".
    { rewrite big_sepL_sep. iFrame "Hi Ho". }
    iApply (big_sepL_mono with "H"). iIntros (k i _) "[Hi Ho]".
    rewrite /disk_slot_raw /ops_own
            (d_info_b_of_z i) (d_info_status_of_z i) (d_ops_of_z i)
            (d_ops_res_of_z i) (d_ops_sec_of_z i) /dinfo_raw /dops_raw.
    iDestruct "Hi" as "[Hb Hs]". iFrame "Ho Hs Hb".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE TWO SLEEPLOCK FAMILIES.                                         *)
  (*                                                                    *)
  (* A buffer's per-element carve gives BOTH things [main_globals_raw]    *)
  (* asks of it -- the sleeplock at +16 and the LRU link pair at +72/+80  *)
  (* -- so the two big-ops are ONE family plus [big_sepL_sep], not two    *)
  (* traversals of the same range (which could not both own it).          *)
  (* ------------------------------------------------------------------ *)
  (* the per-element shape, NAMED: the family's [Φ] is applied to the element
     address, and a LAMBDA there leaves the per-element goal a beta-redex that
     [iApply] will not see through. *)
  Local Definition bnode_raw (a : Arch.pa) : iProp Σ :=
    (sl_raw (buf_lock a) ∗ blink_raw a)%I.

  Lemma boot_buf_node (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 88 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 88) -∗ bnode_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                  = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct (boot_ran_split g A (A + 16) (A + 88) ltac:(lia) ltac:(lia)
                 with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 16) (A + 16 + 44) (A + 88)
                 ltac:(lia) ltac:(lia) with "H") as "[Hs H]".
    iDestruct (boot_sl_raw g (A + 16) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 16 Hal eq_refl)) with "Hcl Hs")
      as "Hs".
    iDestruct (boot_ran_split g (A + 16 + 44) (A + 72) (A + 88)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_blink_raw g A Hmem Hlo Hhi Hal with "Hcl H") as "H".
    rewrite /bnode_raw /buf_lock E16 off_of_z. iFrame "Hs H".
  Qed.

  Lemma boot_bcache_nodes (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g buf_base (buf_base + buf_stride * Z.of_nat NBUF)
    -∗ ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) ∗
       ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)).
  Proof.
    intro Hmem. iIntros "#Hcl H".
    iDestruct (boot_stride_family_seq g bnode_raw
                 buf_base buf_stride NBUF
                 ltac:(unfold buf_stride; lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side buf_base buf_stride NBUF 88
                                   text_end ram_hi i A Hi HA
                                   ltac:(unfold buf_stride; lia)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       assert (T1 : A <= A + 88) by lia;
                       assert (T2 : A + 88 <= A + buf_stride)
                         by (unfold buf_stride; lia);
                       iIntros "#Hcl H";
                       iDestruct (boot_ran_split g A (A + 88) (A + buf_stride)
                                    T1 T2 with "H") as "[H _]";
                       iApply (boot_buf_node g A Hmem Q1 Q2 Q3 with "Hcl H"))
                 with "Hcl H") as "H".
    rewrite /bnode_raw big_sepL_sep. iDestruct "H" as "[H1 H2]".
    iSplitL "H1".
    - iApply (big_sepL_mono with "H1"). iIntros (n k _) "Hk".
      rewrite (bnode_of_z k). iExact "Hk".
    - iApply (big_sepL_mono with "H2"). iIntros (n k _) "Hk".
      rewrite (bnode_of_z k). iExact "Hk".
  Qed.

  (* the NINODE inode sleeplocks: the same family, at the itable's stride, and
     with nothing else per element. *)
  Lemma boot_inode_locks (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g inode_lock_base
                   (inode_lock_base + inode_stride * Z.of_nat NINODE)
    -∗ ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)).
  Proof.
    intro Hmem. iIntros "#Hcl H".
    iDestruct (boot_stride_family_seq g sl_raw
                 inode_lock_base inode_stride NINODE
                 ltac:(unfold inode_stride; lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side inode_lock_base inode_stride NINODE
                                   44 text_end ram_hi i A Hi HA
                                   ltac:(unfold inode_stride; lia)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       assert (T1 : A <= A + 44) by lia;
                       assert (T2 : A + 44 <= A + inode_stride)
                         by (unfold inode_stride; lia);
                       iIntros "#Hcl H";
                       iDestruct (boot_ran_split g A (A + 44) (A + inode_stride)
                                    T1 T2 with "H") as "[H _]";
                       iApply (boot_sl_raw g A Hmem Q1 Q2 Q3 with "Hcl H"))
                 with "Hcl H") as "H".
    iApply (big_sepL_mono with "H"). iIntros (n i _) "Hi".
    rewrite (inode_lock_of_z i). iExact "Hi".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [SpecMain.main_locks_raw]'s ELEVEN.                                 *)
  (*                                                                    *)
  (* Inherently eleven applications of [boot_lk_raw]: the eleven         *)
  (* [struct spinlock]s sit at UNRELATED symbols, not at a stride.  What *)
  (* the lemma buys is the address bridge for each (ten of them ARE      *)
  (* [mword_of_int <symbol>]; [disk_lock] alone needs [disk_lock_of_z])  *)
  (* and the ORDER -- the windows are taken in ADDRESS order, which is   *)
  (* the order the client's cuts out of the one .bss range must follow   *)
  (* ([main_lock_windows] is that check).                               *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_main_locks_raw (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g KernelSyms.cons (KernelSyms.cons + 24) -∗
    boot_raw_ran g KernelSyms.pr (KernelSyms.pr + 24) -∗
    boot_raw_ran g KernelSyms.tx_lock (KernelSyms.tx_lock + 24) -∗
    boot_raw_ran g KernelSyms.kmem (KernelSyms.kmem + 24) -∗
    boot_raw_ran g KernelSyms.pid_lock (KernelSyms.pid_lock + 24) -∗
    boot_raw_ran g KernelSyms.wait_lock (KernelSyms.wait_lock + 24) -∗
    boot_raw_ran g KernelSyms.tickslock (KernelSyms.tickslock + 24) -∗
    boot_raw_ran g KernelSyms.bcache (KernelSyms.bcache + 24) -∗
    boot_raw_ran g KernelSyms.itable (KernelSyms.itable + 24) -∗
    boot_raw_ran g KernelSyms.ftable (KernelSyms.ftable + 24) -∗
    boot_raw_ran g (KernelSyms.disk + 296) (KernelSyms.disk + 296 + 24)
    -∗ main_locks_raw.
  Proof.
    intro Hmem. iIntros "#Hcl H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11".
    iDestruct (boot_lk_raw g KernelSyms.cons Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H1") as "H1".
    iDestruct (boot_lk_raw g KernelSyms.pr Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H2") as "H2".
    iDestruct (boot_lk_raw g KernelSyms.tx_lock Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H3") as "H3".
    iDestruct (boot_lk_raw g KernelSyms.kmem Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H4") as "H4".
    iDestruct (boot_lk_raw g KernelSyms.pid_lock Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H5") as "H5".
    iDestruct (boot_lk_raw g KernelSyms.wait_lock Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H6") as "H6".
    iDestruct (boot_lk_raw g KernelSyms.tickslock Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H7") as "H7".
    iDestruct (boot_lk_raw g KernelSyms.bcache Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H8") as "H8".
    iDestruct (boot_lk_raw g KernelSyms.itable Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H9") as "H9".
    iDestruct (boot_lk_raw g KernelSyms.ftable Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H10") as "H10".
    iDestruct (boot_lk_raw g (KernelSyms.disk + 296) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl H11") as "H11".
    rewrite /main_locks_raw /pid_lock_addr /wait_lock_addr /bcache_addr
            /itable_addr disk_lock_of_z.
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H3"; [iExact "H3"|].
    iSplitL "H2"; [iExact "H2"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|].
    iSplitL "H7"; [iExact "H7"|]. iSplitL "H8"; [iExact "H8"|].
    iSplitL "H9"; [iExact "H9"|]. iSplitL "H10"; [iExact "H10"|].
    iExact "H11".
  Qed.

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
