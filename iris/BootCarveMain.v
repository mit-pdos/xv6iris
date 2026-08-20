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
Require Import KMap.
Require Import BootCarve.
Require Import PageGeom KallocInv.
Require Import SpecFreerange.
Require Import WpLock SpecProcinit.
Require Import ConsoleInv.
(* the vocabulary of the STRUCTURED conjuncts (slice 2b).  [Import] is not
   transitive, so each file whose predicate is named below has to be imported
   here even though [SpecMain] already requires all of them. *)
Require Import ProcGeom UserPtTree ProcInv SwtchCtx SchedCtx.
(* the itable's ENTRIES (not just their sleeplocks): [IcacheBoot.ientry_raw]
   is the shape [icache_boot] takes, and [IcacheRef]/[InodeInv]/[InodeLock]
   are the field addresses it is stated over.  IMPORTED BEFORE [SpecIinit],
   deliberately: [IcacheRef] has its own [NINODE], and every [NINODE] in this
   file is [SpecIinit]'s (they are the same 50, but not the same constant). *)
Require Import DinodeEnc IcacheRef InodeInv InodeLock IcacheBoot.
Require Import SleepLock BcacheInv SpecIinit.
(* the bcache's PAYLOAD rows: [BufOwn]'s field addresses, [BioInv]'s [bpa] /
   [brefcnt], and [BioInitAt.buf_raw] -- the named row [bio_init_at] takes and
   [SpecMain.main_globals_raw] carries across binit (stage (f)). *)
Require Import BufOwn BioInv BioInitAt.
Require Import DiskInv SpecVirtioDiskInit.
(* the [struct log]'s cell names, for rows (A) of the fsinit bundle
   (fs-cfg-boot.md (f-2)) *)
Require Import LogDefs LogInv.
Require Import SpecMain.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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

(* ...and the same one step further down, for the four HALFWORD fields of the
   dinode mirror ([InodeInv.i_type] and its three siblings). *)
Lemma z_mod8_mod2 (A : Z) : A mod 8 = 0 -> A mod 2 = 0.
Proof.
  intro H. apply Z.mod_divide in H; [| lia]. apply Z.mod_divide; [lia |].
  apply (Z.divide_trans 2 8); [exists 4; reflexivity | exact H].
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
(* BSIZE, for the [struct buf] data array.  A [nat] literal of this size is
   a unary successor chain that [lia]'s zify hook cannot relate to a computed
   bound (durable-notes), so the equation is stated once and rewritten. *)
Lemma z_of_nat_1024 : Z.of_nat 1024%nat = 1024.
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

(* THE ITABLE'S ENTRY ARRAY, at the ENTRY rather than at its sleeplock.
   [SpecIinit]'s cursor walks the sleeplocks from [itable+40] because that is
   what iinit's loop does; the entries themselves start 16 bytes earlier, at
   [itable+24] (just past the 24-byte spinlock), and their 136-byte records
   are what the byte carve has to cut -- one family, not two, since the two
   ranges OVERLAP and no two big-ops can both own them (the [bnode_raw]
   precedent below).  The array ends exactly at [IcacheRef.ientry NINODE],
   i.e. at the next symbol; the old sleeplock-anchored window ran 16 bytes
   past it. *)
Definition inode_entry_base : Z := KernelSyms.itable + 24.

Lemma ientry_of_z (k : nat) :
  ientry k = pa_of_z (inode_entry_base + inode_stride * Z.of_nat k).
Proof. reflexivity. Qed.

(* the family's element address, offset to the sleeplock inside it, IS
   [SpecIinit]'s cursor -- the address bridge between the two spellings, and
   the reason one family can discharge both of [main_globals_raw]'s inode
   big-ops.  ([IcacheBoot.inode_lock_is_ientry_lock] is the same fact stated
   the other way round, over [IcacheRef]'s [i_lock] and [ientry].) *)
Lemma i_lock_of_entry (k : nat) :
  i_lock (pa_of_z (inode_entry_base + inode_stride * Z.of_nat k))
  = inode_lock k.
Proof.
  assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
  rewrite /i_lock inode_lock_of_z /pa_of_z E16 addv_moi_moi.
  f_equal. unfold inode_entry_base, inode_lock_base. lia.
Qed.

Lemma proc_addr_of_z (i : nat) :
  proc_addr i = pa_of_z (KernelSyms.proc + proc_size * Z.of_nat i).
Proof. rewrite proc_addr_acur. reflexivity. Qed.

Lemma disk_lock_of_z : disk_lock = pa_of_z (KernelSyms.disk + 296).
Proof.
  assert (E : (sign_extend' 64 (mword_of_int 0x128 : mword 12) : mword 64)
              = mword_of_int 296) by (apply bv_eq; vm_compute; reflexivity).
  unfold disk_lock. rewrite E. apply off_of_z.
Qed.

(* ...and its four siblings, the [struct disk] fields [main_globals_raw] names:
   the three queue pointers at +0/+8/+16, the [free[8]] byte array at +24 and
   [DiskInv]'s [used_idx] at +32.  Same one-[vm_compute] reduction of the
   sign-extended 12-bit literal, except [d_used_idx] which is spelled with
   [pa_add] and reduces by [avi_mword] instead. *)
Lemma disk_desc_of_z : disk_desc = pa_of_z KernelSyms.disk.
Proof. reflexivity. Qed.

Lemma disk_avail_of_z : disk_avail = pa_of_z (KernelSyms.disk + 8).
Proof.
  assert (E : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
              = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
  unfold disk_avail. rewrite E. apply off_of_z.
Qed.

Lemma disk_used_of_z : disk_used = pa_of_z (KernelSyms.disk + 16).
Proof.
  assert (E : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
              = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
  unfold disk_used. rewrite E. apply off_of_z.
Qed.

Lemma disk_free_of_z : disk_free = pa_of_z (KernelSyms.disk + 24).
Proof.
  assert (E : (sign_extend' 64 (mword_of_int 24 : mword 12) : mword 64)
              = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
  unfold disk_free. rewrite E. apply off_of_z.
Qed.

Lemma d_used_idx_of_z : d_used_idx = pa_of_z (KernelSyms.disk + 32).
Proof.
  unfold d_used_idx, DiskInv.disk_base, pa_add.
  rewrite (_ : Z.of_nat 32%nat = 32); [| reflexivity].
  unfold pa_of_z. apply avi_mword.
Qed.

(* the bcache's LIST SENTINEL: [bhead] IS [bnode NBUF], i.e. the family's
   address one past the last buffer, so no extra lemma is needed for it -- this
   is [bnode_of_z] at [NBUF], named because the client's cut chain takes the
   sentinel's link pair out of its own window. *)
Lemma bhead_of_z : bhead = pa_of_z (buf_base + buf_stride * Z.of_nat NBUF).
Proof. exact (bnode_of_z NBUF). Qed.

(* the eleven [struct spinlock] windows [main_locks_raw] enumerates, IN
   ADDRESS ORDER and pairwise disjoint -- which is what lets a client cut all
   eleven out of the one .bss range with [boot_ran_split] alone.  Every step
   is [x + 24 <= y] on two literals, so the whole check is one [vm_compute]
   per conjunct.  (The full .bss decomposition -- which of these gaps holds
   which other bundle -- is tabulated in claude-notes/completed/crash.md.)

   ALL ELEVEN WINDOWS ARE 24 BYTES, [tx_lock] included: it is a [struct
   spinlock], which the layout confirms exactly -- [pr] = 0x80012348,
   [tx_lock] = 0x80012360 and [kmem] = 0x80012378, so the linker left 24
   bytes on each side of it and there is no slack in either direction. *)
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
  Context `{!riscvGS Σ, !xv6G Σ}.

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
  (* THE CONSOLE RING, out of [cons + 24 .. cons + 164).                 *)
  (*                                                                    *)
  (* [ConsoleInv.cons_res] is what cons.lock protects: the 128 input     *)
  (* bytes and the three index words r/w/e at +152/+156/+160.  It is the *)
  (* one piece of [SpecConsoleintr.console_caps] the boot supply did not *)
  (* carry, and without it main cannot run [WpLock.newlock] over the     *)
  (* lock consoleinit has just initialised.  The four bytes of padding   *)
  (* between the ring's end and [pr] are dropped, as everywhere.         *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_cons_res (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= KernelSyms.cons ->
    KernelSyms.cons + 164 <= ram_hi ->
    KernelSyms.cons mod 4 = 0 ->
    kmap_static_claims -∗
    boot_raw_ran g (KernelSyms.cons + 24) (KernelSyms.cons + 164) -∗
    cons_res.
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    assert (Hal4 : forall k : Z, k mod 4 = 0 -> (KernelSyms.cons + k) mod 4 = 0)
      by (intros k Hk; rewrite Z.add_mod; [| lia]; rewrite Hal Hk; reflexivity).
    (* the four windows, in address order *)
    iDestruct (boot_ran_split g (KernelSyms.cons + 24) (KernelSyms.cons + 152)
                 (KernelSyms.cons + 164) ltac:(lia) ltac:(lia) with "H") as "[Hb H]".
    iDestruct (boot_ran_split g (KernelSyms.cons + 152) (KernelSyms.cons + 156)
                 (KernelSyms.cons + 164) ltac:(lia) ltac:(lia) with "H") as "[Hr H]".
    iDestruct (boot_ran_split g (KernelSyms.cons + 156) (KernelSyms.cons + 160)
                 (KernelSyms.cons + 164) ltac:(lia) ltac:(lia) with "H") as "[Hw He]".
    (* the three index words *)
    iDestruct (boot_ran_cell4 g (KernelSyms.cons + 152) Hmem ltac:(lia) ltac:(lia)
                 ltac:(apply Hal4; reflexivity) with "Hcl Hr") as (rr) "Hr".
    iDestruct (boot_ran_cell4 g (KernelSyms.cons + 156) Hmem ltac:(lia) ltac:(lia)
                 ltac:(apply Hal4; reflexivity) with "Hcl Hw") as (ww) "Hw".
    iDestruct (boot_ran_eq g (KernelSyms.cons + 160) (KernelSyms.cons + 164)
                 (KernelSyms.cons + 160) (KernelSyms.cons + 160 + 4)
                 eq_refl ltac:(lia) with "He") as "He".
    iDestruct (boot_ran_cell4 g (KernelSyms.cons + 160) Hmem ltac:(lia) ltac:(lia)
                 ltac:(apply Hal4; reflexivity) with "Hcl He") as (ee) "He".
    (* the 128 ring bytes *)
    assert (Hb128 : KernelSyms.cons + 152
                    = KernelSyms.cons + 24 + Z.of_nat INPUT_BUF_SIZE)
      by (unfold INPUT_BUF_SIZE; cbn; lia).
    iDestruct (boot_ran_eq g (KernelSyms.cons + 24) (KernelSyms.cons + 152)
                 (KernelSyms.cons + 24) (KernelSyms.cons + 24 + Z.of_nat INPUT_BUF_SIZE)
                 eq_refl Hb128 with "Hb") as "Hb".
    iDestruct (boot_ran_mem_run g (KernelSyms.cons + 24) INPUT_BUF_SIZE Hmem
                 ltac:(lia) ltac:(unfold INPUT_BUF_SIZE; cbn; lia) with "Hcl Hb") as "Hb".
    (* re-anchor every address on [a_cons] *)
    assert (Hbyte : forall j : nat,
              pa_add (pa_of_z (KernelSyms.cons + 24)) j
              = pa_add a_cons (cons_buf_off + j)).
    { intro j. rewrite !pa_add_of_z. f_equal. unfold cons_buf_off. lia. }
    iDestruct (cons_data_of_run (fun j => boot_byte (KernelSyms.cons + 24 + Z.of_nat j))
                 (pa_of_z (KernelSyms.cons + 24)) Hbyte with "Hb") as (bs) "[%Hlen Hb]".
    assert (Hcell : forall o : Z,
              (sign_extend' 64 (mword_of_int o : mword 12) : mword 64) = mword_of_int o ->
              pa_of_z (KernelSyms.cons + o) = coff_of a_cons o).
    { intros o Ho. rewrite /coff_of Ho off_of_z. reflexivity. }
    iEval (rewrite (Hcell 152 ltac:(apply bv_eq; vm_compute; reflexivity))) in "Hr".
    iEval (rewrite (Hcell 156 ltac:(apply bv_eq; vm_compute; reflexivity))) in "Hw".
    iEval (rewrite (Hcell 160 ltac:(apply bv_eq; vm_compute; reflexivity))) in "He".
    rewrite /cons_res /a_cons_r /a_cons_w /a_cons_e.
    iExists rr, ww, ee, bs. iFrame "Hr Hw He Hb". iPureIntro. exact Hlen.
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
  (* THE BUFFER FAMILY: THE WHOLE 1112-BYTE [struct buf].                 *)
  (*                                                                    *)
  (* A buffer's per-element carve gives ALL THREE things                  *)
  (* [main_globals_raw] asks of it -- the sleeplock at +16, the LRU link  *)
  (* pair at +72/+80, and [BioInitAt.buf_raw]'s payload (the four zeroed  *)
  (* metadata words, the refcnt, and the 1024 data bytes) -- so the three *)
  (* big-ops are ONE family plus [big_sepL_sep], never three traversals   *)
  (* of the same range (which could not all own it).                      *)
  (*                                                                    *)
  (* fs.h's [struct buf], and the element window is the FULL stride:      *)
  (*                                                                    *)
  (*   +0  valid  +4  disk  +8  dev  +12 blockno                          *)
  (*   +16 lock (struct sleeplock, 44 B)         [+60 padding]            *)
  (*   +64 refcnt                                [+68 padding]            *)
  (*   +72 prev   +80 next                                                *)
  (*   +88 data[BSIZE]                          (ends exactly at +1112)   *)
  (*                                                                    *)
  (* THE FIVE WORD CELLS ARE PINNED TO ZERO, which is why this lemma      *)
  (* takes [img_end] rather than [text_end]: the bcache is .bss past the  *)
  (* image, so the loader's zero is a FACT ([boot_ran_cell4_bss]) and     *)
  (* [BioInv.bio_init]'s "every buffer starts invalid at blockno 0" is a  *)
  (* reading of the image, not an assumption.  [ientry_raw]'s [ref] cell  *)
  (* is the precedent.  The data bytes stay contents-existential --       *)
  (* nothing reads them before the first [bread].                         *)
  (* ------------------------------------------------------------------ *)

  (* the payload, at one record's own base.  Its [k]-indexed reading IS
     [BioInitAt.buf_raw k] by conversion ([bpa k] is [bnode k] is
     [pa_of_z (buf_base + buf_stride * k)]), which is what lets the family's
     third half be handed over with no address bridge. *)
  Local Definition bpay_raw (a : Arch.pa) : iProp Σ :=
    (b_valid a ↦₄ (mword_of_int 0 : mword 32) ∗
     b_disk a ↦₄ (mword_of_int 0 : mword 32) ∗
     b_dev a ↦₄ (mword_of_int 0 : mword 32) ∗
     b_blockno a ↦₄ (mword_of_int 0 : mword 32) ∗
     (pa_add a 64%nat) ↦₄ (mword_of_int 0 : mword 32) ∗
     (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
        [∗ list] j ↦ byte ∈ bs, pa_add (b_data a) j ↦ₘ byte))%I.

  (* the per-element shape, NAMED: the family's [Φ] is applied to the element
     address, and a LAMBDA there leaves the per-element goal a beta-redex that
     [iApply] will not see through. *)
  Local Definition bnode_raw (a : Arch.pa) : iProp Σ :=
    (sl_raw (buf_lock a) ∗ blink_raw a ∗ bpay_raw a)%I.

  Lemma boot_buf_node (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    img_end <= A -> A + 1112 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 1112) -∗ bnode_raw (pa_of_z A).
  Proof.
    intros Hmem Hbss Hhi Hal. iIntros "#Hcl H".
    assert (Hlo : text_end <= A)
      by exact (z_lo_trans text_end img_end A ltac:(vm_compute; discriminate) Hbss).
    assert (Hal4 : A mod 4 = 0) by exact (z_mod8_mod4 A Hal).
    assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                  = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
    (* the data array's bound, over [Z]: a [nat] literal this size is not
       something [lia] can relate to a computed bound (durable-notes). *)
    assert (Hdlo : A + 88 <= A + 88 + Z.of_nat 1024%nat)
      by (rewrite z_of_nat_1024; lia).
    assert (Hdhi : A + 88 + Z.of_nat 1024%nat <= A + 1112)
      by (rewrite z_of_nat_1024; lia).
    assert (Hdram : A + 88 + Z.of_nat 1024%nat <= ram_hi)
      by (rewrite z_of_nat_1024; lia).
    (* ---- +0 valid / +4 disk / +8 dev / +12 blockno: PINNED zeros ---- *)
    iDestruct (boot_ran_split g A (A + 4) (A + 1112) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H]".
    iDestruct (boot_ran_cell4_bss g A (mword_of_int 0 : mword 32) Hmem Hlo Hbss
                 ltac:(lia) Hal4
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H0") as "H0".
    iDestruct (boot_ran_split g (A + 4) (A + 4 + 4) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[H1 H]".
    iDestruct (boot_ran_cell4_bss g (A + 4) (mword_of_int 0 : mword 32) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 4 Hal4 eq_refl))
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H1") as "H1".
    iDestruct (boot_ran_split g (A + 4 + 4) (A + 8) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 8) (A + 8 + 4) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[H2 H]".
    iDestruct (boot_ran_cell4_bss g (A + 8) (mword_of_int 0 : mword 32) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 8 Hal4 eq_refl))
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H2") as "H2".
    iDestruct (boot_ran_split g (A + 8 + 4) (A + 12) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 12) (A + 12 + 4) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[H3 H]".
    iDestruct (boot_ran_cell4_bss g (A + 12) (mword_of_int 0 : mword 32) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 12 Hal4 eq_refl))
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H3") as "H3".
    (* ---- +16: the sleeplock binit initialises ---- *)
    iDestruct (boot_ran_split g (A + 12 + 4) (A + 16) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 16) (A + 16 + 44) (A + 1112)
                 ltac:(lia) ltac:(lia) with "H") as "[Hs H]".
    iDestruct (boot_sl_raw g (A + 16) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 16 Hal eq_refl)) with "Hcl Hs")
      as "Hs".
    (* ---- +64: refcnt, PINNED ---- *)
    iDestruct (boot_ran_split g (A + 16 + 44) (A + 64) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 64) (A + 64 + 4) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[H4 H]".
    iDestruct (boot_ran_cell4_bss g (A + 64) (mword_of_int 0 : mword 32) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 64 Hal4 eq_refl))
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H4") as "H4".
    (* ---- +72 .. +88: the LRU link pair binit threads ---- *)
    iDestruct (boot_ran_split g (A + 64 + 4) (A + 72) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 72) (A + 88) (A + 1112) ltac:(lia)
                 ltac:(lia) with "H") as "[Hln H]".
    iDestruct (boot_blink_raw g A Hmem Hlo ltac:(lia) Hal with "Hcl Hln")
      as "Hln".
    (* ---- +88: the 1024 data bytes, contents existential ---- *)
    iDestruct (boot_ran_split g (A + 88) (A + 88 + Z.of_nat 1024%nat) (A + 1112)
                 Hdlo Hdhi with "H") as "[Hd _]".
    iDestruct (boot_ran_bytes_list g (A + 88) 1024%nat Hmem ltac:(lia) Hdram
                 with "Hcl Hd") as (bs) "[%Hbs Hd]".
    (* ---- assemble ---- *)
    rewrite /bnode_raw /bpay_raw /buf_lock /b_valid /b_disk /b_dev /b_blockno
            /b_data E16 off_of_z
            (pa_add_of_z A 4%nat) (pa_add_of_z A 8%nat) (pa_add_of_z A 12%nat)
            (pa_add_of_z A 64%nat) (pa_add_of_z A 88%nat).
    rewrite (_ : A + Z.of_nat 4%nat = A + 4); [| lia].
    rewrite (_ : A + Z.of_nat 8%nat = A + 8); [| lia].
    rewrite (_ : A + Z.of_nat 12%nat = A + 12); [| lia].
    rewrite (_ : A + Z.of_nat 64%nat = A + 64); [| lia].
    rewrite (_ : A + Z.of_nat 88%nat = A + 88); [| lia].
    iSplitL "Hs"; [iExact "Hs" |]. iSplitL "Hln"; [iExact "Hln" |].
    iSplitL "H0"; [iExact "H0" |]. iSplitL "H1"; [iExact "H1" |].
    iSplitL "H2"; [iExact "H2" |]. iSplitL "H3"; [iExact "H3" |].
    iSplitL "H4"; [iExact "H4" |].
    iExists bs. iSplitR; [iPureIntro; exact Hbs |]. iExact "Hd".
  Qed.

  Lemma boot_bcache_nodes (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g buf_base (buf_base + buf_stride * Z.of_nat NBUF)
    -∗ ([∗ list] k ∈ seq 0 NBUF, sl_raw (buf_lock (bnode k))) ∗
       ([∗ list] k ∈ seq 0 NBUF, blink_raw (bnode k)) ∗
       ([∗ list] k ∈ seq 0 NBUF, buf_raw k).
  Proof.
    intro Hmem. iIntros "#Hcl H".
    iDestruct (boot_stride_family_seq g bnode_raw
                 buf_base buf_stride NBUF
                 ltac:(unfold buf_stride; lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side buf_base buf_stride NBUF 1112
                                   img_end ram_hi i A Hi HA
                                   ltac:(unfold buf_stride; lia)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       assert (Tw : A + buf_stride = A + 1112)
                         by (unfold buf_stride; lia);
                       iIntros "#Hcl H";
                       iDestruct (boot_ran_eq g A (A + buf_stride) A (A + 1112)
                                    eq_refl Tw with "H") as "H";
                       iApply (boot_buf_node g A Hmem Q1 Q2 Q3 with "Hcl H"))
                 with "Hcl H") as "H".
    (* ONE [big_sepL_sep] PER SPLIT, AND THE SECOND ONE SCOPED.  A repeated
       [!big_sepL_sep] sees through [blink_raw]'s own two-conjunct body (it is
       a transparent Definition) and shatters it into two big-ops nothing can
       reassemble -- the same trap [BootShared]'s [hart_strans] note records. *)
    rewrite /bnode_raw big_sepL_sep. iDestruct "H" as "[H1 H]".
    iEval (rewrite big_sepL_sep) in "H". iDestruct "H" as "[H2 H3]".
    iSplitL "H1".
    - iApply (big_sepL_mono with "H1"). iIntros (n k _) "Hk".
      rewrite (bnode_of_z k). iExact "Hk".
    - iSplitL "H2".
      + iApply (big_sepL_mono with "H2"). iIntros (n k _) "Hk".
        rewrite (bnode_of_z k). iExact "Hk".
      + iApply (big_sepL_mono with "H3"). iIntros (n k _) "Hk".
        iExact "Hk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* A RUN OF WORD CELLS inside a record, contents existential:          *)
  (* [boot_ctx_cells] at width 4, and in the same [pa_of_z base] +       *)
  (* [mword_of_int (off + 4*j)] spelling -- which IS [InodeInv.i_addr]   *)
  (* at [off = 80], so its consumer needs no address rewriting at all.   *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_word4_cells (g : gstate) (C : Z) (n : nat) (off : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= C + off -> C + off + 4 * Z.of_nat n <= ram_hi ->
    (C + off) mod 4 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g (C + off) (C + off + 4 * Z.of_nat n)
    -∗ (∃ l : list (bv 32), ⌜length l = n⌝ ∗
          [∗ list] j ↦ a ∈ l,
            add_vec (pa_of_z C) (mword_of_int (off + 4 * Z.of_nat j)) ↦₄ a).
  Proof.
    intro Hmem. revert off. induction n as [|k IH]; intros off Hlo Hhi Hal.
    - iIntros "_ _". iExists []. iSplitR; [done |]. done.
    - iIntros "#Hcl H".
      assert (Hd1 : C + off <= C + off + 4) by lia.
      assert (Hd2 : C + off + 4 <= C + off + 4 * Z.of_nat (S k)) by lia.
      assert (Eo : C + (off + 4) = C + off + 4) by lia.
      assert (Ehi : C + off + 4 * Z.of_nat (S k)
                    = C + (off + 4) + 4 * Z.of_nat k) by lia.
      assert (Elo : C + off + 4 = C + (off + 4)) by lia.
      assert (Hchi : C + off + 4 <= ram_hi) by lia.
      assert (Hilo : text_end <= C + (off + 4)) by lia.
      assert (Hihi : C + (off + 4) + 4 * Z.of_nat k <= ram_hi) by lia.
      assert (Hial : (C + (off + 4)) mod 4 = 0)
        by (rewrite Eo; exact (z_mod_addo 4 (C + off) 4 Hal eq_refl)).
      assert (Ehd : off + 4 * Z.of_nat 0%nat = off) by lia.
      iDestruct (boot_ran_split g (C + off) (C + off + 4)
                   (C + off + 4 * Z.of_nat (S k)) Hd1 Hd2 with "H") as "[Hc H]".
      iDestruct (boot_ran_cell4 g (C + off) Hmem Hlo Hchi Hal with "Hcl Hc")
        as (v) "Hc".
      iDestruct (boot_ran_eq g _ _ (C + (off + 4))
                   (C + (off + 4) + 4 * Z.of_nat k) Elo Ehi with "H") as "H".
      iDestruct (IH (off + 4) Hilo Hihi Hial with "Hcl H") as (l) "[%Hlen Hl]".
      iExists (v :: l). iSplitR; [iPureIntro; cbn [length]; by rewrite Hlen |].
      rewrite big_sepL_cons. iSplitL "Hc".
      + rewrite Ehd off_of_z. iExact "Hc".
      + iApply (big_sepL_mono with "Hl"). iIntros (j a _) "Ha".
        rewrite (_ : off + 4 * Z.of_nat (S j) = off + 4 + 4 * Z.of_nat j); [| lia].
        iExact "Ha".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE itable ENTRY, out of its own 136 bytes.                          *)
  (*                                                                    *)
  (* [bnode_raw]'s situation exactly: the entry's window carries BOTH    *)
  (* things [main_globals_raw] asks of the table -- iinit's sleeplock at *)
  (* +16 and [IcacheBoot.ientry_raw_at]'s cells around it -- so it is    *)
  (* ONE family plus [big_sepL_sep], never two traversals of the same    *)
  (* range.  The layout (fs.h's [struct inode]):                          *)
  (*                                                                    *)
  (*   +0  dev    +4  inum   +8  ref   [+12 padding]                     *)
  (*   +16 lock (struct sleeplock, 44 B)          [+60 padding]          *)
  (*   +64 valid                                                        *)
  (*   +68 type   +70 major  +72 minor  +74 nlink  +76 size              *)
  (*   +80 addrs[13]                              [+132 padding]         *)
  (*                                                                    *)
  (* [ref] IS PINNED TO ZERO, and that is why the lemma takes [img_end]  *)
  (* rather than [text_end]: [IcacheInv.iref_cells ∅] wants that exact   *)
  (* word, and the itable is .bss past the image so the loader's zero is *)
  (* a FACT ([BootCarve.boot_ran_cell4_bss]), not an assumption.  The    *)
  (* [d_used_idx] and [kmem+24] conjuncts of [main_globals_raw] are the  *)
  (* same claim and the precedent.  Everything else is contents-         *)
  (* existential, which is all the cache's boot step needs.              *)
  (* ------------------------------------------------------------------ *)
  Local Definition inode_node_raw (a : Arch.pa) : iProp Σ :=
    (sl_raw (i_lock a) ∗ ientry_raw_at a)%I.

  Lemma boot_inode_entry (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    img_end <= A -> A + 136 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 136)
    -∗ inode_node_raw (pa_of_z A).
  Proof.
    intros Hmem Hbss Hhi Hal. iIntros "#Hcl H".
    assert (Hlo : text_end <= A)
      by exact (z_lo_trans text_end img_end A ltac:(vm_compute; discriminate) Hbss).
    assert (Hal4 : A mod 4 = 0) by exact (z_mod8_mod4 A Hal).
    assert (Hal2 : A mod 2 = 0) by exact (z_mod8_mod2 A Hal).
    (* the sign-extended 12-bit field displacements, once each *)
    assert (E0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                 = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (E4 : (sign_extend' 64 (mword_of_int 4 : mword 12) : mword 64)
                 = mword_of_int 4) by (apply bv_eq; vm_compute; reflexivity).
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                 = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
    assert (E16 : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                  = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
    assert (E64 : (sign_extend' 64 (mword_of_int 64 : mword 12) : mword 64)
                  = mword_of_int 64) by (apply bv_eq; vm_compute; reflexivity).
    assert (E68 : (sign_extend' 64 (mword_of_int 68 : mword 12) : mword 64)
                  = mword_of_int 68) by (apply bv_eq; vm_compute; reflexivity).
    assert (E70 : (sign_extend' 64 (mword_of_int 70 : mword 12) : mword 64)
                  = mword_of_int 70) by (apply bv_eq; vm_compute; reflexivity).
    assert (E72 : (sign_extend' 64 (mword_of_int 72 : mword 12) : mword 64)
                  = mword_of_int 72) by (apply bv_eq; vm_compute; reflexivity).
    assert (E74 : (sign_extend' 64 (mword_of_int 74 : mword 12) : mword 64)
                  = mword_of_int 74) by (apply bv_eq; vm_compute; reflexivity).
    assert (E76 : (sign_extend' 64 (mword_of_int 76 : mword 12) : mword 64)
                  = mword_of_int 76) by (apply bv_eq; vm_compute; reflexivity).
    (* ---- +0: dev ---- *)
    iDestruct (boot_ran_split g A (A + 4) (A + 136) ltac:(lia) ltac:(lia)
                 with "H") as "[H0 H]".
    iDestruct (boot_ran_cell4 g A Hmem Hlo ltac:(lia) Hal4 with "Hcl H0")
      as (vdev) "H0".
    (* ---- +4: inum ---- *)
    iDestruct (boot_ran_split g (A + 4) (A + 4 + 4) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H1 H]".
    iDestruct (boot_ran_cell4 g (A + 4) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 4 Hal4 eq_refl)) with "Hcl H1")
      as (vinum) "H1".
    (* ---- +8: ref, PINNED to the loader's zero ---- *)
    iDestruct (boot_ran_split g (A + 4 + 4) (A + 8) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 8) (A + 8 + 4) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H2 H]".
    iDestruct (boot_ran_cell4_bss g (A + 8) (mword_of_int 0 : mword 32) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 8 Hal4 eq_refl))
                 ltac:(intros j _; apply nth_byte_zero; vm_compute; reflexivity)
                 with "Hcl H2") as "H2".
    (* ---- +16: the sleeplock iinit initialises ---- *)
    iDestruct (boot_ran_split g (A + 8 + 4) (A + 16) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 16) (A + 16 + 44) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[Hs H]".
    iDestruct (boot_sl_raw g (A + 16) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 16 Hal eq_refl)) with "Hcl Hs")
      as "Hs".
    (* ---- +64: valid ---- *)
    iDestruct (boot_ran_split g (A + 16 + 44) (A + 64) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 64) (A + 64 + 4) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H3 H]".
    iDestruct (boot_ran_cell4 g (A + 64) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 64 Hal4 eq_refl)) with "Hcl H3")
      as (vvalid) "H3".
    (* ---- +68 .. +76: the dinode mirror's five metadata cells ---- *)
    iDestruct (boot_ran_split g (A + 64 + 4) (A + 68) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 68) (A + 68 + 2) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H4 H]".
    iDestruct (boot_ran_cell2 g (A + 68) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 2 A 68 Hal2 eq_refl)) with "Hcl H4")
      as (vtype) "H4".
    iDestruct (boot_ran_split g (A + 68 + 2) (A + 70) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 70) (A + 70 + 2) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H5 H]".
    iDestruct (boot_ran_cell2 g (A + 70) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 2 A 70 Hal2 eq_refl)) with "Hcl H5")
      as (vmajor) "H5".
    iDestruct (boot_ran_split g (A + 70 + 2) (A + 72) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 72) (A + 72 + 2) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H6 H]".
    iDestruct (boot_ran_cell2 g (A + 72) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 2 A 72 Hal2 eq_refl)) with "Hcl H6")
      as (vminor) "H6".
    iDestruct (boot_ran_split g (A + 72 + 2) (A + 74) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 74) (A + 74 + 2) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H7 H]".
    iDestruct (boot_ran_cell2 g (A + 74) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 2 A 74 Hal2 eq_refl)) with "Hcl H7")
      as (vnlink) "H7".
    iDestruct (boot_ran_split g (A + 74 + 2) (A + 76) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 76) (A + 76 + 4) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[H8 H]".
    iDestruct (boot_ran_cell4 g (A + 76) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 76 Hal4 eq_refl)) with "Hcl H8")
      as (vsize) "H8".
    (* ---- +80: the thirteen addrs cells ---- *)
    iDestruct (boot_ran_split g (A + 76 + 4) (A + 80) (A + 136) ltac:(lia)
                 ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 80) (A + 80 + 4 * Z.of_nat 13%nat)
                 (A + 136) ltac:(lia) ltac:(lia) with "H") as "[H9 _]".
    iDestruct (boot_word4_cells g A 13%nat 80 Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 80 Hal4 eq_refl)) with "Hcl H9")
      as (l) "[%Hlen Hl]".
    (* ---- assemble ---- *)
    rewrite /inode_node_raw /ientry_raw_at /inode_raw /inode_meta
            /i_lock /i_dev /i_inum /i_ref /i_valid
            /i_type /i_major /i_minor /i_nlink /i_size.
    (* [i_dev]'s displacement is 0, so [off_of_z] leaves [pa_of_z (A + 0)] *)
    rewrite E0 E4 E8 E16 E64 E68 E70 E72 E74 E76 !off_of_z Z.add_0_r.
    iSplitL "Hs"; [iExact "Hs" |].
    iSplitL "H0"; [iExists vdev; iExact "H0" |].
    iSplitL "H1"; [iExists vinum; iExact "H1" |].
    iSplitL "H2"; [iExact "H2" |].
    iSplitL "H3"; [iExists vvalid; iExact "H3" |].
    iSplitL "H4 H5 H6 H7 H8".
    { iExists (MkDinode vtype vmajor vminor vnlink vsize l).
      cbn [di_type di_major di_minor di_nlink di_size].
      iSplitL "H4"; [iExact "H4" |]. iSplitL "H5"; [iExact "H5" |].
      iSplitL "H6"; [iExact "H6" |]. iSplitL "H7"; [iExact "H7" |].
      iExact "H8". }
    iExists l. iSplitR; [iPureIntro; exact Hlen |]. iExact "Hl".
  Qed.

  (* the NINODE entries: the family, at the itable's stride and anchored at
     the ENTRY array's own base.  Gives both of [main_globals_raw]'s inode
     conjuncts -- the sleeplocks iinit takes, and the cells [icache_boot]
     takes. *)
  Lemma boot_inode_entries (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g inode_entry_base
                   (inode_entry_base + inode_stride * Z.of_nat NINODE)
    -∗ ([∗ list] i ∈ seq 0 NINODE, sl_raw (inode_lock i)) ∗
       ([∗ list] k ∈ seq 0 NINODE, ientry_raw k).
  Proof.
    intro Hmem. iIntros "#Hcl H".
    iDestruct (boot_stride_family_seq g inode_node_raw
                 inode_entry_base inode_stride NINODE
                 ltac:(unfold inode_stride; lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side inode_entry_base inode_stride NINODE
                                   136 img_end ram_hi i A Hi HA
                                   ltac:(unfold inode_stride; lia)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       assert (T1 : A <= A + 136) by lia;
                       assert (T2 : A + 136 <= A + inode_stride)
                         by (unfold inode_stride; lia);
                       iIntros "#Hcl H";
                       iDestruct (boot_ran_split g A (A + 136) (A + inode_stride)
                                    T1 T2 with "H") as "[H _]";
                       iApply (boot_inode_entry g A Hmem Q1 Q2 Q3 with "Hcl H"))
                 with "Hcl H") as "H".
    rewrite /inode_node_raw big_sepL_sep. iDestruct "H" as "[H1 H2]".
    iSplitL "H1".
    - iApply (big_sepL_mono with "H1"). iIntros (n k _) "Hk".
      rewrite (i_lock_of_entry k). iExact "Hk".
    - iApply (big_sepL_mono with "H2"). iIntros (n k _) "Hk".
      rewrite /ientry_raw -(ientry_of_z k). iExact "Hk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE STATIC [struct log], ROWS (A) OF THE fsinit BUNDLE.              *)
  (*                                                                    *)
  (* 168 bytes at [KernelSyms.log], and NOTHING carved them before stage *)
  (* (f): the whole record was one of the dropped gaps in the .bss walk. *)
  (* Layout (LogInv.v's own header): spinlock@0 (24B), start@24,         *)
  (* outstanding@28, committing@32, dev@36, ncommit@40, lh.n@44,         *)
  (* lh.block[i]@48+4i, thirty of them.                                  *)
  (*                                                                    *)
  (* [outstanding] and [committing] come out PINNED AT ZERO -- the       *)
  (* record is .bss past [img_end], so [boot_ran_cell4_bss] gives the    *)
  (* VALUE rather than an existential, which is what initlog's contract  *)
  (* (and hence [SpecFsinit]'s premise pile) asks for.  The thirty       *)
  (* [lh.block] words are a stride family at stride 4, so BootCarve §11  *)
  (* gives them out of one range with the per-element carve written      *)
  (* once.                                                              *)
  (*                                                                    *)
  (* The three spinlock cells are carved DIRECTLY rather than through    *)
  (* [boot_lk_raw]: every other cell here lands in [pa_of_z]'s spelling  *)
  (* and one uniform set of address bridges is what makes the assembly   *)
  (* below an [iFrame] instead of nine conversions.                     *)
  (* ------------------------------------------------------------------ *)
  Lemma log_nm_of_z : lock_name_field log_addr = pa_of_z (KernelSyms.log + 8).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma log_cpu_of_z : lock_cpu log_addr = pa_of_z (KernelSyms.log + 16).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma l_start_of_z : l_start = pa_of_z (KernelSyms.log + 24).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma l_out_of_z : l_out = pa_of_z (KernelSyms.log + 28).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma l_cmt_of_z : l_cmt = pa_of_z (KernelSyms.log + 32).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma l_dev_of_z : l_dev = pa_of_z (KernelSyms.log + 36).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma l_ncommit_of_z : l_ncommit = pa_of_z (KernelSyms.log + 40).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma lh_n_of_z : lh_n_pa = pa_of_z (KernelSyms.log + 44).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma log_lk_of_z : log_addr = pa_of_z KernelSyms.log.
  Proof. reflexivity. Qed.

  Lemma lh_block_of_z (i : nat) :
    lh_block i = pa_of_z (KernelSyms.log + 48 + 4 * Z.of_nat i).
  Proof.
    rewrite /lh_block /log_pa /log_addr.
    change (mword_of_int KernelSyms.log : Arch.pa) with (pa_of_z KernelSyms.log).
    rewrite pa_add_of_z. f_equal. lia.
  Qed.

  Lemma boot_log_raw (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g KernelSyms.log (KernelSyms.log + 168) -∗ main_log_raw.
  Proof.
    intro Hmem. iIntros "#Hcl H".
    assert (Hflo : text_end <= KernelSyms.log + 48)
      by (vm_compute; discriminate).
    assert (Hfhi : KernelSyms.log + 48 + 4 * Z.of_nat LOGBLOCKS <= ram_hi)
      by (unfold LOGBLOCKS; vm_compute; discriminate).
    (* ---- the spinlock's three cells ---- *)
    iDestruct (boot_ran_split g KernelSyms.log (KernelSyms.log + 4)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hw H]".
    iDestruct (boot_ran_cell4 g KernelSyms.log Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hw") as (vlock) "Hw".
    iDestruct (boot_ran_split g (KernelSyms.log + 4) (KernelSyms.log + 8)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (KernelSyms.log + 8) (KernelSyms.log + 16)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hn H]".
    iDestruct (boot_ran_eq g (KernelSyms.log + 8) (KernelSyms.log + 16)
                 (KernelSyms.log + 8) (KernelSyms.log + 8 + 8) eq_refl
                 ltac:(lia) with "Hn") as "Hn".
    iDestruct (boot_ran_cell8 g (KernelSyms.log + 8) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hn") as (vname) "Hn".
    iDestruct (boot_ran_split g (KernelSyms.log + 16) (KernelSyms.log + 24)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hc H]".
    iDestruct (boot_ran_eq g (KernelSyms.log + 16) (KernelSyms.log + 24)
                 (KernelSyms.log + 16) (KernelSyms.log + 16 + 8) eq_refl
                 ltac:(lia) with "Hc") as "Hc".
    iDestruct (boot_ran_cell8 g (KernelSyms.log + 16) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hc") as (vcpu) "Hc".
    (* ---- the six scalar fields ---- *)
    iDestruct (boot_ran_split g (KernelSyms.log + 24) (KernelSyms.log + 28)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hst H]".
    iDestruct (boot_ran_cell4 g (KernelSyms.log + 24) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hst") as (v_start) "Hst".
    iDestruct (boot_ran_split g (KernelSyms.log + 28) (KernelSyms.log + 32)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hout H]".
    iDestruct (boot_ran_cell4_bss g (KernelSyms.log + 28)
                 (mword_of_int 0 : mword 32) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                 ltac:(intros j _; apply BootCarve.nth_byte_zero;
                       vm_compute; reflexivity) with "Hcl Hout") as "Hout".
    iDestruct (boot_ran_split g (KernelSyms.log + 32) (KernelSyms.log + 36)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hcmt H]".
    iDestruct (boot_ran_cell4_bss g (KernelSyms.log + 32)
                 (mword_of_int 0 : mword 32) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                 ltac:(intros j _; apply BootCarve.nth_byte_zero;
                       vm_compute; reflexivity) with "Hcl Hcmt") as "Hcmt".
    iDestruct (boot_ran_split g (KernelSyms.log + 36) (KernelSyms.log + 40)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hdv H]".
    iDestruct (boot_ran_cell4 g (KernelSyms.log + 36) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hdv") as (v_dev) "Hdv".
    iDestruct (boot_ran_split g (KernelSyms.log + 40) (KernelSyms.log + 44)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hnc H]".
    iDestruct (boot_ran_cell4 g (KernelSyms.log + 40) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hnc") as (v_nc) "Hnc".
    iDestruct (boot_ran_split g (KernelSyms.log + 44) (KernelSyms.log + 48)
                 (KernelSyms.log + 168) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) with "H") as "[Hn2 H]".
    iDestruct (boot_ran_cell4 g (KernelSyms.log + 44) Hmem
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; reflexivity) with "Hcl Hn2") as (v_n) "Hn2".
    (* ---- the thirty header slots, one stride family ---- *)
    iDestruct (boot_ran_eq g (KernelSyms.log + 48) (KernelSyms.log + 168)
                 (KernelSyms.log + 48)
                 (KernelSyms.log + 48 + 4 * Z.of_nat LOGBLOCKS)
                 eq_refl ltac:(unfold LOGBLOCKS; vm_compute; reflexivity)
                 with "H") as "H".
    iDestruct (boot_stride_family_seq g (fun a => ∃ w : mword 32, a ↦₄ w)%I
                 (KernelSyms.log + 48) 4 LOGBLOCKS ltac:(lia)
                 ltac:(intros i A Hi HA HA1 HA2;
                       iIntros "#Hcl2 Hb";
                       iApply (boot_ran_cell4 g A Hmem ltac:(lia) ltac:(lia)
                                 ltac:(rewrite HA;
                                       apply (z_mod_mul 4 (KernelSyms.log + 48) 4);
                                       [vm_compute; reflexivity | reflexivity])
                                 with "Hcl2 Hb"))
                 with "Hcl H") as "Hblk".
    (* ---- assemble, every address in [pa_of_z]'s spelling ---- *)
    rewrite /main_log_raw.
    iExists vlock, v_start, v_dev, v_nc, v_n, vname, vcpu.
    rewrite log_nm_of_z log_cpu_of_z l_start_of_z l_out_of_z l_cmt_of_z
            l_dev_of_z l_ncommit_of_z lh_n_of_z log_lk_of_z.
    iFrame "Hw Hn Hc Hst Hdv Hout Hcmt Hnc Hn2".
    iApply (big_sepL_mono with "Hblk"). iIntros (n i _) "Hi".
    rewrite lh_block_of_z. iExact "Hi".
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

  (* ================================================================== *)
  (* [proc_raw] / [proc_pub]: ONE process slot, and then the family.      *)
  (*                                                                    *)
  (* Four RUNS inside a [struct proc] have no cell wrapper of their own,  *)
  (* so they get one each here: the 14-word saved context, the sixteen    *)
  (* null [ofile] slots, the 16-byte name array, and (through            *)
  (* [BootCarve.boot_ran_cell8_bss]) the four PINNED zeros.  Each is      *)
  (* stated GENERICALLY in the record's base and the field's offset, and  *)
  (* then restated in the consumer's own vocabulary -- the restatement is *)
  (* one [iApply], because [p_ofile] / [p_name] / [ctx_cells] ARE those    *)
  (* address forms by definition.                                        *)
  (* ================================================================== *)

  (* the saved-context save area: [n] doublewords from [C + off]. *)
  Lemma boot_ctx_cells (g : gstate) (C : Z) (n : nat) (off : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= C + off -> C + off + 8 * Z.of_nat n <= ram_hi ->
    (C + off) mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g (C + off) (C + off + 8 * Z.of_nat n)
    -∗ (∃ vs : list (mword 64), ⌜length vs = n⌝ ∗ ctx_cells_at (pa_of_z C) off vs).
  Proof.
    intro Hmem. revert off. induction n as [|k IH]; intros off Hlo Hhi Hal.
    - iIntros "_ _". iExists []. iSplitR; [done |]. cbn [ctx_cells_at]. done.
    - iIntros "#Hcl H".
      (* ALL the arithmetic first: once an [mword] witness is in context the
         zify hook makes [lia] answer "Cannot find witness" (durable-notes). *)
      assert (Hd1 : C + off <= C + off + 8) by lia.
      assert (Hd2 : C + off + 8 <= C + off + 8 * Z.of_nat (S k)) by lia.
      assert (Eo : C + (off + 8) = C + off + 8) by lia.
      assert (Ehi : C + off + 8 * Z.of_nat (S k)
                    = C + (off + 8) + 8 * Z.of_nat k) by lia.
      assert (Elo : C + off + 8 = C + (off + 8)) by lia.
      assert (Hchi : C + off + 8 <= ram_hi) by lia.
      assert (Hilo : text_end <= C + (off + 8)) by lia.
      assert (Hihi : C + (off + 8) + 8 * Z.of_nat k <= ram_hi) by lia.
      assert (Hial : (C + (off + 8)) mod 8 = 0)
        by (rewrite Eo; exact (z_mod_addo 8 (C + off) 8 Hal eq_refl)).
      iDestruct (boot_ran_split g (C + off) (C + off + 8)
                   (C + off + 8 * Z.of_nat (S k)) Hd1 Hd2 with "H") as "[Hc H]".
      iDestruct (boot_ran_cell8 g (C + off) Hmem Hlo Hchi Hal with "Hcl Hc")
        as (v) "Hc".
      iDestruct (boot_ran_eq g _ _ (C + (off + 8))
                   (C + (off + 8) + 8 * Z.of_nat k) Elo Ehi with "H") as "H".
      iDestruct (IH (off + 8) Hilo Hihi Hial with "Hcl H") as (vs) "[%Hlen Hvs]".
      iExists (v :: vs). iSplitR; [iPureIntro; cbn [length]; by rewrite Hlen |].
      cbn [ctx_cells_at]. iSplitL "Hc"; [rewrite off_of_z; iExact "Hc" | iExact "Hvs"].
  Qed.

  Lemma boot_own_ctx (g : gstate) (C : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= C -> C + 112 <= ram_hi -> C mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g C (C + 112) -∗ own_ctx (pa_of_z C).
  Proof.
    intros Hmem Hlo Hhi Hal. iIntros "#Hcl H".
    iDestruct (boot_ran_eq g C (C + 112) (C + 0) (C + 0 + 8 * Z.of_nat 14%nat)
                 ltac:(lia) ltac:(lia) with "H") as "H".
    iDestruct (boot_ctx_cells g C 14%nat 0 Hmem ltac:(lia) ltac:(lia)
                 ltac:(rewrite Z.add_0_r; exact Hal) with "Hcl H") as (vs) "[%Hlen Hvs]".
    rewrite /own_ctx /ctx_cells. iExists vs. iSplitR; [done |]. iExact "Hvs".
  Qed.

  (* a run of [n] PINNED-zero doublewords from [C + off] -- the sixteen null
     [p->ofile] slots (and, at n = 1, any single zeroed pointer cell). *)
  Lemma boot_zero_cells (g : gstate) (C : Z) (n : nat) (off : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= C + off -> img_end <= C + off ->
    C + off + 8 * Z.of_nat n <= ram_hi -> (C + off) mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g (C + off) (C + off + 8 * Z.of_nat n)
    -∗ ([∗ list] fd ↦ v ∈ replicate n (zero_reg : mword 64),
          add_vec (pa_of_z C) (mword_of_int (off + 8 * Z.of_nat fd)) ↦₈ v).
  Proof.
    intro Hmem. revert off. induction n as [|k IH]; intros off Hlo Hbss Hhi Hal.
    - iIntros "_ _". done.
    - iIntros "#Hcl H".
      assert (Hd1 : C + off <= C + off + 8) by lia.
      assert (Hd2 : C + off + 8 <= C + off + 8 * Z.of_nat (S k)) by lia.
      assert (Eo : C + (off + 8) = C + off + 8) by lia.
      assert (Ehi : C + off + 8 * Z.of_nat (S k)
                    = C + (off + 8) + 8 * Z.of_nat k) by lia.
      assert (Elo : C + off + 8 = C + (off + 8)) by lia.
      assert (Hchi : C + off + 8 <= ram_hi) by lia.
      assert (Hilo : text_end <= C + (off + 8)) by lia.
      assert (Hibss : img_end <= C + (off + 8)) by lia.
      assert (Hihi : C + (off + 8) + 8 * Z.of_nat k <= ram_hi) by lia.
      assert (Hial : (C + (off + 8)) mod 8 = 0)
        by (rewrite Eo; exact (z_mod_addo 8 (C + off) 8 Hal eq_refl)).
      assert (Ehd : off + 8 * Z.of_nat 0%nat = off) by lia.
      iDestruct (boot_ran_split g (C + off) (C + off + 8)
                   (C + off + 8 * Z.of_nat (S k)) Hd1 Hd2 with "H") as "[Hc H]".
      iDestruct (boot_ran_cell8_bss g (C + off) (zero_reg : mword 64) Hmem Hlo Hbss
                   Hchi Hal nth_byte_zero8 with "Hcl Hc") as "Hc".
      iDestruct (boot_ran_eq g _ _ (C + (off + 8))
                   (C + (off + 8) + 8 * Z.of_nat k) Elo Ehi with "H") as "H".
      iDestruct (IH (off + 8) Hilo Hibss Hihi Hial with "Hcl H") as "Hrest".
      cbn [replicate]. iSplitL "Hc".
      + rewrite Ehd off_of_z. iExact "Hc".
      + iApply (big_sepL_mono with "Hrest"). iIntros (fd v _) "Hv".
        rewrite (_ : off + 8 * Z.of_nat (S fd) = off + 8 + 8 * Z.of_nat fd); [| lia].
        iExact "Hv".
  Qed.

  (* a byte ARRAY inside the record, contents existential: [p->name[16]]. *)
  Lemma boot_name_cells (g : gstate) (C : Z) (n : nat) (off : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= C + off -> C + off + Z.of_nat n <= ram_hi ->
    kmap_static_claims -∗ boot_raw_ran g (C + off) (C + off + Z.of_nat n)
    -∗ (∃ bs : list (bv 8), ⌜length bs = n⌝ ∗
          [∗ list] i ↦ b ∈ bs,
            add_vec (pa_of_z C) (mword_of_int (off + Z.of_nat i)) ↦ₘ b).
  Proof.
    intros Hmem Hlo Hhi. iIntros "#Hcl H".
    iDestruct (boot_ran_bytes_list g (C + off) n Hmem Hlo Hhi with "Hcl H")
      as (bs) "[%Hlen Hbs]".
    iExists bs. iSplitR; [done |].
    iApply (big_sepL_mono with "Hbs"). iIntros (i b _) "Hb".
    rewrite off_of_z (_ : C + (off + Z.of_nat i) = C + off + Z.of_nat i); [| lia].
    iEval (rewrite pa_add_of_z) in "Hb". iExact "Hb".
  Qed.

  (* ---- the three runs, in the consumer's own vocabulary ---- *)

  Lemma boot_ofile_cells (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    img_end <= A -> A + 336 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗
    boot_raw_ran g (A + 208) (A + 208 + 8 * Z.of_nat NOFILE)
    -∗ ofile_cells (pa_of_z A) (replicate NOFILE (zero_reg : mword 64)).
  Proof.
    intros Hmem Hbss Hhi Hal.
    assert (Hlo : text_end <= A)
      by exact (z_lo_trans text_end img_end A ltac:(vm_compute; discriminate) Hbss).
    rewrite /ofile_cells.
    iApply (boot_zero_cells g A NOFILE 208 Hmem ltac:(lia) ltac:(lia)
              ltac:(unfold NOFILE; lia) (z_mod_addo 8 A 208 Hal eq_refl)).
  Qed.

  Lemma boot_proc_name (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> A + 360 <= ram_hi ->
    kmap_static_claims -∗
    boot_raw_ran g (A + 344) (A + 344 + Z.of_nat PNAMELEN)
    -∗ (∃ bs : list (bv 8), ⌜length bs = PNAMELEN⌝ ∗
          pname_cells (pa_of_z A) (DfracOwn 1) bs).
  Proof.
    intros Hmem Hlo Hhi. rewrite /pname_cells.
    iApply (boot_name_cells g A PNAMELEN 344 Hmem ltac:(lia)
              ltac:(unfold PNAMELEN; lia)).
  Qed.

  (* ---- ONE process slot: everything the image owes about [proc[i]] ----
     [proc_raw]'s three own cells plus [proc_dormant_nofd], AND the two
     PUBLIC conjuncts [main_globals_raw] lists separately ([p_chan] and
     [proc_pub]) -- one lemma, because [p_pid ↦₄{1/2}] appears in BOTH halves
     (inside [proc_dormant_nofd] and inside [proc_pub]) and the image can only
     hand out the cell ONCE: it is carved in full at +48 and SPLIT.
     The four PINNED zeros ([sz] at +72, [pagetable] at +80, [trapframe] at
     +88, [cwd] at +336) come from [boot_ran_cell8_bss]; the [pv_sz] bound
     [uint (pv_sz V) <= uvm_maxsz] is then free.  [p_parent] (+56) is claimed
     by no bundle and is dropped with the padding. *)
  Local Definition proc_slot_raw (a : Arch.pa) : iProp Σ :=
    (proc_raw a ∗ (∃ ch : SailStdpp.Values.mword 64, p_chan a ↦₈ ch) ∗
     proc_pub a)%I.

  Lemma boot_proc_slot (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    img_end <= A -> A + 360 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 360)
    -∗ proc_slot_raw (pa_of_z A).
  Proof.
    intros Hmem Hbss Hhi Hal. iIntros "#Hcl H".
    assert (Hlo : text_end <= A)
      by exact (z_lo_trans text_end img_end A ltac:(vm_compute; discriminate) Hbss).
    assert (Hal4 : A mod 4 = 0) by exact (z_mod8_mod4 A Hal).
    (* the field-address bridges, and every alignment fact, BEFORE any cell is
       destructed: once an [mword] witness is in context the zify hook makes
       [lia] fail (durable-notes). *)
    assert (E48 : (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64)
                  = mword_of_int 48) by (apply bv_eq; vm_compute; reflexivity).
    assert (E72 : (sign_extend' 64 (mword_of_int 72 : mword 12) : mword 64)
                  = mword_of_int 72) by (apply bv_eq; vm_compute; reflexivity).
    assert (E80 : (sign_extend' 64 (mword_of_int 80 : mword 12) : mword 64)
                  = mword_of_int 80) by (apply bv_eq; vm_compute; reflexivity).
    assert (E88 : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
                  = mword_of_int 88) by (apply bv_eq; vm_compute; reflexivity).
    assert (M24 : (A + 24) mod 4 = 0) by exact (z_mod_addo 4 A 24 Hal4 eq_refl).
    assert (M32 : (A + 32) mod 8 = 0) by exact (z_mod_addo 8 A 32 Hal eq_refl).
    assert (M40 : (A + 40) mod 4 = 0) by exact (z_mod_addo 4 A 40 Hal4 eq_refl).
    assert (M44 : (A + 44) mod 4 = 0) by exact (z_mod_addo 4 A 44 Hal4 eq_refl).
    assert (M48 : (A + 48) mod 4 = 0) by exact (z_mod_addo 4 A 48 Hal4 eq_refl).
    assert (M64 : (A + 64) mod 8 = 0) by exact (z_mod_addo 8 A 64 Hal eq_refl).
    assert (M72 : (A + 72) mod 8 = 0) by exact (z_mod_addo 8 A 72 Hal eq_refl).
    assert (M80 : (A + 80) mod 8 = 0) by exact (z_mod_addo 8 A 80 Hal eq_refl).
    assert (M88 : (A + 88) mod 8 = 0) by exact (z_mod_addo 8 A 88 Hal eq_refl).
    assert (M96 : (A + 96) mod 8 = 0) by exact (z_mod_addo 8 A 96 Hal eq_refl).
    assert (M336 : (A + 336) mod 8 = 0) by exact (z_mod_addo 8 A 336 Hal eq_refl).
    (* the fourteen windows, in address order.  A window is re-anchored by an
       EMPTY split, so every cut's [lo] is literally the [A + off] its cell
       lemma asks for. *)
    iDestruct (boot_ran_split g A (A + 24) (A + 360) ltac:(lia) ltac:(lia)
                 with "H") as "[Hlk H]".
    iDestruct (boot_ran_split g (A + 24) (A + 24 + 4) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hst H]".
    iDestruct (boot_ran_split g (A + 24 + 4) (A + 32) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 32) (A + 32 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hch H]".
    iDestruct (boot_ran_split g (A + 32 + 8) (A + 40) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 40) (A + 40 + 4) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hkl H]".
    iDestruct (boot_ran_split g (A + 40 + 4) (A + 44) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 44) (A + 44 + 4) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hxs H]".
    iDestruct (boot_ran_split g (A + 44 + 4) (A + 48) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 48) (A + 48 + 4) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hpid H]".
    iDestruct (boot_ran_split g (A + 48 + 4) (A + 64) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 64) (A + 64 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hks H]".
    iDestruct (boot_ran_split g (A + 64 + 8) (A + 72) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 72) (A + 72 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hsz H]".
    iDestruct (boot_ran_split g (A + 72 + 8) (A + 80) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 80) (A + 80 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hpg H]".
    iDestruct (boot_ran_split g (A + 80 + 8) (A + 88) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 88) (A + 88 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Htf H]".
    iDestruct (boot_ran_split g (A + 88 + 8) (A + 96) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 96) (A + 96 + 112) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hctx H]".
    iDestruct (boot_ran_split g (A + 96 + 112) (A + 208) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 208) (A + 208 + 8 * Z.of_nat NOFILE) (A + 360)
                 ltac:(lia) ltac:(unfold NOFILE; lia) with "H") as "[Hof H]".
    iDestruct (boot_ran_split g (A + 208 + 8 * Z.of_nat NOFILE) (A + 336) (A + 360)
                 ltac:(unfold NOFILE; lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 336) (A + 336 + 8) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[Hcwd H]".
    iDestruct (boot_ran_split g (A + 336 + 8) (A + 344) (A + 360)
                 ltac:(lia) ltac:(lia) with "H") as "[_ H]".
    iDestruct (boot_ran_split g (A + 344) (A + 344 + Z.of_nat PNAMELEN) (A + 360)
                 ltac:(lia) ltac:(unfold PNAMELEN; lia) with "H") as "[Hnm _]".
    (* the cells *)
    iDestruct (boot_lk_raw g A Hmem Hlo ltac:(lia) Hal with "Hcl Hlk") as "Hlk".
    iDestruct (boot_ran_cell4 g (A + 24) Hmem ltac:(lia) ltac:(lia) M24
                 with "Hcl Hst") as (vst) "Hst".
    iDestruct (boot_ran_cell8 g (A + 32) Hmem ltac:(lia) ltac:(lia) M32
                 with "Hcl Hch") as (vch) "Hch".
    iDestruct (boot_ran_cell4 g (A + 40) Hmem ltac:(lia) ltac:(lia) M40
                 with "Hcl Hkl") as (vkl) "Hkl".
    iDestruct (boot_ran_cell4 g (A + 44) Hmem ltac:(lia) ltac:(lia) M44
                 with "Hcl Hxs") as (vxs) "Hxs".
    iDestruct (boot_ran_cell4 g (A + 48) Hmem ltac:(lia) ltac:(lia) M48
                 with "Hcl Hpid") as (vpid) "Hpid".
    iDestruct (boot_ran_cell8 g (A + 64) Hmem ltac:(lia) ltac:(lia) M64
                 with "Hcl Hks") as (vks) "Hks".
    iDestruct (boot_ran_cell8_bss g (A + 72) (zero_reg : mword 64) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia) M72 nth_byte_zero8
                 with "Hcl Hsz") as "Hsz".
    iDestruct (boot_ran_cell8_bss g (A + 80) (zero_reg : mword 64) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia) M80 nth_byte_zero8
                 with "Hcl Hpg") as "Hpg".
    iDestruct (boot_ran_cell8_bss g (A + 88) (zero_reg : mword 64) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia) M88 nth_byte_zero8
                 with "Hcl Htf") as "Htf".
    iDestruct (boot_ran_cell8_bss g (A + 336) (zero_reg : mword 64) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia) M336 nth_byte_zero8
                 with "Hcl Hcwd") as "Hcwd".
    iDestruct (boot_own_ctx g (A + 96) Hmem ltac:(lia) ltac:(lia) M96
                 with "Hcl Hctx") as "Hctx".
    iDestruct (boot_ofile_cells g A Hmem Hbss ltac:(lia) Hal with "Hcl Hof")
      as "Hof".
    iDestruct (boot_proc_name g A Hmem Hlo ltac:(lia) with "Hcl Hnm")
      as (bs) "[%Hbs Hnm]".
    (* the pid cell is owned by BOTH halves at a half each *)
    iAssert ((pa_of_z (A + 48)) ↦₄{DfracOwn (1/2)} vpid ∗
             (pa_of_z (A + 48)) ↦₄{DfracOwn (1/2)} vpid)%I with "[Hpid]"
      as "[Hpid1 Hpid2]".
    { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hpid". }
    rewrite /proc_slot_raw /proc_raw /proc_pub /proc_dormant_nofd /proc_fields
            /p_state /p_chan /p_killed /p_xstate /p_pid /p_kstack /p_sz
            /p_pagetable /p_trapframe /p_context /p_cwd
            E48 E72 E80 E88 !off_of_z.
    iSplitL "Hlk Hst Hks Hpid1 Hsz Hcwd Hnm Hof Hctx Hpg Htf".
    { iExists vst, vks.
      iSplitL "Hlk"; [iExact "Hlk" |]. iSplitL "Hst"; [iExact "Hst" |].
      iSplitL "Hks"; [iExact "Hks" |].
      iExists (MkPPriv (zero_reg : mword 64)
                 (UPTD (mword_of_int 0 : mword 44) (mword_of_int 0 : mword 44) ∅ ∅)
                 [] (replicate NOFILE (zero_reg : mword 64))
                 (zero_reg : mword 64) bs), vpid.
      cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
      iSplitR; [iPureIntro; split_and!;
                [reflexivity | reflexivity | vm_compute; discriminate] |].
      iSplitL "Hpid1"; [iExact "Hpid1" |].
      iSplitL "Hsz Hcwd Hnm".
      { iSplitL "Hsz"; [iExact "Hsz" |]. iSplitL "Hcwd"; [iExact "Hcwd" |].
        iSplitR; [iPureIntro; exact Hbs |]. iExact "Hnm". }
      iSplitL "Hof"; [iExact "Hof" |]. iSplitL "Hctx"; [iExact "Hctx" |].
      iSplitL "Hpg"; [iExact "Hpg" |]. iExact "Htf". }
    iSplitL "Hch"; [iExists vch; iExact "Hch" |].
    iExists vkl, vxs, vpid.
    iSplitL "Hkl"; [iExact "Hkl" |]. iSplitL "Hxs"; [iExact "Hxs" |].
    iExact "Hpid2".
  Qed.

  (* ...and the 64 slots, out of the one [proc[]] range: ONE family, whose
     per-element carve gives both of [main_globals_raw]'s proc big-ops. *)
  Lemma boot_procs_raw (g : gstate) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    kmap_static_claims -∗
    boot_raw_ran g KernelSyms.proc
                   (KernelSyms.proc + proc_size * Z.of_nat NPROC)
    -∗ ([∗ list] i ∈ seq 0 NPROC, proc_raw (proc_addr i)) ∗
       ([∗ list] i ∈ seq 0 NPROC,
          (∃ ch : SailStdpp.Values.mword 64, p_chan (proc_addr i) ↦₈ ch) ∗
          proc_pub (proc_addr i)).
  Proof.
    intro Hmem. iIntros "#Hcl H".
    iDestruct (boot_stride_family_seq g proc_slot_raw
                 KernelSyms.proc proc_size NPROC
                 ltac:(unfold proc_size; lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side KernelSyms.proc proc_size NPROC 360
                                   img_end ram_hi i A Hi HA
                                   ltac:(unfold proc_size; lia)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; discriminate)
                                   ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity))
                         as (Q1 & Q2 & Q3);
                       assert (T1 : A <= A + 360) by lia;
                       assert (T2 : A + 360 <= A + proc_size)
                         by (unfold proc_size; lia);
                       iIntros "#Hcl H";
                       iDestruct (boot_ran_split g A (A + 360) (A + proc_size)
                                    T1 T2 with "H") as "[H _]";
                       iApply (boot_proc_slot g A Hmem Q1 Q2 Q3 with "Hcl H"))
                 with "Hcl H") as "H".
    rewrite /proc_slot_raw big_sepL_sep. iDestruct "H" as "[H1 H2]".
    iSplitL "H1".
    - iApply (big_sepL_mono with "H1"). iIntros (n i _) "Hi".
      rewrite (proc_addr_of_z i). iExact "Hi".
    - iApply (big_sepL_mono with "H2"). iIntros (n i _) "Hi".
      rewrite (proc_addr_of_z i). iExact "Hi".
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
