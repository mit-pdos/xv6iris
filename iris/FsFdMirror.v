(* FsFdMirror.v -- THE PER-PROCESS FS/FD MIRROR, and the pure step table
   the enriched u-tier syscall rows are tied to.

   Design of record: claude-notes/design/fd-row-pilot.md (the FD-ROW
   PILOT).  This file is the PURE half of the pilot's seam: a process's
   user-tier view of its own file-descriptor table and -- era-0/solo
   scoped, see the design's section 5 -- of the abstract file system,
   as ONE record [umirror]; and per enriched syscall row a PURE relation
   [ufs_step] saying how one call moves it.  The iProp half (the enriched
   trap-contract arm that deposits the mirror's user half and hands it
   back stepped) is UexecRetFs.v; the era-0 instantiation and the pilot
   theorems are FdRowPilot.v.

   NOTHING HERE IS A NEW SPEC OF THE KERNEL.  Every arm of [ufs_step] is
   a reading of a landed AU contract's arm at the mirror:

   - open's success arm is [SpecSysOpenAU.open_post_ok_plain]'s three-way
     split (device / file / dir-at-O_RDONLY) with the fd pinned to the
     LEAST CLOSED row -- fdalloc's own scan order, [SpecFdalloc.fd_frees]'s
     head read at the mirror -- and the trunc delta is the contract's own
     [delta_trunc];
   - mknod's success arm is [SpecSysMknodAU.delta_create] at a fresh inum
     (the ADev child), keyed by the parent-prefix resolve exactly as
     [mknod_parent_elems] keys the AU walk;
   - EVERY row keeps the honest [-1] blanket: no landed contract promises
     a syscall succeeds (argstr, table-full, out-of-inodes are always
     available), so [-1] is never refuted and carries no information --
     the landed determinism stance.

   THE RESOLVE CAVEAT, recorded where it bites: [um_resolve] is
   [FsAbs.apath_at] from ROOTINO on a leading '/', else from the cwd leg.
   The kernel's walk is namex (SpecNamex R8: dots and device boundaries
   have their own rules), and the two agree on the dot-free, non-empty,
   directory-only paths the pilot exercises; the enriched-loop prover
   must align the general case BEFORE widening [uenr_dom] past the pilot
   rows (worklist, FD-ROW PILOT stage P5).

   Require block: SpecSysOpenAU.v's, VERBATIM (durable-notes: trimmed
   imports have OOM'd the build), plus nothing. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import VcGen.        (* [trunc32_unsigned] -- argfd's C [int] read *)
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecDirlink.
Require Import SpecFdalloc.
Require Import ConsoleInv.
Require Import SpecSysOpen.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import PathElems.
Require Import FsTree.
Require Import FsBytesGamma.
Require FsImg.
Require Import SpecSysMknodAU.
Require Import SpecSysWriteAU.
Require Import FsAbsEra.
Require Import FsAbsEraMknod.
Require Import FsAbsMknodFire.
Require Import FsAbs.
Import Defs.
Require Import TsoCtx.
Require Import SpecSysOpenAU.   (* [om_*], [delta_trunc] -- the mode readings
                                   and the one no-CREATE delta, reused *)
Require Import UsysMemOk.       (* [usys_fd_ok] -- UPSTREAM'S per-syscall
                                   DESCRIPTOR table.  The mirror's fd leg is a
                                   READING of it (section 5b), never a twin:
                                   off the enriched rows [ufs_step_at] IS that
                                   table, and on them the agreement is proven.
                                   Cone: [UsysMemOk]'s own requires are
                                   [ProcGeom] / [TfUser] / [UserPtTree] /
                                   [ProcPtOwn] / [UserPerm] / [FdSlots], all
                                   below this file already; nothing upstream
                                   requires [FsFdMirror], so there is no
                                   cycle. *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE MIRROR RECORD                                                 *)
(* ===================================================================== *)

(* the user-tier reading of a process's own syscall-visible fs state:
   its descriptor table (per-process, unconditionally its own), and --
   solo-scoped, design section 5 -- the abstract view and the cwd leg *)
Record umirror := MkUmirror {
  um_fdt : list fdstate;
  um_av  : aview;
  um_cwd : Z;
}.

(* ===================================================================== *)
(*  2.  THE FD TABLE, PURELY                                              *)
(* ===================================================================== *)

(* [fdt0] and [fdt0_length] now live in [FdSlots], beside the mint that
   produces them. *)

(* fdalloc's scan: the first closed row.  [fd_frees]'s head, read at the
   mirror. *)
Fixpoint fd_lowest_closed (l : list fdstate) : option nat :=
  match l with
  | [] => None
  | FdClosed :: _ => Some 0%nat
  | _ :: l' => S <$> fd_lowest_closed l'
  end.

Lemma fd_lowest_closed_fdt0 : fd_lowest_closed fdt0 = Some 0%nat.
Proof. reflexivity. Qed.

Lemma fd_lowest_closed_bound (l : list fdstate) (fd : nat) :
  fd_lowest_closed l = Some fd -> (fd < length l)%nat.
Proof.
  revert fd. induction l as [| st l IH]; intros fd H; [discriminate H |].
  cbn in H. destruct st.
  - injection H as <-. cbn. lia.
  - destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| discriminate H].
    cbn in H. injection H as <-. cbn. specialize (IH k eq_refl). lia.
Qed.

(* ===================================================================== *)
(*  3.  THE PATH STRING, READ OFF THE IMAGE                               *)
(* ===================================================================== *)

(* the NUL byte, and xv6's own path bound (MAXPATH = 128) *)
Definition unul : bv 8 := (mword_of_int 0 : mword 8).
Definition UMAXPATH : nat := 128%nat.

(* the NUL-terminated string at [a] in image [M]: what argstr fetches.
   [None] when the run leaves the image or exceeds the bound -- the
   enriched row's [-1] escape covers that arm ([ufs_step] below). *)
Fixpoint ustr_read_aux (M : gmap Z (bv 8)) (a : Z) (fuel : nat)
    : option (list (bv 8)) :=
  match fuel with
  | O => None
  | S f =>
      match M !! a with
      | None => None
      | Some b => if decide (b = unul) then Some []
                  else cons b <$> ustr_read_aux M (a + 1) f
      end
  end.

Definition ustr_read (M : gmap Z (bv 8)) (a : Z) : option (list (bv 8)) :=
  ustr_read_aux M a UMAXPATH.

(* a string as a byte FUNCTION, the heap-resource spelling ([UserHeap]'s
   runs are [nat -> bv 8]); index [length pl] is the terminator *)
Definition ustr_bytes (pl : list (bv 8)) : nat -> bv 8 :=
  fun j => nth j pl unul.

(* the read, established from pointwise presence -- the pure half of the
   leaf's string tie (UexecRetFs.v holds the resource half) *)
Lemma ustr_read_aux_of (M : gmap Z (bv 8)) (pl : list (bv 8)) (a : Z)
    (fuel : nat) :
  (length pl < fuel)%nat ->
  Forall (fun b : bv 8 => b <> unul) pl ->
  (forall j : nat, (j <= length pl)%nat ->
     M !! (a + Z.of_nat j) = Some (ustr_bytes pl j)) ->
  ustr_read_aux M a fuel = Some pl.
Proof.
  revert a fuel. induction pl as [| b pl IH]; intros a fuel Hf Hall HM.
  - destruct fuel as [| f]; [cbn in Hf; lia |].
    cbn. pose proof (HM 0%nat ltac:(cbn; lia)) as H0.
    cbn in H0. rewrite Z.add_0_r in H0. rewrite H0.
    destruct (decide (unul = unul)) as [_ | Hc];
      [reflexivity | exfalso; exact (Hc eq_refl)].
  - destruct fuel as [| f]; [cbn in Hf; lia |].
    cbn. pose proof (HM 0%nat ltac:(cbn; lia)) as H0.
    cbn in H0. rewrite Z.add_0_r in H0. rewrite H0.
    inversion Hall as [| b' pl' Hb Hall']; subst b' pl'.
    destruct (decide (b = unul)) as [Hc | _]; [exfalso; exact (Hb Hc) |].
    rewrite (IH (a + 1) f).
    + reflexivity.
    + cbn in Hf. lia.
    + exact Hall'.
    + intros j Hj.
      pose proof (HM (S j) ltac:(cbn; lia)) as HS.
      cbn in HS.
      replace (a + 1 + Z.of_nat j) with (a + Z.pos (Pos.of_succ_nat j))
        by lia.
      exact HS.
Qed.

Lemma ustr_read_of (M : gmap Z (bv 8)) (pl : list (bv 8)) (a : Z) :
  (length pl < UMAXPATH)%nat ->
  Forall (fun b : bv 8 => b <> unul) pl ->
  (forall j : nat, (j <= length pl)%nat ->
     M !! (a + Z.of_nat j) = Some (ustr_bytes pl j)) ->
  ustr_read M a = Some pl.
Proof. intros Hf Hall HM. exact (ustr_read_aux_of M pl a UMAXPATH Hf Hall HM). Qed.

(* ===================================================================== *)
(*  4.  THE RESOLVE (the walk, read at the mirror)                        *)
(* ===================================================================== *)

(* namex's start rule: absolute paths at the root, relative ones at the
   cwd leg *)
Definition um_start (u : umirror) (pl : list (bv 8)) : Z :=
  if decide (pl !! 0%nat = Some SLASH) then FsImg.ROOTINO else um_cwd u.

Definition um_resolve (u : umirror) (pl : list (bv 8)) : option Z :=
  apath_at (um_av u) (um_start u pl) (path_elems pl).

(* the parent-prefix resolve, [mknod_parent_elems]'s spelling *)
Definition um_resolve_parent (u : umirror) (pl : list (bv 8)) : option Z :=
  apath_at (um_av u) (um_start u pl) (mknod_parent_elems pl).

(* ===================================================================== *)
(*  5.  THE STEP TABLE (the enriched rows, pure)                          *)
(* ===================================================================== *)

(* the pilot rows' syscall numbers (kernel/syscall.h) *)
Definition USYS_open  : Z := 15.
Definition USYS_mknod : Z := 17.
Definition USYS_dup   : Z := 10.

(* WHICH ENRICHED ROWS TAKE A PATH.  open and mknod read argument 0 as a
   POINTER and fetch a string through it ([ufs_step] below); dup reads
   argument 0 as a descriptor NUMBER.  The split matters and is not
   cosmetic: forcing the string fetch on dup's row would make its only
   satisfiable arm the [-1] blanket (a small integer is not the address of
   a NUL-terminated string in the image), i.e. a contract the enriched loop
   could NOT discharge on a dup that succeeds.  So the path fetch is keyed
   by [uenr_path], and the enriched domain is that plus dup. *)
Definition uenr_path (n : Z) : bool :=
  bool_decide (n = USYS_open) || bool_decide (n = USYS_mknod).

(* which numbers take the enriched arm -- a FIXED decidable set so the trap
   contract's case analysis stays pure *)
Definition uenr_dom (n : Z) : bool :=
  uenr_path n || bool_decide (n = USYS_dup).

Lemma uenr_path_dom (n : Z) : uenr_path n = true -> uenr_dom n = true.
Proof. intros H. unfold uenr_dom. rewrite H. reflexivity. Qed.

(* --------------------------------------------------------------------- *)
(*  The three word readings the agreement with [usys_fd_ok] needs.  All    *)
(*  SECTION-FREE and closed, so the [vm_compute]s below are safe           *)
(*  (durable-notes: [vm_compute] on a goal carrying a section variable     *)
(*  HANGS rather than fails).                                              *)
(* --------------------------------------------------------------------- *)

(* a small non-negative literal reads back as itself, unsigned... *)
Lemma um_uint_moi (z : Z) : (0 <= z < 2 ^ 63)%Z ->
  uint (mword_of_int z : mword 64) = z.
Proof.
  intros Hz.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (H64 : (0 <= z < 2 ^ 64)%Z) by lia.
  rewrite uint_unsigned. rewrite moi64_unsigned. exact (bvw64_small z H64).
Qed.

(* ...and signed *)
Lemma um_signed_moi (z : Z) : (0 <= z < 2 ^ 63)%Z ->
  bv_signed (mword_of_int z : mword 64) = z.
Proof.
  intros Hz.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (H64 : (0 <= z < 2 ^ 64)%Z) by lia.
  unfold bv_signed. rewrite moi64_unsigned. rewrite (bvw64_small z H64).
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
  rewrite Hhm. lia.
Qed.

(* a word whose SIGNED reading is non-negative reads the same unsigned --
   what turns [argfd]'s signed test (our dup row's key) into the index
   [usys_fd_ok] inserts at *)
Lemma um_uint_of_signed (b : mword 64) :
  (0 <= bv_signed b)%Z -> uint b = bv_signed b.
Proof.
  intros Hs. rewrite uint_unsigned.
  assert (Hsi : sint b = bv_signed b) by reflexivity.
  rewrite <- Hsi in Hs |- *.
  exact (sint64_unsigned b Hs).
Qed.

(* a 64-bit word whose signed reading is a SMALL non-negative number reads
   the same through a C [int].  [argfd] narrows its argument to 32 bits
   before using it -- which is what [usys_argfd] records -- while the
   mirror's dup row keys on the full 64-bit signed reading; below 2^31 the
   two are the same number, and the row's own lookup (into a table of
   [NOFILE] slots) is what puts the argument below 2^31. *)
Lemma um_trunc32_signed_small (b : mword 64) :
  (0 <= bv_signed b < 2 ^ 31)%Z -> bv_signed (trunc32 b) = bv_signed b.
Proof.
  intros Hr.
  assert (Hu : bv_unsigned b = bv_signed b).
  { rewrite <- uint_unsigned. apply um_uint_of_signed. lia. }
  assert (Hh : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
  unfold bv_signed at 1. rewrite trunc32_unsigned Hu.
  rewrite (bvw32_small (bv_signed b) ltac:(lia)).
  apply bv_swrap_small. rewrite Hh. lia.
Qed.

(* the two readings of the FAILURE value, which every row's failure arm is
   keyed on *)
Lemma um_signed_moi_neg1 :
  bv_signed (mword_of_int (-1) : mword 64) = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma um_uint_moi_neg1 :
  uint (mword_of_int (-1) : mword 64) = 18446744073709551615%Z.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  A -1 RETURN MOVES NO DESCRIPTOR, ON EVERY ROW OF UPSTREAM'S TABLE.     *)
(*                                                                        *)
(*  Stated about [usys_fd_ok] alone -- it is a fact about THEIR table, not *)
(*  about the mirror -- because it is what every one of our rows' honest   *)
(*  [-1] blanket has to hand back.  The four rows fail two different ways: *)
(*  close and pipe report success by returning zero, so their row is       *)
(*  guarded on [uint r = 0] and [-1] fails the guard; dup and open report  *)
(*  it by returning the DESCRIPTOR, so their row is a disjunction and the  *)
(*  untouched table is simply its right side.  [-1] needs no argument at   *)
(*  all on those two -- the right disjunct is available unconditionally.   *)
(* ===================================================================== *)
Lemma usys_fd_ok_neg1 (n : Z) (tf : list (mword 64)) (sts : list fdstate) :
  usys_fd_ok n tf (mword_of_int (-1) : mword 64) sts sts.
Proof.
  assert (Hnz : uint (mword_of_int (-1) : mword 64) <> 0%Z).
  { rewrite um_uint_moi_neg1. discriminate. }
  unfold usys_fd_ok.
  destruct (decide (n = UsysMemOk.USYS_close)) as [_ | _].
  { destruct (decide (uint (mword_of_int (-1) : mword 64) = 0%Z))
      as [Hc | _]; [ exfalso; exact (Hnz Hc) | reflexivity ]. }
  destruct (decide (n = UsysMemOk.USYS_dup)) as [_ | _]; [ by right | ].
  destruct (decide (n = UsysMemOk.USYS_open)) as [_ | _]; [ by right | ].
  destruct (decide (n = UsysMemOk.USYS_pipe)) as [_ | _].
  { destruct (decide (uint (mword_of_int (-1) : mword 64) = 0%Z))
      as [Hc | _]; [ exfalso; exact (Hnz Hc) | reflexivity ]. }
  reflexivity.
Qed.

Section Steps.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* open, at a fetched path [pl] and mode word [vom].                    *)
  (*                                                                     *)
  (* The [-1] blanket first (the landed stance: the value does not say    *)
  (* which failure fired and success is never promised); then the success *)
  (* arm: the walk resolved, the fd is the least closed row, and the arm  *)
  (* is keyed by the observed [anode] exactly as                          *)
  (* [SpecSysOpenAU.open_post_ok_plain] keys its three.                   *)
  (* ------------------------------------------------------------------ *)
  Definition ufs_open_at (pl : list (bv 8)) (vom : mword 64)
      (r : mword 64) (u u' : umirror) : Prop :=
    (r = (mword_of_int (-1) : mword 64) /\ u' = u)
    \/ (exists (i : Z) (a : anode) (fd : nat),
          um_resolve u pl = Some i
          /\ um_av u !! i = Some a
          /\ fd_lowest_closed (um_fdt u) = Some fd
          /\ r = (mword_of_int (Z.of_nat fd) : mword 64)
          /\ ((* DEVICE (the init arm): major in range, O_TRUNC never
                 applies *)
              (exists (ma mi : Z) (nl : nat),
                 a = MkAnode (ADev ma mi) nl
                 /\ 0 <= ma <= NDEV_max
                 /\ u' = MkUmirror
                           (<[fd := FdOpen (om_readable vom)
                                      (om_writable vom) (FdDevice ma)]>
                              (um_fdt u))
                           (um_av u) (um_cwd u))
              \/ (* FILE: the one delta of the no-CREATE surface, iff
                    O_TRUNC *)
              (exists (bs : list (bv 8)) (nl : nat),
                 a = MkAnode (AFile bs) nl
                 /\ u' = MkUmirror
                           (<[fd := FdOpen (om_readable vom)
                                      (om_writable vom) (FdInode i)]>
                              (um_fdt u))
                           (if om_trunc vom then delta_trunc i (um_av u)
                            else um_av u)
                           (um_cwd u))
              \/ (* DIRECTORY, at O_RDONLY exactly (the whole-int test) *)
              (exists (e : gmap fname Z) (nl : nat),
                 a = MkAnode (ADir e) nl
                 /\ om_arg vom = 0
                 /\ u' = MkUmirror
                           (<[fd := FdOpen true false (FdInode i)]>
                              (um_fdt u))
                           (um_av u) (um_cwd u)))).

  (* ------------------------------------------------------------------ *)
  (* mknod, at a fetched path [pl] and the two short device words.        *)
  (* Success is [delta_create] at a fresh inum -- the AU's fused delta -- *)
  (* keyed by the parent-prefix resolve and the missing name.             *)
  (* ------------------------------------------------------------------ *)
  Definition ufs_mknod_at (pl : list (bv 8)) (ma mi : Z)
      (r : mword 64) (u u' : umirror) : Prop :=
    (r = (mword_of_int (-1) : mword 64) /\ u' = u)
    \/ (exists (d i : Z) (nm : fname) (e : gmap fname Z) (nl : nat),
          list_basics.last (path_elems pl) = Some nm
          /\ um_resolve_parent u pl = Some d
          /\ um_av u !! d = Some (MkAnode (ADir e) nl)
          /\ e !! nm = None
          /\ um_av u !! i = None
          /\ 0 < i
          /\ r = (mword_of_int 0 : mword 64)
          /\ u' = MkUmirror (um_fdt u)
                    (delta_create d nm i (ADev ma mi) (um_av u))
                    (um_cwd u)).

  (* ------------------------------------------------------------------ *)
  (* dup, at the descriptor word in argument 0.                           *)
  (*                                                                      *)
  (* sys_dup is argfd + fdalloc + filedup.  The [-1] blanket covers both   *)
  (* of its failures (the argument is not an open descriptor; the table    *)
  (* is full); the success arm says the argument names an OPEN row, the    *)
  (* new descriptor is fdalloc's least closed one, and THE TWO ROWS ARE    *)
  (* EQUAL -- filedup shares the [struct file] rather than copying it, so  *)
  (* the mirror's reading of the new row is literally the old row.  The    *)
  (* fd leg is the only leg that moves: dup touches neither the abstract   *)
  (* view nor the cwd.                                                     *)
  (* ------------------------------------------------------------------ *)
  (* the descriptor is read the way argfd reads it: [argint] into a C [int],
     i.e. the SIGNED word, with the negative half rejected.  Keying the row
     on [bv_signed vfd] rather than on "some [ofd] whose encoding is [vfd]"
     is what makes the row USABLE: the caller knows the word it passed, and
     no injectivity argument about [mword_of_int] is needed to get from it
     to the index. *)
  Definition ufs_dup_at (vfd : mword 64) (r : mword 64) (u u' : umirror)
      : Prop :=
    (r = (mword_of_int (-1) : mword 64) /\ u' = u)
    \/ (exists (nfd : nat) (st : fdstate),
          0 <= bv_signed vfd
          /\ um_fdt u !! Z.to_nat (bv_signed vfd) = Some st
          /\ st <> FdClosed
          /\ fd_lowest_closed (um_fdt u) = Some nfd
          /\ r = (mword_of_int (Z.of_nat nfd) : mword 64)
          /\ u' = MkUmirror (<[nfd := st]> (um_fdt u)) (um_av u) (um_cwd u)).

  (* the table, keyed by the number; the trapframe supplies the argument
     words the way the kernel reads them (a1 = the mode / major, a2 = the
     minor; [dev_arg] is the AU's short reading) *)
  Definition ufs_arg (tf : list (mword 64)) (k : nat) : mword 64 :=
    tf !!! tf_arg_idx k.

  Definition ufs_step_at (n : Z) (pl : list (bv 8)) (tf : list (mword 64))
      (r : mword 64) (u u' : umirror) : Prop :=
    if decide (n = USYS_open) then ufs_open_at pl (ufs_arg tf 1) r u u'
    else if decide (n = USYS_mknod) then
      ufs_mknod_at pl (dev_arg (ufs_arg tf 1)) (dev_arg (ufs_arg tf 2))
        r u u'
    else if decide (n = USYS_dup) then ufs_dup_at (ufs_arg tf 0) r u u'
    else
      (* OFF THE ENRICHED ROWS THE MIRROR'S FD LEG *IS* UPSTREAM'S TABLE.
         This arm used to read [u' = u] -- "no other syscall moves the
         mirror" -- which is FALSE of the descriptor table on three of
         upstream's own rows ([UsysMemOk.usys_fd_ok]: close, pipe and a dup
         that is not in [uenr_dom] all move it) and would have been an
         undischargeable contract the day [uenr_dom] widened, exactly the
         shape stage P5's dup finding hit.  Delegating instead is the v3
         discipline: our carrier READS their ghost/table rather than
         restating it, so the arm is true by construction and the enriched
         loop discharges it from the dispatcher's own [sysc_fd_ok] post.
         Nothing is claimed about the shared legs here -- a quiet row's
         [um_av]/[um_cwd] is the SHARED state's business (chdir moves the
         cwd, write/unlink/mkdir move the view), and claiming otherwise
         would just move the same false conjunct one leg over. *)
      usys_fd_ok n tf r (um_fdt u) (um_fdt u').

  (* ...and with the path read off the image at argument 0 FOR THE PATH
     ROWS, plus the honest escape when it cannot be read (argstr fails, the
     syscall returns -1, the mirror does not move).  A non-path enriched row
     (dup) does not read the image at all, and its [pl] is irrelevant --
     [ufs_step_at] does not mention it there. *)
  Definition ufs_step (n : Z) (tf : list (mword 64)) (Mi : gmap Z (bv 8))
      (r : mword 64) (u u' : umirror) : Prop :=
    if uenr_path n then
      (r = (mword_of_int (-1) : mword 64) /\ u' = u)
      \/ (exists pl : list (bv 8),
            ustr_read Mi (uint (ufs_arg tf 0)) = Some pl
            /\ ufs_step_at n pl tf r u u')
    else ufs_step_at n [] tf r u u'.

  (* ------------------------------------------------------------------ *)
  (* The forced-arm readers: what a program actually applies.             *)
  (* ------------------------------------------------------------------ *)

  (* an unresolvable path forces the blanket: the success arm is
     unsatisfiable, so the call returned -1 and moved nothing *)
  Lemma ufs_open_at_miss (pl : list (bv 8)) (vom r : mword 64)
      (u u' : umirror) :
    um_resolve u pl = None ->
    ufs_open_at pl vom r u u' ->
    r = (mword_of_int (-1) : mword 64) /\ u' = u.
  Proof.
    intros Hmiss [H | (i & a & fd & Hres & _)]; [exact H |].
    rewrite Hmiss in Hres. discriminate Hres.
  Qed.

  (* a non-(-1) return forces the success facts *)
  Lemma ufs_open_at_hit (pl : list (bv 8)) (vom r : mword 64)
      (u u' : umirror) :
    ufs_open_at pl vom r u u' ->
    r <> (mword_of_int (-1) : mword 64) ->
    exists (i : Z) (a : anode) (fd : nat),
      um_resolve u pl = Some i
      /\ um_av u !! i = Some a
      /\ fd_lowest_closed (um_fdt u) = Some fd
      /\ r = (mword_of_int (Z.of_nat fd) : mword 64)
      /\ ((exists (ma mi : Z) (nl : nat),
             a = MkAnode (ADev ma mi) nl
             /\ 0 <= ma <= NDEV_max
             /\ u' = MkUmirror
                       (<[fd := FdOpen (om_readable vom)
                                  (om_writable vom) (FdDevice ma)]>
                          (um_fdt u))
                       (um_av u) (um_cwd u))
          \/ (exists (bs : list (bv 8)) (nl : nat),
                a = MkAnode (AFile bs) nl
                /\ u' = MkUmirror
                          (<[fd := FdOpen (om_readable vom)
                                     (om_writable vom) (FdInode i)]>
                             (um_fdt u))
                          (if om_trunc vom then delta_trunc i (um_av u)
                           else um_av u)
                          (um_cwd u))
          \/ (exists (e : gmap fname Z) (nl : nat),
                a = MkAnode (ADir e) nl
                /\ om_arg vom = 0
                /\ u' = MkUmirror
                          (<[fd := FdOpen true false (FdInode i)]>
                             (um_fdt u))
                          (um_av u) (um_cwd u))).
  Proof.
    intros [[Hr _] | H] Hne; [exfalso; exact (Hne Hr) | exact H].
  Qed.

  (* a non-(-1) return forces mknod's success facts *)
  Lemma ufs_mknod_at_hit (pl : list (bv 8)) (ma mi : Z) (r : mword 64)
      (u u' : umirror) :
    ufs_mknod_at pl ma mi r u u' ->
    r <> (mword_of_int (-1) : mword 64) ->
    exists (d i : Z) (nm : fname) (e : gmap fname Z) (nl : nat),
      list_basics.last (path_elems pl) = Some nm
      /\ um_resolve_parent u pl = Some d
      /\ um_av u !! d = Some (MkAnode (ADir e) nl)
      /\ e !! nm = None
      /\ um_av u !! i = None
      /\ 0 < i
      /\ r = (mword_of_int 0 : mword 64)
      /\ u' = MkUmirror (um_fdt u)
                (delta_create d nm i (ADev ma mi) (um_av u))
                (um_cwd u).
  Proof.
    intros [[Hr _] | H] Hne; [exfalso; exact (Hne Hr) | exact H].
  Qed.

  (* a non-(-1) return forces dup's success facts *)
  Lemma ufs_dup_at_hit (vfd r : mword 64) (u u' : umirror) :
    ufs_dup_at vfd r u u' ->
    r <> (mword_of_int (-1) : mword 64) ->
    exists (nfd : nat) (st : fdstate),
      0 <= bv_signed vfd
      /\ um_fdt u !! Z.to_nat (bv_signed vfd) = Some st
      /\ st <> FdClosed
      /\ fd_lowest_closed (um_fdt u) = Some nfd
      /\ r = (mword_of_int (Z.of_nat nfd) : mword 64)
      /\ u' = MkUmirror (<[nfd := st]> (um_fdt u)) (um_av u) (um_cwd u).
  Proof.
    intros [[Hr _] | H] Hne; [exfalso; exact (Hne Hr) | exact H].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* 5b.  THE AGREEMENT WITH UPSTREAM'S DESCRIPTOR TABLE.                *)
  (*                                                                     *)
  (* [UsysMemOk.usys_fd_ok] is upstream's pure per-syscall row for the    *)
  (* PROCESS'S DESCRIPTORS -- the same shape, keyed on the same number,   *)
  (* and the thing the kernel dispatcher discharges                      *)
  (* ([SpecSyscall.sysc_fd_ok], [UsysMemOkSpec.sysc_fd_ok_usys]).  The    *)
  (* mirror's fd leg must not be a SECOND opinion about the same code, so *)
  (* below is the receipt that it is not:                                *)
  (*                                                                     *)
  (*   - off the enriched rows the mirror's leg IS their row              *)
  (*     (definitional, since the delegation above);                      *)
  (*   - on the three enriched rows the mirror's leg REFINES their row -- *)
  (*     ours pins the descriptor NUMBER ([fd_lowest_closed], fdalloc's   *)
  (*     own scan) and the row's TYPE, theirs says only that the returned *)
  (*     slot is now open at SOME type and mode (open), or that it is a   *)
  (*     copy of the argument's (dup); mknod touches no descriptor on     *)
  (*     either side.                                                     *)
  (*                                                                     *)
  (* SO THE TWO TABLES CANNOT DISAGREE, and when the enriched loop steps  *)
  (* the real fd view by [usys_fd_ok] it may step the mirror's leg by     *)
  (* [ufs_step] at the same time: [ufs_step_fd_agrees] is exactly the     *)
  (* obligation that would otherwise be owed at every enriched call.      *)
  (*                                                                     *)
  (* THE LENGTH PREMISE is the bundle's own invariant                     *)
  (* ([FdSlots.fd_frags] carries [length sts = NOFILE], read off the      *)
  (* residue by [FdRowMint.mirror_tied_fdlen]).  It is what makes the     *)
  (* returned fd a SMALL number, so that the row's index -- theirs is     *)
  (* [Z.to_nat (uint r)], ours is the [nat] itself -- is the same index.  *)
  (* ------------------------------------------------------------------ *)
  Lemma ufs_step_at_fd_agrees (n : Z) (pl : list (bv 8))
      (tf : list (mword 64)) (r : mword 64) (u u' : umirror) :
    length (um_fdt u) = NOFILE ->
    ufs_step_at n pl tf r u u' ->
    usys_fd_ok n tf r (um_fdt u) (um_fdt u').
  Proof.
    intros Hlen Hst.
    assert (HN : NOFILE = 16%nat) by (vm_compute; reflexivity).
    assert (E63 : (2 ^ 63 = 9223372036854775808)%Z)
      by (vm_compute; reflexivity).
    unfold ufs_step_at in Hst.
    destruct (decide (n = USYS_open)) as [-> | Hno].
    { (* ---- open = 15, against upstream's open row ---- *)
      unfold usys_fd_ok.
      destruct (decide (USYS_open = UsysMemOk.USYS_close)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_open = UsysMemOk.USYS_dup)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_open = UsysMemOk.USYS_open)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      destruct Hst as [[-> ->] | (i & a & fd & Hres & Hrow & Hfd & -> & Harm)].
      - (* the blanket: a failing open installs nothing, which is their
           row's right disjunct *)
        right. reflexivity.
      - (* the success arm: ours pins the descriptor, and theirs MATCHES the
           returned word against it -- [usys_ret_is] is an equation on the
           word, not a decode of it, so exhibiting [fd] closes the goal with
           no bitvector arithmetic at all. *)
        left. exists fd.
        destruct Harm as [(ma & mi & nl & _ & _ & ->)
                         | [(bs & nl & _ & ->) | (e & nl & _ & _ & ->)]].
        + exists (om_readable (ufs_arg tf 1)), (om_writable (ufs_arg tf 1)),
                 (FdDevice ma).
          split; reflexivity.
        + exists (om_readable (ufs_arg tf 1)), (om_writable (ufs_arg tf 1)),
                 (FdInode i).
          split; reflexivity.
        + exists true, false, (FdInode i). split; reflexivity. }
    destruct (decide (n = USYS_mknod)) as [-> | Hnm].
    { (* ---- mknod = 17: NEITHER table moves a descriptor.  Upstream has
           no mknod row at all, and that is right against the C: sys_mknod
           is create() + iunlockput, with no [fdalloc] anywhere in it. ---- *)
      unfold usys_fd_ok.
      destruct (decide (USYS_mknod = UsysMemOk.USYS_close)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_mknod = UsysMemOk.USYS_dup)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_mknod = UsysMemOk.USYS_open)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_mknod = UsysMemOk.USYS_pipe)) as [Hc | _];
        [ discriminate Hc | ].
      destruct Hst as [[_ ->] | (d & i & nm & e & nl & _ & _ & _ & _ & _ &
                                _ & _ & ->)];
        reflexivity. }
    destruct (decide (n = USYS_dup)) as [-> | Hnd].
    { (* ---- dup = 10, against upstream's dup row ---- *)
      unfold usys_fd_ok.
      destruct (decide (USYS_dup = UsysMemOk.USYS_close)) as [Hc | _];
        [ discriminate Hc | ].
      destruct (decide (USYS_dup = UsysMemOk.USYS_dup)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      unfold ufs_arg in Hst.
      destruct Hst as [[-> ->]
                      | (nfd & st & Hnn & Hlk & _ & Hfd & -> & ->)].
      - (* a failing dup installs nothing: the row's right disjunct *)
        right. reflexivity.
      - (* the success arm.  The DESCRIPTOR needs no argument -- the row
           matches the returned word against it, and the post's [r] IS that
           word.  THE ARGUMENT'S INDEX is the one thing to bridge: ours keys
           the row on the full 64-bit [bv_signed] (the mirror's own
           reading), theirs on the C [int] [usys_argfd], and the row's
           lookup into a [NOFILE]-slot table is what puts the argument in
           the range where the two agree. *)
        left. exists nfd. split; [ reflexivity | ].
        pose proof (lookup_lt_Some _ _ _ Hlk) as Hlt.
        rewrite Hlen HN in Hlt.
        apply (proj1 (Nat2Z.inj_lt _ _)) in Hlt.
        rewrite (Z2Nat.id _ Hnn) in Hlt.
        assert (Hsm : (0 <= bv_signed (tf !!! tf_arg_idx 0) < 2 ^ 31)%Z).
        { change (Z.of_nat 16) with 16%Z in Hlt.
          assert (H16 : (16 < 2 ^ 31)%Z) by lia.
          exact (conj Hnn (Z.lt_trans _ _ _ Hlt H16)). }
        unfold usys_argfd. rewrite (um_trunc32_signed_small _ Hsm).
        rewrite (list_lookup_total_correct (um_fdt u)
                   (Z.to_nat (bv_signed (tf !!! tf_arg_idx 0))) st Hlk).
        reflexivity. }
    (* ---- every other number: the arm IS their row ---- *)
    exact Hst.
  Qed.

  (* ...and the same at the contract's own relation.  The path rows' extra
     escape (the string at argument 0 is unreadable, so argstr fails and the
     call returns -1) lands on [usys_fd_ok_neg1], which is why the escape
     costs the agreement nothing. *)
  Lemma ufs_step_fd_agrees (n : Z) (tf : list (mword 64))
      (Mi : gmap Z (bv 8)) (r : mword 64) (u u' : umirror) :
    length (um_fdt u) = NOFILE ->
    ufs_step n tf Mi r u u' ->
    usys_fd_ok n tf r (um_fdt u) (um_fdt u').
  Proof.
    intros Hlen Hst. unfold ufs_step in Hst.
    destruct (uenr_path n) eqn:Hp.
    - destruct Hst as [[-> ->] | (pl & _ & Hst)].
      + exact (usys_fd_ok_neg1 n tf (um_fdt u)).
      + exact (ufs_step_at_fd_agrees n pl tf r u u' Hlen Hst).
    - exact (ufs_step_at_fd_agrees n [] tf r u u' Hlen Hst).
  Qed.

  (* THE BUNDLE'S INVARIANT SURVIVES, which is what makes the stepped
     mirror re-indexable at [fd_frags]: [FdSlots.fd_frags] carries
     [length sts = NOFILE] inside it, so a step that could change the
     length would be a step no residue could accept.  Upstream proves it
     of their table ([usys_fd_ok_length]); by the agreement it holds of
     ours. *)
  Lemma ufs_step_fd_len (n : Z) (tf : list (mword 64))
      (Mi : gmap Z (bv 8)) (r : mword 64) (u u' : umirror) :
    length (um_fdt u) = NOFILE ->
    ufs_step n tf Mi r u u' ->
    length (um_fdt u') = NOFILE.
  Proof.
    intros Hlen Hst.
    rewrite <- Hlen.
    exact (usys_fd_ok_length n tf r (um_fdt u) (um_fdt u')
             (ufs_step_fd_agrees n tf Mi r u u' Hlen Hst)).
  Qed.

End Steps.

(* ===================================================================== *)
(*  6.  THE GHOST: the mirror's two halves                                *)
(* ===================================================================== *)

Section MirrorGhost.
  Context {Σ : gFunctors}.
  Context `{!ghost_varG Σ umirror}.

  (* the user's half; the kernel's rides the enriched loop's residue *)
  Definition mcur (γ : gname) (u : umirror) : iProp Σ :=
    ghost_var γ (1/2)%Qp u.

  Lemma mcur_agree (γ : gname) (u u' : umirror) :
    mcur γ u -∗ mcur γ u' -∗ ⌜u = u'⌝.
  Proof. iApply ghost_var_agree. Qed.

  Lemma mcur_update (γ : gname) (u u' v : umirror) :
    mcur γ u -∗ mcur γ u' ==∗ mcur γ v ∗ mcur γ v.
  Proof.
    iIntros "H1 H2".
    iMod (ghost_var_update_halves v with "H1 H2") as "[$ $]".
    done.
  Qed.

  Lemma mcur_alloc (u : umirror) :
    ⊢ |==> ∃ γ : gname, mcur γ u ∗ mcur γ u.
  Proof.
    iMod (ghost_var_alloc u) as (γ) "H".
    iEval (rewrite -Qp.half_half) in "H".
    iDestruct "H" as "[H1 H2]".
    iModIntro. iExists γ. iFrame "H1 H2".
  Qed.

End MirrorGhost.
