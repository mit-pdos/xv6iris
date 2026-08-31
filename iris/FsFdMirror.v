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

(* the table a fresh process is born with (allocproc; FdSlots.fdst_map0
   is the same fact at the ghost) *)
Definition fdt0 : list fdstate := replicate NOFILE FdClosed.

Lemma fdt0_length : length fdt0 = NOFILE.
Proof. reflexivity. Qed.

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

(* the two pilot rows' syscall numbers (kernel/syscall.h) *)
Definition USYS_open  : Z := 15.
Definition USYS_mknod : Z := 17.

(* which numbers take the enriched arm -- the pilot's two, and a FIXED
   decidable set so the trap contract's case analysis stays pure *)
Definition uenr_dom (n : Z) : bool :=
  bool_decide (n = USYS_open) || bool_decide (n = USYS_mknod).

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
    else u' = u.

  (* ...and with the path read off the image at argument 0, plus the
     honest escape when it cannot be read (argstr fails, the syscall
     returns -1, the mirror does not move) *)
  Definition ufs_step (n : Z) (tf : list (mword 64)) (Mi : gmap Z (bv 8))
      (r : mword 64) (u u' : umirror) : Prop :=
    (r = (mword_of_int (-1) : mword 64) /\ u' = u)
    \/ (exists pl : list (bv 8),
          ustr_read Mi (uint (ufs_arg tf 0)) = Some pl
          /\ ufs_step_at n pl tf r u u').

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
