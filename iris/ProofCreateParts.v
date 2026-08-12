(* ProofCreateParts.v -- the pure and frame-level lemmas create's proof
   (fs-sysfile S5b) needs, landed ahead of the walk so that the walk is
   about the WP and nothing else.  Four groups, none of which touches a
   contract:

   (1) THE RECORD SURGERY.  create writes inode metadata with three
       halfword stores and nothing else -- [sh s5,70(s2)] / [sh s6,72(s2)]
       / [sh a5,74(s2)] at +0x90..+0x9a (major, minor, nlink := 1),
       [sh zero,74(s2)] at +0x11c (the fail arm's nlink := 0), and
       [lhu/addiw/sh 74(s1)] at +0x10a..+0x110 (the parent's nlink++).
       Every one of them is [cr_setf], and the two facts a re-park of
       [IcacheEscrow.ic_loaded] needs -- [InodeLock.inode_ok] and
       [DirView.dir_ok] -- survive it for the same reason: neither
       predicate mentions major, minor or nlink.

   (2) THE SIZE CAP AFTER A dirlink.  [SpecDirlink]'s postcondition offers
       [bv_unsigned (di_size dn') < 2 ^ 31] but NOT [inode_ok]'s tighter
       [<= MAXFILE * BSIZE] -- the clause S3i had to add to [SpecWritei]
       as a preservation and which [SpecDirlink] (frozen at S2, before
       S3h) never grew.  The cap is nevertheless RECOVERABLE by the
       caller, and [cr_size_cap] is the recovery: the append lands at a
       slot at most [dir_nrec] and writes at most sixteen bytes, so the
       new size is at most the old plus sixteen, which is exactly
       dirlink's own "the append fits" premise.  (The one clause that is
       NOT recoverable is [InodeInv.inode_sized data'] -- see the S5a
       section's finding 2.)

   (3) THE TWO NAME LITERALS.  dirlink wants FOURTEEN bytes of name
       buffer; the "." and ".." arguments at +0xd6 / +0xea are rodata
       addresses 0x800075c0 and 0x800075c8, whose fourteen-byte windows
       run into their neighbours ("." 's window contains the ".." two
       bytes further on, and ".." 's contains the head of "unlink").
       [DirentEnc.bname] cuts at the first NUL, so both windows name the
       right string -- and both are PERSISTENT, out of [kernel_data], so
       create pays nothing to produce them and nothing to get them back.

   (4) THE FRAME AND LEDGER CONSTANTS, as arithmetic facts.

   Nothing here is create-specific in a way that would justify hiding it,
   but nothing else needs it yet either, so it lives beside the proof. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import KernelText.
Require Import KernelDataInv.
Require Import FsCrash.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import SpecIalloc.
Require Import SpecCreate.
From Kernel Require KernelData.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  (1) THE RECORD SURGERY                                                *)
(* ===================================================================== *)

(* The ONLY shape of dinode update create performs: the three metadata
   halfwords move and the type, size and address array do not.  All five
   of create's inode stores are instances. *)
Definition cr_setf (dn : dinode) (mj mn nl : mword 16) : dinode :=
  MkDinode (di_type dn) mj mn nl (di_size dn) (di_addrs dn).

Lemma cr_setf_type dn mj mn nl : di_type (cr_setf dn mj mn nl) = di_type dn.
Proof. reflexivity. Qed.

Lemma cr_setf_size dn mj mn nl : di_size (cr_setf dn mj mn nl) = di_size dn.
Proof. reflexivity. Qed.

Lemma cr_setf_addrs dn mj mn nl : di_addrs (cr_setf dn mj mn nl) = di_addrs dn.
Proof. reflexivity. Qed.

Lemma cr_setf_major dn mj mn nl : di_major (cr_setf dn mj mn nl) = mj.
Proof. reflexivity. Qed.

Lemma cr_setf_minor dn mj mn nl : di_minor (cr_setf dn mj mn nl) = mn.
Proof. reflexivity. Qed.

Lemma cr_setf_nlink dn mj mn nl : di_nlink (cr_setf dn mj mn nl) = nl.
Proof. reflexivity. Qed.

Lemma cr_setf_wf dn mj mn nl : dinode_wf dn -> dinode_wf (cr_setf dn mj mn nl).
Proof. rewrite /dinode_wf /cr_setf /=. exact id. Qed.

(* THE RE-PARK'S FIRST HALF.  [inode_ok]'s seven conjuncts mention the
   type, the size, the address array, the block map and the data -- and
   NONE of them mentions major, minor or nlink. *)
Lemma cr_setf_inode_ok (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) (mj mn nl : mword 16) :
  inode_ok cov logstart dn bm data ->
  inode_ok cov logstart (cr_setf dn mj mn nl) bm data.
Proof. rewrite /inode_ok /cr_setf /=. exact id. Qed.

(* THE RE-PARK'S SECOND HALF.  [dir_ok] is an implication on the type
   whose conclusion mentions only the size. *)
Lemma cr_setf_dir_ok (nib : nat) (dn : dinode) (data : nat -> list (bv 8))
    (mj mn nl : mword 16) :
  dir_ok nib dn data -> dir_ok nib (cr_setf dn mj mn nl) data.
Proof. rewrite /dir_ok /cr_setf /=. exact id. Qed.

(* ...and the region's arm selector (fs-icache.md 16.5: iupdate keeps ONE
   contract and picks between [dinode_at] and [imark] on this test, so
   both of create's iupdates of a LIVE inode stay on the [dinode_at]
   side, and the fail arm's nlink := 0 does NOT move it -- the arm is
   keyed on the TYPE, not the link count). *)
Lemma cr_setf_type_nz dn mj mn nl :
  bv_unsigned (di_type dn) <> 0 ->
  bv_unsigned (di_type (cr_setf dn mj mn nl)) <> 0.
Proof. rewrite /cr_setf /=. exact id. Qed.

(* create's three stores at +0x90..+0x9a, as ONE update: the intermediate
   states are [cr_setf] too, so the walk never has to name them. *)
Lemma cr_setf_compose dn mj1 mn1 nl1 mj2 mn2 nl2 :
  cr_setf (cr_setf dn mj1 mn1 nl1) mj2 mn2 nl2 = cr_setf dn mj2 mn2 nl2.
Proof. reflexivity. Qed.

(* the fail arm keeps the metadata it had and only zeroes the link count *)
Lemma cr_setf_clear dn mj mn nl :
  cr_setf (cr_setf dn mj mn nl) mj mn (bv_0 16) = cr_setf dn mj mn (bv_0 16).
Proof. reflexivity. Qed.

(* THE ALLOCATE ARM'S RECORD, as [cr_setf] over ialloc's claim: this is
   the identity that ties [SpecCreate.create_made] to the walk, and it is
   the reason [create_made] was worth naming. *)
Lemma cr_made_setf (ty mj mn : mword 16) :
  cr_setf (ialloc_fresh ty) mj mn (mword_of_int 1 : mword 16)
  = create_made ty mj mn.
Proof. reflexivity. Qed.

(* ...and the fail arm's, which is the same record with the link count
   back to zero -- the state iupdate flushes at +0x122 *)
Lemma cr_made_clear (ty mj mn : mword 16) :
  cr_setf (create_made ty mj mn) mj mn (bv_0 16)
  = MkDinode ty mj mn (bv_0 16) (bv_0 32) (replicate 13 (bv_0 32)).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  (2) THE SIZE CAP AFTER A dirlink                                      *)
(* ===================================================================== *)

(* dirlink appends at [16 * k0] with [k0 <= dir_nrec size] and writes at
   most sixteen bytes, so [max(size, 16*k0 + tot) <= size + 16] and
   dirlink's OWN "the append fits" premise is the cap.  The size equation
   is taken in the shape [DirView.dir_ok_dirlink] already takes it, so
   one derivation from [dn' = wi_dinode ...] serves both consumers. *)
Lemma cr_size_cap (dn dn' : dinode) (k0 tot : nat) :
  (k0 <= dir_nrec (bv_unsigned (di_size dn)))%nat ->
  (tot <= 16)%nat ->
  bv_unsigned (di_size dn) + 16 <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_size dn')
    = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
  bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof.
  intros Hk0 Htot Hfit Hsz.
  assert (Hnn : 0 <= bv_unsigned (di_size dn))
    by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
  destruct (dir_nrec_range (bv_unsigned (di_size dn)) Hnn) as [Hlo _].
  rewrite Hsz. lia.
Qed.

(* the same arithmetic in the shape the FRESH child needs it: a directory
   ialloc just claimed has size 0, so its first two links land at 0 and
   16 and the cap is [32 <= MAXFILE * BSIZE], which is a constant. *)
Lemma cr_size_cap_fresh (dn : dinode) :
  bv_unsigned (di_size dn) = 0 ->
  bv_unsigned (di_size dn) + 16 <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof. intros ->. rewrite /MAXFILE /BSIZE. lia. Qed.

(* ...and the second link's, one record further along *)
Lemma cr_size_cap_fresh2 (dn : dinode) :
  bv_unsigned (di_size dn) = 16 ->
  bv_unsigned (di_size dn) + 16 <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof. intros ->. rewrite /MAXFILE /BSIZE. lia. Qed.

(* ===================================================================== *)
(*  (3) THE TWO NAME LITERALS                                             *)
(* ===================================================================== *)

Definition cr_dot_addr : Z := 0x800075c0.
Definition cr_dotdot_addr : Z := 0x800075c8.

(* the fourteen bytes each window actually holds, read off
   kernel-rocq/KernelData.v.  "." 's window runs into ".." (bytes 8 and 9)
   and ".." 's into "unlink" (bytes 8..13); [bname] cuts at the first NUL,
   so neither matters -- but OWNERSHIP is of all fourteen, so the
   functions must be honest. *)
Definition cr_dot_list : list (bv 8) :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0x2e; Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0].

Definition cr_dotdot_list : list (bv 8) :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
   Z_to_bv 8 0x75; Z_to_bv 8 0x6e; Z_to_bv 8 0x6c; Z_to_bv 8 0x69;
   Z_to_bv 8 0x6e; Z_to_bv 8 0x6b].

Definition cr_dot_f (j : nat) : bv 8 := cr_dot_list !!! j.
Definition cr_dotdot_f (j : nat) : bv 8 := cr_dotdot_list !!! j.

(* THE CANONICAL NAMES.  This is what makes [DirentEnc.de_of_name] name
   the right record: dirlink stores [de_of_name inum (bname 14 fn)]. *)
Lemma cr_dot_name : bname 14 cr_dot_f = [Z_to_bv 8 0x2e].
Proof. vm_compute. reflexivity. Qed.

Lemma cr_dotdot_name : bname 14 cr_dotdot_f = [Z_to_bv 8 0x2e; Z_to_bv 8 0x2e].
Proof. vm_compute. reflexivity. Qed.

Section CreateParts.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [KernelDataInv.kernel_data_window] extracts the bytes of a machine
     WORD; a name literal is a byte STRING that is not NUL-terminated
     within its window, so neither that lemma nor [kernel_data_string]
     applies.  This is the same proof at a byte function. *)
  Lemma cr_kd_bytes (A : Z) (W : nat) (f : nat -> bv 8) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    (forall j, (j < W)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some (f j)) ->
    kernel_data -∗
    ([∗ list] j ∈ seq 0 W, (pa_add a j) ↦ₘ□ f j).
  Proof.
    iIntros (-> HA Hbytes) "#Hd". iApply big_sepL_intro. iIntros "!>" (i j Hi).
    apply lookup_seq in Hi. destruct Hi as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat i)%Z (f i) with "Hd").
    apply map_lookup_filter_Some_2; [apply Hbytes; exact Hlt | cbn; lia].
  Qed.

  (* the two instances, at the two rodata addresses the auipc/addi pairs
     at +0xd2..+0xd6 and +0xe6..+0xea compute *)
  Lemma cr_dot_window (a : mword 64) :
    a = mword_of_int cr_dot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ cr_dot_f j).
  Proof.
    intros ->. iApply (cr_kd_bytes cr_dot_addr 14 cr_dot_f _ eq_refl
                         ltac:(unfold text_end, cr_dot_addr; lia)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

  Lemma cr_dotdot_window (a : mword 64) :
    a = mword_of_int cr_dotdot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ□ cr_dotdot_f j).
  Proof.
    intros ->. iApply (cr_kd_bytes cr_dotdot_addr 14 cr_dotdot_f _ eq_refl
                         ltac:(unfold text_end, cr_dotdot_addr; lia)).
    intros j Hj.
    do 14 (destruct j as [|j]; [vm_compute; reflexivity |]).
    exfalso. lia.
  Qed.

End CreateParts.

(* ===================================================================== *)
(*  (4) THE CONSTANTS                                                     *)
(* ===================================================================== *)

Lemma cr_K_value : K_create = 106%nat.
Proof. reflexivity. Qed.

Lemma cr_slots_value : create_slots = 3%nat.
Proof. reflexivity. Qed.

(* the frame's own geometry: 80 bytes, ten slots, the name buffer at the
   bottom ([addi a1,s0,-80] = [s0 - 80] = the entry sp - 80 = sp + 0) *)
Definition cr_frame_bytes : Z := 80.
Definition cr_frame_slots : nat := 10%nat.
Definition cr_name_off : Z := -80.

Lemma cr_frame_slots_bytes :
  Z.of_nat cr_frame_slots * 8 = cr_frame_bytes.
Proof. reflexivity. Qed.

Lemma cr_name_in_frame : cr_frame_bytes + cr_name_off = 0.
Proof. reflexivity. Qed.
