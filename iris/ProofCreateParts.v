(* ProofCreateParts.v -- the pure and frame-level lemmas create's proof
   (fs-sysfile S5b) needs, landed ahead of the walk so that the walk is
   about the WP and nothing else.  Four groups, none of which touches a
   contract:

   (1) THE RECORD SURGERY.  create writes inode metadata with three
       halfword stores and nothing else -- [sh s5,70(s3)] / [sh s6,72(s3)]
       / [sh a4,74(s3)] at +0x9c / +0xa0 / +0xa6 (major, minor, nlink := 1),
       [sh zero,74(s3)] at +0x12e (the fail arm's nlink := 0), and
       [lhu/addiw/sh 74(s1)] at +0x11c..+0x122 (the parent's nlink++).
       (The child is in s3 on the allocate half -- s3 is the register the
       prologue does NOT save; see SpecCreate.v's header.)
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
       buffer; the "." and ".." arguments the auipc/addi pairs at
       +0xe4/+0xe8 and +0xf8/+0xfc compute are the rodata
       addresses 0x800075e0 and 0x800075e8, whose fourteen-byte windows
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
(* [nx_sext16_inj] -- the halfword-decision cluster B' hoisted out of
   ProofNamex precisely so create could name it. *)
Require Import ProofNamexParts.
(* the shift-pair and signed-reading facts the +0x5e range test needs *)
Require Import BvShift.
(* [uint_unsigned]: [uint] IS [bv_unsigned] at width 64, which is both of
   the [bltu]'s operands.  Required explicitly because Import is not
   transitive -- RiscvExtras is already in this file's cone via InodeInv,
   so the row costs no build time.  (Note for a future sweep: the tree
   carries SEVEN copies of the width-32 instance under seven names, plus
   this width-64 one, while UserBits.uint_unsigned_n is already the
   general form.) *)
Require Import RiscvExtras.
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

Definition cr_dot_addr : Z := 0x800075e0.
Definition cr_dotdot_addr : Z := 0x800075e8.

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
     at +0xe4..+0xe8 and +0xf8..+0xfc compute.  Both re-checked against
     CodeCreate.v after the bump: create + 0xe4 + 0x3000 - 1622
     = 0x800075e0 and create + 0xf8 + 0x3000 - 1634 = 0x800075e8.  THE TWO
     ADDRESSES DID NOT MOVE -- create itself shifted +14 and the two addi
     immediates shifted -14 (2488 -> 2474, 2476 -> 2462), which cancels
     exactly; .rodata stayed put. *)
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
(*  (3b) THE FOUND ARM'S TWO TYPE DECISIONS (D0 pre-stage 3)              *)
(*                                                                        *)
(*  create's found arm runs TWO tests and they are NOT the same shape as  *)
(*  namex's, which is why [ProofNamexParts.nx_tdir_eq]/[_ne] do not        *)
(*  transfer even though the guard's [c.beqz] pair does:                   *)
(*                                                                        *)
(*    +0x4c  li  a5,2                                                     *)
(*    +0x4e  bne s4,a5 -> +0x80          type != T_FILE          [SIGNED] *)
(*    +0x52  lhu a5,68(s2)               ip->type              [UNSIGNED] *)
(*    +0x56  addiw a5,a5,-2                                               *)
(*    +0x58  slli a5,a5,48                                                *)
(*    +0x5a  srli a5,a5,48                                                *)
(*    +0x5c  li  a4,1                                                     *)
(*    +0x5e  bltu a4,a5 -> +0x80         (ip->type - 2) mod 2^16 > 1      *)
(*                                                                        *)
(*  The FIRST is namex's shape at a different literal: the argument [ty]   *)
(*  reached create in a1 SIGN-extended by the ABI, so the [bne] compares   *)
(*  whole 64-bit registers and [sign_extend' 64]'s injectivity on          *)
(*  [mword 16] decides the halfword exactly.  Those two lemmas are below   *)
(*  and they are three-line corollaries of [nx_sext16_inj], exactly as     *)
(*  [nx_tdir_eq]/[_ne] are.                                                *)
(*                                                                        *)
(*  The SECOND is a ZERO-EXTENDED RANGE TEST and has no analogue anywhere  *)
(*  in the tree: [lhu] zero-extends, the [addiw] wraps at 32 bits, and the *)
(*  [slli 48; srli 48] pair truncates back to sixteen, so the compared     *)
(*  word is [(ip->type - 2) mod 2^16] and the [bltu a4,a5] falls through   *)
(*  exactly on [ip->type in {2,3}].  [cr_trange] NAMES that word -- it is  *)
(*  what the three ALU leaves leave in a5, spelled at their own output     *)
(*  shapes -- so the walk never has to write the term out, and the two     *)
(*  values the contract's F-OK arm claims are computed below.             *)
(* ===================================================================== *)

Lemma cr_sext_two :
  (sign_extend' 64 T_FILE : mword 64) = (mword_of_int 2 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* +0x4e, TAKEN: the requested type is not T_FILE, so the arm is F-BAD *)
Lemma cr_tfile_ne (t : mword 16) : t <> T_FILE ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 2 : mword 64) = true.
Proof.
  intro Hne. unfold neq_vec.
  rewrite (proj2 (eq_vec_false_iff _ _)); [reflexivity |].
  intro Hc. apply Hne. apply nx_sext16_inj. rewrite Hc cr_sext_two.
  reflexivity.
Qed.

(* +0x4e, FALL-THROUGH: the requested type IS T_FILE, which is the [ty =
   T_FILE] conjunct [SpecCreate]'s [made = false] arm claims *)
Lemma cr_tfile_eq (t : mword 16) : t = T_FILE ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 2 : mword 64) = false.
Proof.
  intros ->. unfold neq_vec. rewrite cr_sext_two.
  rewrite (proj2 (eq_vec_true_iff _ _) eq_refl). reflexivity.
Qed.

(* THE WORD THE THREE ALU LEAVES LEAVE IN a5, at their own output shapes:
   [wp_lhu_s_sconf] gives [zero_extend' 64 t], [wp_caddiw_s_sconf] gives
   [sign_extend' 64 (subrange_vec_dec (add_vec _ (sign_extend' 64
   (sign_extend' 12 imm))) 31 0)], and [wp_cslli_s_sconf] /
   [wp_csrli_s_sconf] give [shift_bits_left] / [shift_bits_right] at
   [subrange_vec_dec shamt (log2_xlen - 1) 0].  Naming it is what keeps the
   [bltu] side condition one lemma application wide. *)
Definition cr_trange (t : mword 16) : mword 64 :=
  shift_bits_right
    (shift_bits_left
       (sign_extend' 64
          (subrange_vec_dec
             (add_vec (zero_extend' 64 t : mword 64)
                      (sign_extend' 64
                         (sign_extend' 12 (mword_of_int 62 : mword 6))))
             31 0))
       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0).

(* the two values the F-OK arm is about, computed *)
Lemma cr_trange_file : cr_trange T_FILE = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_trange_device : cr_trange T_DEVICE = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ...so at either of them the [bltu a4,a5] at +0x5e FALLS THROUGH, which
   is ARM F-OK. *)
Lemma cr_trange_file_fall :
  zopz0zI_u (mword_of_int 1 : mword 64) (cr_trange T_FILE) = false.
Proof. rewrite cr_trange_file. vm_compute. reflexivity. Qed.

Lemma cr_trange_device_fall :
  zopz0zI_u (mword_of_int 1 : mword 64) (cr_trange T_DEVICE) = false.
Proof. rewrite cr_trange_device. vm_compute. reflexivity. Qed.

(* ---- AND THE CONVERSE, WHICH IS THE RANGE TEST'S REAL CONTENT --------
   ARM F-OK's contract clause is [di_type dn = T_FILE \/ di_type dn =
   T_DEVICE], and nothing but this direction supplies it: falling through
   the [bltu] must IMPLY the type is one of the two.  The chain is four
   steps and every one of them is conversion or a named lemma.

   [cr_inner] is the 32-bit intermediate the [addiw] leaves.  Naming it is
   what makes [cr_trange_bv] a [reflexivity]: the whole Sail cast layer --
   [with_word], [get_word], [to_word], [autocast], [MachineWord.cast_idx]
   -- is the IDENTITY at concrete widths, and stdpp's [bv_*_unsigned]
   lemmas on this path are all [Proof. done. Qed.], so the wrapper stack
   collapses by conversion alone with no [change] gymnastics. *)
Definition cr_inner (t : mword 16) : bv 32 :=
  bv_extract 0 32 (bv_add (bv_zero_extend 64 t)
      (bv_sign_extend 64 (bv_sign_extend 12 (mword_of_int 62 : mword 6)))).

Lemma cr_trange_bv (t : mword 16) :
  bv_unsigned (cr_trange t)
  = Z.shiftr (bv_wrap 64
      (Z.shiftl (bv_unsigned (bv_sign_extend 64 (cr_inner t))) 48)) 48.
Proof. reflexivity. Qed.

(* the [lhu] zero-extends and the [addiw] wraps at 32, so the intermediate
   is [(type - 2) mod 2^32]; the [-2] arrives as the 64-bit constant
   [2^64 - 2], which is [sign_extend' 64 (sign_extend' 12 62)]. *)
Lemma cr_inner_unsigned (t : mword 16) :
  bv_unsigned (cr_inner t) = (bv_unsigned t - 2) `mod` 4294967296.
Proof.
  unfold cr_inner.
  (* ssreflect [rewrite] takes SPACES, not commas *)
  rewrite bv_extract_unsigned bv_add_unsigned.
  (* [lia] cannot see through the [Z.to_N 16] the width elaborates to *)
  rewrite (bv_zero_extend_unsigned 64 t ltac:(vm_compute; discriminate)).
  assert (Hc : bv_unsigned (bv_sign_extend 64
                  (bv_sign_extend 12 (mword_of_int 62 : mword 6)) : bv 64)
               = 18446744073709551614)
    by (vm_compute; reflexivity).
  rewrite Hc.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296.
  rewrite mod_2_64_32 sub2_wrap64_32. reflexivity.
Qed.

(* THE BRIDGE: the [slli 48; srli 48] pair keeps the low sixteen bits
   ([BvShift.bv_wrap_shift_pair]), and the sign extension in the middle
   does not disturb them ([BvShift.swrap_low_32_16]). *)
Lemma cr_trange_unsigned (t : mword 16) :
  bv_unsigned (cr_trange t) = (bv_unsigned t - 2) `mod` 65536.
Proof.
  rewrite cr_trange_bv bv_wrap_shift_pair_16 bv_sign_extend_unsigned.
  (* [bv_signed] is the HEAD -- unfolding [bv_swrap] alone does nothing --
     and [bv_modulus] must come LAST, because [bv_half_modulus]
     reintroduces it. *)
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296.
  rewrite mod_2_64_16 swrap_low_32_16 cr_inner_unsigned mod_2_32_16.
  reflexivity.
Qed.

(* the pure arithmetic, over [Z] with no bitvector in sight so that [lia]
   works normally (the tree's standing rule for bv-heavy contexts) *)
Lemma cr_range_Z (T : Z) : 0 <= T < 65536 -> T <> 2 -> T <> 3 ->
  1 < (T - 2) `mod` 65536.
Proof.
  intros Hr H2 H3.
  destruct (Z.le_gt_cases 2 T) as [Hge|Hlt].
  - assert (Hs : (T - 2) `mod` 65536 = T - 2).
    { apply Z.mod_small. lia. }
    lia.
  - assert (Heq : (T - 2) `mod` 65536 = T - 2 + 1 * 65536).
    { assert (Ha : (T - 2 + 1 * 65536) `mod` 65536 = (T - 2) `mod` 65536).
      { apply Z.mod_add. lia. }
      assert (Hb : (T - 2 + 1 * 65536) `mod` 65536 = T - 2 + 1 * 65536).
      { apply Z.mod_small. lia. }
      lia. }
    lia.
Qed.

(* +0x5e TAKEN: the found inode is neither a file nor a device -> ARM F-BAD *)
Lemma cr_trange_out (t : mword 16) :
  t <> T_FILE -> t <> T_DEVICE ->
  zopz0zI_u (mword_of_int 1 : mword 64) (cr_trange t) = true.
Proof.
  intros H2 H3. unfold zopz0zI_u.
  rewrite !uint_unsigned cr_trange_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 64) = 1)
    by (vm_compute; reflexivity).
  rewrite H1. apply Z.ltb_lt.
  assert (Hne2 : bv_unsigned t <> 2)
    by (intro Hc; apply H2, bv_eq; rewrite Hc; reflexivity).
  assert (Hne3 : bv_unsigned t <> 3)
    by (intro Hc; apply H3, bv_eq; rewrite Hc; reflexivity).
  apply cr_range_Z; [| exact Hne2 | exact Hne3].
  destruct (bv_unsigned_in_range _ t) as [Hlo Hhi].
  split; [exact Hlo |]. change (bv_modulus (Z.to_N 16)) with 65536 in Hhi.
  exact Hhi.
Qed.

(* +0x5e FALL-THROUGH: ARM F-OK, and this is the clause the contract wants *)
Lemma cr_trange_in (t : mword 16) :
  zopz0zI_u (mword_of_int 1 : mword 64) (cr_trange t) = false ->
  t = T_FILE \/ t = T_DEVICE.
Proof.
  intro Hf.
  destruct (Z.eq_dec (bv_unsigned t) 2) as [He|H2].
  { left. apply bv_eq. rewrite He. reflexivity. }
  destruct (Z.eq_dec (bv_unsigned t) 3) as [He|H3].
  { right. apply bv_eq. rewrite He. reflexivity. }
  assert (Hn2 : t <> T_FILE) by (intros ->; apply H2; reflexivity).
  assert (Hn3 : t <> T_DEVICE) by (intros ->; apply H3; reflexivity).
  rewrite (cr_trange_out t Hn2 Hn3) in Hf. discriminate.
Qed.

(* ===================================================================== *)
(*  (4) THE CONSTANTS                                                     *)
(* ===================================================================== *)

(* 10 own slots + nameiparent's 98.  Moved 106 -> 108 with the copyout chain
   that pushed dirlookup 82 -> 84 (SpecCreate.v's note on [K_create] has the
   whole ladder); 9da28f5's [dp->nlink == 0] guard did NOT move it, because
   the frame is still 80 bytes. *)
Lemma cr_K_value : K_create = 108%nat.
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
