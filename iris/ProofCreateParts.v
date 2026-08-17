(* ProofCreateParts.v -- the pure and frame-level lemmas create's proof
   (fs-sysfile S5b) needs, landed ahead of the walk so that the walk is
   about the WP and nothing else.  Three groups, none of which touches a
   contract:

   (There was a fourth, the SIZE CAP AFTER A dirlink: [cr_size_cap]
   recovered [inode_ok]'s [di_size <= MAXFILE * BSIZE] from dirlink's "the
   append fits" premise, which the contract no longer has.  D₀-a repair 3b
   retired the premise as unsuppliable and [SpecDirlink] now RELAYS writei's
   own size-cap preservation, so the caller reads the cap off the
   postcondition and the arithmetic has no consumer.)

   (1) THE RECORD SURGERY.  create writes inode metadata with three
       halfword stores and nothing else -- [sh s5,70(s3)] / [sh s6,72(s3)]
       / [sh a4,74(s3)] at +0xb4 / +0xb8 / +0xbe (major, minor, nlink := 1),
       [sh zero,74(s3)] at +0x146 (the fail arm's nlink := 0), and
       [lhu/addiw/sh 74(s1)] at +0x134..+0x13a (the parent's nlink++).
       (The child is in s3 on the allocate half -- s3 is the register the
       prologue does NOT save; see SpecCreate.v's header.)
       Every one of them is [cr_setf], and the two facts a re-park of
       [IcacheEscrow.ic_loaded] needs -- [InodeLock.inode_ok] and
       [DirView.dir_ok] -- survive it for the same reason: neither
       predicate mentions major, minor or nlink.

   (2) THE TWO NAME LITERALS.  dirlink wants FOURTEEN bytes of name
       buffer; the "." and ".." arguments the auipc/addi pairs at
       +0xfc/+0x100 and +0x110/+0x114 compute are the rodata
       addresses 0x800075e0 and 0x800075e8, whose fourteen-byte windows
       run into their neighbours ("." 's window contains the ".." two
       bytes further on, and ".." 's contains the head of "unlink").
       [DirentEnc.bname] cuts at the first NUL, so both windows name the
       right string -- and both are PERSISTENT, out of [kernel_data], so
       create pays nothing to produce them and nothing to get them back.

   (3) THE FRAME AND LEDGER CONSTANTS, as arithmetic facts.

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
Require Import KernelText.
Require Import KernelDataInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import SpecIalloc.
Require Import SpecCreate.
(* [nx_sext16_inj] -- the halfword-decision cluster B' hoisted out of
   ProofNamex precisely so create could name it. *)
Require Import ProofNamexParts.
(* the shift-pair and signed-reading facts the +0x6c range test needs *)
Require Import BvShift.
(* [uint_unsigned]: [uint] IS [bv_unsigned] at width 64, which is both of
   the [bltu]'s operands.  Required explicitly because Import is not
   transitive -- RiscvExtras is already in this file's cone via InodeInv,
   so the row costs no build time.  (Note for a future sweep: the tree
   carries SEVEN copies of the width-32 instance under seven names, plus
   this width-64 one, while UserBits.uint_unsigned_n is already the
   general form.) *)
Require Import RiscvExtras.
(* [stk_push] / [stk_pop] / [stk_frm], and the K constants of every callee *)
Require Import KernelRvcDecode.
(* [caddi16sp_imm] / [caddi4spn_imm] *)
Require Import WpMmodeLeafBase.
Require Import StackOwn.
Require Import SpecNameiparent SpecIlock SpecDirlookup SpecIunlockput
        SpecIupdate SpecDirlink.
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

(* create's three stores at +0xa8..+0xb2, as ONE update: the intermediate
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
   back to zero -- the state iupdate flushes at +0x13a *)
Lemma cr_made_clear (ty mj mn : mword 16) :
  cr_setf (create_made ty mj mn) mj mn (bv_0 16)
  = MkDinode ty mj mn (bv_0 16) (bv_0 32) (replicate 13 (bv_0 32)).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  (2) THE TWO NAME LITERALS                                             *)
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
     at +0xfc..+0x100 and +0x110..+0x114 compute.  Both re-checked against
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

  (* ...and the same two windows WEAKENED to KT1, which is the tier
     [SpecDirlink]'s name-buffer premise is stated at (its other caller,
     sys_link, passes a frame local).  The [.]/[..] strings are .rodata, so
     the KT0 window is the real fact and this is [mem_ktier_mono]. *)
  Lemma cr_dot_window_kt1 (a : mword 64) :
    a = mword_of_int cr_dot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ[KT1]□ cr_dot_f j).
  Proof.
    intros ->. iIntros "Hkd".
    iDestruct (cr_dot_window _ eq_refl with "Hkd") as "H".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "H".
    iApply (mem_ktier_mono _ KT1 with "H").
  Qed.

  Lemma cr_dotdot_window_kt1 (a : mword 64) :
    a = mword_of_int cr_dotdot_addr ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 14, (pa_add a j) ↦ₘ[KT1]□ cr_dotdot_f j).
  Proof.
    intros ->. iIntros "Hkd".
    iDestruct (cr_dotdot_window _ eq_refl with "Hkd") as "H".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "H".
    iApply (mem_ktier_mono _ KT1 with "H").
  Qed.

End CreateParts.

(* ===================================================================== *)
(*  (3b) THE FOUND ARM'S TWO TYPE DECISIONS (D0 pre-stage 3)              *)
(*                                                                        *)
(*  create's found arm runs TWO tests and they are NOT the same shape as  *)
(*  namex's, which is why [ProofNamexParts.nx_tdir_eq]/[_ne] do not        *)
(*  transfer even though the guard's [c.beqz] pair does:                   *)
(*                                                                        *)
(*    +0x5a  li  a5,2                                                     *)
(*    +0x5c  bne s4,a5 -> +0x98          type != T_FILE          [SIGNED] *)
(*    +0x60  lhu a5,68(s2)               ip->type              [UNSIGNED] *)
(*    +0x64  addiw a5,a5,-2                                               *)
(*    +0x66  slli a5,a5,48                                                *)
(*    +0x68  srli a5,a5,48                                                *)
(*    +0x6a  li  a4,1                                                     *)
(*    +0x6c  bltu a4,a5 -> +0x98         (ip->type - 2) mod 2^16 > 1      *)
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

(* +0x5c, TAKEN: the requested type is not T_FILE, so the arm is F-BAD *)
Lemma cr_tfile_ne (t : mword 16) : t <> T_FILE ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 2 : mword 64) = true.
Proof.
  intro Hne. unfold neq_vec.
  rewrite (proj2 (eq_vec_false_iff _ _)); [reflexivity |].
  intro Hc. apply Hne. apply nx_sext16_inj. rewrite Hc cr_sext_two.
  reflexivity.
Qed.

(* +0x5c, FALL-THROUGH: the requested type IS T_FILE, which is the [ty =
   T_FILE] conjunct [SpecCreate]'s [made = false] arm claims *)
Lemma cr_tfile_eq (t : mword 16) : t = T_FILE ->
  neq_vec (sign_extend' 64 t : mword 64) (mword_of_int 2 : mword 64) = false.
Proof.
  intros ->. unfold neq_vec. rewrite cr_sext_two.
  rewrite (proj2 (eq_vec_true_iff _ _) eq_refl). reflexivity.
Qed.

(* THE WORD THE THREE ALU LEAVES LEAVE IN a5, at their own output shapes:
   [wp_lhu_s_sconf (kt := KT1) (ktd := KT0)] gives [zero_extend' 64 t], [wp_caddiw_s_sconf] gives
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

(* ...so at either of them the [bltu a4,a5] at +0x6c FALLS THROUGH, which
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

(* +0x6c TAKEN: the found inode is neither a file nor a device -> ARM F-BAD *)
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

(* +0x6c FALL-THROUGH: ARM F-OK, and this is the clause the contract wants *)
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
(*  (3c) THE FRAME, AND THE K SPLIT (D0 step 2's arithmetic layer)        *)
(*                                                                        *)
(*  create's frame is 80 bytes / TEN slots, and every one of the walk's    *)
(*  stack addresses is one of these twelve equations.  They are            *)
(*  hypothesis-free corollaries of [KernelRvcDecode]'s generic             *)
(*  [stk_push] / [stk_pop] / [stk_frm], exactly as the same cluster is     *)
(*  derived inside eleven other proof functors.                           *)
(*                                                                        *)
(*  A DUPLICATION WORTH FIXING, SIZED HERE SO SOMEBODY CAN.                *)
(*  [KernelRvcDecode.v] already carries the 32-, 48- and 64-byte instances *)
(*  ([stk_push_32] ... [stk_pop_64]) beside the generic lemmas -- but NOT  *)
(*  the 80-byte ones, so ELEVEN proof files (balloc, dirlink, filestat,    *)
(*  installtrans, kwait, mappages, procmapstacks, scheduler, uartwrite,    *)
(*  uvmalloc, uvmcopy) each re-derive an identical private copy INSIDE     *)
(*  their functor, where nobody else can see it -- and this file is now a  *)
(*  twelfth.  The lemmas are hypothesis-free and character-identical, so   *)
(*  this is the "near-duplicates that cannot see each other" rule in       *)
(*  durable-notes at eleven-fold: add [stk_push_80] / [stk_pop_80] /       *)
(*  [stk_frm_80_k] to KernelRvcDecode.v and delete twelve copies.  Not     *)
(*  done here because that file's rebuild cone is the whole tree and this  *)
(*  increment has no other reason to pay it.                              *)
(* ===================================================================== *)

Lemma cr_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
  = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_pop (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi s0,sp,80] at +0x10: the frame pointer is the ENTRY sp.
   THE EXTENSION IS [sign_extend'], NOT [zero_extend']: the immediate is a
   positive twelve-bit field so the two agree in VALUE, but they are
   different TERMS and [WpSconfAlu.wp_caddi4spn_s_sconf]'s post is written
   with the signed one, so the zero-extended reading does not rewrite at
   the call site.  (The [c.sdsp] / [c.ldsp] slot addresses below really are
   [zero_extend'] -- that is [WpSconfMem.wp_csdsp_s_sconf]'s own form --
   which is why only this one lemma differs.) *)
Lemma cr_fp (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi a1,s0,-80] at +0x18 / +0x40 (and +0xd2 / +0x126 on the allocate
   half): the sixteen-byte [name[DIRSIZ]] local is the BOTTOM of the frame,
   i.e. the entry sp minus eighty, which is [pa_stk sp0 10] -- the same
   address the two unused frame slots 9 and 10 name.  Base-encoded, so the
   immediate is the raw twelve-bit [4016] and not a [caddi*] field. *)
Lemma cr_name_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4016 : mword 12)) = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* the eight slot addresses the seven prologue saves and s3's late save use:
   ra 72 -> slot 1, s0 64 -> 2, s1 56 -> 3, s2 48 -> 4, s3 40 -> 5,
   s4 32 -> 6, s5 24 -> 7, s6 16 -> 8.  (Slots 9 and 10 are the sixteen-byte
   [name] local at sp+0, which the walk addresses as [s0 - 80], not as a
   slot.) *)
Lemma cr_frm1 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm2 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm3 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm4 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm5 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm6 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm7 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma cr_frm8 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 8.
Proof. apply stk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* THE K SPLIT.  create's own frame is ten slots and its deepest callee is
   nameiparent at 98, so every callee runs at [K - 10] and the seven of them
   fit with the slack the ladder in SpecCreate.v's header records. *)
Lemma cr_kb (K : nat) : (K_create <= K)%nat ->
  (10 <= K)%nat /\ (K_nameiparent <= K - 10)%nat /\ (K_ilock <= K - 10)%nat
  /\ (K_dirlookup <= K - 10)%nat /\ (K_iunlockput <= K - 10)%nat
  /\ (K_ialloc <= K - 10)%nat /\ (K_iupdate <= K - 10)%nat
  /\ (K_dirlink <= K - 10)%nat /\ ((K - 10) + 10)%nat = K.
Proof.
  lia.
Qed.

(* ===================================================================== *)
(*  (3d) THE MKDIR ARM'S [dp->nlink++]: WHY THE NLINK_MAX GUARD IS NOT    *)
(*       ENOUGH BY ITSELF, AND WHAT (L4) ADDS (the twelfth stop, D0-b)    *)
(*                                                                        *)
(*  The arm's +0x134..+0x13a is [lhu a5,74(s1)] / [c.addiw a5,1] /         *)
(*  [sh a5,74(s1)] -- a SIXTEEN-BIT increment, whatever the widths in      *)
(*  between -- and what the ledger wants of it is the Z-level equation     *)
(*  [bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn0) + 1].  Those   *)
(*  agree exactly when the old halfword is not [65535].                    *)
(*                                                                        *)
(*  WHAT THE WALK HOLDS ABOUT THAT HALFWORD IS TWO DISEQUALITIES, AND      *)
(*  NEITHER IS THAT ONE.  The [c.beqz] at +0x2e gives [di_nlink dp <> 0];  *)
(*  the xv6 117c0e7 gate at +0x36 gives [di_nlink dp <> 32767] on the      *)
(*  ty = T_DIR route.  The theorem below is the witness that the two       *)
(*  together do NOT exclude the wrap: at [65535] -- signed [-1] -- both    *)
(*  hold and the increment equation is FALSE.  The gate is a SIGNED test   *)
(*  ([lh] at +0x2a, [>= NLINK_MAX] on a [short] compiled to [== 32767])    *)
(*  and the ledger's premise was an UNSIGNED one; the gap between them is  *)
(*  the range fact that [nlink] is a NONNEGATIVE short.                    *)
(*                                                                        *)
(*  That gap is now closed by [InodeRegion]'s (L4), and the theorem stays  *)
(*  here as the reason (L4) exists -- it is the one statement that says    *)
(*  why the kernel fix alone was not the end of it.  It is also the        *)
(*  standing check on any future attempt to weaken (L4): delete the        *)
(*  clause and this corner comes straight back.                           *)
(* ===================================================================== *)

(* THE REFUTATION.  [65535] passes both of create's guards and wraps. *)
Theorem cr_nlink_guard_leaves_the_wrap :
  let h : mword 16 := mword_of_int 65535 in
  h <> (mword_of_int 0 : mword 16)                       (* the +0x2e guard *)
  /\ h <> (mword_of_int 32767 : mword 16)                (* the +0x36 gate  *)
  /\ bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) <> bv_unsigned h + 1.
Proof.
  cbn zeta. split_and!.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
  - vm_compute. discriminate.
Qed.

(* WHAT CLOSES IT IS (L4), AND IT LIVES WHERE THE RECORD DOES.
   [InodeRegion.ireg_link_ok]'s third conjunct
   [bv_unsigned (di_nlink d) <= 32767], with
   [InodeRegion.ireg_nlink_step] / [ireg_nlink_bump] as its arithmetic --
   the two lemmas this comment used to carry, moved down to the file that
   owns the ledger, because the region is the only place the bound is open
   and a second copy up here would be a near-duplicate that could not see
   its twin.  [ireg_nlink_bump] is a CONJUNCTION on purpose: the first half
   is the Z-level increment [wp_iupdate_link] used to demand of its caller,
   the second is (L4)'s own preservation, and neither holds without the
   other's hypothesis.  What create supplies at the mint is now only what
   its WALK has: the value the [sh] committed, and the guard's branch. *)

(* ===================================================================== *)
(*  (3) THE CONSTANTS                                                     *)
(* ===================================================================== *)

(* 10 own slots + nameiparent's 104.  Moved 108 -> 114 with the bmap chain
   that pushed dirlookup 84 -> 90 (SpecCreate.v's note on [K_create] has the
   whole ladder); 9da28f5's [dp->nlink == 0] guard did NOT move it, because
   the frame is still 80 bytes. *)
Lemma cr_K_value : K_create = 124%nat.
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
