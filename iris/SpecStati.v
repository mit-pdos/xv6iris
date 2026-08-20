(* SpecStati.v -- the public interface of stati.

     void stati(struct inode *ip, struct stat *st) {
       st->dev   = ip->dev;
       st->ino   = ip->inum;
       st->type  = ip->type;
       st->nlink = ip->nlink;
       st->size  = ip->size;
     }

   46 bytes, 18 instructions: a 2-slot frame and five load/store pairs.  No
   branch, no call, no lock -- the whole content of the contract is WHICH
   cells are read and WHICH are written, and both were read off the
   instruction stream rather than off any header.

   ---- struct stat's GEOMETRY, DERIVED FROM THE CODE -------------------

   The five stores, verbatim from CodeStati.v:

       +0x0a  c.sw  a5,  0(a1)     st->dev    -- 4 bytes
       +0x0e  c.sw  a5,  4(a1)     st->ino    -- 4 bytes
       +0x14  sh    a5,  8(a1)     st->type   -- 2 bytes
       +0x1c  sh    a5, 10(a1)     st->nlink  -- 2 bytes
       +0x24  c.sd  a5, 16(a1)     st->size   -- 8 bytes

   so [st_dev]@0, [st_ino]@4, [st_type]@8, [st_nlink]@10, [st_size]@16, and
   BYTES 12..15 ARE NEVER WRITTEN -- they are the alignment hole before the
   8-byte size, and [stat_at] below deliberately does not mention them.  A
   caller that has to copy the whole 24-byte struct out to user space owns
   those four bytes separately; saying anything about them here would be a
   claim stati does not make.

   The five loads, and their extensions:

       +0x08  c.lw  a5,  0(a0)     ip->dev    (int)
       +0x0c  c.lw  a5,  4(a0)     ip->inum   (uint)
       +0x10  lh    a5, 68(a0)     ip->type   (short, SIGN-extended)
       +0x18  lh    a5, 74(a0)     ip->nlink  (short, SIGN-extended)
       +0x20  lwu   a5, 76(a0)     ip->size   (uint, ZERO-extended)

   The AST's boolean is [is_unsigned], so [false] is lh/lw and [true] is
   lhu/lwu -- easy to read backwards.  Only ONE of the five extensions is
   observable in the postcondition: the first four are immediately truncated
   back to their own width by the matching store ([trunc16]/[trunc32] of a
   sign-extension is the identity), but the fifth is a 4-byte load followed
   by an 8-BYTE store, so [st->size] is the ZERO-extension of [ip->size].
   That is the one place a mis-read of the flag would have produced a false
   contract, and it is the one place the flag is stated below.

   ---- WHAT IT OWNS ----------------------------------------------------

   stati is a pure field copy and its footprint is exactly the cells it
   touches.  On the inode side those are the two IDENTITY cells ([i_dev],
   [i_inum] -- at any dfrac, since it only reads them, and the caller's
   halves out of SpecIlock's postcondition are exactly [DfracOwn (1/2)])
   and [InodeInv.inode_meta], the five-cell metadata bundle that
   [IcacheEscrow.ic_loaded] carries.  All three come back untouched.

   THE CALLER HOLDS THE INODE LOCKED, and that is what makes the metadata
   bundle available: it is one conjunct of the checked-out [ic_loaded]
   SpecIlock hands out, at the same existential [dn].  No sleeplock, no
   escrow and no icache invariant appears here, though -- stati never
   consults any of them, and stating it over [ic_loaded] would make the
   contract depend on the whole file-system environment to say something
   about five loads.  A caller destructs [ic_loaded]'s [inode_meta] conjunct,
   calls stati, and puts it back.

   The entry pointer is NOT constrained to be [IcacheRef.ientry k]: stati
   does no arithmetic on slots and has no panic to refute, so it is stated
   at an arbitrary [ip].

   stati does not sleep and does not call, so there is no [cpu_own], no
   [procs_inv], and no parking premise. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import DinodeEnc.
Require Import InodeInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  struct stat's geometry -- READ OFF stati's OWN STORES                 *)
(* ===================================================================== *)

(* Stated in the 12-bit displacement form the sw/sh/sd that reach them
   encode, exactly as [IcacheRef.i_dev] / [InodeInv.i_type] are, so a
   store's effective address unifies with the cell without rewriting. *)
Definition st_dev   (st : mword 64) : mword 64 :=
  add_vec st (sign_extend' 64 (mword_of_int 0 : mword 12)).
Definition st_ino   (st : mword 64) : mword 64 :=
  add_vec st (sign_extend' 64 (mword_of_int 4 : mword 12)).
Definition st_type  (st : mword 64) : mword 64 :=
  add_vec st (sign_extend' 64 (mword_of_int 8 : mword 12)).
Definition st_nlink (st : mword 64) : mword 64 :=
  add_vec st (sign_extend' 64 (mword_of_int 10 : mword 12)).
Definition st_size  (st : mword 64) : mword 64 :=
  add_vec st (sign_extend' 64 (mword_of_int 16 : mword 12)).

Section StatBuf.
  Context `{!riscvGS Σ}.

  (* THE FIVE FIELDS stati WRITES, and only those: bytes 12..15 (the
     alignment hole) are NOT part of this bundle. *)
  Definition stat_at (st : mword 64)
      (dev ino : mword 32) (ty nl : mword 16) (sz : mword 64) : iProp Σ :=
    (* the [struct stat] is the CALLER's frame local (filestat's [st], which
       sys_fstat then copies out), so it is at the post-boot tier. *)
    (st_dev   st ↦₄[KT1] dev ∗
     st_ino   st ↦₄[KT1] ino ∗
     st_type  st ↦₂[KT1] ty  ∗
     st_nlink st ↦₂[KT1] nl  ∗
     st_size  st ↦₈[KT1] sz)%I.

  Global Instance stat_at_timeless st dev ino ty nl sz :
    Timeless (stat_at st dev ino ty nl sz).
  Proof. rewrite /stat_at. apply _. Qed.
End StatBuf.

(* stati's own frame is 16 bytes (2 slots); it calls nothing. *)
Notation K_stati := (2%nat) (only parsing).
Definition wp_stati_sconf_body
    `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (mm : regfile)
    (ip st : mword 64)
    (dev inum : mword 32) (dn : dinode)
    (dev0 ino0 : mword 32) (ty0 nl0 : mword 16) (sz0 : mword 64)
    (K : nat) (dqd dqn : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.stati in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_stati <= K)%nat ->
  (* a0 = ip, a1 = st *)
  mm !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  mm !!! Regidx (mword_of_int 11 : mword 5) = st ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  (* the two identity cells -- READ ONLY, so any dfrac *)
  i_dev  ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  (* the locked inode's metadata bundle ([ic_loaded]'s conjunct) *)
  inode_meta ip dn -∗
  (* the caller's stat buffer, at whatever it happened to hold *)
  stat_at st dev0 ino0 ty0 nl0 sz0 -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    ⌜callee_saved mm mr⌝ -∗
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    i_dev  ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn -∗
    (* THE FIVE FIELDS.  Only [size] carries an extension, and it is the
       ZERO-extension, because [lwu] feeds an 8-byte [sd]. *)
    stat_at st dev inum (di_type dn) (di_nlink dn)
            (zero_extend' 64 (di_size dn : mword 32)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type STATI.
  Parameter wp_stati_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (mm : regfile)
      (ip st : mword 64)
      (dev inum : mword 32) (dn : dinode)
      (dev0 ino0 : mword 32) (ty0 nl0 : mword 16) (sz0 : mword 64)
      (K : nat) (dqd dqn : dfrac) (b : bool) (p : mword 64),
      wp_stati_sconf_body mm ip st dev inum dn dev0 ino0 ty0 nl0 sz0
                          K dqd dqn b p.
End STATI.
