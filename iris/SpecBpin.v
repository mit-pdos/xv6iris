(* SpecBpin.v -- the public interface of bpin, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void bpin(struct buf *b) {
       acquire(&bcache.lock);
       b->refcnt++;
       release(&bcache.lock);
     }

   Minting a reference with no sleeplock involved: the caller supplies one
   [bslot] (the finite unit that keeps the unchecked increment a faithful
   int -- FdSlots' conservation recipe, see BioInv.v) and receives a
   [bref]: the count fragment plus a real fraction of the buffer's
   dev/blockno cells, split off the bcache resource's retained share.  The
   values come out existentially -- a caller that knows the buffer's key
   (e.g. one holding [bio_locked]'s half-fraction cells) pins them by
   fractional agreement on contact.

   Unlike filedup there is no [ref < 1] panic check and no held-lock
   requirement: bpin at refcnt == 0 legally mints the first reference. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import WpLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import BcacheInv BioInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Definition wp_bpin_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (bn : bio_names) (k : nat)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bpin in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* bpin's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
     below that. *)
  (14 <= K)%nat ->
  (* the tp register holds THIS cpu's id (acquire/release cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the buffer being pinned *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  sie_cap_gpr γ m K -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  bio_ctx bn -∗
  panic_wp -∗
  (* THE premise that makes the unchecked [refcnt++] safe *)
  bslot bn -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    cpu_own γ n eb p C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (∃ (q : Qp) (dev bno : mword 32), bref bn k q dev bno) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BPIN.
  Parameter wp_bpin_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (bn : bio_names) (k : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat),
      wp_bpin_sconf_body γ Φ bn k m n eb p C K.
End BPIN.
