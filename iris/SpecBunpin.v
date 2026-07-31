(* SpecBunpin.v -- the public interface of bunpin, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void bunpin(struct buf *b) {
       acquire(&bcache.lock);
       b->refcnt--;
       release(&bcache.lock);
     }

   bpin's inverse: the reference goes back (its count fragment burned, its
   dev/blockno cell fraction rejoining the bcache resource's retained share)
   and the caller's [bslot] comes back out.  No LRU motion: unlike brelse, a
   bunpin that drops the count to zero leaves the buffer where it sits in
   the list.  The decrement arithmetic (the departing fraction q is at most
   the outstanding total, whole when the count is 1) is the Arc algebra's
   own law -- no premise beyond the reference itself. *)
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
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import WpLock SleepLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import BufOwn BcacheInv BioInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Definition wp_bunpin_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (bn : bio_names) (k : nat)
    (q : Qp) (dev bno : mword 32)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bunpin in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* bunpin's own frame is 4 slots; acquire/release want 10 below that. *)
  (14 <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the buffer being unpinned *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  bio_ctx bn -∗
  panic_wp_any -∗
  (* the reference being surrendered *)
  bref bn k q dev bno -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    bslot bn -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BUNPIN.
  Parameter wp_bunpin_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (bn : bio_names) (k : nat)
      (q : Qp) (dev bno : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool),
      wp_bunpin_sconf_body Φ bn k q dev bno m n eb p C K b.
End BUNPIN.
