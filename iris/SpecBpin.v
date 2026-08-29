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
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import LockRank.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

Definition wp_bpin_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (bn : bio_names) (V : bio_view Σ) (k : nat)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bpin in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* bpin's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
     below that. *)
  (14 <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the buffer being pinned *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  bio_ctx bn V -∗
  (* THE premise that makes the unchecked [refcnt++] safe *)
  bslot -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (∃ (q : Qp) (dev bno : mword 32), bref bn k q dev bno) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BPIN.
  Parameter wp_bpin_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (bn : bio_names) (V : bio_view Σ) (k : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string),
      wp_bpin_sconf_body bn V k m n eb p K b lks.
End BPIN.
