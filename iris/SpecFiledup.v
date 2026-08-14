(* SpecFiledup.v -- the public interface of filedup, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     struct file *filedup(struct file *f) {
       acquire(&ftable.lock);
       if (f->ref < 1) panic("filedup");
       f->ref++;
       release(&ftable.lock);
       return f;
     }

   Duplicating a reference is the ONE operation that must run under
   ftable.lock and bump the physical count, which is why [file_ref] is
   deliberately not duplicable: this spec is the only way to get a second one.
   The new reference's fraction comes out of the caller's -- each side leaves
   with q/2 -- so nothing is conjured and the invariant's leftover share
   [file_rest] is untouched.  See claude-notes/design/file-table.md.

   The [f->ref < 1] panic arm is dead: the caller's [file_ref] puts slot k in
   the authority's domain, so the count is a positive [positive] and the
   sign-extended [blez] test falls through.  That is the whole content of
   "filedup's caller really does hold a reference". *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
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
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import PanicStub.
Require Import IntrDefs.
Require Import CpuOwn.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  The one thing filedup will rest on -- NOT stated as an axiom         *)
(* ------------------------------------------------------------------ *)

(* xv6's filedup increments [f->ref] with no overflow check.  The ftable
   invariant needs every count to stay a faithful [int] (< 2^31) -- that is
   what makes [ref == 0] mean "free" and what the sign-extended branch tests
   read -- but NO unconditional increment can preserve a finite bound, so
   filedup cannot re-establish it.  That is a real (if astronomically
   unreachable) bug in the C, not an artifact of the model, and it is being
   fixed upstream by bounding the count in the code.

   Do NOT paper over it with an axiom.  The missing step is

     forall n, Z.pos n < 2^31 -> Z.pos (Pos.succ n) < 2^31

   which is FALSE at n = 2^31 - 1, so asserting it would make every proof in
   any file that transitively requires this one vacuous.  The contract below
   is therefore stated without it, and filedup is deliberately left unproven
   until the check lands -- at which point the branch it adds becomes a live
   arm of this spec (see "when the check lands" in
   claude-notes/design/file-table.md), so a proof written against today's
   instruction sequence would have to be thrown away regardless. *)

(* ------------------------------------------------------------------ *)

Definition wp_filedup_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
    (k : nat) (q : Qp) (Cf : fcontent)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool)
    (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filedup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* filedup's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
     below that. *)
  (14 <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the file being duplicated *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  locks_below lks (lock_rank "ftable") ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  panic_wp_any -∗
  (* THE precondition that makes [f->ref++] safe: the duplicate needs a
     descriptor to live in, and there are only FDSLOTS of those. *)
  fd_slot -∗
  file_ref γf k q Cf -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr
      /\ mr !!! Regidx (mword_of_int 10 : mword 5) = fnode k ⌝ -∗
    file_ref γf k (q/2)%Qp Cf -∗
    file_ref γf k (q/2)%Qp Cf -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEDUP.
  Parameter wp_filedup_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool)
      (lks : gset nat),
      wp_filedup_sconf_body γl γf k q Cf m n eb p C K b lks.
End FILEDUP.
