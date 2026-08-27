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
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import LockRank.
Require Import IntrDefs.
Require Import CpuOwn.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import IrefSlots.  (* [iref_frac] rides [file_core] -- FileInvDefs *)
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  Why [f->ref++] is safe -- a conserved supply, NOT an axiom           *)
(* ------------------------------------------------------------------ *)

(* xv6's filedup increments [f->ref] with no overflow check, and the ftable
   invariant needs every count to stay a faithful [int] (< 2^31) -- that is
   what makes [ref == 0] mean "free" and what the sign-extended branch tests
   read.  No unconditional increment can preserve a finite bound on its own,
   and the missing step

     forall n, Z.pos n < 2^31 -> Z.pos (Pos.succ n) < 2^31

   is FALSE at n = 2^31 - 1: asserting it as an axiom would make every proof
   in any file that transitively requires this one vacuous.  Do NOT.

   The bound is a WHOLE-KERNEL fact instead: every holder of a file reference
   is some process's descriptor, and there are at most NPROC * (NOFILE + FDSPARE)
   = FDSLOTS of those.  That fact is carried as a resource (FdSlots.v): the
   ftable holds one [fd_slot] per outstanding reference, the supply is fixed
   at FDSLOTS, and the contract below takes the caller's [fd_slot] -- the
   descriptor the duplicate will live in.  Adding it to the ones the table
   already holds gives [Pos.to_nat n + 1 <= FDSLOTS] by auth validity alone
   ([fd_slots_no_overflow]), with no arithmetic and no local update, and
   FDSLOTS < 2^31 does the rest.  ProofFiledup.v is the proof; upstream's C
   is unchanged (no bound check was added, none is needed). *)

(* ------------------------------------------------------------------ *)

Definition wp_filedup_sconf_body `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
    (k : nat) (q : Qp) (Cf : fcontent) (st : fdstate)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool)
    (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.filedup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* filedup's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
     below that. *)
  (14 <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the file being duplicated *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  locks_below lks "ftable" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_ftable γl γf -∗
  (* THE precondition that makes [f->ref++] safe: the duplicate needs a
     descriptor to live in, and there are only FDSLOTS of those. *)
  fd_slot -∗
  file_ref γf k q Cf st -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr
      /\ mr !!! Regidx (mword_of_int 10 : mword 5) = fnode k ⌝ -∗
    file_ref γf k (q/2)%Qp Cf st -∗
    file_ref γf k (q/2)%Qp Cf st -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FILEDUP.
  Parameter wp_filedup_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId} (γl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent) (st : fdstate)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool)
      (lks : gset string),
      wp_filedup_sconf_body γl γf k q Cf st m n eb p K b lks.
End FILEDUP.
