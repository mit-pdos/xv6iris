(* SpecIdup.v -- the public interface of idup(), stated as an ASSUMED
   contract.  There is no [ProofIdup.v]: this is the [Module Type] +
   [Axiom]-in-the-Link shape (claude-notes/design/spec-modules.md, "An
   ASSUMED callee"), the same pattern [SpecIput.v] already uses and for the
   same reason -- [LinkIdup.v] supplies the single instance, so kfork's own
   proof stays a functor over this interface and proving idup later replaces
   exactly two files.

     struct inode *idup(struct inode *ip) {
       acquire(&itable.lock);
       ip->ref++;
       release(&itable.lock);
       return ip;
     }

   @ KernelSyms.idup = 0x800031a6, 26 bytes: a 32-byte ra/s0/s1 frame around
   one acquire/[ip->ref++]/release, no sleep and no callee besides the lock
   pair.

   WHY ASSUMED.  Exactly [SpecIput.v]'s reason: there is no inode model in
   this tree (design/proc-struct.md, "holes to be honest about"), so
   [ProcInv.cwd_ref ip] is [FileInv.inode_ref ip 1], and [inode_ref] is
   LITERALLY [emp] -- a placeholder with [file_ref]'s shape, waiting for the
   itable invariant and its per-inode fractional algebra to exist.  Nothing
   about [ip->ref] or [itable.lock] can be verified against real code until
   then, so the contract states only what a caller (kfork, and later
   sys_chdir's own idup-free path if it ever needs one) actually depends on:
   idup hands back a SECOND reference to the same inode, and returns the
   pointer it was given.

   WHY THE FRACTION IS FREE.  [inode_ref] being [emp] means
   [FileInv.inode_ref_split] holds trivially at ANY split -- in particular
   [inode_ref ip 1 ⊣⊢ inode_ref ip 1 ∗ inode_ref ip 1] via the unit law for
   [∗], since [emp ∗ emp ⊣⊢ emp].  So this contract could be proven with NO
   axiom at all *if* it needed only that algebraic fact -- but it also needs
   the real machine effect (acquiring itable.lock, incrementing a field of a
   [struct inode] this tree does not model the layout of), which is not
   statable yet, so the whole thing is assumed together rather than split
   into a proven ghost lemma plus an assumed machine step.

   THE SIE/[cpu_own] BOOKKEEPING mirrors [SpecFiledup.v]'s (same shape:
   acquire immediately followed by release, no sleep in between) -- the net
   external effect of a fully-nested critical section is to leave [n]/[eb]/
   the SIE index [b] exactly as they came in, which is what a real proof
   would derive from [acquire]'s and [release]'s own contracts and is
   asserted directly here since there is no such proof to derive it from. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import FileInv.
Require Import ProcInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* idup's own frame is 4 slots; acquire/release want 10 below that. *)
Definition K_idup : nat := 14%nat.

Definition wp_idup_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile)
    (ip : mword 64) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.idup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_idup <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  cwd_ref ip -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ip ⌝ -∗
    cwd_ref ip -∗
    cwd_ref ip -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IDUP.
  Parameter wp_idup_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile)
      (ip : mword 64) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_idup_sconf_body Φ m ip n eb p C K b.
End IDUP.
