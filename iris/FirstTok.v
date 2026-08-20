(*  FirstTok.v -- proc.c's [static int first], AS A RESOURCE A PROCESS
    CARRIES.

    forkret's first act after [release(&p->lock)] is

        if (__atomic_load_n(&first, __ATOMIC_ACQUIRE)) { fsinit(); ...; }

    and the branch is decided by WHICH ARM OF THIS DISJUNCTION the running
    process holds.  That is the whole design: no invariant, no mask, no
    atomicity argument.  The resource decides the branch, and the two arms
    are mutually exclusive as resources, so the kernel's own "exactly one
    process ever takes it" is a theorem about ownership rather than a claim
    about scheduling.

      - [first_addr ↦₄ 1] is EXCLUSIVE.  At most one process can hold it,
        and holding it is the right to run the boot arm: fsinit, the store
        of 0, kexec("/init").  The boot chain deposits it into the FIRST
        process's block ([SpecUserinit]) and nothing else can ever have it.

      - [first_addr ↦₄□ 0 ∗ fs_ready] is PERSISTENT, hence free for every
        process forever.  A process holding it reads 0, so the [c.beqz] at
        forkret+0x24 is TAKEN and the boot arm is dead -- and it already
        has the file system it would otherwise have had to build.

    The two cannot coexist: [DfracOwn 1] and [DfracDiscarded] at one
    address are incompatible, so the moment the boot arm persists its
    store, no second holder of the exclusive arm can exist.  That is the
    one-shot, without a one-shot ghost.

    WHY [fs_ready] RIDES IN THE SECOND ARM.  forkret's tail hands the trap
    loop a residue, and the loop's bundle wants the fs environment.  In the
    boot arm forkret BUILDS it (fsinit's post, sealed by
    [FsReady.fs_ready_establish]); in the steady arm it must already have
    it, and the only honest source is the process's own block.  Carrying it
    here is what lets forkret's contract drop the [first] premise
    altogether instead of trading it for an fs premise. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskInv.
Require Import LogInv.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import FsCfg.
Require Import FsReady.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* the static [int first], at its identity-mapped kernel address.
   [SpecForkret] names the same cell; this is the definition it uses. *)
Definition first_addr : mword 64 := mword_of_int KernelSyms.first_1.

Section FirstTok.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  Context `{!xv6G Σ} `{ICFG : icfg} `{FSC : fscfg}.

  Definition first_tok : iProp Σ :=
    ((first_addr ↦₄ (mword_of_int 1 : mword 32))
     ∨ (first_addr ↦₄□ (mword_of_int 0 : mword 32) ∗ fs_ready))%I.

  (* the steady-state arm is persistent, so a process that has booted can
     hand a copy to every process it creates -- which is how kfork pays the
     child's block without the parent losing anything. *)
  Lemma first_tok_done : first_addr ↦₄□ (mword_of_int 0 : mword 32) -∗ fs_ready -∗ first_tok.
  Proof. iIntros "H #F". iRight. iFrame "H F". Qed.

  Lemma first_tok_boot : first_addr ↦₄ (mword_of_int 1 : mword 32) -∗ first_tok.
  Proof. iIntros "H". by iLeft. Qed.

  (* THE TWO ARMS ARE MUTUALLY EXCLUSIVE, and this is the lemma that says
     the boot arm runs at most once.  Not used by forkret's walk (which
     cases on its OWN token) -- it is here because it is the property the
     design rests on, and a reader should be able to check it. *)
  Lemma first_tok_boot_excl :
    first_addr ↦₄ (mword_of_int 1 : mword 32) -∗
    first_addr ↦₄□ (mword_of_int 0 : mword 32) -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word4_pointsto_agree with "H1 H2") as %Hv.
    exfalso. revert Hv. vm_compute. discriminate.
  Qed.

End FirstTok.
