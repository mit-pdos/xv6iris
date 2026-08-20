(* SpecNameiRootBoot.v -- [namei("/")] AT THE BOOT CLIENT'S PREMISES.

   This is [SpecNamei.wp_namei_root_body] with the four INODE-CACHE rows
   removed and nothing else changed: same entry, same budget, same lock
   order, same two path bytes, same [IcacheRef.inode_held] out.  It is the
   ONE assumed contract in the boot cone ([LinkNameiRootBoot.v] holds the
   [Axiom]), and it replaced a much larger one -- [userinit]'s whole body,
   which is now PROVEN against it ([ProofUserinit.v]).

   ---- WHAT IS ASSUMED, EXACTLY ------------------------------------------

   The delta against the PROVEN corner ([ProofNameiRoot.v] /
   [LinkNameiRoot.v], which discharges [SpecNamei.NAMEI_ROOT]) is four
   rows and no more:

     is_itable2 γl cn γfs γi cov logstart nib dev     the itable spinlock
     itable_inv                                       the fifty [ref] words
     ic_escrows cn γfs γi cov logstart                every entry's escrow
     ireg_inv γi γfs inodestart nib                   the inode region

   All four are [namei]'s only because they are [SpecIget]'s: namei's body
   is one [namex] call, namex's absolute arm is one [iget(ROOTDEV, ROOTINO)],
   and iget takes them to acquire [itable.lock], to open the [ref] words
   across its read-modify-writes, to name whichever of the fifty slots its
   scan stops at, and (ghost-only, on the recycle arm) to move the region's
   count half from 0 to 1.  Nothing else in userinit's cone names any of
   them.

   ALL FOUR ARE PERSISTENT, and that is what makes this a clean seam: the
   assumption is not about a resource being spent, it is about the cache
   EXISTING at the moment userinit runs.  It does not yet, because
   [IcacheBoot.icache_boot] -- the one fupd that produces the first three,
   with [IcacheBoot.ireg_alloc] for the fourth -- needs the stocked inode
   pool, which needs the fs BLOCK layer wired into main
   (claude-notes/projects/fs-icache.md, C7 owed (ii)/(c)).

   ---- HOW IT GETS DISCHARGED --------------------------------------------

   By APPLYING the proof that already exists.  When main can hand over the
   four rows, [LinkNameiRootBoot.v]'s [Axiom] is replaced by a functor over
   [LinkNameiRoot.NameiRoot] that simply supplies them -- the boot client
   holds them, this contract does not mention them, and every premise below
   is already one of [SpecNamei.wp_namei_root_body]'s.  No proof about
   namei has to be redone, and userinit's does not change at all.

   ---- THE TWO CONFIG TIES ARE *NOT* PREMISES, AND THAT IS A FINDING -----

   [icfg_dev = ROOTDEV] and [0 < icfg_nib] are the conditions under which
   the corner's [iget(1,1)] is a reference THIS cache can hold
   ([SpecIget]'s [bv_unsigned ROOTINO < 16 * nib]), and they matter: at
   [icfg_nib = 0] the [IcacheRef.inode_held] this contract returns carries
   [bv_unsigned inum < 0] and cannot exist, so the assumption would be
   vacuous rather than merely unproved.

   THEY ARE STILL NOT PREMISES, because a premise has to be dischargeable by
   the caller and these are not -- not at [SystemAdequacy]'s concrete
   functor list, which is where they would have to land.  [icfg] reaches a
   proof as a superclass FIELD of [FileInv.fileG], and at [xv6Σ] that
   instance is [subG_fileΣ], whose body is [solve_inG] closed by **Qed**.
   So [icfg_dev] is stuck behind an opaque constant: [reflexivity] fails
   with "unable to unify ROOTDEV with icfg_dev" even though the instance
   plainly says [mword_of_int 1], and [vm_compute] -- which ignores opacity
   -- does not fail either, it grinds through the [solve_inG] term for
   fifteen minutes and reports nothing.  (Same failure shape as
   durable-notes.md's "vm_compute on a goal containing a section variable
   does not fail, it HANGS", one level over.)

   This is fs-icache.md C7 (c)'s ambient-[icfg] tie seen from below, and it
   is structural: nothing can be proved about the cache's configuration
   until [IcacheRef.icfg_alloc] runs inside the boot fupd.  So the
   configuration is a property of the INSTANCE instead, and
   [SystemAdequacy.adequacy_icfg] is chosen to satisfy it -- see the note
   there.  Anyone re-pointing this [Axiom] at [LinkNameiRoot.NameiRoot]
   supplies the ties from the same place the four icache rows come from.

   ---- WHAT IS *NOT* ASSUMED ---------------------------------------------

   Everything the corner does with the two path bytes, the frame, the
   register discipline and the epilogue is still PROVEN -- [ProofNameiRoot]
   and [ProofNamexRoot] are untouched and stay in the build against
   [SpecNamei.NAMEI_ROOT].  This file does not weaken them; it states the
   same walk at the premises the boot client can actually produce. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import LockRank.
Require Import SpecPanic.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* [SpecNamei.K_namei_root]'s figure -- namei's 4-slot frame over namex's
   corner's 28 -- written as the literal because requiring [SpecNamei] here
   would drag the whole walk's cone (the log, the bio cache, the bitmap)
   into main's, and this file exists precisely to keep it out.  That is
   durable-notes.md's sanctioned trade for a budget numeral: say what the
   number is and where it comes from.  [ProofUserinit]'s own figure is
   [4 + K_namei_root_boot], so a change here still propagates. *)
Notation K_namei_root_boot := (74%nat) (only parsing).

Definition wp_namei_root_boot_body
    `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (dqp : dfrac)
    (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in    (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_namei_root_boot <= K)%nat ->
  (* [+3], not [+1]: namex's iget acquires itable.lock and its LIVE panic
     arm fires inside that critical section, where printk takes two more. *)
  (Z.of_nat n + 3 < 2 ^ 31)%Z ->
  (* iget acquires and releases "itable" internally *)
  locks_below lks "itable" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* iget's "iget: no inodes" arm is live code *)
  panic_env -∗
  (* THE precondition that makes iget's mint safe, on both arms *)
  iref_slot -∗
  (* the path: [pv] holds '/' and [pv+1] holds the terminator.  The fraction
     is a parameter because userinit's "/" is a .rodata string literal, i.e.
     [KernelDataInv.kernel_data]'s [↦ₘ□]. *)
  pa_add pv 0 ↦ₘ{dqp} SLASH -∗
  pa_add pv 1 ↦ₘ{dqp} NUL -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (ipv : mword 64),
      ⌜ callee_saved m mr
        /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ipv ⌝ -∗
      sie_cap_gpr KT1 mr K b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      pa_add pv 0 ↦ₘ{dqp} SLASH -∗
      pa_add pv 1 ↦ₘ{dqp} NUL -∗
      inode_held ipv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEI_ROOT_BOOT.
  Parameter wp_namei_root_boot :
    forall `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string),
      wp_namei_root_boot_body dqp m n K eb p b lks.
End NAMEI_ROOT_BOOT.
