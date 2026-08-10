(* SpecIdup.v -- the public interface of idup(), stated over the REAL inode
   cache and no longer assumed.

     struct inode *idup(struct inode *ip) {
       acquire(&itable.lock);
       ip->ref++;
       release(&itable.lock);
       return ip;
     }

   @ KernelSyms.idup = 0x800031a6, 54 bytes (ilock begins at 0x800031dc):
   a 32-byte ra/s0/s1 frame around one acquire / [ip->ref++] / release.  No
   branch, no sleep, and no callee besides the lock pair -- idup is the
   SMALLEST function that exercises the whole icache design end to end,
   which is why it is proven before iget and iput.

   ---- WHAT CHANGED, AND WHY IT BROKE NOTHING --------------------------

   This contract used to be an [Axiom] in [LinkIdup.v], stated over
   [ProcInv.cwd_ref] -- i.e. over [FileInv.inode_ref], which is literally
   [emp].  The header then explained that nothing about [ip->ref] or
   [itable.lock] was statable against real code because no inode model
   existed.  [IcacheInv.v] is that model, so the excuse is gone.

   Restating it was free because idup HAS NO CALLERS: nothing in the tree
   applies [wp_idup_sconf] (iput, by contrast, has two).  The old
   postcondition could not survive the change in any case -- it returned
   [cwd_ref ip ∗ cwd_ref ip], i.e. fraction 1 twice, which is satisfiable
   only while the predicate is [emp].  A real duplicate splits the caller's
   share, and that is what the two [q/2]s below are.

   ---- THE TWO PREMISES A READER SHOULD LOOK AT TWICE -------------------

   [is_itable2] is the itable spinlock over the v2 resource (design §13.2/
   §13.3: the pure slot->inum map [ci] and the uncached POOL ride inside it
   alongside the authority half).  idup moves only the [ref] word and [M],
   so both of those ride through its critical section untouched -- the flip
   from [is_itable] is a re-framing, not a re-proof (§13.4).

   [itable_inv γ] is where the [ref] WORDS live -- not in [itable.lock]'s
   resource.  idup writes one while holding the lock, so it opens the
   invariant and joins the two halves of the authority; that the halves meet
   only under the lock is exactly what makes [lw; addiw; sw] atomic in the
   proof.  See [IcacheInv.v]'s header for why the words cannot live in the
   lock (ilock and iunlock read them holding nothing).

   ---- IT TAKES A SHARE AND HANDS BACK A REFERENCE ----------------------

   [ip->ref++] does not need a reference to start from.  It needs a claim
   that the entry cannot be freed underneath it, and a count-0 SHARE is
   already that: a positive share blocks [IcacheInv.iref_close_last_step]'s
   [q = qt], so the entry stays.  What the increment then does is turn that
   claim into a reference of its own, at the SAME fraction -- which is
   exactly the [n -> n+1] the [sw] performs and nothing else.

   THE OLD SHAPE WAS AN ARTEFACT OF THE ALGEBRA.  This contract used to take
   a REFERENCE and hand back TWO HALF-references, because a share could not
   be spoken of at all: the count component was [positiveR], which has no
   zero, so halving was the only way to make two things out of one.  It cost
   the caller a factor of two on every call -- kfork's parent halved its cwd
   fraction on every [fork].  It does not any more: the parent sheds a share
   ([IcacheInv.inode_ref_split_shr]), hands it over, and gets a reference
   back for the child.

   [iref_slot] is what makes the increment SAFE, and it is not bookkeeping.
   [ip->ref++] is unconditional, so it cannot re-establish "the count is
   still an int" on its own -- the missing step is false at 2^31 - 1 and no
   axiom may assert it ([IrefSlots.v]'s header, and [SpecFiledup.v]'s before
   it).  A unit of the FIXED supply is evidence that the system has an
   actual place to keep the new reference, and it is the caller's job to
   bring one, exactly as filedup's caller brings an [fd_slot].

   The SIE/[cpu_own] bookkeeping is [SpecFiledup.v]'s, and for the same
   reason: a fully-nested acquire/release leaves [n], [eb] and the SIE
   index [b] as they came in.  Unlike filedup's, this is now DERIVED from
   the two lock contracts rather than asserted.                            *)
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
Require Import WpLock.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SpecPanic.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* idup's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
   below that -- filedup's [K] budget exactly, and for the same frame. *)
Definition K_idup : nat := 14%nat.

Definition wp_idup_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !irefNameG Σ, !irefslotG Σ,
      !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (nib : nat)
    (k : nat) (q : Qp) (dev inum : mword 32)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.idup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_idup <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 = ip, and a [struct inode *] IS its slot: [ientry_inj]. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ientry k ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_itable2 γl cn γfs γi cov logstart nib -∗
  itable_inv -∗
  panic_wp_any -∗
  (* THE precondition that makes [ip->ref++] safe -- see the header. *)
  iref_slot -∗
  (* A SHARE, not a reference -- see the header. *)
  inode_shr k q dev inum -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr
      /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ientry k ⌝ -∗
    (* ... and ONE reference back, at the share's own fraction *)
    inode_ref k q dev inum -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IDUP.
  Parameter wp_idup_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !irefNameG Σ, !irefslotG Σ,
             !diskGhostG Σ, !fsLogG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat)
      (k : nat) (q : Qp) (dev inum : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_idup_sconf_body γl cn γfs γi cov logstart nib k q dev inum
                         m n eb p C K b.
End IDUP.
