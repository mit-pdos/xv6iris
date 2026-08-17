(* SpecFetchaddr.v -- the public interface of fetchaddr(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     int fetchaddr(uint64 addr, uint64 *ip) {
       struct proc *p = myproc();
       if (addr >= p->sz || addr + sizeof(uint64) > p->sz)
         return -1;                 // both tests needed, in case of overflow
       if (copyin(p->pagetable, (char * )ip, addr, sizeof( *ip)) != 0)
         return -1;
       return 0;
     }

   @ KernelSyms.fetchaddr = 0x8000277a, 26 instructions / 74 bytes; a 32-byte
   frame with all four slots used (ra / s0 / s1 = addr / s2 = ip).

   THE ALTITUDE.  fetchaddr is the first function that spans the two tiers
   the [struct proc] work has kept apart: it is a [proc_priv] consumer (it
   calls myproc() and reads two of the private fields) whose whole body is a
   call to copyin, which is stated one tier DOWN over the bare [p_sz] /
   [p_pagetable] cells plus [ProcPtOwn.proc_pt].  [ProcInv.proc_priv_copy] is
   that bridge, and the shape of this spec follows from it:

   - the process comes back with its descriptor EXTENDED ([uptd_ext]: same
     root, same trapframe, a user map that only gained entries), because
     copyin may fault pages in on the way.  Everything else about the block
     is unchanged, which is what [upd_upt] says;
   - [p->sz <= MAXVA] is NOT a premise here.  It is a premise of copyin, of
     copyout and of vmfault, all of which take the bare cell -- but a caller
     at THIS altitude holds nothing but [proc_priv], so it could not
     discharge one.  The bound lives in [proc_priv] instead and this proof
     pays copyin's premise out of it.

   WHAT *ip GETS.  Nothing, and that is the honest reading rather than a
   weakness: the bytes come from USER memory, about which the kernel may
   assume nothing, and [proc_pt] owns the user pages with existential
   contents (see SpecCopyin.v).  So the two arms of [fetchaddr_post] are
   about OWNERSHIP, not values:

   - the range test failed: [*ip] is untouched (fetchaddr returned before
     calling copyin), and the answer is -1;
   - the range test passed: the caller still owns [*ip], now holding SOME
     value -- a copyin that gives up part-way has already written a prefix,
     so this is the right statement on BOTH copyin exits.

   THE RETURN VALUE IS NOT AN UNCONSTRAINED DISJUNCTION.  [r = 0] implies the
   second arm, i.e. [fetch_ok addr (pv_sz V)] -- a caller that gets 0 learns
   the whole doubleword lay inside the process's address space.  It cannot
   learn more: copyin's own contract permits failure (an unmapped page that
   vmfault declines to back), so "returns 0" is not a function of the inputs
   the way argfd's answer is. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* fetchaddr's own frame is 4 slots; copyin wants 50 below it (walkaddr 10,
   vmfault 38, memmove 2) and myproc 10, so 50 covers both calls. *)
Notation fetchaddr_stack := (54%nat) (only parsing).
(* ===================================================================== *)
(*  What fetchaddr TESTS.                                                 *)
(* ===================================================================== *)
(* The C is two unsigned compares -- [addr >= p->sz] and [addr + 8 > p->sz],
   the second one there to catch the wrap the first would miss -- and the
   machine keeps them as two ([bgeu s1,a5] then [bltu a5,a4] with
   [a4 = addr + 8]).  Under [proc_priv]'s [p->sz <= MAXVA] invariant they
   collapse to ONE arithmetic condition, because a [addr] that survives the
   first test is below 2^38 and [addr + 8] cannot then wrap.  ProofFetchaddr's
   [fa_z_ge_bad] / [fa_z_range] / [fa_z_lt_bad] are that collapse; stating the
   contract in the collapsed form is what keeps it readable. *)
Definition fetch_ok (addr szv : mword 64) : Prop :=
  (uint addr + 8 <= uint szv)%Z.

Section SpecFetchaddr.
  Context `{!riscvGS Σ}.

  (* fetchaddr's result, keyed by the returned a0 (the [argfd_post] shape). *)
  Definition fetchaddr_post (ip oldv addr szv r : mword 64) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ ¬ fetch_ok addr szv⌝ ∗ ip ↦₈ oldv
     ∨ ⌜(r = (mword_of_int 0 : mword 64) \/ r = (mword_of_int (-1) : mword 64))
        /\ fetch_ok addr szv⌝ ∗ ∃ w : mword 64, ip ↦₈ w)%I.

End SpecFetchaddr.

Definition wp_fetchaddr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (γf : gname)
    (m : regfile) (av : nat) (eb : bool) (p : mword 64)
    (pid : mword 32) (V : pprivate) (oldv : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fetchaddr in
  let addr := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ip := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (fetchaddr_stack <= av)%nat ->
  sie_cap_gpr kt m av b p -∗
  (* [n = 0]: copyin's chain reaches vmfault, whose kalloc runs with
     interrupts un-pushed (SpecCopyin.v) *)
  cpu_own 0%nat eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  kalloc_env γa None -∗
  ip ↦₈ oldv -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr kt mf av b p -∗
      cpu_own 0%nat eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid (upd_upt V P') -∗
      fetchaddr_post ip oldv addr (pv_sz V)
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FETCHADDR.
  Parameter wp_fetchaddr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (γf : gname) (m : regfile) (av : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (oldv : mword 64) (b : bool) (lks : gset string),
      wp_fetchaddr_sconf_body kt γa γf m av eb p pid V oldv b lks.
End FETCHADDR.
