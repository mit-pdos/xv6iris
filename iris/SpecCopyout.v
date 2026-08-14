(* SpecCopyout.v -- the public interface of Copyout, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int copyout(pagetable_t pagetable, uint64 dstva, char *src, uint64 len) {
       while (len > 0) {
         va0 = PGROUNDDOWN(dstva);
         if (va0 >= MAXVA) return -1;
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, va0, 0)) == 0) return -1;
         pte = walk(pagetable, va0, 0);
         if (( *pte & PTE_W) == 0) return -1;   // no copyout over user text
         n = PGSIZE - (dstva - va0);  if (n > len) n = len;
         memmove((void * )(pa0 + (dstva - va0)), src, n);
         len -= n; src += n; dstva = va0 + PGSIZE;
       }
       return 0;
     }

   The mirror of SpecCopyin.v, and stated at the same [proc_pt] altitude:
   copyout PRESERVES the valid-user-page-table predicate and hands back a
   descriptor EXTENDING the one it was given, with every entry it gained
   below [p->sz] ([uptd_ext_sz szv]).  Read its header for why the two exits
   share one resource story, and for why the size bound is free.

   THE SOURCE BUFFER COMES BACK UNCHANGED ([src_bytes] on both sides) -- the
   one functional guarantee this contract makes, and the one a caller needs
   (it still owns, and can still read, what it asked to be copied out).

   WHAT THE USER PAGES END UP HOLDING is deliberately NOT stated.  [proc_pt]
   owns the pages it maps with EXISTENTIAL contents (the user-safety
   altitude -- see SpecVmfault.v), so there is no resource in this contract
   that could record the bytes that were written.  Saying what the process
   will read back needs a contents-indexed refinement of [proc_pt], which
   the user-execution layer cannot carry through a return to user mode
   anyway (user code overwrites its own pages); noted, not built.

   Note also what the [PTE_W] test does NOT buy: [proc_pt] is preserved
   whether or not the target leaf is writable, since its pages are
   contents-existential either way.  The test is honoured as a third
   failure arm, not as a precondition -- so a caller need know nothing
   about which of its pages are read-only. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import PtTree.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.


(* ===================================================================== *)
(*  copyout NO LONGER DEPENDS ON THE RUNNING PROCESS AT ALL.               *)
(* ===================================================================== *)
(* There used to be exactly ONE place where it did -- the [vmfault] in the
   loop that backs a page the walk did not find -- and it was load-bearing
   enough to shape this whole file.  vmfault read [p->sz] for its bound test
   and mapped into [p->pagetable], NOT into the table it was handed, so the
   [p_sz] / [p_pagetable] premises this contract carried were really the
   unstated claim "the table you are copying into IS the running process's".

   That claim was true of every caller except exec, which copies its argument
   strings into a table it has BUILT but not yet installed.  So the premise
   had been turned into a resource with two shapes selected by a ghost
   boolean [arm]: the process's own cells, or [co_mapped] -- "every byte the
   copy touches is already a valid user leaf", under which walkaddr never
   returns 0 and the vmfault call is dead.

   *** ALL OF THAT IS DELETED, because xv6 `4f2fc8b` fixed the conflation at
   the source. ***  vmfault now takes the size as an ARGUMENT and maps into
   the [pagetable] it was handed (SpecVmfault.v); copyout gained a matching
   [psz] parameter (a1, shifting dstva/src/len down to a2/a3/a4) and passes
   it straight down.  copyout therefore touches neither proc cell on any
   path, so there is no premise left to pay for and nothing for [arm] to
   select between: [co_license], [co_mapped], the [arm] index, the
   [COPYOUT_GEN] interface and the [dqs]/[dqp] parameters are all gone, and
   what remains is ONE contract over an arbitrary [proc_pt P].

   THIS RETIRES kexec's FIRST UPSTREAM BLOCKER (claude-notes/projects/
   kexec.md) -- and retires it more cheaply than the [arm] route did.  kexec
   no longer has to establish [co_mapped] over its destination range (a
   per-byte "already a valid user leaf" obligation, which is why phase C was
   going to need it); it just passes the new image's size in a1.  A caller
   that wants the fault path dead outright passes [szv := 0]: vmfault's
   [va >= psz] test then fires on every va, and [uptd_ext_sz 0 P P'] reads
   back [P' = P].  The ghost boolean has become an ordinary argument.

   WHAT NONE OF THIS BUYS: success.  The [va0 >= MAXVA] test and the [PTE_W]
   test are still live, so the -1 arm remains reachable and the
   postcondition still offers both.  That is the honest reading -- a caller
   that needs to rule -1 out must know its leaves are writable, and no
   caller in the tree does. *)

(* THE ONE CONTRACT.  Every caller -- either_copyout, piperead, kwait, readi,
   sys_pipe, and now kexec -- speaks this one; see ProofCopyout.v. *)
Definition wp_copyout_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyout in
  (* a0 = pagetable, a1 = psz, a2 = dstva, a3 = src, a4 = len *)
  let src := mm !!! Regidx (mword_of_int 13) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 14-slot frame + vmfault's 38 (walkaddr needs 10, walk 8, memmove 2).
     COPYOUT'S FRAME GREW AND ITS SIBLINGS' DID NOT, so this is 52 where
     SpecCopyin / SpecCopyinstr are still 50.  [psz] has to survive the
     walkaddr / vmfault / memmove calls in the loop, so gcc keeps it in s11 --
     which means s11 is now SAVED: `addi sp,sp,-112` (13 saved registers + one
     pad slot), against `-96` for copyin and copyinstr, whose extra argument
     dies before the first call.  Getting this wrong is not a soundness hole,
     it is an unsatisfiable premise: at 50 the body would run at 50 - 14 = 36
     and vmfault demands 38. *)
  (52 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes -- and that is
     now the WHOLE requirement; it need not be the running process's. *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the size argument, in a1 *)
  mm !!! Regidx (mword_of_int 11) = szv ->
  mm !!! Regidx (mword_of_int 14) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (Z.of_nat len < 2 ^ 64)%Z ->
  (* it respects MAXVA (vmfault's premise) *)
  (uint szv <= 2 ^ 38)%Z ->
  (* vmfault's kalloc keeps its transient noff increment in int range;
     [lvl] is otherwise generic (usertrap calls at 0, the pipe loops at 1) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b lks -∗
    pc_is ret_tgt -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYOUT.
  Parameter wp_copyout_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat),
      wp_copyout_sconf_body γa mm P szv len src_bytes K lvl eb p C b lks.
End COPYOUT.
