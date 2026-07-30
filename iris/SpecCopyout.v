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
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.

Notation CPO := KernelSyms.copyout.

Definition wp_copyout_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyout in
  let src := mm !!! Regidx (mword_of_int 12) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 12-slot frame + vmfault's 38 (walkaddr needs 10, walk 8, memmove 2) *)
  (50 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes -- the same
     table [p->pagetable] holds, which is what vmfault will map into *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 13) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (Z.of_nat len < 2 ^ 64)%Z ->
  (* p->sz respects MAXVA (vmfault's premise) *)
  (uint szv <= 2 ^ 38)%Z ->
  (* vmfault's kalloc keeps its transient noff increment in int range;
     [lvl] is otherwise generic (usertrap calls at 0, the pipe loops at 1) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b -∗
  cpu_own lvl eb p C -∗
  kernel_text -∗
  pc_is pcE -∗
  p_sz p ↦₈{dqs} szv -∗
  p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd),
    sie_cap_gpr mr K b -∗
    cpu_own lvl eb p C -∗
    pc_is ret_tgt -∗
    p_sz p ↦₈{dqs} szv -∗
    p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type COPYOUT.
  Parameter wp_copyout_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool),
      wp_copyout_sconf_body γa Φ mm P szv len src_bytes K lvl eb p C dqs dqp b.
End COPYOUT.
