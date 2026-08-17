(* SpecCopyin.v -- the public interface of Copyin, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int copyin(pagetable_t pagetable, uint64 psz, char *dst, uint64 srcva,
                uint64 len) {
       while (len > 0) {
         va0 = PGROUNDDOWN(srcva);
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, psz, va0, 1)) == 0) return -1;
         n = PGSIZE - (srcva - va0);  if (n > len) n = len;
         memmove(dst, (void * )(pa0 + (srcva - va0)), n);
         len -= n; dst += n; srcva = va0 + PGSIZE;
       }
       return 0;
     }

   STATED AT THE [proc_pt] ALTITUDE, like vmfault: copyin PRESERVES the
   valid-user-page-table predicate of the table it reads through, and -- as
   it may fault pages in on the way -- hands back a descriptor EXTENDING the
   one it was given ([uptd_ext_sz szv]: same root, same trapframe, a user map
   that only gained entries, and every entry it gained BELOW [szv]).  The
   size bound is not extra work: vmfault backs a page only after ruling out
   [va >= psz], so the fact is already in the loop; stating it is what lets
   a [proc_priv] caller rebuild its block (ProcInv.proc_priv_copy), which a
   bare [uptd_ext] cannot.  Both exits, 0 and -1, deliver that; a run that
   gives up part-way has still copied a prefix and still faulted in whatever
   it faulted in, so there is nothing to roll back and no reason to split
   the resource story across the two arms.

   WHAT THE DESTINATION BUFFER GETS is unconstrained: [dst_new] is
   universally quantified in the continuation, i.e. the caller learns only
   that it still owns [len] bytes at [dst].  THIS IS NOT A WEAKNESS OF THE
   PROOF -- it is the honest reading of the function.  The bytes copyin
   copies come from USER memory, which the kernel may make no assumption
   about at all; and [proc_pt] owns the user pages with existential contents
   (the user-safety altitude -- see SpecVmfault.v), so there is no other
   value the postcondition could name.  A caller that wants to constrain
   what it read must validate the bytes itself.

   The kalloc tier and [cpu_own] are threaded through only because vmfault
   needs them; copyin allocates nothing of its own.

   *** THE SIZE IS AN ARGUMENT NOW, AND THE TWO PROC CELLS ARE GONE. ***
   xv6 `4f2fc8b` gave copyin a [psz] parameter (a1, shifting dst/srcva/len
   down to a2/a3/a4) and made the vmfault beneath it honest: it bounds
   against the [psz] handed in rather than `myproc()->sz`, and maps into the
   [pagetable] handed in rather than `myproc()->pagetable` (SpecVmfault.v).
   copyin therefore touches NEITHER proc cell, so [p_sz p ↦₈{dqs} szv] and
   [p_pagetable p ↦₈{dqp} …] are gone, and with them the [dqs]/[dqp]
   parameters.  [szv] is simply the a1 register value.

   That is not bookkeeping: [p_pagetable p ↦ page_base P.(ud_root)] was the
   unstated claim "the table you are reading through IS the running
   process's".  It was true of every caller, and it is why the contract could
   not be used on a table built but not yet installed.  It is no longer
   claimed, because it is no longer true of the code. *)
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
Require Import CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_copyin_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (mm : regfile)
    (P : uptd) (szv : mword 64) (len : nat) (dst_olds : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyin in
  (* a0 = pagetable, a1 = psz, a2 = dst, a3 = srcva, a4 = len *)
  let dst := mm !!! Regidx (mword_of_int 12) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 12-slot frame + vmfault's 38 (walkaddr needs 10, memmove 2) *)
  (50 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes -- and that is
     now the WHOLE requirement.  It used to have to be [p->pagetable] as
     well, because the vmfault beneath mapped there regardless; it does not
     any more (SpecVmfault.v). *)
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
  (* order premise at the lowest rank this cone reaches. *)
  locks_below lks "kmem" ->
  sie_cap_gpr kt mm K b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd) (dst_new : nat -> bv 8),
    sie_cap_gpr kt mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYIN.
  Parameter wp_copyin_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string),
      wp_copyin_sconf_body kt γa mm P szv len dst_olds K lvl eb p b lks.
End COPYIN.
