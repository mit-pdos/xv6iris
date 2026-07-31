(* SpecCopyinstr.v -- the public interface of copyinstr(), stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     int copyinstr(pagetable_t pagetable, char *dst, uint64 srcva, uint64 max) {
       int got_null = 0;
       while (got_null == 0 && max > 0) {
         va0 = PGROUNDDOWN(srcva);
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0) return -1;
         n = PGSIZE - (srcva - va0);  if (n > max) n = max;
         char *p = (char * )(pa0 + (srcva - va0));
         while (n > 0) {
           if ( *p == '\0') { *dst = '\0'; got_null = 1; break; }
           else *dst = *p;
           --n; --max; p++; dst++;
         }
         srcva = va0 + PGSIZE;
       }
       return got_null ? 0 : -1;
     }

   @ KernelSyms.copyinstr = 0x800014c8, 188 bytes.  The third member of the
   copyin / copyout family, and the CHEAPEST of the three to state, for two
   reasons that are worth naming because they shape the whole contract:

   1. IT DOES NOT FAULT PAGES IN.  walkaddr is copyinstr's only callee -- an
      unmapped page is simply [-1] -- so there is no vmfault, no kalloc tier,
      no [cpu_own], no [p->sz] and no [uptd_ext]: the descriptor that comes
      back is the descriptor that went in.  ([proc_pt P] on both sides; the
      pagetable argument is pinned to [page_base P.(ud_root)] by a premise,
      so not even the [p->pagetable] cell is needed.)

   2. IT DOES NOT CALL memmove.  The copy is an inline byte loop, which is
      what makes a CONTENTS postcondition possible at all.

   WHAT THE BUFFER GETS -- and here copyinstr differs from copyin in the one
   way that matters.  copyin's destination bytes are unconstrained (see
   SpecCopyin.v): they come from user memory, about which the kernel may
   assume nothing.  That is still true of copyinstr's bytes ONE AT A TIME --
   the contract names no individual byte -- but copyinstr's whole job is to
   establish a STRUCTURAL property of them, namely that the buffer now holds a
   NUL-terminated string.  That is [ByteBuf.bb_cstr f k]: the NUL sits at [k]
   and nowhere before it, so [k] is the length strlen will report, and
   [k < max] says the terminator landed inside the caller's buffer.  Without
   that clause the function would be useless -- fetchstr runs strlen over the
   result -- and with it the failure arm can stay information-free, exactly as
   in the rest of the family: [-1] means either an unmapped page or [max]
   bytes with no NUL among them, and no caller distinguishes them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs HartTp WpNext.
Require Import ByteBuf.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Notation CIS := KernelSyms.copyinstr.

(* copyinstr's answer, keyed by the returned a0.  The 0 arm is what makes the
   function usable; the -1 arm deliberately says nothing (see the header). *)
Definition copyinstr_ret (maxn : nat) (f : nat -> bv 8) (r : mword 64) : Prop :=
  (r = (mword_of_int 0 : mword 64) /\ exists k, (k < maxn)%nat /\ bb_cstr f k)
  \/ r = (mword_of_int (-1) : mword 64).

Definition wp_copyinstr_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (maxn : nat) (dst_olds : nat -> bv 8) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyinstr in
  let dst := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* 10-slot frame + walkaddr's 10 *)
  (20 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes *)
  mm !!! Regidx (mword_of_int 10 : mword 5) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat maxn) : mword 64) ->
  (Z.of_nat maxn < 2 ^ 64)%Z ->
  sie_cap_gpr mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ dst_olds j) -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (mr : regfile) (dst_new : nat -> bv 8),
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    proc_pt P -∗
    ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜copyinstr_ret maxn dst_new (mr !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type COPYINSTR.
  Parameter wp_copyinstr_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (maxn : nat) (dst_olds : nat -> bv 8) (K : nat) (b : bool) (p : mword 64),
      wp_copyinstr_sconf_body Φ mm P maxn dst_olds K b p.
End COPYINSTR.
