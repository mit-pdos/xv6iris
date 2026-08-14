(* SpecCopyinstr.v -- the public interface of copyinstr(), stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     int copyinstr(pagetable_t pagetable, uint64 psz, char *dst,
                   uint64 srcva, uint64 max) {
       int got_null = 0;
       while (got_null == 0 && max > 0) {
         va0 = PGROUNDDOWN(srcva);
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, psz, va0, 1)) == 0) return -1;
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

   The third member of the copyin / copyout family.  It used to be much the
   cheapest of the three to state, for two reasons; xv6 `4f2fc8b` took the
   first of them away.

   1. *** IT FAULTS PAGES IN NOW. ***  walkaddr used to be copyinstr's only
      callee and an unmapped page was simply [-1], so this contract needed
      no vmfault, no kalloc tier, no [cpu_own], no size and no [uptd_ext]:
      the descriptor that came back was the descriptor that went in.  The
      [pa0 == 0] arm now calls [vmfault(pagetable, psz, va0, 1)] exactly as
      copyin's does, which lifts copyinstr to the same altitude as the rest
      of the family: it takes [kalloc_env] and [cpu_own], and hands back a
      descriptor EXTENDING the one it was given ([uptd_ext_sz szv], every
      gained entry below [szv]).  Read SpecCopyin.v's header for the tier;
      the two now differ only in what the DESTINATION gets (point 2).

      The [psz] parameter arrives in a1, shifting dst/srcva/max down to
      a2/a3/a4, and the frame grew to 12 slots -- so [K] is the family's 50
      rather than the old 20.

   2. IT DOES NOT CALL memmove.  The copy is an inline byte loop, which is
      what makes a CONTENTS postcondition possible at all.  This is now the
      ONLY thing that distinguishes copyinstr from copyin.

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
   in the rest of the family: [-1] means an unbackable page or [max] bytes
   with no NUL among them, and no caller distinguishes them.

   NOTE WHAT THE FAULT PATH DOES NOT DISTURB: [bb_cstr] is a property of the
   DESTINATION buffer, which lives in kernel memory and which vmfault never
   touches.  So the success arm is stated exactly as before, and only the
   page-table and kalloc resources move. *)
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
Require Import IntrDefs WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import ByteBuf.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* copyinstr's answer, keyed by the returned a0.  The 0 arm is what makes the
   function usable; the -1 arm deliberately says nothing (see the header). *)
Definition copyinstr_ret (maxn : nat) (f : nat -> bv 8) (r : mword 64) : Prop :=
  (r = (mword_of_int 0 : mword 64) /\ exists k, (k < maxn)%nat /\ bb_cstr f k)
  \/ r = (mword_of_int (-1) : mword 64).

Definition wp_copyinstr_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (P : uptd) (szv : mword 64) (maxn : nat) (dst_olds : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyinstr in
  (* a0 = pagetable, a1 = psz, a2 = dst, a3 = srcva, a4 = max *)
  let dst := mm !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* 12-slot frame + vmfault's 38 (walkaddr needs 10) *)
  (50 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes -- and that is
     the whole requirement; it need not be the running process's. *)
  mm !!! Regidx (mword_of_int 10 : mword 5) = page_base P.(ud_root) ->
  (* the size argument, in a1 *)
  mm !!! Regidx (mword_of_int 11 : mword 5) = szv ->
  mm !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat maxn) : mword 64) ->
  (Z.of_nat maxn < 2 ^ 64)%Z ->
  (* it respects MAXVA (vmfault's premise) *)
  (uint szv <= 2 ^ 38)%Z ->
  (* vmfault's kalloc keeps its transient noff increment in int range *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (* copyinstr -> walkaddr -> walk *)
  locks_below lks "kmem" ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd) (dst_new : nat -> bv 8),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b lks -∗
    pc_is ret_tgt -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜copyinstr_ret maxn dst_new (mr !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYINSTR.
  Parameter wp_copyinstr_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (maxn : nat) (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string),
      wp_copyinstr_sconf_body γa mm P szv maxn dst_olds K lvl eb p C b lks.
End COPYINSTR.
