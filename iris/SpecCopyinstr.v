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
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs WpNext.
Require Import LockRank.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ByteBuf.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* copyinstr's answer, keyed by the returned a0.  The 0 arm is what makes the
   function usable; the -1 arm deliberately says nothing (see the header). *)
Definition copyinstr_ret (maxn : nat) (f : nat -> bv 8) (r : mword 64) : Prop :=
  (r = (mword_of_int 0 : mword 64) /\ exists k, (k < maxn)%nat /\ bb_cstr f k)
  \/ r = (mword_of_int (-1) : mword 64).

(* ===================================================================== *)
(* THE CONTRACT.  IT IS MEMORY-INDEXED, AND THERE IS NO ∃-WEAKENED TWIN. *)
(*                                                                       *)
(* WHAT HAPPENS TO THE PROCESS'S MEMORY:                                 *)
(*                                                                       *)
(* Nothing.  copyinstr READS user memory and WRITES only its kernel      *)
(* destination buffer, and the pages it faults in on the way were        *)
(* ALREADY in the view -- as lazy pages reading 0 -- so vmfault does not *)
(* move it either ([SpecVmfault.wp_vmfault_sconf_mem] is a noop on [M]   *)
(* at this altitude).  The descriptor still grows ([uptd_ext_sz]); the   *)
(* view does not.  [M] is therefore the SAME on the way in and on the    *)
(* way out, on BOTH arms -- which is exactly what a caller holding       *)
(* [ProcInv.proc_priv] needs in order to get its block back at the image *)
(* it handed over, instead of at a fresh existential one.                *)
(*                                                                       *)
(* The BUFFER promise is unchanged: [copyinstr_ret] already says all a   *)
(* caller uses (fetchstr runs strlen over the result), and it is a       *)
(* property of KERNEL memory, which [M] does not describe.  Saying which *)
(* process bytes the buffer received -- copyin's [copyin_got] -- would   *)
(* need the copied-prefix invariant threaded through the byte loop; no   *)
(* caller wants it, so it is deliberately not stated.                    *)
(*                                                                       *)
(* copyin and copyout each keep a [proc_pt]-altitude COROLLARY beside    *)
(* their memory-indexed contract, for the callers that say nothing about *)
(* a memory.  copyinstr has NO such caller -- fetchstr, its only one,    *)
(* holds [ProcInv.proc_priv] and wants its block back at the image it    *)
(* lent -- so the ∃-weakened twin is not written.  Should one ever be    *)
(* wanted, [ProcPtOwn.proc_pt_ptm] derives it in five lines (copyin's    *)
(* twin, which used to be the worked example, is deleted too).           *)
(* ===================================================================== *)
Definition wp_copyinstr_sconf_mem_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (ktb : ktier) (γa : gname) (mm : regfile)
    (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) (maxn : nat)
    (dst_olds : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyinstr in
  let dst := mm !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (50 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10 : mword 5) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 11 : mword 5) = szv ->
  mm !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat maxn) : mword 64) ->
  (Z.of_nat maxn < 2 ^ 64)%Z ->
  (uint szv <= 2 ^ 38)%Z ->
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_ptm P (uint szv) M -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ[ktb] dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd) (dst_new : nat -> bv 8),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    proc_ptm P' (uint szv) M -∗
    ([∗ list] j ∈ seq 0 maxn, (pa_add dst j) ↦ₘ[ktb] dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜copyinstr_ret maxn dst_new (mr !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYINSTR.
  Parameter wp_copyinstr_sconf_mem :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (ktb : ktier) (γa : gname) (mm : regfile)
      (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) (maxn : nat)
      (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string),
      wp_copyinstr_sconf_mem_body ktb γa mm P M szv maxn dst_olds K lvl eb p b lks.
End COPYINSTR.
