(* SpecSysSbrk.v -- the public interface of sys_sbrk(), stated independently
   of its proof.

     uint64 sys_sbrk(void) {
       uint64 addr;
       int t;
       int n;

       argint(0, &n);
       argint(1, &t);
       addr = myproc()->sz;

       if (t == SBRK_EAGER || n < 0) {
         if (growproc(n) < 0) return -1;
       } else {
         // Lazily allocate memory for this process: increase its memory
         // size but don't allocate memory.  If the process uses the
         // memory, vmfault() will allocate it.
         if (addr + n < addr)      return -1;
         if (addr + n > TRAPFRAME) return -1;
         myproc()->sz += n;
       }
       return addr;
     }

   @ KernelSyms.sys_sbrk = 0x80002938, 40 instructions / 120 bytes; a 48-byte
   frame (ra / s0 / s1 = addr, and ONE slot holding both [int] locals).

   TWO PATHS, AND THE LAZY ONE IS WHY THE COHERENCE INVARIANT IS AN
   INEQUALITY.  The eager path is growproc, so this contract simply reuses
   [SpecGrowproc.growproc_ok] rather than restating its four arms.  The lazy
   path raises [p->sz] and maps NOTHING -- vmfault backs the pages later --
   which is exactly the move [ProcInv.proc_priv]'s [um_below] conjunct
   survives by monotonicity ([ProcPtOwn.um_below_mono]).  A coherence
   invariant stated as an EQUALITY between [p->sz] and the mapped domain
   would make this function unprovable; that it is an inequality is what
   xv6's lazy allocation needs.

   WHAT THE CALLER LEARNS.  Failure is total: [-1] means neither the size nor
   the table moved, on all three failure arms (growproc's, and the lazy
   path's two range tests).  Success returns the OLD size -- sbrk's contract
   with userspace -- and says which of the two paths ran.

   THE WRAP TEST IS DEAD.  [addr + n < addr] can only fire if the 64-bit
   addition wraps, and it cannot: [p->sz] is inside the user region and
   [sint n < 2^63] by [RiscvExtras.sint64_range] alone, so the sum is below
   2^64 with room to spare.  No 32-bit bound on [n] is needed to see it, and
   the contract therefore has no disjunct for it.

   BOTH [myproc()] CALLS ARE HERE.  The lazy path calls it a second time and
   re-reads [p->sz] rather than using the saved [addr]; nothing between the
   two writes the cell, so the value is the same one -- but the proof has to
   say so, and that is why [cur_proc]'s stability matters to this function
   and not to growproc. *)
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
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecGrowproc.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* sys_sbrk's own frame is 6 slots; growproc wants 46 below it, argint 18
   and myproc 10, so 46 covers every call. *)
Definition sys_sbrk_stack : nat := 52%nat.

(* ===================================================================== *)
(*  The two syscall arguments, as the machine reads them back.            *)
(* ===================================================================== *)
(*   argint stores [trunc32 v] into the caller's [int] cell, and the [lw]
   that reloads it sign-extends.  So the value that reaches growproc, and
   the value compared against SBRK_EAGER, are these. *)
Definition sbrk_arg (v : mword 64) : mword 64 := sign_extend' 64 (trunc32 v).

(* SBRK_EAGER = 1 (kernel/riscv.h) *)
Definition sbrk_eager (v1 : mword 64) : Prop :=
  sbrk_arg v1 = (mword_of_int 1 : mword 64).

(* ===================================================================== *)
(*  WHAT sys_sbrk DID.                                                    *)
(* ===================================================================== *)
Definition sys_sbrk_ok (V : pprivate) (v0 v1 : mword 64)
    (P' : uptd) (szv' r : mword 64) : Prop :=
  (* FAILED -- and failure is total: neither half of the address space
     moved.  All three failure arms (growproc's, and the lazy path's
     TRAPFRAME test) return before writing anything. *)
  (r = (mword_of_int (-1) : mword 64) /\ P' = pv_upt V /\ szv' = pv_sz V)
  \/
  (* SUCCEEDED -- the answer is the OLD size, which is sbrk's contract with
     userspace, and one of the two paths ran. *)
  (r = pv_sz V /\
   ( (* EAGER: t == SBRK_EAGER, or a shrink.  growproc did all of it, and
        this is its own postcondition at a return value of 0. *)
     ( (sbrk_eager v1 \/ (sint (sbrk_arg v0) < 0)%Z) /\
       growproc_ok (pv_sz V) (sbrk_arg v0) (pv_upt V) P' szv'
                   (mword_of_int 0 : mword 64) )
     \/
     (* LAZY: the size alone moves, the table does not, and the new size is
        inside the user region.  vmfault backs the pages on demand. *)
     ( ~ sbrk_eager v1 /\ (0 <= sint (sbrk_arg v0))%Z /\
       P' = pv_upt V /\
       (uint (pv_sz V) + sint (sbrk_arg v0) <= uvm_maxsz)%Z /\
       szv' = add_vec (pv_sz V) (sbrk_arg v0) ) )).

Definition wp_sys_sbrk_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname)
    (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (v0 v1 : mword 64) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_sbrk in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the two syscall arguments, out of the trapframe page [proc_priv]
     carries *)
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  pv_tf V !! tf_arg_idx 1 = Some v1 ->
  (sys_sbrk_stack <= av)%nat ->
  sie_cap_gpr m av b p -∗
  (* [n = 0]: growproc's uvmalloc reaches kalloc with interrupts un-pushed *)
  cpu_own 0%nat eb p C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd) (szv' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      ⌜sys_sbrk_ok V v0 v1 P' szv'
         (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own 0%nat eb p C b -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid (upd_sz (upd_upt V P') szv') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSSBRK.
  Parameter wp_sys_sbrk_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (v0 v1 : mword 64) (b : bool),
      wp_sys_sbrk_sconf_body γa γf m av eb p C pid V v0 v1 b.
End SYSSBRK.
