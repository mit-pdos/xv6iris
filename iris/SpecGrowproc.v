(* SpecGrowproc.v -- the public interface of growproc(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     int growproc(int n) {
       uint64 sz;
       struct proc *p = myproc();

       sz = p->sz;
       if (n > 0) {
         if (sz + n > TRAPFRAME)                       return -1;
         if ((sz = uvmalloc(p->pagetable, sz, sz + n, PTE_W)) == 0)
                                                       return -1;
       } else if (n < 0) {
         sz = uvmdealloc(p->pagetable, sz, sz + n);
       }
       p->sz = sz;
       return 0;
     }

   @ KernelSyms.growproc = 0x80001c0a, 37 instructions / 98 bytes; a 32-byte
   frame with all four slots used (ra / s0 / s1 = n / s2 = p).

   THE ALTITUDE.  growproc is a [proc_priv] consumer whose body is two calls
   stated one tier DOWN, over the bare [p->sz] / [p->pagetable] cells plus
   [ProcPtOwn.proc_pt] (SpecUvmalloc.v / SpecUvmdealloc.v).
   [ProcInv.proc_priv_addrspace] is that bridge, and unlike fetchaddr's
   [proc_priv_copy] BOTH halves move: growproc is the function that writes
   [p->sz], and the invariant tying the size to the map has to be
   re-established at the new pair.

   WHY THIS FUNCTION HAS NO PREMISE ABOUT ITS ARGUMENT, AND NONE ABOUT THE
   TABLE.  Both are consequences of [proc_priv]'s two size conjuncts
   (ProcInv.v), and neither could have been a premise -- a caller at this
   altitude holds nothing else:

   - [uvmalloc] must be told the run [PGROUNDUP(sz) .. sz+n) is FRESH (else
     mappages panics on a remap, and the OOM rollback is not exact).
     growproc pays that out of [um_below (pv_sz V)]: nothing is mapped at or
     above [p->sz], and the run starts at PGROUNDUP(p->sz).  This is the
     invariant the whole coherence apparatus exists for.
   - [n] is unconstrained.  Every arm is total in it, including the one
     where [sz + n] WRAPS ([sbrk(-1)] on a zero-sized process computes
     2^64 - 1): the C reaches uvmdealloc with that value and uvmdealloc
     returns [oldsz] unchanged, which is exactly what [uvmd_np]'s guard
     makes the contract say.

   THE POSTCONDITION IS THE C's FOUR PATHS, and the return value determines
   which: -1 means NOTHING moved (both failure arms roll back exactly, the
   second because uvmalloc's own contract does), 0 means the size moved to
   [szv'] and the table with it.  The three 0-arms are distinguished by the
   sign of [n] and are mutually exclusive, so a caller reads off exactly one.

   AMBIGUITY THE MACHINE HAS AND THE CONTRACT DOES NOT.  The C tests
   uvmalloc's result against 0, which is also what uvmalloc returns on a
   zero-length SUCCESS -- but not here: on this arm [n > 0] and
   [p->sz <= TRAPFRAME], so the new size is strictly positive and [beqz] can
   only mean failure.  The contract states the unambiguous reading. *)
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
Require Import FdSlots FileInv ProcInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* growproc's own frame is 4 slots; uvmalloc wants 42 below it (mappages 32,
   kalloc 14, uvmdealloc 26) and myproc 10, so 42 covers every call. *)
Definition growproc_stack : nat := 46%nat.

(* ===================================================================== *)
(*  WHAT growproc DID, as a function of [n] and the return value.         *)
(* ===================================================================== *)
(*   [szv] / [P] are the size and descriptor on entry, [szv'] / [P'] the
   ones on exit, and [r] the returned a0.  Four arms, one per path through
   the C; the [P' = P] ones say the table is untouched down to the
   descriptor RECORD, not merely up to [proc_pt]. *)
Definition growproc_ok (szv n : mword 64) (P P' : uptd) (szv' r : mword 64) : Prop :=
  (* (1) FAILED -- either the range test or uvmalloc.  Nothing moved: the
     range test runs before any call, and uvmalloc's OOM arm restores the
     descriptor it was handed exactly (SpecUvmalloc.v). *)
  (r = (mword_of_int (-1) : mword 64) /\ P' = P /\ szv' = szv)
  \/
  (* (2) GREW -- n > 0 and the new size fits under TRAPFRAME.  The map
     gained precisely the run [PGROUNDUP(sz) .. sz+n); which pages kalloc
     returned is not determined, so [P'] is pinned by extension + domain,
     exactly as uvmalloc's own success arm pins it. *)
  (r = (mword_of_int 0 : mword 64) /\ (0 < sint n)%Z /\
   (uint (add_vec szv n) <= uvm_maxsz)%Z /\
   szv' = add_vec szv n /\
   uptd_ext P P' /\
   dom (ud_um P') = dom (ud_um P)
                    ∪ vpn_run (svpn_of (pgroundup szv)) (uvma_np szv (add_vec szv n)))
  \/
  (* (3) UNCHANGED -- n = 0.  The C stores [sz] back over itself. *)
  (r = (mword_of_int 0 : mword 64) /\ sint n = 0 /\ P' = P /\ szv' = szv)
  \/
  (* (4) SHRANK -- n < 0.  The map lost the run above PGROUNDUP(sz+n) and
     the pages went back to kalloc.  The size is [sz + n] unless that
     WRAPPED past [sz], in which case uvmdealloc did nothing and returned
     the old size -- one disjunct, and the only place [n]'s unboundedness
     shows through. *)
  (r = (mword_of_int 0 : mword 64) /\ (sint n < 0)%Z /\
   P' = uptd_del_run P (svpn_of (pgroundup (add_vec szv n)))
                       (uvmd_np szv (add_vec szv n)) /\
   ( ((uint (add_vec szv n) < uint szv)%Z /\ szv' = add_vec szv n)
     \/ ((uint szv <= uint (add_vec szv n))%Z /\ szv' = szv) )).

Definition wp_growproc_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.growproc in
  let n := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (growproc_stack <= av)%nat ->
  sie_cap_gpr m av b p -∗
  (* [n = 0]: uvmalloc's kalloc runs with interrupts un-pushed *)
  cpu_own 0%nat eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd) (szv' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      ⌜growproc_ok (pv_sz V) n (pv_upt V) P' szv'
         (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own 0%nat eb p C b -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid (upd_sz (upd_upt V P') szv') -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type GROWPROC.
  Parameter wp_growproc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (b : bool),
      wp_growproc_sconf_body γa γf Φ m av eb p C pid V b.
End GROWPROC.
