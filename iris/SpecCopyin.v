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

   WHAT THE DESTINATION BUFFER GETS is named by the MEMORY-INDEXED form
   below, [wp_copyin_sconf_mem]: it runs at [proc_ptm P (uint szv) M], the
   contents-indexed refinement of [proc_pt] (ProcPtOwn.v §5c), and its
   success arm promises [copyin_got M srcva len dst_new] -- byte [j] of the
   destination IS what the process's memory view holds at user va
   [srcva + j].  [M] comes back UNCHANGED: copyin only reads, and the
   lazily-backed pages a fault may add are already in the view
   (SpecVmfault.v), so the promise can be stated against the INPUT [M].

   [wp_copyin_sconf] is the existential-[M] corollary, in which [dst_new] is
   simply universally quantified -- the caller learns only that it still
   owns [len] bytes at [dst].  That is what every current caller speaks, and
   for most of them it is the right altitude: the bytes copyin copies come
   from USER memory, which the kernel may make no assumption about, so a
   caller that wants to constrain what it read must validate the bytes
   itself either way.  What the indexed form buys is the ability to say
   WHICH user bytes those were.

   The [-1] arm promises nothing about the destination.  A run that gives up
   part-way has copied a prefix, and which prefix is not observable from the
   return value.

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
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


(* THE BUFFER CARRIES ITS OWN TIER [ktb], below the hart's regime [KT1].
   It is FORCED and it is the same two-tier shape [WpSconfMem]'s merged
   leaves have: this function's kernel buffer is a FRAME local at [KT1] for
   one caller and a KT0 page/bio window for the next, and one shared tier
   cannot state both.  See SpecMemmove.v's note. *)
Definition wp_copyin_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (ktb : ktier) `{!KtierLe ktb KT1} (γa : gname) (mm : regfile)
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
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd) (dst_new : nat -> bv 8),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(* THE MEMORY-INDEXED CONTRACT: WHAT THE DESTINATION BUFFER GETS.        *)
(*                                                                       *)
(* The contract above leaves [dst_new] universally quantified, which was *)
(* the honest reading while [proc_pt] owned the user pages with          *)
(* EXISTENTIAL contents.  Now that the process's memory is NAMED         *)
(* ([ProcPtOwn.proc_ptm P sz M] -- a [gmap] from USER VIRTUAL ADDRESS to *)
(* byte, covering the LAZY pages too), the postcondition can say what    *)
(* the buffer holds: ON THE SUCCESS ARM byte [j] of the destination IS   *)
(* the byte the process has at [srcva + j].                              *)
(*                                                                       *)
(* [M] IS THE SAME ON BOTH SIDES.  copyin writes no user memory, and the *)
(* pages it faults in on the way were ALREADY in the view -- as lazy     *)
(* pages reading 0 -- so vmfault does not move it either                 *)
(* ([SpecVmfault.wp_vmfault_sconf_mem]).  The descriptor still grows     *)
(* ([uptd_ext_sz]); the view does not.  That is what lets the promise be *)
(* stated against the [M] the caller handed in.                          *)
(*                                                                       *)
(* THE -1 ARM PROMISES NOTHING about the buffer.  A run that gives up    *)
(* part-way has copied a prefix, and which prefix is not observable from *)
(* the return value.                                                     *)
(*                                                                       *)
(* [wp_copyin_sconf] stays as the [proc_pt]-altitude COROLLARY, so the   *)
(* callers that say nothing about the bytes do not have to name a        *)
(* memory.                                                               *)
(* ===================================================================== *)

(* byte [j] of the destination is the process's byte at [srcva + j] *)
Definition copyin_got (M : gmap Z (bv 8)) (srcva : mword 64) (len : nat)
    (dst_new : nat -> bv 8) : Prop :=
  forall j : nat, (j < len)%nat ->
    M !! uint (add_vec_int srcva (Z.of_nat j)) = Some (dst_new j).

Definition wp_copyin_sconf_mem_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (ktb : ktier) `{!KtierLe ktb KT1} (γa : gname) (mm : regfile)
    (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) (len : nat)
    (dst_olds : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyin in
  let dst := mm !!! Regidx (mword_of_int 12) in
  let srcva := mm !!! Regidx (mword_of_int 13) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (50 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 11) = szv ->
  mm !!! Regidx (mword_of_int 14) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (Z.of_nat len < 2 ^ 64)%Z ->
  (uint szv <= 2 ^ 38)%Z ->
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_ptm P (uint szv) M -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd) (dst_new : nat -> bv 8),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    proc_ptm P' (uint szv) M -∗
    ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] dst_new j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
       /\ copyin_got M srcva len dst_new)
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYIN.
  Parameter wp_copyin_sconf_mem :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (ktb : ktier) `{!KtierLe ktb KT1} (γa : gname) (mm : regfile)
      (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) (len : nat)
      (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string),
      wp_copyin_sconf_mem_body ktb γa mm P M szv len dst_olds K lvl eb p b lks.
  Parameter wp_copyin_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (ktb : ktier) `{!KtierLe ktb KT1} (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (dst_olds : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string),
      wp_copyin_sconf_body ktb γa mm P szv len dst_olds K lvl eb p b lks.
End COPYIN.
