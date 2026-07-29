(* SpecPipewrite.v -- the public interface of pipewrite, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int pipewrite(struct pipe *pi, uint64 addr, int n);

   pipewrite copies up to [n] bytes from user address [addr] into the pipe,
   sleeping on [&pi->nwrite] while the pipe is full, and returns the number
   it copied -- or -1 if the read end closed or the process was killed while
   it waited.  @ KernelSyms.pipewrite = 0x8000449e, ~84 instructions, a
   112-byte frame; ra/s0..s5 saved in the prologue, s6..s10 SHRINK-WRAPPED
   onto the paths that need them.

   THE ALTITUDE.  Two objects meet here, and the spec sits at each one's
   public tier:

   - the PIPE, at the reference tier (PipeInv.v): [is_pipe] is persistent
     and [pipe_ref γp w q] -- ANY end, ANY positive fraction -- is the whole
     credential story.  It is what licenses acquire (and release, and the
     re-acquire inside sleep) on the pipe's cancellable lock, and it comes
     back untouched.  Everything pipewrite does to the pipe's fields happens
     under [pi->lock] and is invisible to the caller: the counters move, the
     queue coupling [pipe_count_ok] is preserved, and no contract weaker
     than a contents-indexed pipe could say more (see design/pipe.md).

   - the PROCESS, at the [proc_priv] altitude (the fetchaddr shape): the
     copies go through [pr->pagetable] and may fault pages in, so the block
     comes back with its user-table descriptor EXTENDED ([uptd_ext],
     transitive across the loop's copyin calls) and everything else intact.

   THE RETURN VALUE ([pipe_rw_ret]): -1, or some 0 <= i <= max 0 n.  The
   spec deliberately does not say WHICH: how many bytes fit is decided by
   concurrent readers, and whether a byte crossed at all is decided by
   copyin's own contract (an unmapped user page vmfault declines to back
   fails the copy).  A 0-or-negative [n] returns 0 -- but still takes the
   lock and still wakes the readers, exactly as the C does.

   INTERRUPT LEVEL IS PINNED AT 0: sleep parks through sched(), whose
   invariant demands noff = 1 -- the pipe lock and nothing else -- so
   pipewrite as a whole must be entered with no lock held.  The running-
   thread bundle ([own_ctx] + [sched_vc] + [procs_inv], SpecSleep.v's shape)
   is threaded through for the same reason.

   Design & worklist: claude-notes/projects/pipe-rw.md. *)
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
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
Require Import PipeInv.
Require Import SpecPanic.
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation PW := KernelSyms.pipewrite.

(* pipewrite's own frame is 14 slots; the deepest callee is copyin at 50
   (walkaddr 10 / vmfault 38 / memmove 2); sleep wants 22, wakeup 18,
   killed 14, myproc/acquire/release 10. *)
Definition pipewrite_stack : nat := 64%nat.

Definition wp_pipewrite_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !pipeG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γlp : gname)
    (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (n : Z) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pipewrite in
  let pj := proc_addr j in
  let pi := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the tp register holds THIS cpu's id (the whole callee row's convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the process running here is proc j (sleep/killed's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (pipewrite_stack <= av)%nat ->
  sie_cap_gpr γ m av -∗
  (* noff = 0: sleep demands the pipe lock be the ONLY lock held *)
  cpu_own γ 0%nat eb pj C -∗
  kernel_text -∗ pc_is pcE -∗
  (* the pipe, and a share of one end -- the whole credential *)
  is_pipe γl γp pi -∗
  pipe_ref γp w q -∗
  (* the process block (copyin's tier is reached via proc_priv_copy) *)
  proc_priv γf pj pid V -∗
  kalloc_env γa None cid_word -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv γ Φ γs -∗
  panic_wp -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜pipe_rw_ret n (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ 0%nat eb pj C -∗
      pc_is ret_tgt -∗
      pipe_ref γp w q -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PIPEWRITE.
  Parameter wp_pipewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !pipeG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z),
      wp_pipewrite_sconf_body γ γa γf Φ γs j γlp γl γp w q m av eb C pid V n.
End PIPEWRITE.
