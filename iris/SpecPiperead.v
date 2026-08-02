(* SpecPiperead.v -- the public interface of piperead, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int piperead(struct pipe *pi, uint64 addr, int n);

   piperead copies up to [n] bytes out of the pipe to user address [addr],
   sleeping on [&pi->nread] while the pipe is empty and the write end is
   still open, and returns the number it copied -- or -1 if the process was
   killed while it waited, or if the very first copyout failed.
   @ KernelSyms.piperead = 0x80004596, ~80 instructions, a 96-byte frame;
   ra/s0..s5 saved in the prologue, s6..s8 SHRINK-WRAPPED onto the paths
   that need them.

   THE MIRROR of SpecPipewrite.v -- read its header for the altitude story
   (the pipe at the reference tier, the process at the [proc_priv] tier,
   [pipe_rw_ret], and why noff is pinned at 0).  The one asymmetry worth
   noting: piperead can return 0 where pipewrite would sleep again -- a
   closed write end ends the wait -- and its -1-on-copyout-failure arm only
   fires when NOTHING was copied yet (i == 0); a partial success returns
   the partial count, exactly like pipewrite.  [pipe_rw_ret] covers both
   readings, and the spec deliberately does not distinguish them: which one
   happens is decided by concurrent writers.

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
Require Import HartTp WpNext.
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

Notation PR := KernelSyms.piperead.

(* piperead's own frame is 12 slots; the deepest callee is copyout at 50
   (walkaddr 10 / walk 8 / vmfault 38 / memmove 2); sleep wants 22,
   wakeup 18, killed 14, myproc/acquire/release 10. *)
Definition piperead_stack : nat := 62%nat.

Definition wp_piperead_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !pipeG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γlp : gname)
    (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (n : Z) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.piperead in
  let pj := proc_addr j in
  let pi := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the process running here is proc j (sleep/killed's linkage) *)
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  (* a2 is the int argument [n] *)
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (piperead_stack <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  (* noff = 0: sleep demands the pipe lock be the ONLY lock held *)
  cpu_own 0%nat eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the pipe, and a share of one end -- the whole credential *)
  is_pipe γl γp pi -∗
  pipe_ref γp w q -∗
  (* the process block (copyout's tier is reached via proc_priv_copy) *)
  proc_priv γf pj pid V -∗
  kalloc_env γa None -∗
  (* the running-thread bundle (SpecSleep.v) *)
  procs_inv Φ γs -∗
  panic_wp_any -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜pipe_rw_ret n (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0%nat eb pj C b -∗
      pc_is ret_tgt -∗
      pipe_ref γp w q -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PIPEREAD.
  Parameter wp_piperead_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !pipeG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname)
      (γl : gname) (γp : pipe_names) (w : bool) (q : Qp)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool),
      wp_piperead_sconf_body γa γf Φ γs j γlp γl γp w q m av eb C pid V n b.
End PIPEREAD.
