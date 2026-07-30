(* SpecSched.v -- the public interface of Sched, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   sched() parks the current process: entered holding EXACTLY p->lock
   (noff == 1, interrupts off, saved base enable [eb = true] -- a kernel
   thread that can park always got here from interrupts-enabled code, and
   that is what makes the trap-CSR exchange below balanced), with the
   process's state already moved to a parked state (yield sets RUNNABLE,
   sleep sets SLEEPING -- [needs_ctx st]).  It swtches into this CPU's
   scheduler context, handing over the held lock, the state/chan cells, the
   trap CSRs and the per-CPU cells (the p_sched chain payload, SchedCtx.v).

   IT DOES NOT RETURN ON THE HART IT PARKED FROM.  Proc contexts are
   MIGRATABLE ([ctx_adm = None], SwtchCtx.v): any hart's scheduler may
   dispatch this process, swtch does not save tp, and the resumed thread
   inherits the resuming hart's.  So the continuation is quantified over the
   resuming hart [h] AND its per-hart SIE ghost [g], every resource it
   receives is spelled at [(h, g)], and its conclusion is hart [h]'s own
   [WP (LoopE h)].  The register postcondition weakens to
   [callee_saved_notp m mf] (everything but tp) plus the far more
   informative [mf !!! x4 = cid_word_of h] -- see CalleeSaved.v.

   What the continuation gets back: same j, state now RUNNING, lock held on
   hart [h], the trap CSRs and hart [h]'s [intr_handler_avail g] (the
   dispatch payload's, which is what a caller's own release/retune needs
   under the fresh ghost), c->proc back at proc j, and a FRESH parked
   scheduler context under ▷ -- hart [h]'s, hence [sched_vc_at h g]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SD := KernelSyms.sched.

Definition wp_sched_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
    (m : regfile) (av : nat) (eb : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sched in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  needs_ctx st = true ->
  (* THE PARKING PRECONDITION: the saved base enable is [true].  At level 1
     with [eb = true] the pushing acquire has taken the trap CSRs out of the
     re-enabled SIE arm, so the parking thread genuinely HOLDS them and can
     hand them across -- which the chain payload demands unconditionally
     (the scheduler always holds a set at every dispatch).  A parked kernel
     thread always got here from interrupts-enabled code, so this costs
     nothing. *)
  eb = true ->
  (16 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv Φ γs -∗
  proc_held cpu_id j γl st ch -∗
  (* handed over at the crossing, taken back from the dispatch payload. *)
  trap_csrs -∗
  (* the cpu bundle at level 1 (xv6 asserts noff==1 at sched), slot [emp]:
     the parked-scheduler slot content is the ▷ sched_vc premise below.
     sched PRESERVES [eb] across the park -- its intena save/restore is
     exactly the eb retune back to the caller's own state, now realized
     against the DISPATCHING hart's ghost [g] from the payload's own
     [intr_handler_avail g] (the entry stash is about the wrong name). *)
  cpu_own γ 1 eb pj emp -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ (h : CPU) (g : gname) (mf : regfile) (ch' : mword 64),
      ⌜callee_saved_notp m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word_of h⌝ -∗
      sie_cap_gpr (CID := h) g mf av -∗
      pc_is (CID := h) ret_tgt -∗
      proc_held h j γl RUNNING ch' -∗
      trap_csrs (CID := h) -∗
      intr_handler_avail (CID := h) g -∗
      cpu_own (CID := h) g 1 eb pj emp -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc_at Φ γs h g (a_cpu_ctx (cid_word_of h)) pj -∗
      WP (LoopE h : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SCHED.
  Parameter wp_sched_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
      (m : regfile) (av : nat) (eb : bool),
      wp_sched_sconf_body γ Φ γs j γl st ch m av eb.
End SCHED.
