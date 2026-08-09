(* SpecKerneltrap.v -- kerneltrap()'s interface, in TWO layers.

   [KERNELTRAP] (bottom of this file) is the real thing: the house-spec
   contract of the C function, discharged by ProofKerneltrap.v.

   [KERNELTRAP_RETURNS] (first) is the LEGACY round-trip contract kernelvec
   was written against and which [LinkKerneltrap.v] still supplies with an
   [Axiom].  It says nothing about what kerneltrap DOES -- only that it
   returns, preserving the caller's registers, saved-register stack windows,
   and S-mode config cells.  It exists only until [ProofKernelvec.v] is
   rewired onto [KERNELTRAP] (explicit-cpuid Stage 2: the handler contract
   has to start handing the handler the trap CSRs, [cpu_hart], a deeper
   stack carve and a hart-generic Loeb -- see
   claude-notes/projects/kerneltrap.md).  THE DAY THAT LANDS, DELETE
   [KERNELTRAP_RETURNS], [kv_cell], [kt_clobbered] AND [LinkKerneltrap.v]'s
   axiom; nothing else refers to them.

   Keeping two interfaces for one function is not the intended end state,
   and the removal condition above is the whole reason it is tolerable now:
   the new contract cannot be CONSUMED until the engine changes, and the old
   one cannot be deleted until it is.                                       *)

(* ===================================================================== *)
(* LAYER 1: the legacy assumed round-trip contract (to be deleted).       *)
(*                                                                       *)
(*   misa / mseccfg / elp / pma_regions / htif are pinned persistently by *)
(*   [hw_config] and the minstret counter cells live in the (persistent)  *)
(*   [minstret_inv], so neither appears in the footprint; sepc is NOT in  *)
(*   it either (kerneltrap saves and restores it), so it frames around    *)
(*   the call.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto WpUart.
Require Import SpecDevintr.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section KvCell.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* the 8-byte stack cell at address [a] currently holding [v]: a
     doubleword points-to, bundling the 8 byte facts with 8-alignment. *)
  Definition kv_cell (a : mword 64) (v : bv 64) : iProp Σ :=
    word_pointsto a (DfracOwn 1) v.
End KvCell.

(* The caller-saved temporaries a C function (kerneltrap) may clobber:
   ra + t0..t6 + a0..a7 -- exactly the registers kernelvec's assembly saves
   and restores around the call.  Every OTHER register (sp, gp, tp, s0..s11)
   is callee-saved and must be preserved by kerneltrap. *)
Definition kt_clobbered : gset regidx :=
  {[ Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 5 : mword 5);
     Regidx (mword_of_int 6 : mword 5); Regidx (mword_of_int 7 : mword 5);
     Regidx (mword_of_int 10 : mword 5); Regidx (mword_of_int 11 : mword 5);
     Regidx (mword_of_int 12 : mword 5); Regidx (mword_of_int 13 : mword 5);
     Regidx (mword_of_int 14 : mword 5); Regidx (mword_of_int 15 : mword 5);
     Regidx (mword_of_int 16 : mword 5); Regidx (mword_of_int 17 : mword 5);
     Regidx (mword_of_int 28 : mword 5); Regidx (mword_of_int 29 : mword 5);
     Regidx (mword_of_int 30 : mword 5); Regidx (mword_of_int 31 : mword 5) ]}.

Definition wp_kerneltrap_returns_body `{!riscvGS Σ} `{GenId} `{CpuId} `{!sieG Σ}
    (γ : gname) (dq : dfrac)
    (m : regfile) (spv rava : mword 64)
    (satp0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
    (Phi : mval -> iProp Σ) :=
  m !!! Regidx csp_rs1 = spv ->
  m !!! Regidx (mword_of_int 1 : mword 5) = rava ->
  smode_config γ dq -∗
  satp ↦ᵣ satp0 -∗
  tlb ↦ᵣ tlbvec -∗
  pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
  gpr_file m -∗
  kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
  kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
  kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
  kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
  kv_cell pa17 v17 -∗
  ▷ ( ∀ m' : regfile,
      ⌜ ∀ r : regidx, r ∉ kt_clobbered → m' !!! r = m !!! r ⌝ -∗
      smode_config γ dq -∗
      satp ↦ᵣ satp0 -∗
      tlb ↦ᵣ tlbvec -∗
      pc_is rava -∗
      gpr_file m' -∗
      kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
      kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
      kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
      kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
      kv_cell pa17 v17 -∗
      WP (Loop : expr riscv_lang) {{ Phi }} ) -∗
  WP (Loop : expr riscv_lang) {{ Phi }}.

Module Type KERNELTRAP_RETURNS.
  Parameter kerneltrap_returns :
    forall `{!riscvGS Σ} `{GenId} `{CpuId} `{!sieG Σ}
      (γ : gname) (dq : dfrac)
      (m : regfile) (spv rava : mword 64)
      (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
      (Phi : mval -> iProp Σ),
      wp_kerneltrap_returns_body γ dq m spv rava satp0 tlbvec
        pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17
        v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 Phi.
End KERNELTRAP_RETURNS.

(* ===================================================================== *)
(* LAYER 2: THE REAL CONTRACT.                                            *)
(* ===================================================================== *)

(* The public interface of kerneltrap(), the C trap handler kernelvec calls.
   Requires only the definitional layer and its callees' Spec files --
   never a whole-function proof file.

     void kerneltrap() {
       int which_dev = 0;
       uint64 sepc = r_sepc(); uint64 sstatus = r_sstatus(); uint64 scause = r_scause();
       if ((sstatus & SSTATUS_SPP) == 0) panic("kerneltrap: not from supervisor mode");
       if (intr_get() != 0)              panic("kerneltrap: interrupts enabled");
       if ((which_dev = devintr()) == 0) {
         printk("scause=0x%lx sepc=0x%lx stval=0x%lx\n", scause, r_sepc(), r_stval());
         panic("kerneltrap");
       }
       if (which_dev == 2 && myproc() != 0) yield();
       w_sepc(sepc); w_sstatus(sstatus);
     }

   @ KernelSyms.kerneltrap = 0x80002696, 40 instructions, a 48-byte frame
   (ra/s0/s1/s2/s3).

   THE CONTRACT IS STATED AT THE ONE CALL SITE THERE IS.  kerneltrap is
   reached only from kernelvec, i.e. only on a taken S-mode interrupt, so the
   precondition says so -- and that is what makes all THREE panic arms dead:

     panic("not from supervisor mode")  refuted by [Hspp]: the trapped
                                        mstatus has SPP = 1, which the
                                        handler contract's [trap_ms] says;
     panic("interrupts enabled")        refuted for free: the live SIE bit
                                        IS the ambient arm index
                                        ([IntrDefs.sie_arm_half_agree]), and
                                        a handler runs at [b = false];
     printk(...); panic("kerneltrap")   refuted by [Hsc]: scause is threaded
                                        at a PINNED value that devintr
                                        recognises.

   THE POINT OF DOING IT THIS WAY IS THE AXIOM LEDGER.  Closing the third arm
   with [panic_wp_any] instead would have been easy, but printk's general
   (non-panic) path is UNPROVEN, so a live edge to it would put
   [wp_printk_gen_sconf] in the cone -- proving kerneltrap would then trade
   one sanctioned assumed contract for another.  With [Hsc] the cone is
   devintr + myproc + yield + panic, all proven, and discharging this
   contract removes [Kerneltrap.kerneltrap_returns] with nothing taking its
   place.

   WHY [Hsc] IS DISCHARGEABLE AT THE CALL SITE (and why it needs no [mip]
   invariant): the dispatch set is [s_pending = s_mip_bits & mie & mideleg],
   masked by [mie] -- and this kernel writes [sie] exactly once, in start()
   (`w_sie(r_sie() | SIE_SEIE | SIE_STIE)`, bits 9 and 5), never writes
   [mie], and starts from 0.  So no cause but S-external and S-timer can ever
   be pending, which is exactly devintr's two.  See
   [claude-notes/projects/kerneltrap.md].

   HOW THE SPP FACT REACHES THE CHECK: [sret_bits], the ghost mirror of
   mstatus.SPP and SPIE (IntrDefs).  The check runs FOUR instructions after
   entry, and every instruction round-trips [sconf] through
   [wp_instr_s_sconf], whose [exists ms] destroys the identity of the
   mstatus -- so no fact ABOUT a named entry mstatus can survive, and no
   flavour of the bundle rescues it.  What survives is the ghost, threaded
   independently: the caller hands over the travelling half at ('1','1')
   (the trap came from S-mode with interrupts enabled), and agreement with
   the tie inside [sconf] recovers the fact at whatever mstatus the sstatus
   read names.

   BECAUSE OF THAT, THE POSTCONDITION IS ABSOLUTE, NOT RELATIVE.  The final
   [csrw sstatus] writes back the saved word, so the mstatus kerneltrap
   leaves has SPP = 1, SPIE = 1 and SIE = 0 outright -- there is no need to
   name an entry mstatus anywhere in the contract, and the precondition
   threads the PLAIN [sie_cap_gpr].  Only the postcondition uses the
   mstatus-exposing flavour, and only because [sret] is what reads those
   bits.

   The travelling half CROSSES THE PARK with the other trap CSRs: on the
   resuming hart it comes back at that hart's own values, and the final
   [csrw sstatus] re-pins it from the word held in s1 -- a register value,
   which migrates for free.

   THE CROSSING IS REAL: [wp_next true p].  kerneltrap yields on a timer
   interrupt when this cpu has a current process, so execution can resume on
   a DIFFERENT hart -- and [wp_next]'s second escape hatch collapses that
   exactly when [p = zero_reg], which is the same condition the C tests
   (`which_dev == 2 && myproc() != 0`).  The per-hart cells therefore come
   back at the RESUMING hart: sepc holds the epc kerneltrap put back, but
   scause and stval are that hart's own and their values are existential.

   [eb = false] THROUGHOUT, and it is not a convenience.  The trap cleared
   SIE, so yield's own acquire records intena = 0, sched carries that across
   the park, and the matching release does not turn interrupts back on --
   kernelvec's sret is what restores SIE from SPIE.  This is the one place in
   the tree that parks at [eb = false], and today's SpecYield/SpecSched
   demand [eb = true]; see the project note for the generalization that
   owes.                                                                    *)

(* kerneltrap's own frame is 6 slots; the deepest callee is devintr at
   [SpecDevintr.devintr_stack] = 40 (myproc wants 10, yield 20). *)
Definition kerneltrap_stack : nat := 46%nat.

(* THE CHECK THAT KEEPS [IntrDefs.kv_frame_slots] HONEST.  That constant is
   the stack a trap may consume below the interrupted sp, and it has to cover
   kernelvec's own 32-slot frame PLUS this whole cone.  It is written as a
   literal there because this file sits above IntrDefs, so nothing would stop
   the two from drifting -- and drift is exactly the silent kind: growing
   kerneltrap's cone still compiles and only fails deep inside the handler
   proof, at a place that looks unrelated. *)
Lemma kt_carve_fits : (32 + kerneltrap_stack <= kv_frame_slots)%nat.
Proof. unfold kerneltrap_stack, kv_frame_slots. lia. Qed.

Section KtProcRes.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE YIELD ARM'S RESOURCES, UNDER THE DISJUNCTION THAT DECIDES WHETHER
     THE ARM RUNS AT ALL.  yield parks the CURRENT PROCESS, so it wants that
     process's saved-context cells and its half of the park bit; kerneltrap
     reaches yield only when [myproc() != 0].  Keying the disjunction on
     [p = zero_reg] is therefore not a convenience -- it is the same test the
     C makes, and the same one [wp_next]'s second escape hatch uses to
     conclude that a hart with no current proc cannot migrate.

     Threaded and handed back unchanged: neither conjunct is hart-indexed
     (both are indexed by the PROCESS), so both cross a migration for free.
     They are required unconditionally rather than only on the timer path --
     a running kernel thread holds them anyway, and making the precondition
     depend on scause would buy nothing and cost a case split at every
     caller. *)
  Definition kt_proc_res (p : mword 64) : iProp Σ :=
    (⌜ p = zero_reg ⌝ ∨
     ∃ j : nat, ⌜ (j < NPROC)%nat ⌝ ∗ ⌜ proc_addr j = p ⌝ ∗
                running_claim j)%I.
End KtProcRes.

Definition wp_kerneltrap_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γu : uart_names) (γv : disk_names) (γtx γdk γtl : gname)
    (Φ : mval -> iProp Σ) (γs : list gname) (pd pav pu : mword 64)
    (m : regfile) (av : nat) (p : mword 64) (C : iProp Σ)
    (ep sc tv : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kerneltrap in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  length γs = NPROC ->
  (kerneltrap_stack <= av)%nat ->
  (* the trap was taken from a cause devintr RECOGNISES *)
  devintr_ret sc <> (mword_of_int 0 : mword 64) ->
  (* the saved epc is instruction-aligned, so restoring it lands verbatim
     (sepc's write legalizes through the same bit-0 clear [ret_pc] is) *)
  ret_pc ep = ep ->
  sie_cap_gpr m av false p -∗
  (* THE TRAP CAME FROM S-MODE WITH INTERRUPTS ENABLED: SPP = 1 and
     SPIE = 1.  This is the [sret_bits] travelling half, which is what
     carries the fact past the four instructions before the check. *)
  sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
  cpu_own 0 false p C false -∗
  kernel_text -∗ pc_is pcE -∗
  sepc ↦ᵣ ep -∗ scause ↦ᵣ sc -∗ stval ↦ᵣ tv -∗
  devintr_caps γu γv γtx γdk γtl Φ γs pd pav pu -∗
  scheds_inv Φ γs -∗
  kt_proc_res p -∗
  wp_next true p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (ms_f sc' tv' : mword 64),
      ⌜ callee_saved m mf ⌝ -∗
      (* what the sret needs, and all it needs: return to S-mode, re-enable
         interrupts from SPIE, and they are still off until it does *)
      ⌜ _get_Mstatus_SPP  ms_f = ('b"1" : mword 1) ⌝ -∗
      ⌜ _get_Mstatus_SPIE ms_f = ('b"1" : mword 1) ⌝ -∗
      ⌜ _get_Mstatus_SIE  ms_f = ('b"0" : mword 1) ⌝ -∗
      sie_cap_gpr_at ms_f mf av false p -∗
      sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
      cpu_own 0 false p C false -∗
      (* sepc is RESTORED to the trapped pc; scause and stval belong to the
         resuming hart, so their values are existential *)
      sepc ↦ᵣ ep -∗ scause ↦ᵣ sc' -∗ stval ↦ᵣ tv' -∗
      pc_is ret_tgt -∗
      kt_proc_res p -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KERNELTRAP.
  Parameter wp_kerneltrap_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (γtx γdk γtl : gname)
      (Φ : mval -> iProp Σ) (γs : list gname) (pd pav pu : mword 64)
      (m : regfile) (av : nat) (p : mword 64) (C : iProp Σ)
      (ep sc tv : mword 64),
      wp_kerneltrap_sconf_body γu γv γtx γdk γtl Φ γs pd pav pu
        m av p C ep sc tv.
End KERNELTRAP.
