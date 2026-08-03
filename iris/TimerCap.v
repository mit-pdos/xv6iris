(* TimerCap.v -- "S-mode on this hart may reprogram the timer", as ONE
   persistent capability.  A small definitional layer over RiscvPtsto,
   mirroring TicksInv.v one level down from the leaves that consume it
   (WpSconfTimer.v).

     sstc_enabled  -- PERSISTENT: mcounteren.TM = 1 (this hart's)
     stimecmp_free -- the [stimecmp] cell at an ARBITRARY deadline
     stimecmp_inv  -- that cell, in an invariant at [timerN]
     timer_cap     -- sstc_enabled ∗ stimecmp_inv: PERSISTENT, and all that
                      [rdtime] / [csrw stimecmp] need.  THE thing a caller
                      passes down to clockintr; nothing comes back.

   Why the pin.  Two S-mode instructions need the timer: [rdtime] (csrr
   time) and [csrw stimecmp].  The model gates BOTH on mcounteren.TM (the
   [counter_enabled 1 Supervisor] and [is_stimecmp_accessible Supervisor]
   clauses), and gates the write additionally on menvcfg.STCE -- which [sconf]
   already pins by pinning menvcfg = MENVCFG_S.  So mcounteren.TM is the only
   configuration fact a timer leaf must be handed.  xv6 sets it once, in
   timerinit (`w_mcounteren(r_mcounteren() | 2)`), and never writes mcounteren
   again; registers are per-hart ([cpu_reg_name]), so that write can be sealed
   into a PERSISTENT pin ([sstc_enabled_intro]) which every timer leaf and every
   caller then shares for free rather than threading a cell.

   [stimecmp_free] is deliberately the WEAKEST useful invariant on the deadline
   -- ownership of the cell at an arbitrary value.  Nothing in the logic tracks
   what a deadline MEANS: the tick writes mip.STIP := (stimecmp <=u mtime) and
   both mip and mtime live in the value-agnostic [clock_inv] (MinstretInv.v),
   so "when the next timer interrupt fires" is not observable here, and a
   client that must relate the deadline to something else strengthens this
   resource without changing the interface. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The bit the model actually reads.  [counter_enabled] indexes mcounteren   *)
(* with [access_vec_dec _ 1] while [is_stimecmp_accessible] projects it with  *)
(* [_get_Counteren_TM]; the two are the same 1-bit slice.                    *)
(* ---------------------------------------------------------------------- *)
Lemma counteren_TM_access (v : mword 32) : access_vec_dec v 1 = _get_Counteren_TM v.
Proof. reflexivity. Qed.

Section TimerCap.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* S-mode may read [time] and write [stimecmp]: persistent, duplicable. *)
  Definition sstc_enabled : iProp Σ :=
    (∃ mcen : mword 32,
       mcounteren ↦ᵣ□ mcen ∗ ⌜ eq_vec (_get_Counteren_TM mcen) ('b"1") = true ⌝)%I.

  Global Instance sstc_enabled_persistent : Persistent sstc_enabled.
  Proof. apply _. Qed.

  (* the deadline cell, contents existential. *)
  Definition stimecmp_free : iProp Σ := (∃ d : mword 64, stimecmp ↦ᵣ d)%I.

  Lemma stimecmp_free_intro (d : mword 64) : stimecmp ↦ᵣ d -∗ stimecmp_free.
  Proof. iIntros "H". iExists d. iFrame "H". Qed.

  (* ---- the deadline cell, in an INVARIANT.  Nothing in the logic depends on
     the deadline's value (see the header), so the cell has nothing to gain
     from being threaded linearly and everything to lose: every caller on the
     path down to clockintr (kerneltrap, devintr, ...) would have to carry it
     in and out.  Sealed in an invariant instead, the whole timer capability
     becomes PERSISTENT: a caller passes it and gets nothing back to track,
     and the [csrw stimecmp] leaf opens the invariant across its own single
     instruction step (timerN is disjoint from minstretN, so it is openable
     inside the step engine's callback mask).  A client that later DOES need
     to know the deadline holds the cell directly instead -- [stimecmp_free]
     is still the raw form, and this invariant is one ghost step away. *)
  Definition timerN : namespace := nroot .@ "timer".

  Definition stimecmp_inv : iProp Σ := inv timerN stimecmp_free.

  (* THE timer capability: "S-mode on this hart may reprogram the timer". *)
  Definition timer_cap : iProp Σ := (sstc_enabled ∗ stimecmp_inv)%I.

  Global Instance timer_cap_persistent : Persistent timer_cap.
  Proof. apply _. Qed.

  (* construction (the "freeze" ghost step): what a caller does with
     timerinit's postcondition -- the written mcounteren cell, at any
     fraction, with TM set, becomes the persistent pin. *)
  Lemma sstc_enabled_intro (dq : dfrac) (mcen : mword 32) :
    eq_vec (_get_Counteren_TM mcen) ('b"1") = true ->
    reg_pointsto mcounteren dq mcen ==∗ sstc_enabled.
  Proof.
    iIntros (HTM) "Hmcen".
    iMod (reg_pointsto_persist with "Hmcen") as "Hmcen".
    iModIntro. iExists mcen. iFrame "Hmcen". iPureIntro. exact HTM.
  Qed.

  (* the whole capability, from timerinit's postcondition: the written
     mcounteren (TM set) and the written stimecmp cell. *)
  Lemma timer_cap_intro E (dq : dfrac) (mcen : mword 32) (d : mword 64) :
    eq_vec (_get_Counteren_TM mcen) ('b"1") = true ->
    reg_pointsto mcounteren dq mcen -∗ stimecmp ↦ᵣ d ={E}=∗ timer_cap.
  Proof.
    iIntros (HTM) "Hmcen Hstc".
    iMod (sstc_enabled_intro dq mcen HTM with "Hmcen") as "#Hen".
    iMod (inv_alloc timerN E stimecmp_free with "[Hstc]") as "#Hinv".
    { iNext. iApply (stimecmp_free_intro with "Hstc"). }
    iModIntro. iFrame "Hen Hinv".
  Qed.

End TimerCap.
