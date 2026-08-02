(* ProtoSchedsInv.v -- PROTOTYPE for the last open question of the
   explicit-CPUID refactor: how the parked-scheduler record crosses a
   migration.  See claude-notes/projects/explicit-cpuid.md, section
   "THE LEVEL-0/ENABLED-BASE CONE".

   Five proofs (sleep / yield / bread / bwrite / acquiresleep) are blocked
   because they carry [sched_vc] -- hart h's parked scheduler context, which
   owns fourteen EXCLUSIVE words of hart h's struct cpu -- across
   interrupts-enabled instructions, where [wp_next] hands back an
   unconstrained hart.  It is the ONLY stranded resource.

   THE HYPOTHESIS THIS FILE VALIDATES: the difficulty comes entirely from the
   record being THREAD-OWNED, so a migration must carry it.  Make it GLOBAL
   instead -- a [scheds_inv] sibling to [procs_inv], holding per hart either
   "this hart's scheduler is running" or "it is parked with record R" -- and
   it becomes hart-free from the thread's point of view, which is exactly the
   property that crosses for free.  A thread that wants to swtch opens the
   invariant at whatever hart it is NOW on and takes out THAT hart's record.

   Everything below closes with no [Admitted] and no local axiom, against the
   real tree.  It is a prototype in the sense that it is not yet wired into
   [SchedCtx]/[SwtchCtx] -- not in the sense that anything is assumed.

   IT IS IN _CoqProject ON PURPOSE.  ProtoCpuid.v, this refactor's other
   prototype, was left out and duly rotted: by the time anyone read the design
   notes that pointed at it, it no longer typechecked against the interface it
   documented.  A prototype that is not built is not documentation. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots.
Require Import ProcInv.
Require Import SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import RegFile InstrBytes.
Require Import CalleeSaved KernelText.
Require Import SpecPanic.
Require Import Riscv.riscv_extras.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Definition schedsN : namespace := nroot .@ "scheds".

(* ---------------------------------------------------------------------- *)
(* Pure plumbing.                                                          *)
(* ---------------------------------------------------------------------- *)

Lemma fin_enum_lookup (n : nat) (h : fin n) :
  fin_enum n !! (fin_to_nat h) = Some h.
Proof.
  induction h as [|n h IH]; simpl; [done|].
  by rewrite list_lookup_fmap IH.
Qed.

Lemma cpu_enum_lookup (h : CPU) : enum CPU !! (fin_to_nat h) = Some h.
Proof. apply fin_enum_lookup. Qed.

Lemma proc_addr_nonzero (j : nat) :
  (j < NPROC)%nat -> proc_addr j <> (zero_reg : mword 64).
Proof.
  intros Hj Heq.
  apply (f_equal (@bv_unsigned 64)) in Heq.
  rewrite (proc_addr_unsigned j Hj) in Heq.
  assert (bv_unsigned (zero_reg : mword 64) = 0) as Hz
    by (vm_compute; reflexivity).
  rewrite Hz in Heq.
  unfold KernelSyms.proc, proc_size in Heq. lia.
Qed.

Section SchedsInv.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  (* the per-proc "loan receipt" ghost: one [ghost_var bool] per proc slot *)
  Context `{!ghost_varG Σ bool}.

  (* NOTE: NO [Context {CID : CpuId}] in this section.  That is the whole
     point: every definition below is HART-FREE, so a thread carries it
     across a migration for free, exactly like [procs_inv]. *)
  Context (Φ : mval -> iProp Σ).
  Context (γs : list gname).          (* the NPROC proc-lock gnames *)
  Context (γk : list gname).          (* the NPROC loan-receipt gnames *)

  (* ------------------------------------------------------------------ *)
  (* The per-proc loan receipt.                                          *)
  (*                                                                      *)
  (* [park_own j q r]: fraction [q] of proc j's receipt, at value [r].     *)
  (* [r = true]  -- "hart h's scheduler record is RESIDENT in slot h";     *)
  (* [r = false] -- "it is checked out (or the proc is parked)".           *)
  (*                                                                      *)
  (* KEYED BY THE PROC, NOT BY THE HART.  That is what makes the           *)
  (* entitlement hart-free: proc j is dispatched by whatever hart's        *)
  (* scheduler picked it up, and after a migration it is still proc j.     *)
  (* ------------------------------------------------------------------ *)
  Definition park_own (j : nat) (q : Qp) (r : bool) : iProp Σ :=
    (∃ γ : gname, ⌜γk !! j = Some γ⌝ ∗ ghost_var γ q r)%I.

  Definition park_hlf (j : nat) (r : bool) : iProp Σ := park_own j (1/2) r.
  Definition park_full (j : nat) (r : bool) : iProp Σ := park_own j 1 r.

  Lemma park_own_agree (j : nat) (q1 q2 : Qp) (r1 r2 : bool) :
    park_own j q1 r1 -∗ park_own j q2 r2 -∗ ⌜r1 = r2⌝.
  Proof.
    iIntros "(%γ1 & %H1 & Hg1) (%γ2 & %H2 & Hg2)".
    rewrite H1 in H2. injection H2 as ->.
    by iDestruct (ghost_var_agree with "Hg1 Hg2") as %->.
  Qed.

  Local Lemma ghost_var_halve (γ : gname) (r : bool) :
    ghost_var γ 1 r ⊣⊢ ghost_var γ (1/2) r ∗ ghost_var γ (1/2) r.
  Proof.
    iSplit.
    - iIntros "H". iApply (ghost_var_split γ r (1/2) (1/2)).
      rewrite Qp.half_half. iExact "H".
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H".
      try rewrite Qp.half_half. iExact "H".
  Qed.

  Lemma park_split (j : nat) (r : bool) :
    park_full j r ⊣⊢ park_hlf j r ∗ park_hlf j r.
  Proof.
    rewrite /park_full /park_hlf /park_own. iSplit.
    - iIntros "(%γ & %Hγ & Hg)".
      rewrite ghost_var_halve.
      iDestruct "Hg" as "[H1 H2]". iSplitL "H1".
      { iExists γ. iSplit; [done|]. iExact "H1". }
      { iExists γ. iSplit; [done|]. iExact "H2". }
    - iIntros "[(%γ1 & %H1 & Hg1) (%γ2 & %H2 & Hg2)]".
      rewrite H1 in H2. injection H2 as ->.
      iExists γ2. iSplit; [done|].
      rewrite ghost_var_halve. iFrame.
  Qed.

  Lemma park_update (j : nat) (r r' : bool) :
    park_hlf j r -∗ park_hlf j r ==∗ park_hlf j r' ∗ park_hlf j r'.
  Proof.
    rewrite /park_hlf /park_own.
    iIntros "(%γ1 & %H1 & Hg1) (%γ2 & %H2 & Hg2)".
    rewrite H1 in H2. injection H2 as ->.
    iMod (ghost_var_update_halves r' with "Hg1 Hg2") as "[Hg1 Hg2]".
    iModIntro. iSplitL "Hg1".
    { iExists γ2. iSplit; [done|]. iExact "Hg1". }
    { iExists γ2. iSplit; [done|]. iExact "Hg2". }
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The shared half of [cpus[h].proc].                                   *)
  (*                                                                      *)
  (* IN THE REAL DESIGN this is a re-split of what [IntrDefs.cpu_cells]    *)
  (* already owns in full: [cpu_cells] would keep [DfracOwn (1/2)] of      *)
  (* [a_cpu_proc] and the invariant would keep the other half.  It is the  *)
  (* ONLY channel by which the logic can learn -- the proc running on hart *)
  (* h is p -- which is exactly the fact myproc() reads.                    *)
  (* ------------------------------------------------------------------ *)
  Definition cpu_proc_half (h : CPU) (p : mword 64) : iProp Σ :=
    (a_cpu_proc (cid_word_of h) ↦₈{DfracOwn (1/2)} p)%I.

  Local Lemma word_excl (a : Arch.pa) (dq : dfrac) (w w' : mword 64) :
    a ↦₈ w -∗ a ↦₈{dq} w' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word_pointsto_bytes with "H1") as "Hb1".
    iDestruct (word_pointsto_bytes with "H2") as "Hb2".
    cbn [seq]. iDestruct "Hb1" as "[Hc1 _]". iDestruct "Hb2" as "[Hc2 _]".
    iDestruct (mem_pointsto_ne with "Hc1 Hc2") as %Hne. done.
  Qed.

  Local Lemma word_halve (a : Arch.pa) (w : mword 64) :
    a ↦₈ w ⊣⊢ a ↦₈{DfracOwn (1/2)} w ∗ a ↦₈{DfracOwn (1/2)} w.
  Proof. rewrite -word_pointsto_frac_split Qp.div_2 //. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE INVARIANT BODY, per hart.                                        *)
  (*                                                                      *)
  (* Three states, discriminated by TIMELESS data only (a pointsto value   *)
  (* and a ghost bool), so every case split below is available inside a    *)
  (* bare fancy update -- no program step needed to strip the [inv]'s ▷.   *)
  (*                                                                      *)
  (*   c->proc = 0                : hart h's SCHEDULER is running.  No     *)
  (*                                record exists; the scheduler owns its  *)
  (*                                own context cells as [cpu_ctx_free].   *)
  (*   c->proc = proc_addr j, r=1 : proc j runs on h and hart h's          *)
  (*                                scheduler is parked; ITS RECORD LIVES  *)
  (*                                HERE.                                  *)
  (*   c->proc = proc_addr j, r=0 : the record is checked out by the       *)
  (*                                running thread (it is inside sched(),  *)
  (*                                between the take-out and the swtch),   *)
  (*                                or not yet deposited (between the      *)
  (*                                dispatcher's c->proc store and the     *)
  (*                                resumed thread's deposit).             *)
  (*                                                                      *)
  (* The record is stored BARE, not under ▷: [inv] access already supplies *)
  (* the ▷ that every consumer (wp_swtch_sconf's premise) wants.           *)
  (* ------------------------------------------------------------------ *)
  Definition sched_slot (h : CPU) : iProp Σ :=
    (∃ p : mword 64,
       cpu_proc_half h p ∗
       (⌜p = zero_reg⌝
        ∨ (∃ (j : nat) (r : bool),
             ⌜p = proc_addr j /\ (j < NPROC)%nat⌝ ∗
             park_hlf j r ∗
             (if r then sched_vc_at Φ γs h (a_cpu_ctx (cid_word_of h)) p
                   else emp))))%I.

  Definition scheds_inv : iProp Σ :=
    inv schedsN ([∗ list] h ∈ enum CPU, sched_slot h).

  Global Instance scheds_inv_persistent : Persistent scheds_inv.
  Proof. apply _. Qed.

  (* the per-hart slot, extracted from the global body (under ▷) *)
  Local Lemma slot_acc (h : CPU) :
    (▷ [∗ list] h' ∈ enum CPU, sched_slot h') -∗
    ▷ sched_slot h ∗ (▷ sched_slot h -∗ ▷ [∗ list] h' ∈ enum CPU, sched_slot h').
  Proof.
    iIntros "Hb". iEval (rewrite big_sepL_later) in "Hb".
    iDestruct (big_sepL_lookup_acc _ _ (fin_to_nat h) h with "Hb")
      as "[$ Hback]"; [ apply cpu_enum_lookup |].
    iIntros "Hs". iEval (rewrite big_sepL_later).
    iApply ("Hback" with "Hs").
  Qed.

  (* ==================================================================== *)
  (* 2.  TAKE-OUT.                                                        *)
  (*                                                                      *)
  (* The entitlement is exactly two things:                               *)
  (*   - [park_hlf j true]   -- keyed by the PROC.  HART-FREE: it crosses  *)
  (*                            a migration as a plain frame.             *)
  (*   - [cpu_proc_half CID (proc_addr j)] -- hart-indexed, but it is the  *)
  (*                            fragment [cpu_cells] already carries, and  *)
  (*                            [cpu_cells] rides [sie_arm]'s enabled arm, *)
  (*                            so [wp_next] RE-DELIVERS it at the new     *)
  (*                            hart.  It has a transport by construction. *)
  (* Both come back; the invariant is re-closed in the r = false state.    *)
  (* ==================================================================== *)
  Lemma scheds_take `{CID : CpuId} (E : coPset) (j : nat) :
    ↑schedsN ⊆ E -> (j < NPROC)%nat ->
    scheds_inv -∗
    cpu_proc_half cpu_id (proc_addr j) -∗
    park_hlf j true
    ={E}=∗
      ▷ sched_vc_at Φ γs cpu_id (a_cpu_ctx cid_word) (proc_addr j) ∗
      cpu_proc_half cpu_id (proc_addr j) ∗
      park_hlf j false.
  Proof.
    iIntros (HE Hj) "#Hinv Hhalf Htok".
    rewrite /scheds_inv.
    iInv "Hinv" as "Hbody" "Hclose".
    iDestruct (slot_acc cpu_id with "Hbody") as "[Hslot Hback]".
    rewrite /sched_slot.
    iDestruct "Hslot" as (p) "[>Hph Hst]".
    iDestruct (word_pointsto_agree with "Hph Hhalf") as %->.
    iDestruct "Hst" as "[>%Hz | Hst]".
    { exfalso. exact (proc_addr_nonzero j Hj Hz). }
    iDestruct "Hst" as (j' r) "(>[%Hp' %Hj'] & >Htok' & Hrec)".
    assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
    iDestruct (park_own_agree with "Htok Htok'") as %<-.
    (* r = true: the record is resident.  Take it, flip to false. *)
    iMod (park_update j true false with "Htok Htok'") as "[Htok Htok']".
    iMod ("Hclose" with "[Hback Hph Htok']") as "_".
    { iApply "Hback". iNext. iExists (proc_addr j). iFrame "Hph".
      iRight. iExists j, false. iFrame "Htok'". done. }
    iModIntro. iFrame "Hhalf Htok".
    rewrite /cid_word. iExact "Hrec".
  Qed.

  (* ==================================================================== *)
  (* 3.  PUT-BACK.                                                        *)
  (*                                                                      *)
  (* NOT the scheduler's move, and this is a real finding: at its own      *)
  (* swtch the scheduler does NOT hold its record -- the record is         *)
  (* MANUFACTURED by the swtch proof out of the scheduler's continuation   *)
  (* and handed to the RESUMED party through [valid_context_pre]'s wand.   *)
  (* So the deposit is the resumed thread's first move, at its first       *)
  (* instruction after swtch returns.  [scheds_dispatch] below is what     *)
  (* the scheduler does instead.                                          *)
  (* ==================================================================== *)
  Lemma scheds_put (E : coPset) (h : CPU) (j : nat) :
    ↑schedsN ⊆ E -> (j < NPROC)%nat ->
    scheds_inv -∗
    cpu_proc_half h (proc_addr j) -∗
    park_hlf j false -∗
    ▷ sched_vc_at Φ γs h (a_cpu_ctx (cid_word_of h)) (proc_addr j)
    ={E}=∗ cpu_proc_half h (proc_addr j) ∗ park_hlf j true.
  Proof.
    iIntros (HE Hj) "#Hinv Hhalf Htok Hrec".
    rewrite /scheds_inv.
    iInv "Hinv" as "Hbody" "Hclose".
    iDestruct (slot_acc h with "Hbody") as "[Hslot Hback]".
    rewrite /sched_slot.
    iDestruct "Hslot" as (p) "[>Hph Hst]".
    iDestruct (word_pointsto_agree with "Hph Hhalf") as %->.
    iDestruct "Hst" as "[>%Hz | Hst]".
    { exfalso. exact (proc_addr_nonzero j Hj Hz). }
    iDestruct "Hst" as (j' r) "(>[%Hp' %Hj'] & >Htok' & Hemp)".
    assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
    iDestruct (park_own_agree with "Htok Htok'") as %<-.
    iMod (park_update j false true with "Htok Htok'") as "[Htok Htok']".
    iMod ("Hclose" with "[Hback Hph Htok' Hrec]") as "_".
    { iApply "Hback". iNext. iExists (proc_addr j). iFrame "Hph".
      iRight. iExists j, true. iFrame "Htok'". iSplit; [done|]. iExact "Hrec". }
    iModIntro. iFrame.
  Qed.

  (* ==================================================================== *)
  (* 3b. THE SCHEDULER'S TWO MOVES: the c->proc stores.                    *)
  (*                                                                      *)
  (* Because the invariant permanently holds half of [cpus[h].proc], the   *)
  (* two stores the scheduler makes to that field must now happen with the *)
  (* invariant OPEN.  They are exactly the two state transitions, so this  *)
  (* is alignment rather than accident -- but it is a real change to       *)
  (* [CpuOwn.cpu_own_set_proc], which becomes a mask-changing accessor.    *)
  (* ==================================================================== *)

  (* dispatch: c->proc : 0 -> proc_addr j, slot enters the "checked out"   *)
  (* state.  [park_full j false] comes out of proc j's lock.               *)
  Lemma scheds_dispatch (E : coPset) (h : CPU) (j : nat) :
    ↑schedsN ⊆ E -> (j < NPROC)%nat ->
    scheds_inv -∗
    cpu_proc_half h zero_reg -∗
    park_full j false
    ={E,E∖↑schedsN}=∗
      a_cpu_proc (cid_word_of h) ↦₈ zero_reg ∗
      (a_cpu_proc (cid_word_of h) ↦₈ proc_addr j
         ={E∖↑schedsN,E}=∗ cpu_proc_half h (proc_addr j) ∗ park_hlf j false).
  Proof.
    iIntros (HE Hj) "#Hinv Hhalf Hfull".
    rewrite /scheds_inv.
    iInv "Hinv" as "Hbody" "Hclose".
    iDestruct (slot_acc h with "Hbody") as "[Hslot Hback]".
    rewrite /sched_slot.
    iDestruct "Hslot" as (p) "[>Hph Hst]".
    iDestruct (word_pointsto_agree with "Hph Hhalf") as %->.
    iCombine "Hph Hhalf" as "Hcell". rewrite -word_halve.
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    rewrite word_halve. iDestruct "Hcell" as "[Hph Hhalf]".
    rewrite park_split. iDestruct "Hfull" as "[Ht1 Ht2]".
    iMod ("Hclose" with "[Hback Hph Ht1]") as "_".
    { iApply "Hback". iNext. iExists (proc_addr j). iFrame "Hph".
      iRight. iExists j, false. iFrame "Ht1". done. }
    iModIntro. iFrame.
  Qed.

  (* reclaim: c->proc : proc_addr j -> 0, after the parking proc's swtch   *)
  (* resumed us.  The slot is provably record-free (r = false), so nothing *)
  (* is orphaned; the two receipt halves rejoin and go back into proc j's  *)
  (* lock.                                                                *)
  Lemma scheds_reclaim (E : coPset) (h : CPU) (j : nat) :
    ↑schedsN ⊆ E -> (j < NPROC)%nat ->
    scheds_inv -∗
    cpu_proc_half h (proc_addr j) -∗
    park_hlf j false
    ={E,E∖↑schedsN}=∗
      a_cpu_proc (cid_word_of h) ↦₈ proc_addr j ∗
      (a_cpu_proc (cid_word_of h) ↦₈ zero_reg
         ={E∖↑schedsN,E}=∗ cpu_proc_half h zero_reg ∗ park_full j false).
  Proof.
    iIntros (HE Hj) "#Hinv Hhalf Htok".
    rewrite /scheds_inv.
    iInv "Hinv" as "Hbody" "Hclose".
    iDestruct (slot_acc h with "Hbody") as "[Hslot Hback]".
    rewrite /sched_slot.
    iDestruct "Hslot" as (p) "[>Hph Hst]".
    iDestruct (word_pointsto_agree with "Hph Hhalf") as %->.
    iDestruct "Hst" as "[>%Hz | Hst]".
    { exfalso. exact (proc_addr_nonzero j Hj Hz). }
    iDestruct "Hst" as (j' r) "(>[%Hp' %Hj'] & >Htok' & Hemp)".
    assert (j' = j) as -> by (apply (proc_addr_inj j' j Hj' Hj); congruence).
    iDestruct (park_own_agree with "Htok Htok'") as %<-.
    iCombine "Hph Hhalf" as "Hcell". rewrite -word_halve.
    iModIntro. iFrame "Hcell". iIntros "Hcell".
    rewrite word_halve. iDestruct "Hcell" as "[Hph Hhalf]".
    iMod ("Hclose" with "[Hback Hph]") as "_".
    { iApply "Hback". iNext. iExists zero_reg. iFrame "Hph". by iLeft. }
    iModIntro. iFrame "Hhalf". rewrite park_split. iFrame.
  Qed.

  (* ==================================================================== *)
  (* 5.  ALLOCATION.                                                      *)
  (*                                                                      *)
  (* Nothing below [SchedCtx] names [scheds_inv]; [main] allocates it when *)
  (* γs (and γk) exist.  The price -- and it is the design's one genuine   *)
  (* boot-story cost -- is that main must be HANDED half of EVERY hart's   *)
  (* c->proc cell, since the body is a [∗ list] over all 8 harts and each  *)
  (* hart's own precondition currently owns its cells in full.            *)
  (* ==================================================================== *)
  Lemma scheds_alloc (E : coPset) :
    ([∗ list] h ∈ enum CPU, cpu_proc_half h zero_reg) ={E}=∗ scheds_inv.
  Proof.
    iIntros "Hcells". rewrite /scheds_inv.
    iApply inv_alloc. iNext.
    iApply (big_sepL_mono with "Hcells").
    iIntros (k h Hk) "Hc". iExists zero_reg. iFrame "Hc". by iLeft.
  Qed.

  (* ==================================================================== *)
  (* THE VACUITY TRAP, recorded because it is easy to fall into: with the  *)
  (* invariant holding a permanent HALF of c->proc, a take-out lemma       *)
  (* stated against today's FULL-cell [cpu_own ... false] is VACUOUS       *)
  (* (fractions 1 + 1/2).  Halving [IntrDefs.cpu_cells]' proc field is     *)
  (* therefore mandatory, not cosmetic.                                    *)
  (* ==================================================================== *)
  Lemma cpu_own_full_is_vacuous `{CID : CpuId} (E : coPset)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    ↑schedsN ⊆ E ->
    scheds_inv -∗ cpu_own n eb p C false ={E}=∗ False.
  Proof.
    iIntros (HE) "#Hinv Hown".
    iDestruct "Hown" as "(((%Hb & Hnoff & Hint & Hproc) & Hcnt) & HC)".
    iInv "Hinv" as "Hbody" "Hclose".
    iDestruct (slot_acc cpu_id with "Hbody") as "[Hslot _]".
    rewrite /sched_slot. iDestruct "Hslot" as (p0) "[>Hph _]".
    iDestruct (word_excl with "Hproc Hph") as %[].
  Qed.

  (* PUT then TAKE.  The two directions compose -- which is simultaneously
     the NON-VACUITY witness for both: [scheds_put]'s output is exactly
     [scheds_take]'s entitlement, so neither premise set is empty. *)
  Lemma scheds_put_take `{CID : CpuId} (E : coPset) (j : nat) :
    ↑schedsN ⊆ E -> (j < NPROC)%nat ->
    scheds_inv -∗
    cpu_proc_half cpu_id (proc_addr j) -∗
    park_hlf j false -∗
    ▷ sched_vc_at Φ γs cpu_id (a_cpu_ctx cid_word) (proc_addr j)
    ={E}=∗
      ▷ sched_vc_at Φ γs cpu_id (a_cpu_ctx cid_word) (proc_addr j) ∗
      cpu_proc_half cpu_id (proc_addr j) ∗ park_hlf j false.
  Proof.
    iIntros (HE Hj) "#Hinv Hhalf Htok Hrec".
    iMod (scheds_put E cpu_id j with "Hinv Hhalf Htok Hrec")
      as "[Hhalf Htok]"; [done|done|].
    iMod (scheds_take (CID := CID) E j with "Hinv Hhalf Htok")
      as "(Hrec & Hhalf & Htok)"; [done|done|].
    iModIntro. iFrame.
  Qed.

End SchedsInv.

(* ====================================================================== *)
(* 4.  THE PAYOFF: what SpecYield's body becomes.                          *)
(*                                                                        *)
(* Diff against the real [SpecYield.wp_yield_sconf_body]:                  *)
(*   -  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj      (premise)   DELETED   *)
(*   -  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj      (post)      DELETED   *)
(*   +  scheds_inv Φ γs γk                            persistent, hart-free *)
(*   +  park_hlf γk j true                            hart-free token       *)
(* The two additions are exactly as transportable as [procs_inv] and       *)
(* [p_pid] already are, so [wp_next]'s ∀CID lambda carries them for free.  *)
(* ====================================================================== *)
Section Payoff.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !ghost_varG Σ bool}.
  Context `{CID : CpuId}.

  Definition wp_yield_sconf_body'
      (Φ : mval -> iProp Σ) (γs γk : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
    let pcE : mword 64 := mword_of_int KernelSyms.yield in
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    eb = true ->
    (20 <= av)%nat ->
    sie_cap_gpr m av b pj -∗
    cpu_own 0 eb pj C b -∗
    kernel_text -∗ pc_is pcE -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs γk -∗                       (* NEW: persistent, hart-free *)
    panic_wp_any -∗
    own_ctx (p_context pj) -∗
    park_hlf γk j true -∗                       (* NEW: hart-free receipt *)
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av b pj -∗
        cpu_own 0 eb pj C b -∗
        pc_is ret_tgt -∗
        own_ctx (p_context pj) -∗
        park_hlf γk j true -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
End Payoff.

(* ---------------------------------------------------------------------- *)
(* Everything above is CLOSED -- no [Admitted], no local axiom.            *)
(* ---------------------------------------------------------------------- *)
Print Assumptions scheds_take.
Print Assumptions scheds_put.
Print Assumptions scheds_dispatch.
Print Assumptions scheds_reclaim.
Print Assumptions scheds_alloc.
Print Assumptions scheds_put_take.
Print Assumptions cpu_own_full_is_vacuous.
