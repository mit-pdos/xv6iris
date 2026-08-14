(* ProofScheduler.v -- the whole-function sconf-tier proof of scheduler()
   (SpecScheduler.v), as a sealed functor over its callees' interfaces
   (acquire, release, swtch).  See claude-notes/projects/scheduler.md.

   scheduler() never returns, so the spec's conclusion is a bare WP and the
   proof has no epilogue.  Its shape is

     prologue (80-byte frame, ra/s0..s8)            +0x00 .. +0x16
     setup: c->proc = 0, s6 = &c->context,          +0x18 .. +0x46
            s4 = &cpus[cid], s8 = RUNNING, s7 = 1
     c.j into the loop head                          +0x48
     release tail (REJOINING ARMS)                   +0x4a .. +0x54
     inner scan body: acquire / test / dispatch      +0x58 .. +0x7c
     if (!found) wfi                                 +0x7e .. +0x82
     loop head: intr_on / intr_off / re-materialize  +0x86 .. +0xa2

   Three nested pieces, each an iAssert-ed □ lemma so the back edges can reach
   them:

     [Tail]  -- +0x4a..+0x54 proved ONCE over an arbitrary arrival map (the
                [wp_ci_tail] recipe): both the not-RUNNABLE fall and the
                post-swtch jump land there.  Its two exits (recurse / scan
                done) are ∧-CONJOINED, per the search-loop rule.
     [Loop]  -- the bounded proc[] scan, by fuel induction on the remaining
                count, entry +0x58, single exit at +0x7e threaded as a premise.
     [Outer] -- the unbounded dispatch loop, by iLöb, entry +0x86; the two back
                edges are the [bnez s5] taken leaf and the wfi leaf, both of
                which hand their step's ▷ out. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.   (* [minstretN]: the mask the store-AU leaf leaves open *)
Require Import InstrBytes.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpSmodeWfi.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import CodeScheduler.
Require Import SpecAcquire SpecRelease SpecSwtch SpecScheduler.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.
Local Strategy 1000 [pa_stk].

(* ===================================================================== *)
(* Pure helpers: the mword address algebra + the two state facts.         *)
(* ===================================================================== *)






(* the workhorse: pull the (symbolic) per-cpu shift term to the OUTSIDE,
   leaving a CLOSED constant equality. *)
Lemma sc_swap (a sh b : mword 64) : add_vec (add_vec a sh) b = add_vec (add_vec a b) sh.
Proof.
  rewrite (po_addv_assoc a sh b) (add_vec64_comm sh b) (po_addv_assoc a b sh). reflexivity.
Qed.

Lemma sc_reconcile (K sh d MY : mword 64) :
  add_vec K d = MY -> add_vec (add_vec K sh) d = add_vec MY sh.
Proof. intro H. rewrite (sc_swap K sh d). rewrite H. reflexivity. Qed.

Lemma sc_reconcile2 (K sh d MY : mword 64) :
  add_vec MY d = K -> add_vec sh K = add_vec (add_vec MY sh) d.
Proof. intro H. rewrite (sc_swap MY sh d). rewrite H. apply add_vec64_comm. Qed.

(* a saved-register frame slot address in terms of the pushed sp (-80). *)
Lemma sc_frame_bridge (sp0 : mword 64) (j : nat) (uimm : mword 6) :
  bv_unsigned (add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                       (zero_extend' 64 (concat_vec uimm ('b"000"))) : mword 64)
    = bv_wrap 64 (- (8 * Z.of_nat j)) ->
  pa_stk sp0 j
    = add_vec (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
              (zero_extend' 64 (concat_vec uimm ('b"000"))).
Proof.
  intro H.
  assert (Heq : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                        (zero_extend' 64 (concat_vec uimm ('b"000")))
                = (mword_of_int (- (8 * Z.of_nat j)) : mword 64)).
  { apply bv_eq. rewrite H.
    unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. reflexivity. }
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc. rewrite Heq. reflexivity.
Qed.

(* the two struct-proc field addresses in the 12-bit-displacement spelling. *)
Lemma sc_state_addr (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state pa.
Proof.
  assert (H : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Lemma sc_ctx_addr (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 96 : mword 12)) = p_context pa.
Proof.
  assert (H : sign_extend' 64 (mword_of_int 96 : mword 12) = (mword_of_int 96 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

(* the scan's end pointer: &proc[NPROC] is distinct from every array member. *)
Lemma sc_proc_addr_ne_end (i : nat) : (i < NPROC)%nat -> proc_addr i <> proc_addr NPROC.
Proof.
  intros Hi Heq.
  apply (f_equal (@bv_unsigned _)) in Heq.
  rewrite (proc_addr_unsigned i Hi) in Heq.
  assert (Hn : bv_unsigned (proc_addr NPROC) = KernelSyms.proc + proc_size * 64)
    by (vm_compute; reflexivity).
  rewrite Hn in Heq. unfold proc_size in Heq. unfold NPROC in Hi. lia.
Qed.

(* a state that owns a saved context is not one the invariant holds the
   private field block for.  (Case on the two [needs_ctx] disjuncts.) *)
Lemma sc_needs_ctx_not_dormant (st : mword 32) :
  needs_ctx st = true -> inv_dormant st = false.
Proof. exact (inv_dormant_of_needs_ctx st). Qed.

Lemma sc_neq_vec_false (n : Z) (x y : mword n) : neq_vec x y = false -> x = y.
Proof.
  intro H. unfold neq_vec in H. apply negb_false_iff in H.
  apply eq_vec_true_iff. exact H.
Qed.

(* ===================================================================== *)
(* THE SCHEDULER'S CARVE ARITHMETIC.                                      *)
(*                                                                        *)
(* scheduler()'s sp NEVER MOVES after the 10-slot prologue, so the         *)
(* PHYSICAL carve is the constant [av - 10] at every point of the loop.    *)
(* [sie_cap]'s index is that constant MINUS the arm's reserve, so it is    *)
(* arm-dependent -- and it must be, or the loop would have to claim the    *)
(* same [kv_frame_slots] twice (once as usable stack, once as reserve).    *)
(* The loop invariants therefore carry the index as a BINDER [n] plus the  *)
(* side fact [trap_res <arm> + n = av - 10]; writing it as the closed form *)
(* [av - 10 - trap_res b] would leave a STUCK [av - 10 - 0] at the         *)
(* disabled arm ([Nat.sub] recurses on its FIRST argument), which is       *)
(* exactly the trap [IntrDefs]' "left summand" note warns about, one       *)
(* operator over.  These three facts are all the arithmetic that needs.    *)
(* ===================================================================== *)
Lemma sc_res_le (b : bool) : (trap_res b <= kv_frame_slots)%nat.
Proof. destruct b; cbn; lia. Qed.

(* the ONE real enable: [av - 10] usable at the disabled arm re-reads as
   "[kv_frame_slots] set aside plus what is left", which is the shape the
   0 -> 1 flip leaf demands of its pre index. *)
Lemma sc_carve (av : nat) :
  (kv_frame_slots + 20 <= av)%nat ->
  (av - 10)%nat = (trap_res true + (av - 10 - kv_frame_slots))%nat.
Proof. intros Hav. change (trap_res true) with kv_frame_slots. lia. Qed.

(* the index that goes with an arbitrary arm, and the fact that it does. *)
Lemma sc_idx_ok (av : nat) (b : bool) :
  (kv_frame_slots + 20 <= av)%nat ->
  (trap_res b + (av - 10 - trap_res b))%nat = (av - 10)%nat.
Proof. intros Hav. pose proof (sc_res_le b). lia. Qed.

Lemma sc_eq_vec_ne (n : Z) (x y : mword n) : x <> y -> eq_vec x y = false.
Proof. intro H. apply eq_vec_false_iff. exact H. Qed.

(* ===================================================================== *)
(* THE EXPLICIT-CPUID SEAM.  scheduler() never migrates: its [cpus[cid]]  *)
(* register state would name the wrong hart's fields if it did, and it     *)
(* provably cannot, because [kerneltrap] yields only when [myproc() != 0]  *)
(* and this thread's [c->proc] is 0.  That datum is exactly the [p] of the *)
(* ambient [sie_cap_gpr] / [sie_arm], so every enabled step of this proof  *)
(* collapses through [WpNext.wp_next_idle] (p = zero_reg) rather than      *)
(* [wp_next_off] -- the two windows where [p] is a real proc address       *)
(* (+0x68..+0x76) run under a held lock, i.e. at [b = false].              *)
(* ===================================================================== *)

(* At [b = false] the bundle does not mention [p] at all ([sie_arm false p]
   ignores it), so re-tagging the crossing index is pure conversion.  Needed
   twice per dispatch round: c->proc goes 0 -> proc_addr jj at +0x68 and back
   at +0x76, while [wp_swtch_sconf] wants the bundle and [cpu_own] at the SAME
   index. *)
Lemma sc_retag_p `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (mm : regfile) (n : nat) (px qx : mword 64) :
  sie_cap_gpr mm n false px ⊣⊢ sie_cap_gpr mm n false qx.
Proof. reflexivity. Qed.

(* The scheduler's [cpu_own] is always at level 0 with an [emp] context slot,
   and it is opened / rebuilt at five points.  Three one-liners rather than
   five hand-rolled destructuring patterns (the bundle is LEFT-nested now:
   [((cells ∗ count) ∗ C)]). *)
Lemma sc_cpu_own_open `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (px : mword 64) (C : iProp Σ) (eb : bool) (lks : gset nat) :
  cpu_own 0 eb px C false lks -∗
  a_cpu_noff cid_word ↦₄ noff_val 0 ∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) ∗
  intr_count 0 eb ∗
  cur_proc px ∗ cpu_locks_lvl 0 lks ∗ C.
Proof.
  rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
  iIntros "((((_ & Hn & Hi & Hp) & Hl) & Hc) & HC)". iFrame.
Qed.

Lemma sc_cpu_own_mk `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) (lks : gset nat) :
  a_cpu_noff cid_word ↦₄ noff_val 0 -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  intr_count 0 false -∗
  cur_proc px -∗
  cpu_locks_lvl 0 lks -∗
  cpu_own 0 false px emp false lks.
Proof.
  iIntros "Hn Hi Hc Hp Hl". rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
  iFrame "Hn Hi Hc Hp Hl". iPureIntro. vm_compute. reflexivity.
Qed.

Lemma sc_cpu_own_of_cells `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (px : mword 64) (eb : bool) (lks : gset nat) :
  cpu_priv 0 eb px lks -∗ intr_count 0 false -∗ cpu_own 0 false px emp false lks.
Proof.
  rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
  iIntros "((_ & Hn & Hi & Hp) & Hl) Hc". iFrame "Hn Hi Hc Hp Hl".
  iPureIntro. vm_compute. reflexivity.
Qed.

(* The two SIE-flip leaves at the loop head take the count eighth and the
   per-cpu cells SEPARATELY, each guarded by [if eb then emp else _]: at the
   enabled base they are inside [sie_arm]'s arm and the caller holds neither.
   This is exactly what [cpu_own 0 eb p emp eb] carries -- note the index is
   [eb] and NOT a blanket [false] (CpuOwn.cpu_own_eb_agree forces them equal
   at level 0). *)
(* THE HELD SET IS THE LITERAL [∅] HERE, and it has to be: the flip leaf's own
   premise is [cpu_priv 0 true p ∅] ([WpSconfCsr.cpu_priv_pay_on]).  That is
   the "intr_on only with no lock held" rule as a typing constraint, and the
   scheduler is the one caller that can meet it -- its loop head, between the
   previous round's release and the next acquire, is precisely where the held
   set is empty. *)
Lemma sc_flip_pre `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (px : mword 64) (eb : bool) :
  cpu_own 0 eb px emp eb ∅ -∗
  (if eb then emp else intr_count 0 false) ∗
  (if eb then emp else cpu_priv 0 true px ∅).
Proof.
  destruct eb.
  - iIntros "_". iSplitR; done.
  - iIntros "H". iDestruct (sc_cpu_own_open with "H") as "(Hn & Hi & Hc & Hp & Hl & _)".
    iFrame "Hc". rewrite /cpu_priv /cpu_cells. iFrame "Hn Hi Hp Hl".
    iPureIntro. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)

Module SchedulerProof (Acquire : ACQUIRE) (Release : RELEASE) (Swtch : SWTCH) : SCHEDULER.

Section ProofScheduler.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* register indices, named once *)
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).

  (* ---- THE BLOCK STATEMENTS, NAMED (claude-notes/optimization.md, RULE
     ONE) -- [Tail]/[Scan]/[Outer] are each stated below as a bare (no
     [wp_next] wrapper: this whole span runs at the FIXED hart [cid_word] --
     the scheduler thread never migrates) [iAssert] whose body is tens of
     lines of ∀/wands; spelled out in place, EVERY proofmode step re-embeds
     that whole statement in the proof term (the cost is |Δ| times the
     number of steps it survives).  Naming the body turns each into a
     constant applied to [γs]/[av] -- the LEMMA's own binders, not section
     context, so unlike [GEN]/[CID] they must be threaded explicitly
     (optimization.md's "two limits").

     TRANSPARENT ON PURPOSE, same reason as every other file in this tree:
     the use sites below ([iSpecialize]/[iApply "Tail"/"Scan"/"Outer"/"IHo"])
     must unify through them without an extra [iEval (rewrite /X)].

     [Outer] is only ~13 statement lines -- borderline by the line-count
     rule alone -- but it is proved by [iLöb as "IHo"], so its IH is a full
     copy of the statement carried in [Δ] for the ENTIRE dispatch-loop tail
     of the proof (every step from +0x86 through the wfi/dispatch arms);
     folding shrinks that copy to one application, which is the dominant
     share of the win.  [IntrOn] (~10 statement lines, no Löb, no long
     tail) is UNDER the fold threshold and stays inline -- precedent:
     ProofDirlookup's file header records a 13-line body ruled the same
     way. *)

  Definition sc_tail_body (γs : list gname) (av : nat) : iProp Σ :=
    (∀ (jj : nat) (γl : gname) (Mt : regfile) (ebx : bool) (n : nat),
        ⌜(jj < NPROC)%nat⌝ -∗ ⌜γs !! jj = Some γl⌝ -∗
        (* [n] is the index the tail RETURNS at, i.e. the index that goes with
           the round's base enable [ebx] over the fixed carve [av - 10].  Its
           own entry is in-lock (arm [false]) and so at the carve itself. *)
        ⌜ (trap_res ebx + n)%nat = (av - 10)%nat ⌝ -∗
        ⌜ Mt !!! Regidx Rs1 = proc_addr jj
          /\ Mt !!! Regidx Rs2 = proc_addr NPROC
          /\ Mt !!! Regidx Rs3 = sign_extend' 64 RUNNABLE
          /\ add_vec (Mt !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
          /\ Mt !!! Regidx Rs6 = a_cpu_ctx cid_word
          /\ neq_vec (add_vec zero_reg (Mt !!! Regidx Rs7)) zero_reg = true
          /\ trunc32 (Mt !!! Regidx Rs8) = RUNNING ⌝ -∗
        ⌜ neq_vec (Mt !!! Regidx Rs5) zero_reg = false -> ebx = false ⌝ -∗
        (* the tail is entered holding proc jj's lock, i.e. at noff = 1, so
           the ambient SIE index is the literal [false] (CpuOwn.cpu_own_eb_agree)
           however the ROUND's base enable [ebx] came out. *)
        sie_cap_gpr Mt (av - 10)%nat false zero_reg -∗
        pc_is (mword_of_int (KernelSyms.scheduler + 0x4a)) -∗
        locked γl cpu_id -∗
        proc_lock_res γs γl (proc_addr jj) -∗
        (* THE SET IS {proc} ON THE WAY IN AND ∅ ON THE WAY OUT: the tail IS
           the release of proc jj's lock, so it is the one place in this file
           where the held set changes.  Every other [cpu_own] here is at one
           of those two literals. *)
        cpu_own 1 ebx zero_reg emp false {[lock_rank "proc"]} -∗
        trap_csrs -∗
        own_ctx (a_cpu_ctx cid_word) -∗
        ( ( ⌜(S jj < NPROC)%nat⌝ -∗ ∀ (Mn : regfile),
              ⌜ Mn !!! Regidx Rs1 = proc_addr (S jj)
                /\ Mn !!! Regidx Rs2 = proc_addr NPROC
                /\ Mn !!! Regidx Rs3 = sign_extend' 64 RUNNABLE
                /\ add_vec (Mn !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
                /\ Mn !!! Regidx Rs6 = a_cpu_ctx cid_word
                /\ neq_vec (add_vec zero_reg (Mn !!! Regidx Rs7)) zero_reg = true
                /\ trunc32 (Mn !!! Regidx Rs8) = RUNNING ⌝ -∗
              ⌜ neq_vec (Mn !!! Regidx Rs5) zero_reg = false -> ebx = false ⌝ -∗
              sie_cap_gpr Mn n ebx zero_reg -∗
              pc_is (mword_of_int (KernelSyms.scheduler + 0x58)) -∗
              cpu_own 0 ebx zero_reg emp ebx ∅ -∗
              (if ebx then emp else trap_csrs) -∗
              own_ctx (a_cpu_ctx cid_word) -∗
              WP (Loop : expr riscv_lang) )
          ∧ ( ∀ (Me : regfile),
              ⌜ add_vec (Me !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
                /\ Me !!! Regidx Rs6 = a_cpu_ctx cid_word
                /\ neq_vec (add_vec zero_reg (Me !!! Regidx Rs7)) zero_reg = true
                /\ trunc32 (Me !!! Regidx Rs8) = RUNNING ⌝ -∗
              ⌜ neq_vec (Me !!! Regidx Rs5) zero_reg = false -> ebx = false ⌝ -∗
              sie_cap_gpr Me n ebx zero_reg -∗
              pc_is (mword_of_int (KernelSyms.scheduler + 0x7e)) -∗
              cpu_own 0 ebx zero_reg emp ebx ∅ -∗
              (if ebx then emp else trap_csrs) -∗
              own_ctx (a_cpu_ctx cid_word) -∗
              WP (Loop : expr riscv_lang) ) ) -∗
        WP (Loop : expr riscv_lang))%I.

  (* fuel-indexed: [av]/[γs] as above; [fuel] is the recursion measure --
     kept as an explicit trailing parameter so the CALL site can keep
     [∀ fuel] visible (RULE 3) and [iInduction] leaves the IH folded. *)
  Definition sc_scan_body (γs : list gname) (av : nat) (fuel : nat) : iProp Σ :=
    (∀ (jj : nat) (M : regfile) (ebc : bool) (n : nat),
        ⌜(NPROC - jj <= fuel)%nat⌝ -∗ ⌜(jj < NPROC)%nat⌝ -∗
        (* the index that goes with this round's base enable over the fixed
           carve [av - 10] -- see the [sc_res_le]/[sc_idx_ok] header. *)
        ⌜ (trap_res ebc + n)%nat = (av - 10)%nat ⌝ -∗
        ⌜ M !!! Regidx Rs1 = proc_addr jj
          /\ M !!! Regidx Rs2 = proc_addr NPROC
          /\ M !!! Regidx Rs3 = sign_extend' 64 RUNNABLE
          /\ add_vec (M !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
          /\ M !!! Regidx Rs6 = a_cpu_ctx cid_word
          /\ neq_vec (add_vec zero_reg (M !!! Regidx Rs7)) zero_reg = true
          /\ trunc32 (M !!! Regidx Rs8) = RUNNING ⌝ -∗
        ⌜ neq_vec (M !!! Regidx Rs5) zero_reg = false -> ebc = false ⌝ -∗
        (* level 0: the ambient SIE index IS the base enable (cpu_own_eb_agree),
           so [ebc] and NOT a blanket [false]. *)
        sie_cap_gpr M n ebc zero_reg -∗
        pc_is (mword_of_int (KernelSyms.scheduler + 0x58)) -∗
        cpu_own 0 ebc zero_reg emp ebc ∅ -∗
        (if ebc then emp else trap_csrs) -∗
        own_ctx (a_cpu_ctx cid_word) -∗
        ( ∀ (Me : regfile) (eb2 : bool) (n2 : nat),
            ⌜ add_vec (Me !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
              /\ Me !!! Regidx Rs6 = a_cpu_ctx cid_word
              /\ neq_vec (add_vec zero_reg (Me !!! Regidx Rs7)) zero_reg = true
              /\ trunc32 (Me !!! Regidx Rs8) = RUNNING ⌝ -∗
            ⌜ neq_vec (Me !!! Regidx Rs5) zero_reg = false -> eb2 = false ⌝ -∗
            (* a dispatch may hand the round back at a DIFFERENT base enable,
               so the exit carries its own arm AND its own index. *)
            ⌜ (trap_res eb2 + n2)%nat = (av - 10)%nat ⌝ -∗
            sie_cap_gpr Me n2 eb2 zero_reg -∗
            pc_is (mword_of_int (KernelSyms.scheduler + 0x7e)) -∗
            cpu_own 0 eb2 zero_reg emp eb2 ∅ -∗
            (if eb2 then emp else trap_csrs) -∗
            own_ctx (a_cpu_ctx cid_word) -∗
            WP (Loop : expr riscv_lang) ) -∗
        WP (Loop : expr riscv_lang))%I.

  Definition sc_outer_body (av : nat) : iProp Σ :=
    (∀ (M : regfile) (eb : bool) (n : nat),
        ⌜ add_vec (M !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word
          /\ M !!! Regidx Rs6 = a_cpu_ctx cid_word
          /\ neq_vec (add_vec zero_reg (M !!! Regidx Rs7)) zero_reg = true
          /\ trunc32 (M !!! Regidx Rs8) = RUNNING ⌝ -∗
        (* the index that goes with the arm over the fixed carve [av - 10] *)
        ⌜ (trap_res eb + n)%nat = (av - 10)%nat ⌝ -∗
        sie_cap_gpr M n eb zero_reg -∗
        pc_is (mword_of_int (KernelSyms.scheduler + 0x86)) -∗
        cpu_own 0 eb zero_reg emp eb ∅ -∗
        (if eb then emp else trap_csrs) -∗
        own_ctx (a_cpu_ctx cid_word) -∗
        WP (Loop : expr riscv_lang))%I.

  Lemma wp_scheduler_sconf
      (γs : list gname) (m : regfile) (av : nat) (p0 : mword 64)
    : wp_scheduler_sconf_body γs m av p0.
  Proof.
    cbv beta delta [wp_scheduler_sconf_body].
    intros pcE Hp0 Hav. subst p0.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hpanic Hcsrs".
    iAssert (⌜length γs = NPROC⌝)%I as %Hlen.
    { iDestruct "Hprocs" as "[%H _]". iPureIntro. exact H. }
    (* split the entry cpu bundle: the context save area becomes [own_ctx],
       the slot becomes [emp], and the proc cell comes out for the c->proc
       store the setup block performs. *)
    iDestruct (sc_cpu_own_open with "Hcpu") as "(Hnoff & Hint & Hcnt & Hproc & Hlks & Hfree)".
    iDestruct "Hfree" as (ctx0) "[%Hctx0len Hctx0]".
    iAssert (own_ctx (a_cpu_ctx cid_word)) with "[Hctx0]" as "Hown".
    { rewrite /own_ctx. iExists ctx0. iSplit; [iPureIntro; exact Hctx0len | iExact "Hctx0"]. }
    (* ------------------------------------------------------------------ *)
    (* Prologue: 80-byte frame (push 10), save ra/s0..s8.                  *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))).
    iPoseProof (schi_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 59 : mword 6) m av 10 false
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* the ten frame slots *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _)".
    iDestruct "F1" as (u1) "Hf1". iDestruct "F2" as (u2) "Hf2".
    iDestruct "F3" as (u3) "Hf3". iDestruct "F4" as (u4) "Hf4".
    iDestruct "F5" as (u5) "Hf5". iDestruct "F6" as (u6) "Hf6".
    iDestruct "F7" as (u7) "Hf7". iDestruct "F8" as (u8) "Hf8".
    iDestruct "F9" as (u9) "Hf9". iDestruct "F10" as (u10) "Hf10".
    assert (Hb1  : pa_stk sp0 1  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb2  : pa_stk sp0 2  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb3  : pa_stk sp0 3  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb4  : pa_stk sp0 4  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb5  : pa_stk sp0 5  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb6  : pa_stk sp0 6  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb7  : pa_stk sp0 7  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb8  : pa_stk sp0 8  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb9  : pa_stk sp0 9  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    assert (Hb10 : pa_stk sp0 10 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (apply sc_frame_bridge; vm_compute; reflexivity).
    (* +0x02 c.sdsp ra,72 *)
    iPoseProof (schi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x02)) (mword_of_int 9 : mword 6) Rra
              A0 (av - 10)%nat u1 false with "Hcg Hpc Hi02 [Hf1]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hf1". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,64 *)
    iPoseProof (schi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x04)) (mword_of_int 8 : mword 6) Rs0
              A0 (av - 10)%nat u2 false with "Hcg Hpc Hi04 [Hf2]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hf2". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,56 *)
    iPoseProof (schi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x06)) (mword_of_int 7 : mword 6) Rs1
              A0 (av - 10)%nat u3 false with "Hcg Hpc Hi06 [Hf3]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hf3". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,48 *)
    iPoseProof (schi_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x08)) (mword_of_int 6 : mword 6) Rs2
              A0 (av - 10)%nat u4 false with "Hcg Hpc Hi08 [Hf4]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hf4". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a c.sdsp s3,40 *)
    iPoseProof (schi_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x0a)) (mword_of_int 5 : mword 6) Rs3
              A0 (av - 10)%nat u5 false with "Hcg Hpc Hi0a [Hf5]").
    { iEval (rewrite HcspA0 -Hb5). iExact "Hf5". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* +0x0c c.sdsp s4,32 *)
    iPoseProof (schi_0c with "Htext") as "Hi0c".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x0c)) (mword_of_int 4 : mword 6) Rs4
              A0 (av - 10)%nat u6 false with "Hcg Hpc Hi0c [Hf6]").
    { iEval (rewrite HcspA0 -Hb6). iExact "Hf6". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e c.sdsp s5,24 *)
    iPoseProof (schi_0e with "Htext") as "Hi0e".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x0e)) (mword_of_int 3 : mword 6) Rs5
              A0 (av - 10)%nat u7 false with "Hcg Hpc Hi0e [Hf7]").
    { iEval (rewrite HcspA0 -Hb7). iExact "Hf7". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10 c.sdsp s6,16 *)
    iPoseProof (schi_10 with "Htext") as "Hi10".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x10)) (mword_of_int 2 : mword 6) Rs6
              A0 (av - 10)%nat u8 false with "Hcg Hpc Hi10 [Hf8]").
    { iEval (rewrite HcspA0 -Hb8). iExact "Hf8". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* +0x12 c.sdsp s7,8 *)
    iPoseProof (schi_12 with "Htext") as "Hi12".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x12)) (mword_of_int 1 : mword 6) Rs7
              A0 (av - 10)%nat u9 false with "Hcg Hpc Hi12 [Hf9]").
    { iEval (rewrite HcspA0 -Hb9). iExact "Hf9". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* +0x14 c.sdsp s8,0 *)
    iPoseProof (schi_14 with "Htext") as "Hi14".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.scheduler + 0x14)) (mword_of_int 0 : mword 6) Rs8
              A0 (av - 10)%nat u10 false with "Hcg Hpc Hi14 [Hf10]").
    { iEval (rewrite HcspA0 -Hb10). iExact "Hf10". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc _".
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* +0x16 c.addi4spn s0,sp,80 -- the frame pointer, a dead value here *)
    iPoseProof (schi_16 with "Htext") as "Hi16".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.scheduler + 0x16)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 A0 (av - 10)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi16").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> A0) with A1.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* tp is PINNED to the hart now (HartTp.v): the entry premise
       [m !!! x4 = cid_word] is gone and [rget _ Rtp] is this hart's id by
       construction, at every map. *)
    (* ------------------------------------------------------------------ *)
    (* +0x18..+0x1c: a5 := sextw(tp); s6 := 128*a5 = mycpu_a5.            *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (schi_18 with "Htext") as "Hi18".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.scheduler + 0x18)) Ra5 Rtp A1 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    (* NO [rgne] here: the source register IS tp, so the written value stays
       spelled [rget A1 Rtp] and [rget_tp] is what reads it. *)
    set (A2 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A1 Rtp))]> A1).
    change (<[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A1 Rtp))]> A1) with A2.
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a sext.w a5 *)
    iPoseProof (schi_1a with "Htext") as "Hi1a".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.scheduler + 0x1a)) Ra5 (mword_of_int 0 : mword 6)
              A2 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A3 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (A2 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> A2).
    change (<[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (A2 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> A2) with A3.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    assert (HA3a5 : A3 !!! Regidx Ra5
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec (add_vec zero_reg cid_word)
                                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)).
    { rewrite /A3 upd_eq /A2 upd_eq (rget_tp A1). reflexivity. }
    (* +0x1c slli s6,a5,7 *)
    iPoseProof (schi_1c with "Htext") as "Hi1c".
    assert (HA3a5r : rget A3 Ra5
                    = sign_extend' 64 (subrange_vec_dec
                        (add_vec (add_vec zero_reg cid_word)
                                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))
      by (rgne; exact HA3a5).
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x1c)) Rs6 Ra5 (mword_of_int 7 : mword 6)
              (mycpu_a5 cid_word) A3 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite HA3a5r; reflexivity)
              with "Hcg Hpc Hi1c").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx Rs6 := regval_into_reg (mycpu_a5 cid_word)]> A3).
    change (<[Regidx Rs6 := regval_into_reg (mycpu_a5 cid_word)]> A3) with A4.
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    assert (HA4s6 : A4 !!! Regidx Rs6 = mycpu_a5 cid_word) by (rewrite /A4 upd_eq; reflexivity).
    (* ------------------------------------------------------------------ *)
    (* +0x20..+0x2a: c->proc = 0.                                         *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (schi_20 with "Htext") as "Hi20".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.scheduler + 0x20)) Ra4 (mword_of_int 0x10 : mword 20)
              A4 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A5 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A4).
    change (<[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A4) with A5.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24 addi a4,a4,1454 *)
    iPoseProof (schi_24 with "Htext") as "Hi24".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x24)) Ra4 Ra4 (mword_of_int 1584 : mword 12)
              A5 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A6 := <[Regidx Ra4 := regval_into_reg
        (add_vec (A5 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1584 : mword 12)))]> A5).
    change (<[Regidx Ra4 := regval_into_reg
        (add_vec (A5 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1584 : mword 12)))]> A5) with A6.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HA6a4 : A6 !!! Regidx Ra4
                    = add_vec (add_vec (mword_of_int (KernelSyms.scheduler + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                              (sign_extend' 64 (mword_of_int 1584 : mword 12)))
      by (rewrite /A6 upd_eq /A5 upd_eq; reflexivity).
    assert (HA6s6 : A6 !!! Regidx Rs6 = mycpu_a5 cid_word).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate]. exact HA4s6. }
    (* +0x28 c.add a4,a4,s6 *)
    iPoseProof (schi_28 with "Htext") as "Hi28".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.scheduler + 0x28)) Ra4 Rs6 A6 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A7 := <[Regidx Ra4 := regval_into_reg (add_vec (A6 !!! Regidx Ra4) (A6 !!! Regidx Rs6))]> A6).
    change (<[Regidx Ra4 := regval_into_reg (add_vec (A6 !!! Regidx Ra4) (A6 !!! Regidx Rs6))]> A6) with A7.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    assert (Hrec_proc0 : add_vec (A7 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                         = a_cpu_proc cid_word).
    { rewrite /A7 upd_eq HA6a4 HA6s6.
      unfold a_cpu_proc, mycpu_ret. apply sc_reconcile.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x2a sd zero,48(a4) -- the leaf's [pa] reads its base through [rget],
       so the address fact has to be respelled once (guide: derive the twin
       UP FRONT rather than splicing [rgne] into the [iEval] chain). *)
    assert (Hrec_proc0r : add_vec (rget A7 Ra4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                          = a_cpu_proc cid_word) by (rgne; exact Hrec_proc0).
    iPoseProof (schi_2a with "Htext") as "Hi2a".
    (* A PLAIN STORE.  [cpus[cid].proc] is private to this hart -- no
       invariant and no lock holds a fraction of it -- so [IntrDefs.cpu_cells]
       carries the WHOLE cell and the store neither opens anything nor
       changes the mask. *)
    iApply (wp_sd_zero_s_sconf (mword_of_int (KernelSyms.scheduler + 0x2a))
              Ra4 (mword_of_int 48 : mword 12)
              A7 (av - 10)%nat zero_reg false
              with "Hcg Hpc Hi2a [Hproc]").
    { iEval (rewrite Hrec_proc0r). iExact "Hproc". }
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc Hproc".
    iEval (rewrite Hrec_proc0r) in "Hproc".
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x2e..+0x36: s6 := &c->context.                                   *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (schi_2e with "Htext") as "Hi2e".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.scheduler + 0x2e)) Ra4 (mword_of_int 0x10 : mword 20)
              A7 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A8 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x2e) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A7).
    change (<[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x2e) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A7) with A8.
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* +0x32 addi a4,a4,1496 *)
    iPoseProof (schi_32 with "Htext") as "Hi32".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x32)) Ra4 Ra4 (mword_of_int 1626 : mword 12)
              A8 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A9 := <[Regidx Ra4 := regval_into_reg
        (add_vec (A8 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1626 : mword 12)))]> A8).
    change (<[Regidx Ra4 := regval_into_reg
        (add_vec (A8 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1626 : mword 12)))]> A8) with A9.
    assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    assert (HA9a4 : A9 !!! Regidx Ra4
                    = add_vec (add_vec (mword_of_int (KernelSyms.scheduler + 0x2e) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                              (sign_extend' 64 (mword_of_int 1626 : mword 12)))
      by (rewrite /A9 upd_eq /A8 upd_eq; reflexivity).
    assert (HA9s6 : A9 !!! Regidx Rs6 = mycpu_a5 cid_word).
    { rewrite /A9 upd_ne; [| vm_compute; discriminate].
      rewrite /A8 upd_ne; [| vm_compute; discriminate].
      rewrite /A7 upd_ne; [| vm_compute; discriminate]. exact HA6s6. }
    (* +0x36 c.add s6,s6,a4 *)
    iPoseProof (schi_36 with "Htext") as "Hi36".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.scheduler + 0x36)) Rs6 Ra4 A9 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A10 := <[Regidx Rs6 := regval_into_reg (add_vec (A9 !!! Regidx Rs6) (A9 !!! Regidx Ra4))]> A9).
    change (<[Regidx Rs6 := regval_into_reg (add_vec (A9 !!! Regidx Rs6) (A9 !!! Regidx Ra4))]> A9) with A10.
    assert (Hpc38 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    assert (HA10s6 : A10 !!! Regidx Rs6 = a_cpu_ctx cid_word).
    { rewrite /A10 upd_eq HA9s6 HA9a4.
      unfold a_cpu_ctx, mycpu_ret. apply sc_reconcile2.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x38 c.li s8,4 (RUNNING) *)
    iPoseProof (schi_38 with "Htext") as "Hi38".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x38)) Rs8 (mword_of_int 4 : mword 6)
              (sign_extend' 64 (RUNNING : mword 32)) A10 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi38").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A11 := <[Regidx Rs8 := regval_into_reg (sign_extend' 64 (RUNNING : mword 32))]> A10).
    change (<[Regidx Rs8 := regval_into_reg (sign_extend' 64 (RUNNING : mword 32))]> A10) with A11.
    assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3a) in "Hpc".
    assert (HA11a5 : A11 !!! Regidx Ra5
                     = sign_extend' 64 (subrange_vec_dec
                         (add_vec (add_vec zero_reg cid_word)
                                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)).
    { rewrite /A11 upd_ne; [| vm_compute; discriminate].
      rewrite /A10 upd_ne; [| vm_compute; discriminate].
      rewrite /A9 upd_ne; [| vm_compute; discriminate].
      rewrite /A8 upd_ne; [| vm_compute; discriminate].
      rewrite /A7 upd_ne; [| vm_compute; discriminate].
      rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. exact HA3a5. }
    (* +0x3a c.slli a5,7 *)
    iPoseProof (schi_3a with "Htext") as "Hi3a".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x3a)) (Regidx Ra5) Ra5 (mword_of_int 7 : mword 6)
              A11 (av - 10)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A12 := <[Regidx Ra5 := regval_into_reg
        (shift_bits_left (A11 !!! Regidx Ra5) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> A11).
    change (<[Regidx Ra5 := regval_into_reg
        (shift_bits_left (A11 !!! Regidx Ra5) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> A11) with A12.
    assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    assert (HA12a5 : A12 !!! Regidx Ra5 = mycpu_a5 cid_word)
      by (rewrite /A12 upd_eq HA11a5; reflexivity).
    (* +0x3c auipc s4,0x10 *)
    iPoseProof (schi_3c with "Htext") as "Hi3c".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.scheduler + 0x3c)) Rs4 (mword_of_int 0x10 : mword 20)
              A12 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A13 := <[Regidx Rs4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x3c) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A12).
    change (<[Regidx Rs4 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.scheduler + 0x3c) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> A12) with A13.
    assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc40) in "Hpc".
    (* +0x40 addi s4,s4,1426 *)
    iPoseProof (schi_40 with "Htext") as "Hi40".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x40)) Rs4 Rs4 (mword_of_int 1556 : mword 12)
              A13 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A14 := <[Regidx Rs4 := regval_into_reg
        (add_vec (A13 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 1556 : mword 12)))]> A13).
    change (<[Regidx Rs4 := regval_into_reg
        (add_vec (A13 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 1556 : mword 12)))]> A13) with A14.
    assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc44) in "Hpc".
    assert (HA14s4 : A14 !!! Regidx Rs4
                     = add_vec (add_vec (mword_of_int (KernelSyms.scheduler + 0x3c) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                               (sign_extend' 64 (mword_of_int 1556 : mword 12)))
      by (rewrite /A14 upd_eq /A13 upd_eq; reflexivity).
    assert (HA14a5 : A14 !!! Regidx Ra5 = mycpu_a5 cid_word).
    { rewrite /A14 upd_ne; [| vm_compute; discriminate].
      rewrite /A13 upd_ne; [| vm_compute; discriminate]. exact HA12a5. }
    (* +0x44 c.add s4,s4,a5 *)
    iPoseProof (schi_44 with "Htext") as "Hi44".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.scheduler + 0x44)) Rs4 Ra5 A14 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (A15 := <[Regidx Rs4 := regval_into_reg (add_vec (A14 !!! Regidx Rs4) (A14 !!! Regidx Ra5))]> A14).
    change (<[Regidx Rs4 := regval_into_reg (add_vec (A14 !!! Regidx Rs4) (A14 !!! Regidx Ra5))]> A14) with A15.
    assert (Hpc46 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc46) in "Hpc".
    assert (HA15s4 : add_vec (A15 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                     = a_cpu_proc cid_word).
    { rewrite /A15 upd_eq HA14s4 HA14a5.
      unfold a_cpu_proc, mycpu_ret. apply sc_reconcile.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x46 c.li s7,1 *)
    iPoseProof (schi_46 with "Htext") as "Hi46".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x46)) Rs7 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) A15 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi46").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iIntros "Hcg Hpc".
    set (A16 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> A15).
    change (<[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> A15) with A16.
    assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc48) in "Hpc".
    (* the five loop-head pins, established once at [A16]. *)
    assert (HP_s4 : add_vec (A16 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                    = a_cpu_proc cid_word).
    { rewrite /A16 upd_ne; [| vm_compute; discriminate]. exact HA15s4. }
    assert (HP_s6 : A16 !!! Regidx Rs6 = a_cpu_ctx cid_word).
    { rewrite /A16 upd_ne; [| vm_compute; discriminate].
      rewrite /A15 upd_ne; [| vm_compute; discriminate].
      rewrite /A14 upd_ne; [| vm_compute; discriminate].
      rewrite /A13 upd_ne; [| vm_compute; discriminate].
      rewrite /A12 upd_ne; [| vm_compute; discriminate].
      rewrite /A11 upd_ne; [| vm_compute; discriminate]. exact HA10s6. }
    assert (HP_s7 : neq_vec (add_vec zero_reg (A16 !!! Regidx Rs7)) zero_reg = true).
    { rewrite /A16 upd_eq. vm_compute. reflexivity. }
    assert (HP_s8 : trunc32 (A16 !!! Regidx Rs8) = RUNNING).
    { rewrite /A16 upd_ne; [| vm_compute; discriminate].
      rewrite /A15 upd_ne; [| vm_compute; discriminate].
      rewrite /A14 upd_ne; [| vm_compute; discriminate].
      rewrite /A13 upd_ne; [| vm_compute; discriminate].
      rewrite /A12 upd_ne; [| vm_compute; discriminate].
      rewrite /A11 upd_eq. apply trunc32_sext64. }
    (* (the tp pin is no longer a fact about the MAP -- see HartTp.v -- so
       the sixth loop-head pin is simply gone.) *)
    (* refold the cpu bundle at [zero_reg] with an [emp] context slot. *)
    iAssert (cpu_own 0 false zero_reg emp false ∅) with "[Hnoff Hint Hcnt Hproc Hlks]" as "Hcpu".
    { iApply (sc_cpu_own_mk with "Hnoff Hint Hcnt Hproc Hlks"). }
    (* ================================================================== *)
    (* THE RELEASE TAIL, +0x4a..+0x54, over an arbitrary arrival map.      *)
    (* ================================================================== *)
    iAssert (□ sc_tail_body γs av)%I
      with "[]" as "#Tail".
    { iModIntro.
      iIntros (jj γl Mt ebx n) "%Hjj %Hgl %Hn %Hpins %Htie Hcg Hpc Hlocked HR Hcpu Hcsrs Hown Hcont".
      destruct Hpins as (Hp1 & Hp2 & Hp3 & Hp4 & Hp6 & Hp7 & Hp8).
      iPoseProof (procs_inv_lookup γs jj γl Hgl with "Hprocs") as "#Hislock".
      iPoseProof (schi_4a with "Htext") as "Hi4a".
      iPoseProof (schi_4c with "Htext") as "Hi4c".
      iPoseProof (schi_50 with "Htext") as "Hi50".
      iPoseProof (schi_54 with "Htext") as "Hi54".
      (* +0x4a c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.scheduler + 0x4a)) Ra0 Rs1 Mt (av - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4a").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs1))]> Mt).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs1))]> Mt) with T0.
      assert (Hq4c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq4c) in "Hpc".
      (* +0x4c jal release *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.scheduler + 0x4c)) Rra (mword_of_int 2092702 : mword 21)
                T0 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4c").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (T1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x4c) : mword 64) 4)]> T0).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x4c) : mword 64) 4)]> T0) with T1.
      assert (Hqrl : add_vec (mword_of_int (KernelSyms.scheduler + 0x4c) : mword 64) (sign_extend' 64 (mword_of_int 2092702 : mword 21))
                     = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqrl) in "Hpc".
      assert (HT1ra : T1 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.scheduler + 0x4c) : mword 64) 4)
        by (rewrite /T1 upd_eq; reflexivity).
      assert (HT1a0 : T1 !!! Regidx Ra0 = add_vec zero_reg (proc_addr jj)).
      { rewrite /T1 upd_ne; [| vm_compute; discriminate]. rewrite /T0 upd_eq Hp1. reflexivity. }
      assert (Hlka : add_vec (T1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr jj).
      { rewrite HT1a0 add_vec_zero_l. apply addv_sext0. }
      (* trap_csrs -> release's [arm_pay 0 ebx zero_reg] + the loop's
         complement.  The claim half is the IDLE one: the scheduler runs with
         [c->proc == 0], so it mints what the arm is owed for free. *)
      iAssert (arm_pay 0 ebx zero_reg ∗ (if ebx then emp else trap_csrs))%I
        with "[Hcsrs]" as "[Hpay Hcsrs]".
      { rewrite /arm_pay /trap_csrs_pay /cpu_claim_pay. destruct ebx.
        - iSplitL "Hcsrs"; [ iFrame "Hcsrs"; iApply cpu_claim_idle | done ].
        - iSplitR "Hcsrs"; [ iSplit; done | iExact "Hcsrs" ]. }
      (* THE RELEASE THAT MAY RE-ENABLE.  It pops to level 0, so its exit arm
         is the round's base enable [ebx] -- and at [ebx = true] it turns
         interrupts back on, which means its ENTRY index must show the reserve
         explicitly ([trap_res ebx + n]).  [Hn] is exactly that re-spelling of
         the in-lock carve [av - 10]; its exit is [n], the index the tail owes
         its caller. *)
      iEval (rewrite -Hn) in "Hcg".
      iApply (Release.wp_release_sconf γl (proc_addr jj) "proc"%string
                (proc_lock_res γs γl (proc_addr jj)) T1 0 ebx zero_reg emp n
                {[lock_rank "proc"]}
                Hlka ltac:(pose proof (sc_res_le ebx); lia)
                with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
      (* release's crossing index is its EXIT index [outb = ebx] -- it re-enables
         at its last instruction -- and the scheduler thread has no proc, so the
         idle hatch collapses it. *)
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros (mr) "Hcg Hpc %Hcsrl Hcpu".
      (* the release drops the ONE rank this loop iteration took, so the round
         re-enters the loop head at the empty set -- which is what the next
         [intr_on] (and [sc_flip_pre]) requires. *)
      assert (Heqrel : ({[lock_rank "proc"]} : gset nat) ∖ {[lock_rank "proc"]} = ∅)
        by (apply locks_self_del).
      iEval (rewrite Heqrel) in "Hcpu".
      assert (Hq50 : ret_pc (T1 !!! Regidx Rra) = mword_of_int (KernelSyms.scheduler + 0x50))
        by (rewrite HT1ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq50) in "Hpc".
      (* the callee-saved pins survive release *)
      assert (Hmr : forall c : mword 5, is_cs_idx c = true -> mr !!! Regidx c = Mt !!! Regidx c).
      { intros c Hc. rewrite (callee_saved_lookup Hcsrl c Hc).
        rewrite /T1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
        rewrite /T0 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
        reflexivity. }
      assert (Hmr1 : mr !!! Regidx Rs1 = proc_addr jj)
        by (rewrite (Hmr Rs1 ltac:(vm_compute; reflexivity)); exact Hp1).
      (* +0x50 addi s1,s1,360 *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x50)) Rs1 Rs1 (mword_of_int 360 : mword 12)
                mr n ebx ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi50").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (T2 := <[Regidx Rs1 := regval_into_reg
          (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mr).
      change (<[Regidx Rs1 := regval_into_reg
          (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mr) with T2.
      assert (Hq54 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq54) in "Hpc".
      assert (Hsucc : add_vec (proc_addr jj) (sign_extend' 64 (mword_of_int 360 : mword 12)) = proc_addr (S jj))
        by exact (proc_addr_succ jj).
      assert (HT2s1 : T2 !!! Regidx Rs1 = proc_addr (S jj))
        by (rewrite /T2 upd_eq Hmr1; exact Hsucc).
      assert (HT2 : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
                      T2 !!! Regidx c = Mt !!! Regidx c).
      { intros c Hc Hne. rewrite /T2 upd_ne.
        - exact (Hmr c Hc).
        - intro He. injection He as He'. exact (Hne He'). }
      assert (HT2s2 : T2 !!! Regidx Rs2 = proc_addr NPROC)
        by (rewrite (HT2 Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp2).
      assert (HT2s3 : T2 !!! Regidx Rs3 = sign_extend' 64 RUNNABLE)
        by (rewrite (HT2 Rs3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp3).
      assert (HT2s4 : add_vec (T2 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word)
        by (rewrite (HT2 Rs4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp4).
      assert (HT2s5 : T2 !!! Regidx Rs5 = Mt !!! Regidx Rs5)
        by (rewrite (HT2 Rs5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); reflexivity).
      assert (HT2s6 : T2 !!! Regidx Rs6 = a_cpu_ctx cid_word)
        by (rewrite (HT2 Rs6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp6).
      assert (HT2s7 : neq_vec (add_vec zero_reg (T2 !!! Regidx Rs7)) zero_reg = true)
        by (rewrite (HT2 Rs7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp7).
      assert (HT2s8 : trunc32 (T2 !!! Regidx Rs8) = RUNNING)
        by (rewrite (HT2 Rs8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hp8).
      (* +0x54 beq s1,s2 : the scan's end test *)
      destruct (decide (S jj = NPROC)) as [Hend | Hne].
      - (* scan finished: branch TAKEN to +0x7e *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.scheduler + 0x54)) (mword_of_int 42 : mword 13)
                  Rs2 Rs1 T2 n ebx
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(repeat rgne; rewrite HT2s1 HT2s2 Hend; apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi54").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hq7e : add_vec (mword_of_int (KernelSyms.scheduler + 0x54) : mword 64) (sign_extend' 64 (mword_of_int 42 : mword 13))
                       = mword_of_int (KernelSyms.scheduler + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq7e) in "Hpc".
        iDestruct "Hcont" as "[_ Hexit]".
        iApply ("Hexit" $! T2 with "[%] [%] Hcg Hpc Hcpu Hcsrs Hown").
        { split_and!; assumption. }
        { rewrite HT2s5. exact Htie. }
      - (* keep scanning: branch FALLS to +0x58 *)
        assert (HSjj : (S jj < NPROC)%nat) by lia.
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.scheduler + 0x54)) (mword_of_int 42 : mword 13)
                  Rs2 Rs1 T2 n ebx
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(repeat rgne; rewrite HT2s1 HT2s2; apply sc_eq_vec_ne;
                        exact (sc_proc_addr_ne_end (S jj) HSjj))
                  with "Hcg Hpc Hi54").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        assert (Hq58 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x54) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x58))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq58) in "Hpc".
        iDestruct "Hcont" as "[Hnext _]".
        iApply ("Hnext" with "[%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown").
        { exact HSjj. }
        { split_and!; assumption. }
        { rewrite HT2s5. exact Htie. } }
    (* ================================================================== *)
    (* THE INNER SCAN, entry +0x58, fuel induction on the remaining count. *)
    (* ================================================================== *)
    iAssert (□ ( ∀ fuel : nat, sc_scan_body γs av fuel))%I
      with "[]" as "#Scan".
    { iModIntro. iIntros (fuel). iInduction fuel as [|fuel IH] "IH";
        iIntros (jj M ebc n) "%Hfuel %Hjj %Hn %Hpins %Htie Hcg Hpc Hcpu Hcsrs Hown Hexit".
      { exfalso. unfold NPROC in *. lia. }
      destruct Hpins as (Hp1 & Hp2 & Hp3 & Hp4 & Hp6 & Hp7 & Hp8).
      assert (Hex : is_Some (γs !! jj)) by (apply lookup_lt_is_Some_2; rewrite Hlen; exact Hjj).
      destruct Hex as [γl Hgl].
      iPoseProof (procs_inv_lookup γs jj γl Hgl with "Hprocs") as "#Hislock".
      iPoseProof (schi_58 with "Htext") as "Hi58".
      iPoseProof (schi_5a with "Htext") as "Hi5a".
      iPoseProof (schi_5e with "Htext") as "Hi5e".
      iPoseProof (schi_60 with "Htext") as "Hi60".
      (* +0x58 c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.scheduler + 0x58)) Ra0 Rs1 M n ebc
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi58").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (M0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with M0.
      assert (Hr5a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hr5a) in "Hpc".
      (* +0x5a jal acquire *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.scheduler + 0x5a)) Rra (mword_of_int 2092552 : mword 21)
                M0 n ebc ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5a").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (M1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x5a) : mword 64) 4)]> M0).
      change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x5a) : mword 64) 4)]> M0) with M1.
      assert (Hraq : add_vec (mword_of_int (KernelSyms.scheduler + 0x5a) : mword 64) (sign_extend' 64 (mword_of_int 2092552 : mword 21))
                     = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hraq) in "Hpc".
      assert (HM1ra : M1 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.scheduler + 0x5a) : mword 64) 4)
        by (rewrite /M1 upd_eq; reflexivity).
      assert (HM1a0 : M1 !!! Regidx Ra0 = proc_addr jj).
      { rewrite /M1 upd_ne; [| vm_compute; discriminate].
        rewrite /M0 upd_eq Hp1. apply add_vec_zero_l. }
      (* ================================================================ *)
      (* THE ONE OPEN SEAM (report, not a proof gap): [SpecAcquire] now    *)
      (* demands [panic_wp_any] (the hart-GENERIC form, propagated to 23   *)
      (* contracts in 7865e4e), while [SpecScheduler]'s premise is still   *)
      (* the AMBIENT [panic_wp] -- 990544b explicitly kept it ambient      *)
      (* ("scheduler never migrates"), which is true but irrelevant: the   *)
      (* resource acquire asks for is [□ ∀ h, panic_wp (CID := h)] and     *)
      (* nothing derives that from one hart's copy.  Fix (one line each,   *)
      (* both outside this file's scope): [SpecScheduler]'s [panic_wp] ->  *)
      (* [panic_wp_any], and [ProofMain]/[ProofMainSecondary] pass their   *)
      (* existing [Hpany] instead of the [panic_wp_any_at cpu_id]          *)
      (* downgrade.  Verified: with that single substitution this file     *)
      (* compiles clean end to end.                                        *)
      (* ================================================================ *)
      (* the loop-head set is EMPTY (the previous iteration's release emptied
         it, and [intr_on] at +0x86 could not have run otherwise), so acquire's
         order premise is [locks_below ∅ (lock_rank "proc")] -- the degenerate
         case, [LockRank.locks_below_empty].  This acquire is what PRODUCES the
         {proc} set that the c->proc store, the swtch and [sched]'s own
         contract all carry. *)
      assert (Hnoproc : locks_below (∅ : gset nat) (lock_rank "proc"))
        by (exact (locks_below_empty (lock_rank "proc"))).
      iApply (Acquire.wp_acquire_sconf γl "proc"%string
                (proc_lock_res γs γl (proc_addr jj)) M1 0 ebc zero_reg emp n ebc ∅
                ltac:(lia) ltac:(pose proof (sc_res_le ebc); lia) Hnoproc
                with "Hcg Hcpu Htext Hpc [Hislock] Hpanic").
      all: try lkbelow.
      { iEval (rewrite HM1a0). iExact "Hislock". }
      (* acquire's crossing index is its ENTRY [ebc] (a trap can land on its
         first instruction, before push_off disables) -- idle hatch again. *)
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros (msq macq) "%Hmsfq Hcg Hpc %Hcsaq Hlocked HR Hcpu Hpay".
      (* acquire hands back [{[rank "proc"]} ∪ ∅]; normalise it to the literal
         singleton every in-lock site below (and [Tail]) is written at. *)
      assert (Hequn : ({[lock_rank "proc"]} : gset nat) ∪ ∅ = {[lock_rank "proc"]})
        by (apply locks_union_empty).
      iEval (rewrite Hequn) in "Hcpu".
      (* acquire's push_off folded the reserve back into the usable count, so
         the in-lock index is the full carve [av - 10] -- that is exactly what
         [Hn] says, and every in-lock site below is written at it. *)
      iEval (rewrite Hn) in "Hcg".
      assert (Hr5e : ret_pc (M1 !!! Regidx Rra) = mword_of_int (KernelSyms.scheduler + 0x5e))
        by (rewrite HM1ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hr5e) in "Hpc".
      (* after any acquire the scheduler holds [trap_csrs] UNCONDITIONALLY *)
      (* the claim half of [arm_pay] is dropped: the scheduler runs at
         [c->proc == 0], so what it owes back at the next intr_on is the IDLE
         claim, which [cpu_claim_idle] re-mints for free. *)
      iAssert trap_csrs with "[Hcsrs Hpay]" as "Hcsrs".
      { destruct ebc; [ iDestruct "Hpay" as "[$ _]" | iExact "Hcsrs" ]. }
      (* the callee-saved pins survive acquire *)
      assert (Hmq : forall c : mword 5, is_cs_idx c = true -> macq !!! Regidx c = M !!! Regidx c).
      { intros c Hc. rewrite (callee_saved_lookup Hcsaq c Hc).
        rewrite /M1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
        rewrite /M0 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
        reflexivity. }
      assert (Hq1 : macq !!! Regidx Rs1 = proc_addr jj)
        by (rewrite (Hmq Rs1 ltac:(vm_compute; reflexivity)); exact Hp1).
      (* unpack the lock resource *)
      iDestruct (proc_lock_res_elim γs γl (proc_addr jj) with "HR")
        as (st ch) "(Hstate & Hpg & Hchan & Hpub & Hslot)".
      (* +0x5e c.lw a5,24(s1) : read p->state *)
      assert (Hrec_st : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = p_state (proc_addr jj)) by (rgne; rewrite Hq1; apply sc_state_addr).
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.scheduler + 0x5e)) Ra5 Rs1 (mword_of_int 24 : mword 12)
                macq (av - 10)%nat st false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi5e [Hstate]").
      { iEval (rewrite Hrec_st). iExact "Hstate". }
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc Hstate".
      iEval (rewrite Hrec_st) in "Hstate".
      set (M2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 st)]> macq).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 st)]> macq) with M2.
      assert (Hr60 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hr60) in "Hpc".
      assert (HM2a5 : M2 !!! Regidx Ra5 = sign_extend' 64 st) by (rewrite /M2 upd_eq; reflexivity).
      assert (HM2 : forall c : mword 5, is_cs_idx c = true -> M2 !!! Regidx c = M !!! Regidx c).
      { intros c Hc. rewrite /M2 upd_ne.
        - exact (Hmq c Hc).
        - apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]. }
      assert (HM2s1 : M2 !!! Regidx Rs1 = proc_addr jj)
        by (rewrite (HM2 Rs1 ltac:(vm_compute; reflexivity)); exact Hp1).
      assert (HM2s2 : M2 !!! Regidx Rs2 = proc_addr NPROC)
        by (rewrite (HM2 Rs2 ltac:(vm_compute; reflexivity)); exact Hp2).
      assert (HM2s3 : M2 !!! Regidx Rs3 = sign_extend' 64 RUNNABLE)
        by (rewrite (HM2 Rs3 ltac:(vm_compute; reflexivity)); exact Hp3).
      assert (HM2s4 : add_vec (M2 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word)
        by (rewrite (HM2 Rs4 ltac:(vm_compute; reflexivity)); exact Hp4).
      assert (HM2s5 : M2 !!! Regidx Rs5 = M !!! Regidx Rs5)
        by (rewrite (HM2 Rs5 ltac:(vm_compute; reflexivity)); reflexivity).
      assert (HM2s6 : M2 !!! Regidx Rs6 = a_cpu_ctx cid_word)
        by (rewrite (HM2 Rs6 ltac:(vm_compute; reflexivity)); exact Hp6).
      assert (HM2s7 : neq_vec (add_vec zero_reg (M2 !!! Regidx Rs7)) zero_reg = true)
        by (rewrite (HM2 Rs7 ltac:(vm_compute; reflexivity)); exact Hp7).
      assert (HM2s8 : trunc32 (M2 !!! Regidx Rs8) = RUNNING)
        by (rewrite (HM2 Rs8 ltac:(vm_compute; reflexivity)); exact Hp8).
      (* +0x60 bne a5,s3 : the RUNNABLE test *)
      destruct (neq_vec (sign_extend' 64 st) (sign_extend' 64 RUNNABLE)) eqn:Hcmp.
      - (* not RUNNABLE: skip straight to the release tail at +0x4a *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.scheduler + 0x60)) (mword_of_int 8170 : mword 13)
                  Rs3 Ra5 M2 (av - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(repeat rgne; rewrite HM2a5 HM2s3; exact Hcmp)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi60").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hr4a : add_vec (mword_of_int (KernelSyms.scheduler + 0x60) : mword 64) (sign_extend' 64 (mword_of_int 8170 : mword 13))
                       = mword_of_int (KernelSyms.scheduler + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr4a) in "Hpc".
        (* the slot goes back UNTOUCHED *)
        iAssert (proc_lock_res γs γl (proc_addr jj)) with "[Hstate Hpg Hchan Hpub Hslot]" as "HR".
        { rewrite /proc_lock_res. iExists st, ch. iFrame "Hstate Hpg Hchan Hpub Hslot". }
        iApply ("Tail" $! jj γl M2 ebc n with "[%] [%] [%] [%] [%] Hcg Hpc Hlocked HR Hcpu Hcsrs Hown").
        { exact Hjj. }
        { exact Hgl. }
        { exact Hn. }
        { split_and!; assumption. }
        { rewrite HM2s5. exact Htie. }
        iSplit.
        + iIntros (HSjj Mn) "%HpinsN %HtieN Hcg Hpc Hcpu Hcsrs Hown".
          iApply ("IH" $! (S jj) Mn ebc n with "[%] [%] [%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown Hexit").
          { unfold NPROC in *. lia. }
          { exact HSjj. }
          { exact Hn. }
          { exact HpinsN. }
          { exact HtieN. }
        + iIntros (Me) "%HpinsE %HtieE Hcg Hpc Hcpu Hcsrs Hown".
          iApply ("Hexit" $! Me ebc n with "[%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown");
            [ exact HpinsE | exact HtieE | exact Hn ].
      - (* RUNNABLE: dispatch it *)
        assert (Hst : st = RUNNABLE)
          by (apply sext64_32_inj; apply (sc_neq_vec_false 64); exact Hcmp).
        subst st.
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.scheduler + 0x60)) (mword_of_int 8170 : mword 13)
                  Rs3 Ra5 M2 (av - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(repeat rgne; rewrite HM2a5 HM2s3; exact Hcmp)
                  with "Hcg Hpc Hi60").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        assert (Hr64 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x64))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr64) in "Hpc".
        iPoseProof (schi_64 with "Htext") as "Hi64".
        iPoseProof (schi_68 with "Htext") as "Hi68".
        iPoseProof (schi_6c with "Htext") as "Hi6c".
        iPoseProof (schi_70 with "Htext") as "Hi70".
        iPoseProof (schi_72 with "Htext") as "Hi72".
        iPoseProof (schi_76 with "Htext") as "Hi76".
        iPoseProof (schi_7a with "Htext") as "Hi7a".
        iPoseProof (schi_7c with "Htext") as "Hi7c".
        (* the RUNNABLE slot carries the parked context and the receipt; the
           running and dormant arms are both [emp]. *)
        iDestruct (proc_slots_dispatch _ (proc_addr jj) RUNNABLE needs_ctx_RUNNABLE
                     with "Hslot") as "[Hvc Htag]".
        iDestruct (hart_at_any_elim jj Hjj with "Htag") as (hold) "Htag".
        (* RETAG: the tag came out of the not-running guard, where its value
           is meaningless.  Stamp this hart on it; it then crosses WHOLE to
           the dispatched thread, which splits it between [run_slot] and its
           own [cpu_claim] at the release. *)
        iApply fupd_wp.
        iMod (hart_update jj hold cpu_id with "Htag") as "Htag".
        iModIntro.
        (* THE CLAIM IS ISSUED HERE.  RUNNABLE is [unclaimed], so the lock's
           share is the whole mirror; moving it to RUNNING needs no premise,
           and the result is [proc_held]'s whole share -- out of which the
           dispatched thread's half #2 comes at the release. *)
        iApply fupd_wp.
        iMod (pstate_lock_claim (proc_addr jj) RUNNABLE RUNNING
                unclaimed_RUNNABLE unclaimed_RUNNING with "Hpg") as "[Hpl Hph]".
        iDestruct (pstate_whole_split (proc_addr jj) RUNNING) as "[_ Hwj]".
        iDestruct ("Hwj" with "[Hpl Hph]") as "Hpg".
        { rewrite unclaimed_RUNNING. iFrame "Hpl Hph". }
        iModIntro.
        (* +0x64 sw s8,24(s1) : p->state = RUNNING.  Both the base and the
           stored value are read through [rget], so both need respelling. *)
        assert (HM2s1r : rget M2 Rs1 = proc_addr jj) by (rgne; exact HM2s1).
        assert (HM2s8r : trunc32 (rget M2 Rs8) = RUNNING) by (rgne; exact HM2s8).
        iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.scheduler + 0x64)) Rs8 Rs1 (mword_of_int 24 : mword 12)
                  M2 (av - 10)%nat RUNNABLE false with "Hcg Hpc Hi64 [Hstate]").
        { iEval (rewrite HM2s1r sc_state_addr). iExact "Hstate". }
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc Hstate".
        iEval (rewrite HM2s1r sc_state_addr HM2s8r) in "Hstate".
        assert (Hr68 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x68))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr68) in "Hpc".
        (* +0x68 sd s1,48(s4) : c->proc = p *)
        assert (HM2s4r : add_vec (rget M2 Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                         = a_cpu_proc cid_word) by (rgne; exact HM2s4).
        iDestruct (cpu_own_set_proc 1 ebc zero_reg (proc_addr jj) emp {[lock_rank "proc"]} with "Hcpu") as "[Hproc Hback]".
        (* DISPATCH: c->proc : 0 -> &proc[jj].  A PLAIN STORE to memory this
           hart already owns whole -- no invariant, no mask change. *)
        assert (HM2s1rr : rget M2 Rs1 = proc_addr jj) by (rgne; exact HM2s1).
        iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.scheduler + 0x68))
                  Rs1 Rs4 (mword_of_int 48 : mword 12)
                  M2 (av - 10)%nat zero_reg false
                  with "Hcg Hpc Hi68 [Hproc]").
        { iEval (rewrite HM2s4r). iExact "Hproc". }
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc Hproc".
        iEval (rewrite HM2s4r HM2s1rr) in "Hproc".
        iDestruct ("Hback" with "Hproc") as "Hcpu".
        assert (Hr6c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x6c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr6c) in "Hpc".
        (* +0x6c addi a1,s1,96 : &p->context *)
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x6c)) Ra1 Rs1 (mword_of_int 96 : mword 12)
                  M2 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi6c").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        iEval (repeat rgne) in "Hcg".
        set (M3 := <[Regidx Ra1 := regval_into_reg
            (add_vec (M2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> M2).
        change (<[Regidx Ra1 := regval_into_reg
            (add_vec (M2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> M2) with M3.
        assert (Hr70 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x6c) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x70))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr70) in "Hpc".
        (* +0x70 c.mv a0,s6 : &c->context *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.scheduler + 0x70)) Ra0 Rs6 M3 (av - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi70").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        iEval (repeat rgne) in "Hcg".
        set (M4 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Rs6))]> M3).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Rs6))]> M3) with M4.
        assert (Hr72 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x70) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x72))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr72) in "Hpc".
        (* +0x72 jal swtch *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.scheduler + 0x72)) Rra (mword_of_int 1506 : mword 21)
                  M4 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi72").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        set (Mc := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x72) : mword 64) 4)]> M4).
        change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.scheduler + 0x72) : mword 64) 4)]> M4) with Mc.
        assert (Hrsw : add_vec (mword_of_int (KernelSyms.scheduler + 0x72) : mword 64) (sign_extend' 64 (mword_of_int 1506 : mword 21))
                       = mword_of_int KernelSyms.swtch) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hrsw) in "Hpc".
        (* the swtch call site's register facts *)
        assert (HMcra : Mc !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.scheduler + 0x72) : mword 64) 4)
          by (rewrite /Mc upd_eq; reflexivity).
        assert (HMcs1 : Mc !!! Regidx Rs1 = proc_addr jj).
        { rewrite /Mc upd_ne; [| vm_compute; discriminate].
          rewrite /M4 upd_ne; [| vm_compute; discriminate].
          rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2s1. }
        assert (Holdc : Mc !!! Regidx Ra0 = a_cpu_ctx cid_word).
        { rewrite /Mc upd_ne; [| vm_compute; discriminate].
          rewrite /M4 upd_eq.
          rewrite (_ : M3 !!! Regidx Rs6 = a_cpu_ctx cid_word).
          2:{ rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2s6. }
          apply add_vec_zero_l. }
        assert (Hnewc : Mc !!! Regidx Ra1 = p_context (proc_addr jj)).
        { rewrite /Mc upd_ne; [| vm_compute; discriminate].
          rewrite /M4 upd_ne; [| vm_compute; discriminate].
          rewrite /M3 upd_eq HM2s1. apply sc_ctx_addr. }
        (* the cpu context save area's cells go INTO the swtch *)
        iDestruct "Hown" as (ctxvs) "[%Hctxlen Hctxcells]".
        (* the dispatch payload *)
        (* the dispatch payload: the held lock and the trap CSRs this hart's
           acquire produced -- the installed-handler resource rides inside
           them, so the dispatched thread's own intena retune runs under THIS
           hart's (canonical) SIE ghost with nothing extra threaded. *)
        iPoseProof (p_sched_to_proc γs cpu_id jj γl ch Hjj Hgl
                      with "Hcsrs [Hlocked Hstate Hpg Hchan Hpub] Htag") as "HP".
        { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan Hpub". }
        (* the TARGET is proc jj's record, which is MIGRATABLE ([None]) -- any
           hart may dispatch any RUNNABLE proc, so its stored continuation is
           good at every hart, and this hart's [adm] obligation is trivial.
           The record the scheduler deposits for ITSELF stays PINNED: this
           cpu context is only ever resumed from hart cid's own tp. *)
        (* the swtch's crossing index is c->proc, which +0x68 has just set to
           [proc_addr jj]; at [b = false] the bundle does not mention it, so
           the re-tag is conversion (sc_retag_p). *)
        iEval (rewrite (sc_retag_p Mc (av - 10)%nat zero_reg (proc_addr jj))) in "Hcg".
        iApply (Swtch.wp_swtch_sconf (p_sched γs) None (Some cpu_id)
                  (a_cpu_ctx cid_word) (p_context (proc_addr jj))
                  Mc ctxvs (av - 10)%nat ebc (proc_addr jj)
                  Hctxlen Holdc Hnewc (adm_none cpu_id)
                  with "Htext Hcg Hcpu Hpc Hctxcells [Hvc] [HP]").
        { iExact "Hvc". }
        { iEval (rewrite (rget_tp Mc)). iExact "HP". }
        (* [lks'] IS A FRESH, INDEPENDENT BINDER (SpecSwtch.v's resume wand,
           which is [SwtchCtx.valid_context_pre]'s): the thread that will
           eventually resume THIS cpu context -- a proc calling sched() -- is
           in a DIFFERENT critical section from the one suspending here, and
           the swtch primitive ties its held-lock set to nothing.  The entry
           set [{[lock_rank "proc"]}] indexes only the bundle handed IN.
           ================================================================
           OPEN GAP, NOT CLOSED BY THIS PASS -- the mirror image of the one
           ProofSched.v documents at its own [Swtch.wp_swtch_sconf] (that file
           is the OTHER end of this same crossing, resuming the same [p_sched]
           chain).  Everything below -- [cpu_own_set_proc] at +0x76 and the
           [iApply "Tail"] that releases proc jj's lock -- is written at the
           literal [{[lock_rank "proc"]}], because that IS the value in every
           real execution: sched() is only ever called holding exactly p->lock
           at noff == 1, so the resumer's set is that singleton.  But nothing
           available here proves it: [p_sched_at_cpu]'s payload yields
           [proc_held] (which carries the lock TOKEN [locked γl cpu_id], not
           the held-SET fragment [LockSet.lk_in] -- that one lives inside the
           lock INVARIANT's [Some (i, true)] state and cannot be read out
           without opening it), and [cpu_own]'s level index [1] is not tied to
           the cardinality of its set anywhere in the model.  So neither
           [lock_rank "proc" ∈ lks'] nor [lks' ⊆ {[lock_rank "proc"]}] is
           derivable, and [lks' = {[lock_rank "proc"]}] is a protocol fact
           about [SchedCtx.p_sched] that no resource currently states.
           Closing it needs a DESIGN DECISION above this file: likely (a) a
           new ghost conjunct in [SchedCtx.p_sched]'s resume-side payload
           asserting the resumer holds exactly that singleton, together with
           (b) a matching premise on [wp_sched_sconf_body] pinning sched()'s
           own [lks] to it.  Flagged, not guessed: do NOT treat the [Qed]
           below as verified past this point without a build. *)
        iIntros (h m' eb') "%Hadm' %Hcallee Hcg Hcpu Hpc Hctxback Hresume".
        (* cpus[cid].context is only ever resumed from this hart's own tp --
           which is exactly what its pinned index says. *)
        pose proof (adm_pin_inv _ _ Hadm') as Hh. subst h.
        (* the resume side: the payload identifies the parking proc with jj *)
        iDestruct "Hresume" as (A' cret) "[Hvc' Hpay2]".
        iDestruct (p_sched_at_cpu γs cpu_id A' jj cret (rget m' Rtp) Hjj with "Hpay2")
          as "(%Htpv & %Hcret & %HA' & Hcsrs & Hpay3)".
        subst A'.
        iDestruct "Hpay3" as (γl' st' ch') "[%Hfacts (Hheld' & Htag' & Hppay)]".
        destruct Hfacts as [Hgl' Hneeds'].
        assert (γl' = γl) as -> by (rewrite Hgl in Hgl'; injection Hgl'; auto).
        iEval (rewrite /proc_held) in "Hheld'".
        iDestruct "Hheld'" as "(Hlocked & Hstate & Hpg & Hchan & Hpub)".
        (* the callee-saved image equalities *)
        unfold callee_img, ctx_regs in Hcallee. simpl in Hcallee.
        injection Hcallee as Hm1 Hm2 Hm8 Hm9 Hm18 Hm19 Hm20 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27.
        (* the context field is ours again *)
        iAssert (own_ctx (a_cpu_ctx cid_word)) with "[Hctxback]" as "Hown".
        { rewrite /own_ctx. iExists (callee_img Mc).
          iSplit; [ iPureIntro; unfold callee_img, ctx_regs; reflexivity | iExact "Hctxback" ]. }
        assert (Hr76 : ret_pc (m' !!! Regidx Rra) = mword_of_int (KernelSyms.scheduler + 0x76))
          by (rewrite Hm1 HMcra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr76) in "Hpc".
        (* +0x76 sd zero,48(s4) : c->proc = 0 *)
        assert (Hm's4 : add_vec (m' !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                        = a_cpu_proc cid_word).
        { rewrite Hm20.
          rewrite (_ : Mc !!! Regidx Rs4 = M2 !!! Regidx Rs4).
          2:{ rewrite /Mc upd_ne; [| vm_compute; discriminate].
              rewrite /M4 upd_ne; [| vm_compute; discriminate].
              rewrite /M3 upd_ne; [| vm_compute; discriminate]. reflexivity. }
          exact HM2s4. }
        assert (Hm's4r : add_vec (rget m' Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12))
                         = a_cpu_proc cid_word) by (rgne; exact Hm's4).
        (* [lks'], not the entry singleton: this is the post-swtch bundle, so
           it carries the RESUMER's set.  The accessor is set-generic, so this
           step is honest either way; the gap documented at the [iIntros]
           above surfaces at the [iApply "Tail"] below, where [sc_tail_body]
           demands the literal [{[lock_rank "proc"]}]. *)
        iDestruct (cpu_own_set_proc 1 eb' (proc_addr jj) zero_reg emp {[lock_rank "proc"]} with "Hcpu") as "[Hproc Hback]".
        (* RECLAIM: c->proc : &proc[jj] -> 0.  A PLAIN STORE, for the same
           reason the dispatch one is.  The hart tag came back WHOLE in the
           park payload and goes into proc jj's lock below. *)
        iApply (wp_sd_zero_s_sconf (mword_of_int (KernelSyms.scheduler + 0x76))
                  Rs4 (mword_of_int 48 : mword 12)
                  m' (av - 10)%nat (proc_addr jj) false
                  with "Hcg Hpc Hi76 [Hproc]").
        { iEval (rewrite Hm's4r). iExact "Hproc". }
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc Hproc".
        iEval (rewrite Hm's4r) in "Hproc".
        iDestruct ("Hback" with "Hproc") as "Hcpu".
        assert (Hr7a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x76) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x7a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr7a) in "Hpc".
        (* +0x7a c.mv s5,s7 : found := 1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.scheduler + 0x7a)) Rs5 Rs7 m' (av - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi7a").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        iEval (repeat rgne) in "Hcg".
        set (M5 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (m' !!! Regidx Rs7))]> m').
        change (<[Regidx Rs5 := regval_into_reg (add_vec zero_reg (m' !!! Regidx Rs7))]> m') with M5.
        assert (Hr7c : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x7c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr7c) in "Hpc".
        (* the post-swtch arrival pins for the release tail *)
        assert (HMcthr : forall c : mword 5, is_cs_idx c = true -> c <> Rtp ->
                           Mc !!! Regidx c = M2 !!! Regidx c).
        { intros c Hc Hne.
          rewrite /Mc upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
          rewrite /M4 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
          rewrite /M3 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hc]].
          reflexivity. }
        assert (HM5s1 : M5 !!! Regidx Rs1 = proc_addr jj).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm9. exact HMcs1. }
        assert (HM5s2 : M5 !!! Regidx Rs2 = proc_addr NPROC).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm18.
          rewrite (HMcthr Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM2s2. }
        assert (HM5s3 : M5 !!! Regidx Rs3 = sign_extend' 64 RUNNABLE).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm19.
          rewrite (HMcthr Rs3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM2s3. }
        assert (HM5s4 : add_vec (M5 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. exact Hm's4. }
        assert (HM5s6 : M5 !!! Regidx Rs6 = a_cpu_ctx cid_word).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm22.
          rewrite (HMcthr Rs6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM2s6. }
        assert (HM5s7 : neq_vec (add_vec zero_reg (M5 !!! Regidx Rs7)) zero_reg = true).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm23.
          rewrite (HMcthr Rs7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM2s7. }
        assert (HM5s8 : trunc32 (M5 !!! Regidx Rs8) = RUNNING).
        { rewrite /M5 upd_ne; [| vm_compute; discriminate]. rewrite Hm24.
          rewrite (HMcthr Rs8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). exact HM2s8. }
        assert (HM5tie : neq_vec (M5 !!! Regidx Rs5) zero_reg = false -> eb' = false).
        { rewrite /M5 upd_eq. rewrite Hm23.
          rewrite (HMcthr Rs7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
          rewrite HM2s7. intro Hbad. discriminate. }
        (* rebuild the lock resource at the parked state.  ONE lemma for both
           kinds of park (SchedCtx.proc_slots_park_gen): the record the swtch
           handed back, the rejoined receipt, and whatever the crossing's
           [park_pay] carried -- the dormant block at a ZOMBIE park, nothing
           at a resumable one.  The update is that lemma's ZOMBIE arm
           forgetting the record down to its cells. *)
        (* the update is eliminated against the WP through [fupd_wp], the way
           every other fancy-update step in this tree is -- there is no
           [ElimModal] instance for a bare [WP] goal here. *)
        iApply fupd_wp.
        iMod (proc_slots_park_gen γs ⊤ (proc_addr jj) st' Hneeds'
                with "[Hvc'] [Htag'] Hppay") as "Hsl".
        { iEval (rewrite Hcret) in "Hvc'". iExact "Hvc'". }
        { iApply (hart_at_any_intro jj cpu_id Hjj with "Htag'"). }
        (* the park state is [unclaimed] ([park_ok_unclaimed]), so the whole
           mirror the swtch payload carried is the lock's share again. *)
        iDestruct (pstate_whole_split (proc_addr jj) st') as "[Hwk _]".
        iDestruct ("Hwk" with "Hpg") as "[Hpg _]".
        iModIntro.
        iAssert (proc_lock_res γs γl (proc_addr jj))
          with "[Hstate Hpg Hchan Hpub Hsl]" as "HR".
        { rewrite /proc_lock_res. iExists st', ch'.
          iFrame "Hstate Hpg Hchan Hpub Hsl". }
        (* c->proc is 0 again, so re-tag the bundle back to the idle index --
           this is what keeps [wp_next_idle] available at the loop head. *)
        iEval (rewrite (sc_retag_p M5 (av - 10)%nat (proc_addr jj) zero_reg)) in "Hcg".
        (* +0x7c c.j -0x32 : into the release tail *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.scheduler + 0x7c))
                  (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0"))) M5 (av - 10)%nat false
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7c").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hr4a2 : add_vec (mword_of_int (KernelSyms.scheduler + 0x7c) : mword 64)
                          (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0"))))
                        = mword_of_int (KernelSyms.scheduler + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hr4a2) in "Hpc".
        (* THE DISPATCH CHANGED THE ROUND'S BASE ENABLE.  swtch hands the
           bundle back at the RESUMING thread's [eb'] (its own [sie_cap] index
           is arm-[false] on both sides, so the carve is untouched), which
           means the index the tail must return at is the one that goes with
           [eb'] rather than with [ebc].
           ================================================================
           THIS IS WHERE THE OPEN GAP DOCUMENTED AT THE [Swtch.wp_swtch_sconf]
           CONTINUATION ABOVE BITES.  "Hcpu" now carries the swtch resume
           wand's independent [lks'], while [sc_tail_body] is stated at the
           literal [{[lock_rank "proc"]}] -- which is the true value on every
           real execution but is not derivable from anything in scope.  The
           statement is deliberately LEFT at the singleton rather than
           generalised to [lks']: generalising it only relocates the same
           unprovable obligation to the tail's own release, which must produce
           [∅] for the next [intr_on] and so would need [lks' ⊆ {[rank
           "proc"]}] anyway.  Do not paper over this with an [admit]; it wants
           the [SchedCtx.p_sched] ghost fact described above. *)
        iApply ("Tail" $! jj γl M5 eb' (av - 10 - trap_res eb')%nat
                  with "[%] [%] [%] [%] [%] Hcg Hpc Hlocked HR Hcpu Hcsrs Hown").
        { exact Hjj. }
        { exact Hgl. }
        { exact (sc_idx_ok av eb' Hav). }
        { split_and!; assumption. }
        { exact HM5tie. }
        iSplit.
        + iIntros (HSjj Mn) "%HpinsN %HtieN Hcg Hpc Hcpu Hcsrs Hown".
          iApply ("IH" $! (S jj) Mn eb' (av - 10 - trap_res eb')%nat
                    with "[%] [%] [%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown Hexit").
          { unfold NPROC in *. lia. }
          { exact HSjj. }
          { exact (sc_idx_ok av eb' Hav). }
          { exact HpinsN. }
          { exact HtieN. }
        + iIntros (Me) "%HpinsE %HtieE Hcg Hpc Hcpu Hcsrs Hown".
          iApply ("Hexit" $! Me eb' (av - 10 - trap_res eb')%nat
                    with "[%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown");
            [ exact HpinsE | exact HtieE | exact (sc_idx_ok av eb' Hav) ]. }
    (* ================================================================== *)
    (* THE LOOP HEAD'S intr_on, +0x86 -- THE ONE PLACE THE RESERVE IS PAID. *)
    (*                                                                     *)
    (* This is the whole point of the scheduler's carve accounting, so it is *)
    (* worth being explicit about WHY it is a case split and not one leaf.   *)
    (*                                                                     *)
    (* scheduler() is entered from main() with interrupts OFF, and the loop   *)
    (* head is reached again either from the dispatch tail (whose release at  *)
    (* level 0 has already re-enabled, so the arm is [true]) or from the wfi  *)
    (* arm (which proves the arm is [false] and leaves it there).  So BOTH    *)
    (* arms genuinely occur at +0x86, and they are different events:          *)
    (*                                                                       *)
    (*   arm [false] -- a REAL 0 -> 1 flip.  Nobody is holding the trap       *)
    (*     reserve, so the scheduler funds [kv_frame_slots] out of its own    *)
    (*     budget: index [av - 10] (the whole carve is usable at a disabled   *)
    (*     arm) becomes [av - 10 - kv_frame_slots] usable with the reserve    *)
    (*     set aside.  That is [sc_carve], and it is paid ONCE -- on the      *)
    (*     first round, and again only after a wfi.                          *)
    (*                                                                       *)
    (*   arm [true] -- an IDEMPOTENT SET.  SIE is already '1'; the write      *)
    (*     changes no ghost state and, decisively, MOVES NO STACK.  The       *)
    (*     reserve carved on the first round is still set aside, so there is  *)
    (*     nothing to pay and the index does not move.                        *)
    (*                                                                       *)
    (* Using the arm-GENERIC enable leaf for both would demand pre index      *)
    (* [trap_res true + n] at the enabled arm too -- i.e. room to set aside   *)
    (* [kv_frame_slots] in a state where they are ALREADY set aside -- which  *)
    (* forces [av >= 2 * kv_frame_slots + 20].  A factor-of-two reserve is    *)
    (* exactly the shape the arm-dependent carve exists to remove, so the     *)
    (* enabled arm goes through the index-generic idempotent leaf instead.    *)
    (* Both arms converge on ONE state -- arm [true], index                   *)
    (* [av - 10 - kv_frame_slots] -- which is what lets the rest of the loop  *)
    (* body be written once; hence this is its own resource rather than a     *)
    (* [destruct] inside the Löb body.                                        *)
    (* ================================================================== *)
    (* RULE ONE (optimization.md) judgment: NOT folded.  This statement is
       only ~10 lines between [iAssert (□ (] and the closing [))%I] -- under
       the fold threshold (precedent: ProofDirlookup's header records a
       13-line body skipped the same way) -- and "IntrOn" is consumed once,
       immediately, by "Outer" rather than living in [Δ] across a long tail,
       so there is no Löb-IH multiplier to offset the cost of a definition
       either.  Left inline. *)
    iAssert (□ ( ∀ (M : regfile) (eb : bool) (nx : nat),
        ⌜ (trap_res eb + nx)%nat = (av - 10)%nat ⌝ -∗
        sie_cap_gpr M nx eb zero_reg -∗
        cpu_own 0 eb zero_reg emp eb ∅ -∗
        (if eb then emp else trap_csrs) -∗
        pc_is (mword_of_int (KernelSyms.scheduler + 0x86)) -∗
        ( sie_cap_gpr M (av - 10 - kv_frame_slots)%nat true zero_reg -∗
          pc_is (mword_of_int (KernelSyms.scheduler + 0x8a)) -∗
          WP (Loop : expr riscv_lang) ) -∗
        WP (Loop : expr riscv_lang) ))%I
      with "[]" as "#IntrOn".
    { iModIntro. iIntros (M eb nx) "%Hnx Hcg Hcpu Hcsrs Hpc Hk".
      iPoseProof (schi_86 with "Htext") as "Hi86".
      assert (Ho8a' : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x86) : mword 64) 4
                      = mword_of_int (KernelSyms.scheduler + 0x8a))
        by (apply bv_eq; vm_compute; reflexivity).
      (* The flip leaves take the count eighth and the per-cpu cells SEPARATELY,
         each behind an [if eb then emp else _]: at the enabled base both live
         inside [sie_arm]'s arm.  [sc_flip_pre] is exactly [cpu_own 0 eb _ emp eb]
         re-presented in that shape. *)
      iDestruct (sc_flip_pre with "Hcpu") as "[Hcnt Hcells]".
      destruct eb.
      - (* ---- already enabled: the idempotent set, index untouched ---- *)
        assert (Hnx' : nx = (av - 10 - kv_frame_slots)%nat)
          by (change (trap_res true) with kv_frame_slots in Hnx; lia).
        iEval (rewrite Hnx') in "Hcg".
        iApply (wp_csrsi_sstatus_x0_idem_s_sconf (mword_of_int (KernelSyms.scheduler + 0x86))
                  M (av - 10 - kv_frame_slots)%nat with "Hcg Hpc Hi86").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros (ms1) "%Hmsf1 Hcg Hpc".
        iEval (rewrite Ho8a') in "Hpc".
        iApply ("Hk" with "Hcg Hpc").
      - (* ---- disabled: the ONE real enable, funded from the entry budget ---- *)
        assert (Hnx' : nx = (av - 10)%nat) by (cbn in Hnx; lia).
        iEval (rewrite Hnx') in "Hcg".
        iEval (rewrite (sc_carve av Hav)) in "Hcg".
        iApply (wp_csrsi_sstatus_x0_enable_s_sconf (mword_of_int (KernelSyms.scheduler + 0x86))
                  false M (av - 10 - kv_frame_slots)%nat
                  with "Hcg Hcnt Hcsrs Hcells [] Hpc Hi86").
        (* the scheduler runs with [c->proc == 0], so the claim it owes the arm
           is the idle one -- [cpu_claim_idle], for free. *)
        { rewrite /cpu_claim_ext. iApply cpu_claim_idle. }
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros (ms1) "%Hmsf1 Hcg Hpc".
        iEval (rewrite Ho8a') in "Hpc".
        iApply ("Hk" with "Hcg Hpc"). }
    (* ================================================================== *)
    (* THE OUTER DISPATCH LOOP, entry +0x86, by iLöb.                     *)
    (* ================================================================== *)
    iAssert (□ sc_outer_body av)%I
      with "[]" as "#Outer".
    { iModIntro. iLöb as "IHo".
      iIntros (M eb n) "%Hpo %Hn Hcg Hpc Hcpu Hcsrs Hown".
      destruct Hpo as (Ho4 & Ho6 & Ho7 & Ho8).
      iPoseProof (schi_86 with "Htext") as "Hi86".
      iPoseProof (schi_8a with "Htext") as "Hi8a".
      iPoseProof (schi_8e with "Htext") as "Hi8e".
      iPoseProof (schi_90 with "Htext") as "Hi90".
      iPoseProof (schi_94 with "Htext") as "Hi94".
      iPoseProof (schi_98 with "Htext") as "Hi98".
      iPoseProof (schi_9a with "Htext") as "Hi9a".
      iPoseProof (schi_9e with "Htext") as "Hi9e".
      iPoseProof (schi_a2 with "Htext") as "Hia2".
      iPoseProof (schi_7e with "Htext") as "Hi7e".
      iPoseProof (schi_82 with "Htext") as "Hi82".
      (* +0x86 csrsi sstatus,2 : intr_on.  Both arms converge on arm [true] at
         index [av - 10 - kv_frame_slots]; see the [IntrOn] header above for
         why this is a case split and where the one reserve is paid. *)
      iApply ("IntrOn" $! M eb n with "[%] Hcg Hcpu Hcsrs Hpc").
      { exact Hn. }
      iIntros "Hcg Hpc".
      (* +0x8a csrci sstatus,2 : intr_off *)
      (* the disable leaf's premise is [intr_count_pre true 0 true], the PURE
         fact the (now enabled) arm bakes in; it hands the freed cells back as
         [cpu_priv_pay true zero_reg].  Its post index [trap_res true + n] is
         the reserve coming BACK into the usable count -- the scan below runs
         interrupts-off at the full carve [av - 10], which is what [sc_carve]
         re-spells. *)
      iApply (wp_csrci_sstatus_x0_s_sconf (mword_of_int (KernelSyms.scheduler + 0x8a)) M
                (av - 10 - kv_frame_slots)%nat true
                with "Hcg [] Hpc Hi8a").
      { iPureIntro. exact (conj eq_refl eq_refl). }
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      (* the [cpu_claim] the disable leaf now hands back is [cpu_claim
         zero_reg] -- the scheduler runs with [c->proc == 0], so it is the
         idle claim ([IntrDefs.cpu_claim_idle]) and carries nothing.  Dropped
         here rather than threaded: the next [intr_on] round re-derives it. *)
      iIntros (ms2) "%Hmsf2 Hcg Hcnt Hcsrs _ Hcells Hpc".
      iEval (rewrite -(sc_carve av Hav)) in "Hcg".
      assert (Ho8e : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x8a) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x8e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho8e) in "Hpc".
      iAssert (cpu_own 0 false zero_reg emp false ∅) with "[Hcells Hcnt]" as "Hcpu".
      { iApply (sc_cpu_own_of_cells zero_reg true with "Hcells Hcnt"). }
      (* +0x8e c.li s5,0 : found := 0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x8e)) Rs5 (mword_of_int 0 : mword 6)
                (zero_reg : mword 64) M (av - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi8e").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (B0 := <[Regidx Rs5 := regval_into_reg (zero_reg : mword 64)]> M).
      change (<[Regidx Rs5 := regval_into_reg (zero_reg : mword 64)]> M) with B0.
      assert (Ho90 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x90))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho90) in "Hpc".
      (* +0x90 auipc s1,0x11 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.scheduler + 0x90)) Rs1 (mword_of_int 0x11 : mword 20)
                B0 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi90").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (B1 := <[Regidx Rs1 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.scheduler + 0x90) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B0).
      change (<[Regidx Rs1 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.scheduler + 0x90) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> B0) with B1.
      assert (Ho94 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x94))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho94) in "Hpc".
      (* +0x94 addi s1,s1,2414 : &proc[0] *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x94)) Rs1 Rs1 (mword_of_int 2544 : mword 12)
                B1 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi94").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (B2 := <[Regidx Rs1 := regval_into_reg
          (add_vec (B1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 2544 : mword 12)))]> B1).
      change (<[Regidx Rs1 := regval_into_reg
          (add_vec (B1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 2544 : mword 12)))]> B1) with B2.
      assert (Ho98 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x94) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x98))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho98) in "Hpc".
      assert (HB2s1 : B2 !!! Regidx Rs1 = proc_addr 0%nat).
      { rewrite /B2 upd_eq /B1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      (* +0x98 c.li s3,3 : RUNNABLE *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.scheduler + 0x98)) Rs3 (mword_of_int 3 : mword 6)
                (sign_extend' 64 (RUNNABLE : mword 32)) B2 (av - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi98").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (B3 := <[Regidx Rs3 := regval_into_reg (sign_extend' 64 (RUNNABLE : mword 32))]> B2).
      change (<[Regidx Rs3 := regval_into_reg (sign_extend' 64 (RUNNABLE : mword 32))]> B2) with B3.
      assert (Ho9a : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x98) : mword 64) 2 = mword_of_int (KernelSyms.scheduler + 0x9a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho9a) in "Hpc".
      (* +0x9a auipc s2,0x16 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.scheduler + 0x9a)) Rs2 (mword_of_int 0x16 : mword 20)
                B3 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi9a").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      set (B4 := <[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.scheduler + 0x9a) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> B3).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.scheduler + 0x9a) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> B3) with B4.
      assert (Ho9e : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x9a) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x9e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho9e) in "Hpc".
      (* +0x9e addi s2,s2,868 : &proc[NPROC] *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.scheduler + 0x9e)) Rs2 Rs2 (mword_of_int 998 : mword 12)
                B4 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi9e").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (B5 := <[Regidx Rs2 := regval_into_reg
          (add_vec (B4 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 998 : mword 12)))]> B4).
      change (<[Regidx Rs2 := regval_into_reg
          (add_vec (B4 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 998 : mword 12)))]> B4) with B5.
      assert (Hoa2 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x9e) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0xa2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hoa2) in "Hpc".
      (* the entry pins of the scan, at [B5] *)
      assert (HB5s1 : B5 !!! Regidx Rs1 = proc_addr 0%nat).
      { rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2s1. }
      assert (HB5s2 : B5 !!! Regidx Rs2 = proc_addr NPROC).
      { rewrite /B5 upd_eq /B4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HB5s3 : B5 !!! Regidx Rs3 = sign_extend' 64 RUNNABLE).
      { rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_eq. reflexivity. }
      assert (HB5s5 : B5 !!! Regidx Rs5 = zero_reg).
      { rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate].
        rewrite /B0 upd_eq. reflexivity. }
      assert (HB5thr : forall c : mword 5,
                 c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs5 ->
                 B5 !!! Regidx c = M !!! Regidx c).
      { intros c H1 H2 H3 H5.
        rewrite /B5 upd_ne; [| intro He; injection He as He'; exact (H2 He')].
        rewrite /B4 upd_ne; [| intro He; injection He as He'; exact (H2 He')].
        rewrite /B3 upd_ne; [| intro He; injection He as He'; exact (H3 He')].
        rewrite /B2 upd_ne; [| intro He; injection He as He'; exact (H1 He')].
        rewrite /B1 upd_ne; [| intro He; injection He as He'; exact (H1 He')].
        rewrite /B0 upd_ne; [| intro He; injection He as He'; exact (H5 He')].
        reflexivity. }
      assert (HB5s4 : add_vec (B5 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 48 : mword 12)) = a_cpu_proc cid_word).
      { rewrite (HB5thr Rs4 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). exact Ho4. }
      assert (HB5s6 : B5 !!! Regidx Rs6 = a_cpu_ctx cid_word).
      { rewrite (HB5thr Rs6 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). exact Ho6. }
      assert (HB5s7 : neq_vec (add_vec zero_reg (B5 !!! Regidx Rs7)) zero_reg = true).
      { rewrite (HB5thr Rs7 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). exact Ho7. }
      assert (HB5s8 : trunc32 (B5 !!! Regidx Rs8) = RUNNING).
      { rewrite (HB5thr Rs8 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). exact Ho8. }
      (* +0xa2 c.j -0x4a : enter the scan at j = 0 *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.scheduler + 0xa2))
                (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0"))) B5 (av - 10)%nat false
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia2").
      first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
      iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Ho58 : add_vec (mword_of_int (KernelSyms.scheduler + 0xa2) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.scheduler + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ho58) in "Hpc".
      (* the scan runs interrupts-off at the FULL carve: [trap_res false + n]
         is [n] by conversion, so the index equation is [reflexivity]. *)
      iSpecialize ("Scan" $! NPROC).
      iApply ("Scan" $! 0%nat B5 false (av - 10)%nat
                with "[%] [%] [%] [%] [%] Hcg Hpc Hcpu Hcsrs Hown").
      { lia. }
      { unfold NPROC. lia. }
      { reflexivity. }
      { split_and!; assumption. }
      { intros _. reflexivity. }
      (* ---- the scan's single exit, at +0x7e ---- *)
      iIntros (Me eb2 n2) "%Hpe %HtieE %Hn2 Hcg Hpc Hcpu Hcsrs Hown".
      destruct Hpe as (He4 & He6 & He7 & He8).
      assert (HMe5r : rget Me Rs5 = Me !!! Regidx Rs5) by (rgne; reflexivity).
      destruct (neq_vec (Me !!! Regidx Rs5) zero_reg) eqn:Hs5v.
      + (* a proc ran: straight back to the loop head *)
        iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.scheduler + 0x7e)) (mword_of_int 8 : mword 13)
                  Rs5 Me n2 eb2 ltac:(vm_compute; discriminate)
                  ltac:(rewrite HMe5r; exact Hs5v)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7e").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iNext. iIntros "Hcg Hpc".
        assert (Hb86 : add_vec (mword_of_int (KernelSyms.scheduler + 0x7e) : mword 64) (sign_extend' 64 (mword_of_int 8 : mword 13))
                       = mword_of_int (KernelSyms.scheduler + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb86) in "Hpc".
        iApply ("IHo" $! Me eb2 n2 with "[%] [%] Hcg Hpc Hcpu Hcsrs Hown").
        { split_and!; assumption. }
        { exact Hn2. }
      + (* nothing runnable: SIE is provably off, so wfi is legal *)
        assert (Heb : eb2 = false) by (apply HtieE; first [exact Hs5v | reflexivity]).
        subst eb2.
        iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.scheduler + 0x7e)) (mword_of_int 8 : mword 13)
                  Rs5 Me n2 false ltac:(vm_compute; discriminate)
                  ltac:(rewrite HMe5r; exact Hs5v)
                  with "Hcg Hpc Hi7e").
        first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
        iIntros "Hcg Hpc".
        assert (Hb82 : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x7e) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x82))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb82) in "Hpc".
        (* +0x82 wfi -- the ONE leaf with no [wp_next] wrapper (it never
           migrates the hart) *)
        iDestruct (sc_cpu_own_open with "Hcpu") as "(Hnoff & Hint & Hcnt & Hproc & Hlks & _)".
        iApply (wp_wfi_s_sconf (mword_of_int (KernelSyms.scheduler + 0x82)) Me n2 false
                  with "Hcg Hcnt Hpc Hi82").
        iNext. iIntros "Hcg Hcnt Hpc".
        assert (Hb86b : add_vec_int (mword_of_int (KernelSyms.scheduler + 0x82) : mword 64) 4 = mword_of_int (KernelSyms.scheduler + 0x86))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb86b) in "Hpc".
        iAssert (cpu_own 0 false zero_reg emp false ∅) with "[Hnoff Hint Hcnt Hproc Hlks]" as "Hcpu".
        { iApply (sc_cpu_own_mk with "Hnoff Hint Hcnt Hproc Hlks"). }
        iApply ("IHo" $! Me false n2 with "[%] [%] Hcg Hpc Hcpu Hcsrs Hown").
        { split_and!; assumption. }
        { exact Hn2. } }
    (* ------------------------------------------------------------------ *)
    (* +0x48 c.j +0x3e : into the loop head.                              *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (schi_48 with "Htext") as "Hi48".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.scheduler + 0x48))
              (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0"))) A16 (av - 10)%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi48").
    first [ rewrite wp_next_off | rewrite (wp_next_idle _ _ _ eq_refl) ].
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hpc86 : add_vec (mword_of_int (KernelSyms.scheduler + 0x48) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.scheduler + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc86) in "Hpc".
    (* the entry bundle is already tagged at [zero_reg] (the scheduler thread
       has no proc), so no re-tag is owed here. *)
    (* scheduler() is entered with interrupts OFF, which is what makes the
       loop head's first [intr_on] the ONE real enable -- and at the disabled
       arm the index IS the whole carve, so the equation is [reflexivity]. *)
    iApply ("Outer" $! A16 false (av - 10)%nat with "[%] [%] Hcg Hpc Hcpu Hcsrs Hown").
    { split_and!; assumption. }
    { reflexivity. }
  Qed.

End ProofScheduler.

End SchedulerProof.
