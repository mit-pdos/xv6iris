(** * WeakSrvwmoCapstone.v — THE TIER-1 FINAL THEOREM (A4): adequacy ∘ T1

    Design: [claude-notes/design/weak-memory-srvwmo.md] §3; worklist
    [claude-notes/projects/weak-memory-srvwmo.md] (A4).

        [WP package]  ⇒  (adequacy over the pf event language)
                      ∘  [T1: sRVWMO ⊆ pf, program-carrying]
                      =  xv6 is safe on every hart of every machine
                         implementing sRVWMO.

    THE READING.  A machine implementing sRVWMO produces only
    sRVWMO-consistent executions of the program it runs.
    [xv6_srvwmo_safe] below says: EVERY sRVWMO-consistent execution whose
    trace the xv6 event programs can emit ([exec_prog_ok] — T1's
    conformance interface, with the exclusive PAIR arm of A3(iv)) is
    REALIZED by a run of the promise-free event language from the booted
    initial state, ending at the same log; and — the adequacy half,
    candidate-independent — every reachable configuration of that language
    is violation-free and every thread of it is reducible.  Nothing the
    hardware class can produce escapes the WP proofs' reach.

    THE OTHER HALF of the characterization is T2 ([WeakEvInst.t2_ev]):
    every promise-free run of the event instance projects BACK to an
    [exec_wf] axiomatic execution with the same image and the same log —
    so sRVWMO and the promise-free event machine are the same behavior
    set, presented two ways.

    THE PREMISE LEDGER, in full:
      (a) four machine facts about a booted σ0 (fresh era, empty log,
          fresh views) — the same clauses every adequacy statement carries;
      (b) THE WP PACKAGE — the only Iris-side obligation, verbatim
          [WeakEvAdequacy.weak_ev_pf_violation_free]'s;
      (c) the sRVWMO-side hypotheses: [srvwmo_consistent], the boot image,
          and the conformance supply [exec_prog_ok].
    And that is all.  In particular NO [main_premises], NO robustness
    package, NO retag: the whole [robust_main] tower — the tier-2 route —
    is off this path.  [Print Assumptions] (recorded at the
    bottom): exactly the five generated-model reservation axioms.

    A NOTE ON DIRECTION.  The tier-2 capstone
    ([WeakEvCapstone.xv6_ev_weak_robust]) starts from a FULL-machine
    behavior and works to contain it; this theorem starts from the DECLARED
    MODEL's executions.  The two consume the same adequacy exports; only
    this one is premise-free about xv6's weak-memory behavior, which is
    the tier split's whole point (design §0). *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvAdequacy.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakInterp.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakGhost.
Require Import WeakEvAdequacy.
Require Import WeakEvCapstone.

(** THE TIER-1 CAPSTONE. *)
Theorem xv6_srvwmo_safe Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU -> gset register)
    (cd : cand) (pst : nat -> list pexv6) (dv : nat -> dev_state)
    (Hgen : gen = 0%nat)
    (Hpow : wgpow σ0 = true) (Hgen0 : wggen σ0 = 0%nat)
    (Hlog : wglog σ0 = [])
    (Hws : forall cc : CPU, wgws σ0 cc = ws_init) :
  (* (b) THE WP PACKAGE *)
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D cc,
            reg_pointsto_at cc r (DfracOwn 1)
              (register_lookup r (wgregs σ0 cc))) ∗
       ([∗ map] a ↦ b ∈ wgimg σ0, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
       wlog_lb [] ∗
       uart_frag (wgdev σ0).(duart) ∗ plic_frag (wgdev σ0).(dplic) ∗
       virtio_frag (wgdev σ0).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
  (* (c) THE MODEL SIDE: an sRVWMO-consistent execution of the xv6 event
     programs over the boot image *)
  srvwmo_consistent cd ->
  cd_img cd = img_z (wgimg σ0) ->
  pst 0%nat = eps_init σ0 ->
  dv 0%nat = wgdev σ0 ->
  exec_prog_ok pstep_ev pcls_ev pst dv (cand_exec cd) ->
  (* T1 ∘ the language lift: the execution is REALIZED by a pf run of the
     event language, ending at the candidate's own log ... *)
  (exists P' σ',
     rtc epf_run (ep_init gen, σ0) (P', σ') /\
     wglog σ' = cd_log cd (length (cd_tr cd)) /\
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr cd))) /\
  (* ... and ADEQUACY: every reachable configuration of that language is
     violation-free, and every thread of every reachable configuration is
     reducible — candidate-independent, i.e. for the WHOLE behavior set *)
  (forall ρ, rtc epf_run (ep_init gen, σ0) ρ ->
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) /\
  (forall t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) ->
     e2 ∈ t2 ->
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hwp Hcons Himg Hpst0 Hdv0 Hprog.
  have Hlive : ethread_live σ0 gen.
  { rewrite /ethread_live Hpow Hgen0 Hgen. by split. }
  split_and!.
  - (* T1: realizability, program-carried, then lifted to the language *)
    destruct (srvwmo_realizable cd Hcons) as (Hwf & Htr & Heximg).
    destruct (exec_wf_pf_run_prog pstep_ev pcls_ev pst dv (cand_exec cd)
                Hwf Hprog) as (c & Hrun & Hpg & Hdev & Hm).
    rewrite Heximg Himg Hpst0 Hdv0 in Hrun.
    rewrite -(ecfg_of_init gen σ0 Hlog Hws) in Hrun.
    destruct (wp_pf_rtc_epf_rtc (ep_init gen) σ0 c Hlive Hrun)
      as (P' & σ' & Hr & Heq).
    exists P', σ'. split_and!; [exact Hr| |].
    + destruct Hm as (_ & Hlg & _).
      rewrite -(ecfg_of_log P' σ') Heq -Hlg cand_ex_tr.
      exact (cand_elog cd (length (cd_tr cd)) ltac:(lia)).
    + rewrite Heq Hpg cand_ex_tr //.
  - (* adequacy, the violation-freedom half *)
    intros ρ Hρ.
    exact (weak_ev_pf_violation_free Σ gen σ0 D Hgen Hpow Hgen0 Hlog Hws Hwp
             ρ Hρ).
  - (* adequacy, the safety (reducibility) half *)
    intros t2 σ2 e2 Hrtc He2.
    exact (weak_ev_adequacy_reducible Σ gen σ0 D Hgen Hpow Hgen0 Hlog Hws Hwp
             t2 σ2 e2 Hrtc He2).
Qed.

(** THE AUDIT (run at build time, recorded here):

      Print Assumptions xv6_srvwmo_safe.
      Axioms:
      rv64d.valid_reservation
      rv64d.plat_term_write
      rv64d.match_reservation
      rv64d.load_reservation
      rv64d.cancel_reservation

    i.e. EXACTLY the five generated-model reservation axioms.  No
    [main_premises], no robustness package, no shape/liveness record, no
    funext, no classical axiom.  Together with [WeakEvInst.t2_ev] (same
    audit) this is the sRVWMO characterization consumed at tier 1:
    the declared model's executions and the event machine's runs are the
    same behavior set, and the WP package covers all of it. *)
