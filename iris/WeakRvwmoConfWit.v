(** * WeakRvwmoConfWit.v — THE [hemit] NON-VACUITY WITNESS (route B, B0b-1)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4 (B1b's
    conformance bundle) — the gap B0b-1 left open.

    THE GAP.  [WeakRvwmoConf.hart_conf] is the per-hart row-emittability
    relation the whole conformance bundle ([WeakRvwmoSupply.gdexec_qconf])
    is built on, and B0b-1 landed it with only the EMPTY row witnessed
    ([WeakRvwmoConf.hart_conf_nil]).  An empty-row witness proves nothing
    about the relation's shape: an [hemit] that no nonempty row can satisfy
    would still admit it, and every downstream theorem would be vacuous at
    every graph with an event in it.

    THE WITNESS.  A REAL single-instruction emission of the real xv6 kernel:
    the [sw &started] store of [main] — the same instruction
    [WeakEvStarted]'s end-to-end certification measures — at the machine
    monad node it is emitted from ([WeakEvStarted.ev_x2], the residual after
    the fetch and the 179 silent nodes behind it), with its REQUEST
    ([ev_reqw]) read off that node by total projection and inverted by
    [WeakEvLift.ewrite_req_at_inv].  The row is ONE label, the axiomatic
    [LStore] of the flag word at [&started]; the emission is the one block
    [HEone] builds: an EMPTY administrative run and the realizing step.

    WHAT IS AND IS NOT CONCRETE.  The monad, the request, the address, the
    stored value, the access kind and the emitted class are all the real
    machine's — nothing here is hand-built.  The register file [rs], the
    announced-instruction channel [ib], the CPU index and the device fabric
    [d0] are UNIVERSALLY QUANTIFIED, because the [MemWrite] arm of
    [WeakEvInst.pnode_step] reads none of them (the operand lists it puts in
    the wlabel are a function of [ib], and they leave the axiomatic label
    alone — [WeakPromiseBridge.proj_lbl] drops them).  So the witness is
    STRONGER than a fully-instantiated one, not weaker.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakRvwmoGraph.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakEvLift.
Require Import WeakEvStarted.

(* ====================================================================== *)
(** * 1. THE OBJECTS *)

(** The hart, sitting at the store node of [sw &started].  [fn = None]: no
    fence is parked, so [pstep_node] dispatches on the monad. *)
Definition ev_p0 (cpu : CPU) (rs : regstate) (ib : oib32) : pexv6 :=
  PHart cpu ev_x2.2 rs None ib.

(** … and where it lands: the [MemWrite] node's continuation at [inl None],
    named through the projection's own resume function so that no [K] is
    written down. *)
Definition ev_p1 (cpu : CPU) (rs : regstate) (ib : oib32) : pexv6 :=
  PHart cpu (ewrite_resume ev_x2.2) rs None ib.

(** THE WLABEL the step emits.  Plain (the release is carried by the hart's
    [w_relp], which [ws_init] has clear), at [&started], four bytes of
    [lock_one]; the two operand lists are the instruction channel's. *)
Definition ev_wl (ib : oib32) : wlabel :=
  WeakPromise.LStore false (pa_z ev_flag) (wbytes 4 WeakLock.lock_one)
    (deps_asrc (deps_of_ib (ib_bits ib)))
    (deps_vsrc (deps_of_ib (ib_bits ib))).

(** THE ROW: its axiomatic image, ONE graph label. *)
Definition ev_row : list WeakAxiomatic.lbl :=
  [WeakAxiomatic.LStore false (pa_z ev_flag)
     (wbytes 4 WeakLock.lock_one) WCplain].

(** THE EMISSION: one tagged item, no administrative items. *)
Definition ev_em (cpu : CPU) (rs : regstate) (ib : oib32) : hemission :=
  HEm [(ev_wl ib, Some 0%nat)] (ev_p1 cpu rs ib).

(* ====================================================================== *)
(** * 2. THE STEP

    [pnode_step]'s [MemWrite] arm, at the inverted node.  The three request
    facts it needs are [WeakEvStarted]'s own computed ones: the address is
    RAM ([ev_store_ram]), the access kind is unconditional
    ([ev_store_plain]), and the width is nonzero. *)

Lemma ev_pstep (cpu : CPU) (rs : regstate) (ib : oib32) (d0 : dev_state) :
  pstep_ev (ev_p0 cpu rs ib) d0 (ev_wl ib) (ev_p1 cpu rs ib) d0.
Proof.
  destruct (ewrite_req_at_inv 4 ev_x2.2 ev_reqw ev_store_req)
    as (K & Hm & Hres).
  rewrite /pstep_ev /ev_p0 /ev_p1 Hres Hm.
  split; [reflexivity|]. exists None, None.
  split_and!; [reflexivity|reflexivity|]. left.
  rewrite /pstep_node /pnode_step /=.
  split; [done|]. left. rewrite /ev_wl.
  split_and!; reflexivity.
Qed.

(** THE PROJECTION: the wlabel's axiomatic image IS the row's label, and the
    class the language stamps on the message is [WCplain] — [ws_init] has
    [w_relp] clear and the access kind is neither exclusive nor [.rl]. *)
Lemma ev_realizes (cpu : CPU) (rs : regstate) (ib : oib32) :
  hlbl_realizes (ev_p0 cpu rs ib) ws_init
    (WeakAxiomatic.LStore false (pa_z ev_flag)
       (wbytes 4 WeakLock.lock_one) WCplain) (ev_wl ib).
Proof.
  destruct (ewrite_req_at_inv 4 ev_x2.2 ev_reqw ev_store_req)
    as (K & Hm & _).
  rewrite /hlbl_realizes. split_and!; [done|done|done|].
  rewrite /ev_wl /pcls_ev /ev_p0 Hm /pnode_wclass /=. reflexivity.
Qed.

(* ====================================================================== *)
(** * 3. THE WITNESS *)

Theorem ev_hart_conf (i : agent) (cpu : CPU) (rs : regstate) (ib : oib32)
    (d0 : dev_state) :
  hart_conf i ev_row (ev_p0 cpu rs ib) (λ _, d0) (ev_em cpu rs ib).
Proof.
  rewrite /hart_conf /ev_em /ev_row /=.
  apply (HEone (λ _ : nat, d0) 0%nat ws_init
           (WeakAxiomatic.LStore false (pa_z ev_flag)
              (wbytes 4 WeakLock.lock_one) WCplain)
           [] (ev_p0 cpu rs ib) [] (ev_p0 cpu rs ib) d0
           (ev_wl ib) (ev_p1 cpu rs ib) [] (ev_p1 cpu rs ib)).
  - apply ARnil.
  - apply ev_realizes.
  - apply ev_pstep.
  - apply HEnil.
Qed.

(** … and the emission is FABRIC-QUIET, so it is a [gdexec_qconf] block and
    not merely a [gdexec_conf] one. *)
Theorem ev_em_devfree (cpu : CPU) (rs : regstate) (ib : oib32) :
  em_devfree (ev_em cpu rs ib).
Proof.
  rewrite /em_devfree /em_labels /ev_em /=.
  intros [H|H]%elem_of_cons; [by rewrite /ev_wl in H|].
  by apply elem_of_nil in H.
Qed.

(** THE POINT, stated without the objects: [hart_conf] IS INHABITED AT A
    NONEMPTY ROW, by a row whose single label is a real memory event. *)
Corollary hart_conf_nonempty :
  ∃ (i : agent) (row : list WeakAxiomatic.lbl) (p0 : pexv6)
    (d0 : dev_state) (em : hemission),
    row ≠ [] ∧ hart_conf i row p0 (λ _, d0) em ∧ em_devfree em.
Proof.
  exists 0%nat, ev_row, (ev_p0 (0%fin) ev_rs0 ib_none), dev0_state,
         (ev_em (0%fin) ev_rs0 ib_none).
  split_and!; [done|apply ev_hart_conf|apply ev_em_devfree].
Qed.

(* ====================================================================== *)
(** * 4. AUDIT *)

Print Assumptions ev_hart_conf.
Print Assumptions hart_conf_nonempty.
