(** * WeakRvwmoCycWit2.v — THE RE-CONVERGENCE WITNESS (route B)

    THE AUDIT'S RULE.  Every new hypothesis needs a NON-COINCIDENTAL
    satisfiability witness, and a witness built so that the hypothesis
    holds vacuously is the vacuity it was meant to catch.
    [WeakRvwmoCert3] §5b introduced three: [tail_silent] (the instruction
    tail is administrative), [csync]'s DIVERGED arm, and the segment
    iteration [cert_segment''] that consumes them.  This leaf inhabits them
    at a witness read whose VALUE IS USED before the boundary and whose two
    runs carry DIFFERENT values — the two conditions
    [WeakRvwmoCycWit.cy_node_vindep] (the old, value-INDEPENDENT node)
    could not test.

    WHAT IS REAL, AND WHAT IS NOT.

    REAL: the load REQUEST.  [ld_reql] is [WeakRvwmoConfWit2]'s — read off
    the machine at hart 1's spin load [lw a5,0(a4)] at [main+0x16]: width
    4, address [&started] ([ev_flag]), plain access kind, RAM.  REAL: the
    DESTINATION register, [a5] = [x15], whose dependency carrier is
    [wreg 15] — the same register the real instruction writes.

    HAND-BUILT: the instruction TAIL.  The real tail of [lw a5,0(a4)] is
    NINE nodes, measured on the model: [RegWrite x15] (the loaded value —
    THE VALUE IS USED), then [hart_state] (r), [hart_state] (r),
    [nextPC] (r), [PC] (w), [PC] (r), [minstret_increment] (r),
    [minstret] (r), [minstret] (w), and then [Interface.Ret tt].  Of its
    three WRITES only [x15] is a dependency carrier: [ereg_num PC = None]
    and [ereg_num minstret = None].  [WeakEvProv.taint_closure] — the frame
    law [csync]'s re-convergence rests on — requires EVERY written register
    of a divergent remainder to be a carrier the taint set holds, so it
    cannot absorb the [PC] and [minstret] writes even though both runs
    write them with the SAME value (the PC comes from [nextPC], the
    instret from [minstret_increment]; neither reads the loaded word).
    Admitting the real nine-node tail needs the PAIRED refinement of
    [taint_closure] recorded in §4 below, not a bigger taint set.  The tail
    modelled here is therefore the real one's FIRST node — the destination
    write — followed directly by the boundary.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports it.

    NOT IN [_CoqProject] (the task forbade touching it).  The line to add,
    after [WeakRvwmoWalk2.v]:  [WeakRvwmoCycWit2.v] *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakSrvwmoLitmus.
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
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoConfWit.
Require Import WeakRvwmoConfWit2.
Require Import WeakEvProv.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE NODE: the real load, and a tail that USES the value *)

(** [a5], the real destination of [lw a5,0(a4)]; its dependency carrier. *)
Definition w2_rd : register := R_bitvector_64 x15.
Definition w2_T : list wreg := [15%nat].

Lemma w2_rd_num : ereg_num w2_rd = Some 15%nat.
Proof. by vm_compute. Qed.

(** The tail: WRITE THE LOADED VALUE into [a5], then the boundary. *)
Definition w2_k1 (v : type_of_register w2_rd) : M unit :=
  Interface.Next (Interface.RegWrite w2_rd None v) (fun _ => Interface.Ret tt).

Definition w2_val (ans : (bv (8 * 4) * option bool + Arch.abort)%type)
    : type_of_register w2_rd :=
  match ans with
  | inl (w, _) => Z_to_bv 64 (bv_unsigned w)
  | inr _ => Z_to_bv 64 0
  end.

(** THE NODE: the REAL request of [lw a5,0(a4)], and the tail above. *)
Definition w2_m : M unit :=
  Interface.Next (Interface.MemRead 4 ld_reql) (fun ans => w2_k1 (w2_val ans)).

Definition w2_p0 (cpu : CPU) (rs : regstate) (ib : oib32) : pexv6 :=
  PHart cpu w2_m rs None ib.
Definition w2_p1 (w : bv 32) (cpu : CPU) (rs : regstate) (ib : oib32) : pexv6 :=
  PHart cpu (w2_k1 (w2_val (inl (w, None)))) rs None ib.

(** THE STEP, at EVERY answer: the node accepts any four bytes, and the
    successor node CARRIES THE VALUE — [w2_k1 (w2_val …)] — so two
    different answers are two different nodes.  That is precisely what
    [WeakRvwmoCycWit.cy_node_vindep]'s node does NOT do. *)
Lemma w2_pstep (cpu : CPU) (rs : regstate) (ib : oib32) (d : dev_state)
    (t : nat) (w : bv 32) :
  pstep_ev (w2_p0 cpu rs ib) d
    (WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) [])
    (w2_p1 w cpu rs ib) d.
Proof.
  rewrite /pstep_ev /w2_p0 /w2_p1 /w2_m. split; [reflexivity|].
  exists None, None. split_and!; [reflexivity|reflexivity|]. left.
  rewrite /pstep_node /pnode_step /=.
  split; [done|]. left. split; [done|].
  exists w, (ld_tvs t w). split_and!; try reflexivity.
  intros j Hj. simpl in Hj.
  destruct j as [|[|[|[|j]]]];
    [reflexivity|reflexivity|reflexivity|reflexivity|exfalso; lia].
Qed.

Lemma w2_realizes (cpu : CPU) (rs : regstate) (ib : oib32) (ws : wstate)
    (t : nat) (w : bv 32) :
  hlbl_realizes (w2_p0 cpu rs ib) ws
    (WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w))
    (WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) []).
Proof. rewrite /hlbl_realizes. split_and!; [done|done|done|reflexivity]. Qed.

(* ====================================================================== *)
(** * 2. THE TAIL IS SILENT, AND TERMINATION IS A THEOREM *)

Lemma w2_tail_silent (v : type_of_register w2_rd) : tail_silent w2_T (w2_k1 v).
Proof.
  apply ts_next; [exact I| |intros u; destruct u; apply ts_ret].
  intros r Hr. rewrite /pnode_wrs /= in Hr.
  apply elem_of_list_singleton in Hr. subst r.
  exists 15%nat. split; [exact w2_rd_num|apply elem_of_list_here].
Qed.

(** [tail_silent_run] at the witness node: the hart REACHES the boundary,
    by structural induction on the monad — no progress hypothesis. *)
Theorem w2_reaches_boundary (cpu : CPU) (d0 : dev_state)
    (v : type_of_register w2_rd) (rs : regstate) (ib : oib32) :
  ∃ (ls : list wlabel) (rds : list wreg) (wrs : list register) (ann : bool)
    (rs' : regstate) (ib' : oib32),
    (∀ l0, l0 ∈ ls → lb_admin true l0) ∧ LInstr ∉ ls ∧
    phrun cpu ls rds wrs ann (w2_k1 v) rs None ib d0
      (Interface.Ret tt) rs' None ib' d0 ∧
    (∀ r, r ∈ wrs → ∃ n, ereg_num r = Some n ∧ n ∈ w2_T).
Proof. by apply (tail_silent_run w2_T cpu d0 _ (w2_tail_silent v)). Qed.

(* ====================================================================== *)
(** * 3. THE RE-CONVERGENCE, AT TWO GENUINELY DIFFERENT NODES *)

(** THE SUBSTITUTION IS REAL: different answers, different successor
    nodes.  ([WeakRvwmoCycWit.cy_node_vindep] proves the OPPOSITE at its
    own node, which is why that witness could not test §5b.) *)
Lemma w2_step_any (v : type_of_register w2_rd) (rs : regstate) :
  esil_node_any rs (w2_k1 v)
  = Some (register_set w2_rd v rs, Interface.Ret tt).
Proof. reflexivity. Qed.

Definition w2_wrval (rs : regstate) (m : M unit) : type_of_register w2_rd :=
  match esil_node_any rs m with
  | Some (rs', _) => register_lookup w2_rd rs'
  | None => Z_to_bv 64 0
  end.

Lemma w2_wrval_k1 (v : type_of_register w2_rd) (rs : regstate) :
  w2_wrval rs (w2_k1 v) = v.
Proof. rewrite /w2_wrval w2_step_any. by rewrite register_lookup_set. Qed.

Lemma w2_nodes_differ (v1 v2 : type_of_register w2_rd) :
  v1 ≠ v2 → w2_k1 v1 ≠ w2_k1 v2.
Proof.
  intros Hne Heq. apply Hne.
  by rewrite -(w2_wrval_k1 v1 ld_rs0) -(w2_wrval_k1 v2 ld_rs0) Heq.
Qed.

Lemma w2_values_differ :
  w2_val (inl (Z_to_bv 32 0, None)) ≠ w2_val (inl (Z_to_bv 32 1, None)).
Proof. by vm_compute. Qed.

(** [csync]'s DIVERGED arm, inhabited: two runs at DIFFERENT nodes, both
    inside the same instruction's silent tail, register files agreeing off
    the taint set. *)
Theorem w2_csync (v1 v2 : type_of_register w2_rd) (rs1 rs2 : regstate)
    (ib : oib32) :
  dreg_agree (λ n, n ∉ w2_T) rs1 rs2 →
  csync w2_T (w2_k1 v1) rs1 None ib (w2_k1 v2) rs2 None ib.
Proof.
  intros Hag. right.
  split_and!; [reflexivity|reflexivity|apply w2_tail_silent
              |apply w2_tail_silent|exact Hag].
Qed.

(** ... AND THE RE-CONVERGENCE ITSELF: both runs reach the SAME boundary
    node ([boundary_node_const]) with register files that still agree off
    the taint set ([taint_closure]).  This is (O-2) fired at a value that
    is USED. *)
Theorem w2_reconverge (cpu : CPU) (d0 : dev_state)
    (v1 v2 : type_of_register w2_rd) (rs1 rs2 : regstate) (ib1 ib2 : oib32) :
  dreg_agree (λ n, n ∉ w2_T) rs1 rs2 →
  ∃ (ls1 ls2 : list wlabel) (rds1 rds2 : list wreg)
    (wrs1 wrs2 : list register) (ann1 ann2 : bool)
    (rs1' rs2' : regstate) (ib1' ib2' : oib32),
    phrun cpu ls1 rds1 wrs1 ann1 (w2_k1 v1) rs1 None ib1 d0
      (Interface.Ret tt) rs1' None ib1' d0 ∧
    phrun cpu ls2 rds2 wrs2 ann2 (w2_k1 v2) rs2 None ib2 d0
      (Interface.Ret tt) rs2' None ib2' d0 ∧
    at_boundary (Interface.Ret tt) ∧
    dreg_agree (λ n, n ∉ w2_T) rs1' rs2'.
Proof.
  intros Hag.
  destruct (w2_reaches_boundary cpu d0 v1 rs1 ib1)
    as (ls1 & rds1 & wrs1 & ann1 & rs1' & ib1' & _ & _ & Hr1 & Hw1).
  destruct (w2_reaches_boundary cpu d0 v2 rs2 ib2)
    as (ls2 & rds2 & wrs2 & ann2 & rs2' & ib2' & _ & _ & Hr2 & Hw2).
  exists ls1, ls2, rds1, rds2, wrs1, wrs2, ann1, ann2, rs1', rs2', ib1', ib2'.
  split_and!; [exact Hr1|exact Hr2|apply at_boundary_ret|].
  eapply (taint_closure (λ n, n ∉ w2_T) cpu ls1 rds1 wrs1 ann1
            (w2_k1 v1) rs1 None ib1 d0 (Interface.Ret tt) rs1' None ib1' d0
            cpu ls2 rds2 wrs2 ann2
            (w2_k1 v2) rs2 None ib2 d0 (Interface.Ret tt) rs2' None ib2' d0
            Hag Hr1 Hr2).
  intros r Hr. apply elem_of_app in Hr as [Hr|Hr].
  - destruct (Hw1 r Hr) as (n & Hn & Hin). exists n. split; [exact Hn|].
    intros Hno. by apply Hno.
  - destruct (Hw2 r Hr) as (n & Hn & Hin). exists n. split; [exact Hn|].
    intros Hno. by apply Hno.
Qed.

(* ====================================================================== *)
(** * 4. WHAT THIS WITNESS LEAVES OPEN

    (a) THE REAL NINE-NODE TAIL.  Admitting [lw a5,0(a4)]'s own tail (the
        measurement is in the header) needs [WeakEvProv.taint_closure]
        replaced by a PAIRED law: two runs of the SAME code from
        [k v1] / [k v2] stay in step, absorbing the divergence at the ONE
        write into a tainted carrier and mirroring every later node (whose
        [RegWrite] carries its value IN THE NODE, so both runs write the
        same [PC] and the same [minstret]).  The shape is
        [tail_par T m1 m2] with two arms — [tp_wr] (the tainted write,
        after which the continuations are the SAME term) and [tp_eq]
        (the same node, discharged by [WeakEvProv.phrun_dagree]).

    (b) THE SEGMENT, END TO END.  [WeakRvwmoCert3.cert_segment''] cannot be
        instantiated across the boundary here: [WeakEvInst.pnode_step] at
        [Interface.Ret tt] forces the successor to be [RiscvLang.riscv_step
        tick], so any block AFTER the boundary is the real machine's, and
        its administrative stretch to the next memory node is
        [WeakRvwmoAdm]'s 117-node [la_ls] — which is exactly the tail (a)
        rules out for now.

    (c) THE POLICY INTERFACE IS NODE-BLIND.  [WeakRvwmoWalk.wblk_pol_at] is
        handed a [cblk] and the site's LABEL, never the monad node, so
        neither [tail_silent] nor the read-set clause [rds_ok] can be
        discharged at a site: both are properties of the NODE.  That is the
        same obstruction [WeakRvwmoWalk2] §6.2 priced for [wwit_vindep],
        and it is what stands between §5b and the removal of that premise:
        [cert_segment''] must carry a reachability parameter [Nd : nat → M
        unit → Prop] (its two closure laws are one admin run and one block)
        and hand [Nd k m] to the policy. *)

Print Assumptions w2_pstep.
Print Assumptions w2_reaches_boundary.
Print Assumptions w2_reconverge.
