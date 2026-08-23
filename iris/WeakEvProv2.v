(** * WeakEvProv2.v — THE PAIRED TAINT LAW (route B, the audit's [tail_par])

    THE PROBLEM, from the AUDIT ledger of
    [claude-notes/projects/weak-memory-certification.md] and from
    [WeakRvwmoCycWit2] §4(a).

    [WeakEvProv.taint_closure] is the UNPAIRED frame law: two runs that have
    parted company after a witness read agree off [T] plus whatever EITHER
    remainder wrote, PROVIDED every register either remainder writes is a
    dependency carrier the taint set holds ([ereg_num r = Some n], [n ∈ T]).
    That hypothesis is FALSE at the real tail.  The real tail of
    [lw a5,0(a4)] at [main+0x16] is NINE nodes — measured here in §5, not
    asserted: [RegWrite x15] (the loaded value), then reads of [hart_state]
    twice, [nextPC], a write of [PC], a read of [PC], a read of
    [minstret_increment], a read and a WRITE of [minstret], and then
    [Interface.Ret tt].  Of its three writes only [x15] is a carrier
    ([ereg_num PC = None], [ereg_num minstret = None]), so
    [taint_closure]'s hypothesis fails at node 4 and at node 8 — §5's
    [la_tail_taint_closure_fails] is that failure, machine-checked.  And no
    larger taint set repairs it: [dreg_agree]'s premise is about carriers,
    and a non-carrier is quantified over unconditionally.

    THE LAW.  What is true of those two nodes is not that they are tainted
    but that BOTH RUNS WRITE THEM WITH THE SAME VALUE — the [PC] comes from
    [nextPC], the [minstret] from [minstret_increment], and neither reads the
    loaded word.  In this semantics a [RegWrite]'s value is part of the node
    TERM ([WeakEvInst.pnode_step]'s [RegWrite] arm stores [register_set r v
    rs] with [v] taken from the node), so "both runs write the same value" is
    "both runs are at the same node", and the law is a SIMULATION on node
    PAIRS.

    §2 [tpar T m1 m2] — four arms, each an admissible divergence:
      [tp_conv]   the two runs are at the SAME node (re-converged);
      [tp_gen]    the same non-writing outcome, successors related pointwise
                  — this is the [RegRead] arm (the two runs read the same
                  value because the register files agree off [T] and the
                  read set is taint-free), and also every silent node, the
                  announce, the barrier, a memory node and the [MemWrite]
                  retry self-loop;
      [tp_wr_eq]  a register write of the SAME value from two SYNTACTICALLY
                  DIFFERENT continuations — the [PC]/[minstret] arm,
                  admitted with NO carrier condition;
      [tp_wr]     a register write of DIFFERENT values into a CARRIER the
                  taint set holds — the destination write of the witness
                  load, the one place the divergence is paid for.

    §3 [tpar_run] / [tpar_instr]: two runs from [tpar]-related nodes stay in
    step — the same label list, the same read/write/boundary annotations, the
    same successor channel and fabric, nodes still [tpar]-related and
    register files still agreeing off [T].  Existential in the second run for
    [WeakEvProv.instr_dagree]'s reason (a [Choose] and the boundary's [tick]
    are invisible in the label, so equal labels do not pin equal runs); the
    second run is BUILT at the first one's answers, which is the
    certification's use.  [tpar_boundary]: if the first run has reached the
    boundary so has the second — the re-convergence
    ([WeakRvwmoCert3.boundary_node_const]) as a consequence, not a
    hypothesis.

    §4 [tpar_of_witness]: the two continuations of a [MemRead] at two
    answers are [tpar]-related at [T := rd :: T0] as soon as the answer
    reaches the tail ONLY through the destination write's value — the
    formal content of "[DLdRes] enters at the load's own [LRegW rd] and
    nowhere else" ([WeakEvLang.erw_srcs]).  §4.1 is the LAW's own
    non-vacuity, hand-built so that nothing in §3 holds for want of an
    inhabited step: [tw_tpar] pairs a write of the SAME value into the
    NON-carrier [PC] with a write of DIFFERENT values into the carrier
    [x14] ([tw_nodes_differ]: the two nodes really are different terms),
    [tg_tpar] puts a genuine [RegRead] on top of it ([tp_gen]), and
    [tg_nonvacuous] runs the pair end to end through [tpar_reconverge] —
    two runs at different nodes throughout, re-converging at the boundary
    with register files agreeing off the taint set.

    §5 THE REAL TAIL, the instance [WeakRvwmoCycWit2] could not build.
    [la_tail_par]: the two nine-node tails of the real [lw a5,0(a4)], at two
    arbitrary loaded words, both reach [Interface.Ret tt] with the same
    labels and with register files agreeing off [[15]] — the [PC] and
    [minstret] writes admitted BECAUSE EQUAL.  The node facts are read off
    the machine with [WeakRvwmoAdm]'s reflective cursor: the tail's first
    node is the [x15] write (§5 [la_head_reg]) and its continuation IS THE
    SAME TERM at every answer (§5 [la_head_succ]).

    A COST NOTE WORTH KEEPING (measured, this file).  [la_head_succ] — an
    equation between two MONAD TERMS — is closed by the KERNEL'S LAZY
    conversion ([exact_no_check (@eq_refl (M unit) …)]) in 3.0 s at [Qed],
    and is NOT closable by [vm_cast_no_check]: three runs of that variant
    (two of 2 min, one of over 8 min) all ended with no result, at a FLAT
    0.72 GB — so it is not memory pressure, it is simply not converging.
    This INVERTS the tree's usual advice, and the reason is READBACK.  The VM has to
    materialise the NORMAL FORM of the result, and the result here is an
    [M unit]: every unexecuted branch of the Sail step function, under every
    continuation's binder.  Lazy conversion never builds it — it compares
    weak head normal forms and short-circuits the instant two subterms are
    syntactically equal, which after the destination write they are.  The
    rule to carry: [vm_cast_no_check] for a computation whose RESULT is a
    label, a count, a request or a register (§5 uses it seven times, each
    under 0.1 s); the kernel's lazy conversion when the result is a monad
    term.

    A LEAF: nothing imports it, and [WeakEvProv.v] is untouched.  Nothing
    below is [Admitted] or [Axiom]-ed.

    NOT IN [_CoqProject] (the task forbade touching it).  The line to add,
    after [WeakRvwmoCycWit2.v]:  [WeakEvProv2.v] *)
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
Require Import WeakPromise.
Require Import WeakInterp.
Require Import RiscvLang RiscvPtsto.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakEvLift.
Require Import WeakEvProv.
Require Import WeakRvwmoAdm.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE ONE MISSING AGREEMENT LEMMA

    [WeakEvProv.dreg_agree_set] covers a write of the SAME value on both
    sides, [dreg_agree_excl] a write on ONE side into an excluded carrier.
    The paired law needs the two combined: a write on BOTH sides, of
    POSSIBLY DIFFERENT values, into a carrier the agreement excludes. *)

Lemma dreg_agree_excl2 (P : wreg → Prop) (rs1 rs2 : regstate)
    (r : register) (v1 v2 : type_of_register r) :
  (∃ n, ereg_num r = Some n ∧ ¬ P n) →
  dreg_agree P rs1 rs2 →
  dreg_agree P (register_set r v1 rs1) (register_set r v2 rs2).
Proof.
  intros (n & Hn & HP) Hag r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - exfalso. by apply HP, Hr'.
  - rewrite (irrelevant_register_set r' r _ v1 (register_beq_false r' r Hne))
            (irrelevant_register_set r' r _ v2 (register_beq_false r' r Hne)).
    by apply Hag.
Qed.

(** THREE SMALL TOTAL PROJECTIONS OF A REGISTER-WRITE NODE, in
    [WeakRvwmoAdm.eread_width]'s style: the register written, the successor
    node, and the write's effect on a register file.  They are what lets a
    SITE discharge the law's node hypotheses by computation, without ever
    writing a Sail continuation down. *)

Definition mrw_reg (m : M unit) : option register :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc _ =>
      match oc with Interface.RegWrite r _ _ => Some r | _ => None end
  end.

Definition mrw_succ (m : M unit) : M unit :=
  match m with
  | Interface.Ret _ => Interface.Ret tt
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ A return (A → M unit) → M unit with
       | Interface.RegWrite _ _ _ => λ k, k tt
       | _ => λ _, Interface.Ret tt
       end) k
  end.

Definition mrw_set (m : M unit) (rs : regstate) : regstate :=
  match m with
  | Interface.Ret _ => rs
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ A return (A → M unit) → regstate with
       | Interface.RegWrite r _ v => λ _, register_set r v rs
       | _ => λ _, rs
       end) k
  end.

(* ====================================================================== *)
(** * 2. THE RELATION *)

Inductive tpar (T : list wreg) : M unit → M unit → Prop :=
(** RE-CONVERGED: the two runs are at the same node.  No side condition —
    the run-level hypothesis [rds_ok] of §3 is what forbids the two runs
    from re-diverging at a read of a TAINTED carrier. *)
| tp_conv (m : M unit) : tpar T m m
(** THE SAME NON-WRITING OUTCOME, successors related pointwise.  At a
    [RegRead] the two runs take the same value because the register files
    agree off [T] and [rds_ok] says the register is not tainted; at a memory
    node the second run is built at the first one's answer. *)
| tp_gen (A : Type) (oc : Interface.outcome (λ _ : Type, exception) A)
    (k1 k2 : A → M unit) :
    pnode_wrs (Interface.Next oc k1) = [] →
    (∀ v : A, tpar T (k1 v) (k2 v)) →
    tpar T (Interface.Next oc k1) (Interface.Next oc k2)
(** A REGISTER WRITE OF THE SAME VALUE, from two continuations that need not
    be the same term.  NO carrier condition: this is the arm that admits the
    [PC] and [minstret] writes of a real instruction tail. *)
| tp_wr_eq (r : register) (ak : option Arch.sys_reg_id)
    (v : type_of_register r) (k1 k2 : unit → M unit) :
    tpar T (k1 tt) (k2 tt) →
    tpar T (Interface.Next (Interface.RegWrite r ak v) k1)
           (Interface.Next (Interface.RegWrite r ak v) k2)
(** A REGISTER WRITE OF DIFFERENT VALUES INTO A TAINTED CARRIER — the
    witness's destination.  The access kinds may differ too: [pnode_step]
    reads neither. *)
| tp_wr (r : register) (ak1 ak2 : option Arch.sys_reg_id) (n : wreg)
    (v1 v2 : type_of_register r) (k1 k2 : unit → M unit) :
    ereg_num r = Some n → n ∈ T →
    tpar T (k1 tt) (k2 tt) →
    tpar T (Interface.Next (Interface.RegWrite r ak1 v1) k1)
           (Interface.Next (Interface.RegWrite r ak2 v2) k2).

(** THE BOUNDARY IS SHARED.  If the first run has reached [Interface.Ret y]
    so has the second, at the SAME [y]: the other three arms have a
    [Interface.Next] on the left.  This is
    [WeakRvwmoCert3.boundary_node_const]'s content without its two
    [at_boundary] hypotheses. *)
Lemma tpar_boundary (T : list wreg) (y : unit) (m : M unit) :
  tpar T (Interface.Ret y) m → m = Interface.Ret y.
Proof. by inversion 1. Qed.

(** ... and the mirror. *)
Lemma tpar_boundary_r (T : list wreg) (y : unit) (m : M unit) :
  tpar T m (Interface.Ret y) → m = Interface.Ret y.
Proof. by inversion 1. Qed.

(* ====================================================================== *)
(** * 3. THE SIMULATION *)

(** ONE NON-WRITING NODE, paired.  The second run's step is CONSTRUCTED from
    the first one's — same label, same channel move, same fabric, and (at a
    memory node) the same answer. *)
Lemma pnode_step_pair (T : list wreg) (A0 : Type)
    (oc : Interface.outcome (λ _ : Type, exception) A0) (k1 k2 : A0 → M unit)
    (rs1 rs2 : regstate) (ib : oib32) (d : dev_state) (l : wlabel)
    (m1' : M unit) (ors1 : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) :
  pnode_wrs (Interface.Next oc k1) = [] →
  rds_ok (λ n, n ∉ T) (pnode_rds (Interface.Next oc k1)) →
  (∀ v : A0, tpar T (k1 v) (k2 v)) →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  pnode_step (Interface.Next oc k1) rs1 ib d l m1' ors1 fn' d' oib →
  ors1 = None ∧
  ∃ m2' : M unit,
    pnode_step (Interface.Next oc k2) rs2 ib d l m2' None fn' d' oib ∧
    tpar T m1' m2'.
Proof.
  intros Hw Hrds Hk Hag Hst.
  destruct oc as [rr ak | rr ak vv | nn rq | nn rq | ob | sz pa1 | bb | co
                 | to | ff | pa2 | ts | te | A1 eo | msg1 | | | ty | | msg2];
    simpl in Hw, Hrds, Hst |- *.
  - (* RegRead — THE ONE PLACE THE REGISTER FILE IS CONSULTED *)
    have Hlk : register_lookup rr rs1 = register_lookup rr rs2.
    { apply Hag. intros n Hn. exact (pnode_rds_read rr ak k1 _ n Hrds Hn). }
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 (register_lookup rr rs2)).
    split; [by split_and!|]. rewrite Hlk. apply Hk.
  - (* RegWrite — excluded by the written-set hypothesis *)
    by destruct (Hw : [rr] = []).
  - (* MemRead *)
    destruct (dev_addr (Interface.ReadReq.pa rq)) eqn:Hdev.
    + destruct Hst as (w & Hrd & -> & -> & -> & -> & ->).
      split; [reflexivity|]. exists (k2 (inl (w, None))).
      split; [|apply Hk]. by exists w; split_and!.
    + destruct Hst as (Hcoh & [ (Hlat & w & tvs & Hlen & Hby & -> & -> & -> & -> & -> & ->)
                              | (Hlat & w & tvs & Hlen & Hby & -> & -> & -> & -> & -> & ->) ]).
      * split; [reflexivity|]. exists (k2 (inl (w, None))).
        split; [|apply Hk]. split; [exact Hcoh|]. left.
        split; [exact Hlat|]. by exists w, tvs; split_and!.
      * split; [reflexivity|]. exists (k2 (inl (w, None))).
        split; [|apply Hk]. split; [exact Hcoh|]. right.
        split; [exact Hlat|]. by exists w, tvs; split_and!.
  - (* MemWrite *)
    destruct (dev_addr (Interface.WriteReq.pa rq)) eqn:Hdev.
    + destruct Hst as (Hwr & -> & -> & -> & -> & ->).
      split; [reflexivity|]. exists (k2 (inl None)).
      split; [|apply Hk]. by split_and!.
    + destruct Hst as (Hn0 & [ (Hlat & -> & -> & -> & -> & -> & ->)
                             | (Hlat & [ (-> & -> & -> & -> & -> & ->)
                                       | (-> & -> & -> & -> & -> & ->) ]) ]).
      * split; [reflexivity|]. exists (k2 (inl None)).
        split; [|apply Hk]. split; [exact Hn0|]. left.
        by split_and!.
      * split; [reflexivity|]. exists (k2 (inl None)).
        split; [|apply Hk]. split; [exact Hn0|]. right.
        split; [exact Hlat|]. left. by split_and!.
      * (* THE RETRY SELF-LOOP: the successor is the node itself *)
        split; [reflexivity|].
        exists (Interface.Next (Interface.MemWrite nn rq) k2).
        split.
        { split; [exact Hn0|]. right. split; [exact Hlat|].
          right. by split_and!. }
        by apply tp_gen.
  - (* InstrAnnounce *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* BranchAnnounce *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* Barrier *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* CacheOp *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* TlbOp *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* TakeException *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* ReturnException *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* TranslationStart *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* TranslationEnd *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* ExtraOutcome — STUCK *) by destruct Hst.
  - (* GenericFail — STUCK *) by destruct Hst.
  - (* CycleCount *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
  - (* GetCycleCount *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 0%Z). split; [by split_and!|apply Hk].
  - (* Choose *)
    destruct Hst as (ch & -> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 ch).
    split; [by exists ch; split_and!|apply Hk].
  - (* Discard — STUCK *) by destruct Hst.
  - (* Message *)
    destruct Hst as (-> & -> & -> & -> & -> & ->).
    split; [reflexivity|]. exists (k2 tt). split; [by split_and!|apply Hk].
Qed.

(** ONE HART STEP, paired: the annotations ([rds], [ws], [ann]) are carried
    UNCHANGED to the second run — the two runs read the same registers,
    write the same registers and cross the same boundaries. *)
Lemma tpar_step (T : list wreg) (cpu : CPU) (m1 m2 : M unit)
    (rs1 rs2 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (l : wlabel) (rds : list wreg)
    (ws : list register) (ann : bool) (m1' : M unit)
    (ors1 : option regstate) (fn' : option (bool * bool * bool * bool))
    (d' : dev_state) (oib : option oib32) :
  pstep_hw cpu m1 rs1 fn ib d l rds ws ann m1' ors1 fn' d' oib →
  tpar T m1 m2 →
  rds_ok (λ n, n ∉ T) rds →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  ∃ (m2' : M unit) (ors2 : option regstate),
    pstep_hw cpu m2 rs2 fn ib d l rds ws ann m2' ors2 fn' d' oib ∧
    tpar T m1' m2' ∧
    dreg_agree (λ n, n ∉ T) (default rs1 ors1) (default rs2 ors2).
Proof.
  intros Hhw Htp Hrds Hag.
  destruct Hhw as [ (Hfn & Hst & Hr & Hw & Ha)
                  | [ (pr & pw & sr & sw & Hfn & Hst & Hr & Hw & Ha)
                    | (Hst & Hr & Hw & Ha) ] ].
  - (* THE MONAD NODE *)
    subst fn rds ws ann.
    destruct Htp as [m|A0 oc k1 k2 Hnw Hk|r ak v k1 k2 Hk
                    |r ak1 ak2 n v1 v2 k1 k2 Hn HnT Hk].
    + (* RE-CONVERGED: [WeakEvProv]'s own lockstep step serves *)
      destruct (pnode_step_dagree (λ n, n ∉ T) m rs1 rs2 ib d l m1' ors1 fn'
                  d' oib Hrds Hag Hst) as (ors2 & Hst2 & Hag2).
      exists m1', ors2. split_and!.
      * left. by split_and!.
      * apply tp_conv.
      * exact Hag2.
    + (* THE SAME NON-WRITING OUTCOME *)
      destruct (pnode_step_pair T A0 oc k1 k2 rs1 rs2 ib d l m1' ors1 fn' d'
                  oib Hnw Hrds Hk Hag Hst) as (Hors & m2' & Hst2 & Htp2).
      subst ors1. exists m2', None. split_and!.
      * left. by split_and!.
      * exact Htp2.
      * exact Hag.
    + (* THE SAME VALUE WRITTEN — the [PC]/[minstret] arm *)
      destruct Hst as (Hl & Hm & Hors & Hfn' & Hd' & Hoib).
      subst l m1' ors1 fn' d' oib.
      exists (k2 tt), (Some (register_set r v rs2)). split_and!.
      * left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
        by split_and!.
      * exact Hk.
      * simpl. by apply dreg_agree_set.
    + (* DIFFERENT VALUES INTO A TAINTED CARRIER *)
      destruct Hst as (Hl & Hm & Hors & Hfn' & Hd' & Hoib).
      subst l m1' ors1 fn' d' oib.
      exists (k2 tt), (Some (register_set r v2 rs2)). split_and!.
      * left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
        by split_and!.
      * exact Hk.
      * simpl. apply dreg_agree_excl2; [|exact Hag].
        exists n. split; [exact Hn|]. by intros Hno.
  - (* THE PARKED FENCE: the node does not move *)
    subst fn rds ws ann.
    destruct Hst as (Hl & Hm & Hors & Hfn' & Hd' & Hoib).
    subst l m1' ors1 fn' d' oib.
    exists m2, None. split_and!; [|exact Htp|exact Hag].
    right; left. exists pr, pw, sr, sw. by split_and!.
  - (* THE PLIC WIRE: the node does not move, and both runs write the same
       [sig_seip] — it is read off the fabric, which they share *)
    subst rds ws ann.
    destruct Hst as (Hl & Hm & Hfn' & Hd' & Hoib & Hors).
    subst l m1' fn' d' oib ors1.
    exists m2, (Some (register_set sig_seip
                        (bool_to_bit (dev_seip d (fin_to_nat cpu))) rs2)).
    split_and!; [|exact Htp|].
    + right; right. by split_and!.
    + simpl. by apply dreg_agree_set.
Qed.

(** THE LAW.  Two runs from [tpar]-related nodes stay in step to whatever
    the first one reaches; the taint set does NOT grow along the way (it was
    grown once, at the witness — see [tpar_of_witness]). *)
Theorem tpar_run (T : list wreg) (cpu : CPU) (ls : list wlabel)
    (rds : list wreg) (ws : list register) (ann : bool)
    (m1 : M unit) (rs1 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (m1' : M unit) (rs1' : regstate)
    (fn' : option (bool * bool * bool * bool)) (ib' : oib32) (d' : dev_state)
    (m2 : M unit) (rs2 : regstate) :
  phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
  tpar T m1 m2 →
  rds_ok (λ n, n ∉ T) rds →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  ∃ (m2' : M unit) (rs2' : regstate),
    phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
    tpar T m1' m2' ∧ dreg_agree (λ n, n ∉ T) rs1' rs2'.
Proof.
  intros Hrun. revert m2 rs2.
  induction Hrun as [m rs fn ib d|l ls rds rds' ws ws' ann ann' m rs fn ib d
                       m1a ors fn1 oib d1 m2a rs2a fn2 ib2 d2 Hstep Hrun IH];
    intros mb rsb Htp Hrds Hag.
  { exists mb, rsb. split_and!; [apply phrun_nil|exact Htp|exact Hag]. }
  apply rds_ok_app in Hrds as [Hrds1 Hrds2].
  destruct (tpar_step T cpu m mb rs rsb fn ib d l rds ws ann m1a ors fn1 d1
              oib Hstep Htp Hrds1 Hag) as (mb1 & orsb & Hstepb & Htp1 & Hagb).
  destruct (IH mb1 (default rsb orsb) Htp1 Hrds2 Hagb)
    as (mb' & rsb' & Hrunb & Htp' & Hag').
  exists mb', rsb'. split_and!; [|exact Htp'|exact Hag'].
  by eapply phrun_more; [exact Hstepb|exact Hrunb].
Qed.

(** ... at [WeakEvProv.instr_dagree]'s hypothesis shape: the read-set clause
    is about the CHANNEL the run ends with, and "the run stays inside one
    instruction" is the checkable [LInstr ∉ ls]. *)
Theorem tpar_instr (T : list wreg) (cpu : CPU) (ls : list wlabel)
    (rds : list wreg) (ws : list register) (ann : bool)
    (m1 : M unit) (rs1 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (m1' : M unit) (rs1' : regstate)
    (fn' : option (bool * bool * bool * bool)) (ib' : oib32) (d' : dev_state)
    (m2 : M unit) (rs2 : regstate) :
  phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
  tpar T m1 m2 →
  LInstr ∉ ls →
  (∀ n, n ∈ ib_rds ib' → n ∉ T) →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  ∃ (m2' : M unit) (rs2' : regstate),
    phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
    tpar T m1' m2' ∧ dreg_agree (λ n, n ∉ T) rs1' rs2'.
Proof.
  intros Hrun Htp Hni Hib Hag.
  have Hann : ann = false.
  { by eapply phrun_no_instr; [exact Hrun|exact Hni]. }
  have Hcov : ib_rds ib' = ib_rds ib ++ rds.
  { by eapply phrun_ib_rds; [exact Hrun|exact Hann]. }
  eapply tpar_run; [exact Hrun|exact Htp| |exact Hag].
  intros n Hn. apply Hib. rewrite Hcov. apply elem_of_app. by right.
Qed.

(** THE RE-CONVERGENCE, as a corollary rather than a hypothesis: if the
    first run stops at the instruction boundary, so does the second. *)
Corollary tpar_reconverge (T : list wreg) (cpu : CPU) (ls : list wlabel)
    (rds : list wreg) (ws : list register) (ann : bool)
    (m1 : M unit) (rs1 : regstate) (ib : oib32) (d : dev_state)
    (rs1' : regstate) (ib' : oib32) (m2 : M unit) (rs2 : regstate) :
  phrun cpu ls rds ws ann m1 rs1 None ib d (Interface.Ret tt) rs1' None ib' d →
  tpar T m1 m2 →
  rds_ok (λ n, n ∉ T) rds →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  ∃ rs2' : regstate,
    phrun cpu ls rds ws ann m2 rs2 None ib d (Interface.Ret tt) rs2' None ib' d ∧
    dreg_agree (λ n, n ∉ T) rs1' rs2'.
Proof.
  intros Hrun Htp Hrds Hag.
  destruct (tpar_run T cpu ls rds ws ann m1 rs1 None ib d (Interface.Ret tt)
              rs1' None ib' d m2 rs2 Hrun Htp Hrds Hag)
    as (m2' & rs2' & Hrunb & Htp' & Hag').
  rewrite (tpar_boundary T tt m2' Htp') in Hrunb.
  by exists rs2'.
Qed.

(* ====================================================================== *)
(** * 4. THE WITNESS STEP, AND THE TAINT SET'S ONE GROWTH

    [tpar_of_witness]: the two continuations of a [MemRead] node at two
    different answers are [tpar]-related at the EXTENDED taint set
    [rd :: T0] as soon as the answer reaches the tail only through the
    destination register's written VALUE.  That side condition is not an
    assumption about the semantics: it is a property of the node, checked
    at the site — §5 checks it at the real [lw]. *)

Lemma tpar_of_witness (T : list wreg) (r : register)
    (ak1 ak2 : option Arch.sys_reg_id) (n : wreg)
    (v1 v2 : type_of_register r) (k : unit → M unit) :
  ereg_num r = Some n → n ∈ T →
  tpar T (Interface.Next (Interface.RegWrite r ak1 v1) k)
         (Interface.Next (Interface.RegWrite r ak2 v2) k).
Proof.
  intros Hn HnT. eapply tp_wr; [exact Hn|exact HnT|apply tp_conv].
Qed.

(** ... and the taint set's one growth, in [WeakEvProv.taint_closure_load]'s
    form: the incoming agreement is off [T], the outgoing off [rd :: T]. *)
Corollary tpar_run_load (T : list wreg) (rd : wreg) (cpu : CPU)
    (ls : list wlabel) (rds : list wreg) (ws : list register) (ann : bool)
    (m1 : M unit) (rs1 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (m1' : M unit) (rs1' : regstate)
    (fn' : option (bool * bool * bool * bool)) (ib' : oib32) (d' : dev_state)
    (m2 : M unit) (rs2 : regstate) :
  phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
  tpar (rd :: T) m1 m2 →
  rds_ok (λ n, n ∉ rd :: T) rds →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  ∃ (m2' : M unit) (rs2' : regstate),
    phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
    tpar (rd :: T) m1' m2' ∧ dreg_agree (λ n, n ∉ rd :: T) rs1' rs2'.
Proof.
  intros Hrun Htp Hrds Hag.
  eapply tpar_run; [exact Hrun|exact Htp|exact Hrds|].
  eapply dreg_agree_mono; [|exact Hag].
  intros n Hn Hin. apply Hn, elem_of_list_further, Hin.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.1 NON-VACUITY OF THE LAW ITSELF

    A two-node hand-built pair that exercises BOTH write arms at once: a
    write of the SAME value into a NON-CARRIER ([PC], [ereg_num PC = None] —
    the write [WeakEvProv.taint_closure] cannot absorb), and then a write of
    DIFFERENT values into the carrier [x14], which the taint set holds.  The
    two nodes are genuinely different terms. *)

Definition tw_m (v : type_of_register (R_bitvector_64 x14)) : M unit :=
  Interface.Next (Interface.RegWrite PC None (Z_to_bv 64 4))
    (λ _, Interface.Next (Interface.RegWrite (R_bitvector_64 x14) None v)
            (λ _, Interface.Ret tt)).

Lemma tw_pc_not_carrier : ereg_num PC = None.
Proof. by vm_compute. Qed.

Lemma tw_x14_carrier : ereg_num (R_bitvector_64 x14) = Some 14%nat.
Proof. by vm_compute. Qed.

Lemma tw_tpar (v1 v2 : type_of_register (R_bitvector_64 x14)) :
  tpar [14%nat] (tw_m v1) (tw_m v2).
Proof.
  rewrite /tw_m. apply tp_wr_eq.
  eapply tp_wr; [apply tw_x14_carrier|apply elem_of_list_here|apply tp_conv].
Qed.

(** The two nodes are NOT equal when the values differ, so [tp_conv] alone
    could not have served. *)
Lemma tw_nodes_differ (rs : regstate)
    (v1 v2 : type_of_register (R_bitvector_64 x14)) :
  tw_m v1 = tw_m v2 → v1 = v2.
Proof.
  intros Heq.
  have Hpr : ∀ v : type_of_register (R_bitvector_64 x14),
    register_lookup (R_bitvector_64 x14) (mrw_set (mrw_succ (tw_m v)) rs) = v.
  { intros v. by rewrite /tw_m /mrw_succ /mrw_set register_lookup_set. }
  by rewrite -(Hpr v1) -(Hpr v2) Heq.
Qed.

(** [tp_gen] inhabited too, at a genuine [RegRead] whose two continuations
    are DIFFERENT terms: the read register is not tainted, so both runs take
    the same value and the pair descends into §4.1's write pair. *)
Definition tg_m
    (g : type_of_register (R_bitvector_64 x13) →
         type_of_register (R_bitvector_64 x14)) : M unit :=
  Interface.Next (Interface.RegRead (R_bitvector_64 x13) None)
    (λ u, tw_m (g u)).

Lemma tg_tpar (g1 g2 : type_of_register (R_bitvector_64 x13) →
                       type_of_register (R_bitvector_64 x14)) :
  tpar [14%nat] (tg_m g1) (tg_m g2).
Proof. apply tp_gen; [reflexivity|]. intros u. apply tw_tpar. Qed.

(** ... and a RUN of it, so that nothing in §3 is true merely for want of an
    inhabited step: three nodes, reading the carrier [x13], writing the
    NON-carrier [PC] and the carrier [x14], then the boundary. *)
Lemma tg_run (cpu : CPU) (rs : regstate) (d : dev_state)
    (g : type_of_register (R_bitvector_64 x13) →
         type_of_register (R_bitvector_64 x14)) :
  ∃ (ls : list wlabel) (rds : list wreg) (ws : list register) (ann : bool)
    (rs' : regstate) (ib' : oib32),
    phrun cpu ls rds ws ann (tg_m g) rs None ib_none d
      (Interface.Ret tt) rs' None ib' d ∧
    rds = [13%nat] ∧
    ws = [(PC : register); (R_bitvector_64 x14 : register)] ∧
    LInstr ∉ ls.
Proof.
  eexists _, _, _, _, _, _. split_and!.
  - eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /tg_m /pnode_step. by split_and!. }
    eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /tw_m /pnode_step. by split_and!. }
    eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /pnode_step. by split_and!. }
    apply phrun_nil.
  - by vm_compute.
  - by vm_compute.
  - intros Hin. apply elem_of_cons in Hin as [Hin|Hin]; [discriminate Hin|].
    apply elem_of_cons in Hin as [Hin|Hin]; [by destruct (erw_of _ _ _)|].
    apply elem_of_cons in Hin as [Hin|Hin];
      [by destruct (erw_of _ _ _)|by apply elem_of_nil in Hin].
Qed.

(** THE LAW AT THAT PAIR, end to end: two runs that are at DIFFERENT nodes
    throughout, writing a non-carrier with the same value and a carrier with
    different ones, re-converge at the boundary with register files agreeing
    off the taint set. *)
Example tg_nonvacuous (cpu : CPU) (rs1 rs2 : regstate) (d : dev_state)
    (g1 g2 : type_of_register (R_bitvector_64 x13) →
             type_of_register (R_bitvector_64 x14)) :
  dreg_agree (λ n, n ∉ [14%nat]) rs1 rs2 →
  ∃ (ls : list wlabel) (ann : bool) (rs1' rs2' : regstate) (ib' : oib32),
    LInstr ∉ ls ∧
    phrun cpu ls [13%nat] [(PC : register); (R_bitvector_64 x14 : register)]
      ann (tg_m g1) rs1 None ib_none d (Interface.Ret tt) rs1' None ib' d ∧
    phrun cpu ls [13%nat] [(PC : register); (R_bitvector_64 x14 : register)]
      ann (tg_m g2) rs2 None ib_none d (Interface.Ret tt) rs2' None ib' d ∧
    dreg_agree (λ n, n ∉ [14%nat]) rs1' rs2'.
Proof.
  intros Hag.
  destruct (tg_run cpu rs1 d g1)
    as (ls & rds & ws & ann & rs1' & ib' & Hrun1 & -> & -> & Hni).
  destruct (tpar_reconverge [14%nat] cpu ls [13%nat]
              [(PC : register); (R_bitvector_64 x14 : register)] ann
              (tg_m g1) rs1 ib_none d rs1' ib' (tg_m g2) rs2
              Hrun1 (tg_tpar g1 g2)
              ltac:(intros n Hn; apply elem_of_list_singleton in Hn as ->;
                    intros Hin; apply elem_of_list_singleton in Hin;
                    discriminate Hin)
              Hag) as (rs2' & Hrun2 & Hag2).
  by exists ls, ann, rs1', rs2', ib'.
Qed.

(* ====================================================================== *)
(** * 5. THE REAL TAIL — the instance [WeakRvwmoCycWit2] could not build

    The node is [WeakRvwmoAdm]'s: hart 1's spin load [lw a5,0(a4)] at
    [main+0x16], its request read off the machine ([la_load_req]: width 4 at
    [&started], plain, RAM), resumed at an ARBITRARY loaded word.  Every fact
    below is a projection computed by the reflective cursor — nothing about
    the tail is written down. *)

Definition la_st (w : bv 32) : aht := ah_read (bv_unsigned w) la_x2.
Definition la_tl (w : bv 32) : M unit := ah_m (la_st w).
Definition la_end (w : bv 32) : aht := adm_iter false 9 (la_st w).

(** (i) THE TAIL'S FIRST NODE IS THE DESTINATION WRITE, at every answer. *)
Lemma la_head_reg (w : bv 32) : mrw_reg (la_tl w) = Some (R_bitvector_64 x15).
Proof. vm_cast_no_check (eq_refl (Some (R_bitvector_64 x15))). Qed.

Lemma la_rd_carrier : ereg_num (R_bitvector_64 x15) = Some 15%nat.
Proof. by vm_compute. Qed.

(** (ii) THE ANSWER REACHES THE TAIL ONLY THROUGH THAT WRITE'S VALUE: the
    node's CONTINUATION is the SAME TERM at two arbitrary answers.  This is
    the machine-checked form of "[DLdRes] enters at the load's own
    [LRegW rd] and nowhere else" ([WeakEvLang.erw_srcs]) — and it is the
    hypothesis [tpar_of_witness] asks a site for.

    CLOSED BY THE KERNEL'S LAZY CONVERSION, NOT BY THE VM: see the header's
    cost note (4.2 s here; [vm_cast_no_check] does not finish). *)
Lemma la_head_succ (w1 w2 : bv 32) :
  mrw_succ (la_tl w1) = mrw_succ (la_tl w2).
Proof. exact_no_check (@eq_refl (M unit) (mrw_succ (la_tl w1))). Qed.

(** THE RECONSTRUCTION: [tpar_of_witness] at the two computed projections,
    so a site never has to exhibit a Sail continuation. *)
Lemma tpar_of_rw (T : list wreg) (m1 m2 : M unit) (r : register) (n : wreg) :
  mrw_reg m1 = Some r → mrw_reg m2 = Some r →
  ereg_num r = Some n → n ∈ T →
  mrw_succ m1 = mrw_succ m2 →
  tpar T m1 m2.
Proof.
  intros H1 H2 Hn HnT Hs.
  destruct m1 as [y1|A1 oc1 k1]; [discriminate H1|].
  destruct oc1; try discriminate H1.
  destruct m2 as [y2|A2 oc2 k2]; [discriminate H2|].
  destruct oc2; try discriminate H2.
  simpl in H1, H2, Hs. injection H1 as H1. injection H2 as H2. subst reg reg0.
  eapply tp_wr; [exact Hn|exact HnT|]. rewrite Hs. apply tp_conv.
Qed.

(** ... AND THE PAIRING ITSELF, at the real node. *)
Theorem la_tpar (w1 w2 : bv 32) : tpar [15%nat] (la_tl w1) (la_tl w2).
Proof.
  eapply tpar_of_rw;
    [apply la_head_reg|apply la_head_reg|apply la_rd_carrier
    |apply elem_of_list_here|apply la_head_succ].
Qed.

(** (iii) THE TAIL'S SHAPE, computed: nine nodes, no instruction boundary
    among them (the boundary is node 9, [WeakRvwmoAdm.la_stretch_instr]),
    and the channel is untouched — the tail reads no dependency carrier. *)
Lemma la_end_ret (w : bv 32) : ah_m (la_end w) = Interface.Ret tt.
Proof. vm_cast_no_check (@eq_refl (M unit) (Interface.Ret tt)). Qed.

Lemma la_ls_len (w : bv 32) : length (adm_lbls false 9 (la_st w)) = 9%nat.
Proof. vm_cast_no_check (eq_refl 9%nat). Qed.

Lemma la_ls_val (w : bv 32) :
  adm_lbls false 9 (la_st w) =
  LRegW 15 [DLdRes; DReg 14; DReg 39; DReg 45; DReg 44]
  :: LSilent :: LSilent :: LSilent :: LSilent
  :: LSilent :: LSilent :: LSilent :: LSilent :: [].
Proof.
  vm_cast_no_check
    (eq_refl (LRegW 15 [DLdRes; DReg 14; DReg 39; DReg 45; DReg 44]
              :: LSilent :: LSilent :: LSilent :: LSilent
              :: LSilent :: LSilent :: LSilent :: LSilent :: [])).
Qed.

Lemma la_ls_no_instr (w : bv 32) : LInstr ∉ adm_lbls false 9 (la_st w).
Proof.
  rewrite la_ls_val. intros Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]; [discriminate Hin|]).
  by apply elem_of_nil in Hin.
Qed.

Lemma la_end_ibrds (w : bv 32) :
  ib_rds (ah_ib (la_end w)) = ib_rds (ah_ib la_x2).
Proof. vm_cast_no_check (eq_refl (ib_rds (ah_ib la_x2))). Qed.

Lemma la_x2_no_rd : bool_decide (15%nat ∈ ib_rds (ah_ib la_x2)) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Lemma la_end_untainted (w : bv 32) :
  ∀ n, n ∈ ib_rds (ah_ib (la_end w)) → n ∉ [15%nat].
Proof.
  intros n Hn Hin. apply elem_of_list_singleton in Hin as ->.
  have H15 : ¬ (15%nat ∈ ib_rds (ah_ib la_x2)).
  { apply (proj1 (bool_decide_eq_false _)). exact la_x2_no_rd. }
  apply H15. rewrite -(la_end_ibrds w). exact Hn.
Qed.

(** (iv) WHY THE UNPAIRED LAW CANNOT DO IT.  Node 4 of the tail writes [PC]
    and node 8 writes [minstret]; neither is a dependency carrier, so
    [WeakEvProv.taint_closure]'s hypothesis — every register a divergent
    remainder writes is a carrier IN the taint set — is FALSE here, at any
    taint set whatsoever. *)
Lemma la_tail_writes_pc (w : bv 32) :
  pnode_wrs (ah_m (adm_iter false 4 (la_st w))) = [(PC : register)].
Proof. vm_cast_no_check (eq_refl [(PC : register)]). Qed.

Lemma la_tail_writes_minstret (w : bv 32) :
  pnode_wrs (ah_m (adm_iter false 8 (la_st w))) = [(minstret : register)].
Proof. vm_cast_no_check (eq_refl [(minstret : register)]). Qed.

Lemma la_pc_not_carrier : ereg_num PC = None.
Proof. by vm_compute. Qed.

Lemma la_minstret_not_carrier : ereg_num minstret = None.
Proof. by vm_compute. Qed.

Theorem la_tail_taint_closure_fails (T : list wreg) (w : bv 32) :
  ¬ (∀ r, r ∈ pnode_wrs (ah_m (adm_iter false 4 (la_st w))) →
       ∃ n, ereg_num r = Some n ∧ n ∈ T)
  ∧ ¬ (∀ r, r ∈ pnode_wrs (ah_m (adm_iter false 8 (la_st w))) →
       ∃ n, ereg_num r = Some n ∧ n ∈ T).
Proof.
  split; intros Hall.
  - destruct (Hall PC ltac:(rewrite la_tail_writes_pc; apply elem_of_list_here))
      as (n & Hn & _).
    by rewrite la_pc_not_carrier in Hn.
  - destruct (Hall minstret
                ltac:(rewrite la_tail_writes_minstret; apply elem_of_list_here))
      as (n & Hn & _).
    by rewrite la_minstret_not_carrier in Hn.
Qed.

(** (v) THE RUN, from [WeakRvwmoAdm]'s once-proven bridge. *)
Lemma la_phrun (cpu : CPU) (d : dev_state) (w : bv 32) :
  ∃ (rds : list wreg) (ws : list register) (ann : bool),
    phrun cpu (adm_lbls false 9 (la_st w)) rds ws ann
      (la_tl w) (ah_rs la_x2) None (ah_ib la_x2) d
      (Interface.Ret tt) (ah_rs (la_end w)) None (ah_ib (la_end w)) d.
Proof.
  destruct (pevrun_phrun (adm_lbls false 9 (la_st w)) (ahP cpu (la_st w)) d
              (ahP cpu (la_end w)) d (pevrun_of_iter false 9 cpu d (la_st w))
              cpu (la_tl w) (ah_rs la_x2) None (ah_ib la_x2)
              (ah_m (la_end w)) (ah_rs (la_end w)) None (ah_ib (la_end w))
              eq_refl eq_refl) as (rds & ws & ann & Hrun).
  rewrite (la_end_ret w) in Hrun. by exists rds, ws, ann.
Qed.

(** THE INSTANCE.  Two runs of the REAL nine-node tail of [lw a5,0(a4)] at
    two ARBITRARY loaded words: the same labels, the same read/write/boundary
    annotations, both reaching [Interface.Ret tt], and register files that
    still agree off [[15]] — the [PC] and the [minstret] writes admitted
    because EQUAL, which is exactly what [la_tail_taint_closure_fails] says
    the unpaired law cannot do.

    EXISTENTIAL IN THE SECOND RUN, for [WeakEvProv.instr_dagree]'s reason:
    the second run is BUILT at the first one's answers (there are none here —
    the tail is administrative — and the boundary's [tick] is invisible in
    the label), so what is delivered is "the second tail CAN be run in step
    with the first, and then agrees", which is the certification's use.  Its
    first component pins the FIRST run to the machine's own cursor
    ([WeakRvwmoAdm.adm_iter]), so nothing here is up to a choice of run. *)
Theorem la_tail_par (cpu : CPU) (d : dev_state) (w1 w2 : bv 32) :
  ∃ (ls : list wlabel) (rds : list wreg) (ws : list register) (ann : bool)
    (rs2' : regstate),
    length ls = 9%nat ∧ LInstr ∉ ls ∧
    phrun cpu ls rds ws ann (la_tl w1) (ah_rs la_x2) None (ah_ib la_x2) d
      (Interface.Ret tt) (ah_rs (la_end w1)) None (ah_ib (la_end w1)) d ∧
    phrun cpu ls rds ws ann (la_tl w2) (ah_rs la_x2) None (ah_ib la_x2) d
      (Interface.Ret tt) rs2' None (ah_ib (la_end w1)) d ∧
    dreg_agree (λ n, n ∉ [15%nat]) (ah_rs (la_end w1)) rs2'.
Proof.
  destruct (la_phrun cpu d w1) as (rds & ws & ann & Hrun1).
  destruct (tpar_instr [15%nat] cpu (adm_lbls false 9 (la_st w1)) rds ws ann
              (la_tl w1) (ah_rs la_x2) None (ah_ib la_x2) d
              (Interface.Ret tt) (ah_rs (la_end w1)) None (ah_ib (la_end w1)) d
              (la_tl w2) (ah_rs la_x2)
              Hrun1 (la_tpar w1 w2) (la_ls_no_instr w1) (la_end_untainted w1)
              (dreg_agree_refl _ _)) as (m2' & rs2' & Hrun2 & Htp2 & Hag2).
  rewrite (tpar_boundary [15%nat] tt m2' Htp2) in Hrun2.
  exists (adm_lbls false 9 (la_st w1)), rds, ws, ann, rs2'.
  split_and!; [apply la_ls_len|apply la_ls_no_instr|exact Hrun1|exact Hrun2
              |exact Hag2].
Qed.

(* ====================================================================== *)
(** * 6. AUDIT *)

Print Assumptions tpar_run.
Print Assumptions tpar_instr.
Print Assumptions tpar_reconverge.
Print Assumptions tpar_of_witness.
Print Assumptions tw_tpar.
Print Assumptions tg_nonvacuous.
Print Assumptions la_tpar.
Print Assumptions la_tail_taint_closure_fails.
Print Assumptions la_tail_par.
