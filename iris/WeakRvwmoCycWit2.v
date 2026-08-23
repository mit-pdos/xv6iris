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

    WHAT §3b AND §3c ADD (the [wwit_vindep] retirement's acceptance test).
    §3b proves at THIS node the three facts the MIGRATED policy interface
    asks of a witness site — [w2_m] has no administrative step that moves
    it, it reads no register, and every step out of it lands in the silent
    tail at a node the ANSWER determines ([w2_blk_subst]).  §3c then runs
    [WeakRvwmoCert4.seg_step_of_segment] — the generic segment engine the
    walk itself uses — on a one-event row at this load, with a NON-EMPTY
    taint set and the reachability parameter at [ndreach], and its exit
    invariant is [csync]'s DIVERGED arm.  What that does NOT reach is
    recorded in §4(d).

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports it.
    It is in [_CoqProject], after [WeakRvwmoWalk2.v]. *)
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
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoWalk.
Require Import WeakRvwmoCycWit.
Require Import WeakSailComplete.
Require Import WeakEvProv2.

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
(** * 3b. THE NODE IS PINNED, AND THE BLOCK RE-ANSWERED

    The same three facts [WeakRvwmoCycWit] §1.6 proves at the
    value-INDEPENDENT node, here at the value-CARRYING one: [w2_m] has no
    administrative step that moves it (its RAM read emits [LLoad], its
    parked-fence arm [LFence], and the PLIC wire does not move the monad),
    it reads NO register, and every step out of it lands in the
    instruction's silent tail — at a node the ANSWER determines.  That is
    what makes the site datum of the migrated interface discharegable here
    by [csync]'s DIVERGED arm rather than its lockstep one. *)

Lemma w2_m_step_inv (rs : regstate) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate) (fn' : ofence)
    (d' : dev_state) (oib : option oib32) :
  pnode_step w2_m rs ib d l m' ors fn' d' oib →
  ∃ tvs : list (nat * bv 8),
    length tvs = 4%nat ∧
    l = WeakPromise.LLoad false false (pa_z ev_flag) tvs [] ∧
    (∃ v : type_of_register w2_rd, m' = w2_k1 v) ∧
    ors = None ∧ fn' = None ∧ d' = d ∧ oib = None.
Proof.
  rewrite /w2_m /pnode_step /=. intros Hst.
  destruct Hst as (_ & [(_ & w & tvs & Hlen & _ & Hl & Hm & Ho & Hf & Hd
                         & Hoib)
                       |(Hlat & _)]).
  - exists tvs. split_and!;
      [exact Hlen|by rewrite Hl|by exists (w2_val (inl (w, None)))
      |exact Ho|exact Hf|exact Hd|exact Hoib].
  - discriminate Hlat.
Qed.

(** ONE labelled step, as a [pstep_hw] — the annotated run's own inversion. *)
Lemma phrun_one (cpu : CPU) (l : wlabel) (rds : list wreg)
    (wrs : list register) (ann : bool) (m : M unit) (rs : regstate)
    (fn : ofence) (ib : oib32) (d : dev_state) (m' : M unit)
    (rs' : regstate) (fn' : ofence) (ib' : oib32) (d' : dev_state) :
  phrun cpu [l] rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
  ∃ (ors : option regstate) (oib : option oib32) (wrs0 : list register)
    (ann0 : bool),
    pstep_hw cpu m rs fn ib d l rds wrs0 ann0 m' ors fn' d' oib.
Proof.
  intros H. inversion H; subst.
  match goal with
  | Hr : phrun _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hr; subst
  end.
  rewrite app_nil_r. by eexists _, _, _, _.
Qed.

(** [w2_m] READS NO REGISTER: it is a memory node, so its own read set is
    empty, and so is every other arm's. *)
Lemma w2_m_step_rds (cpu : CPU) (rs : regstate) (fn : ofence) (ib : oib32)
    (d : dev_state) (l : wlabel) (rds : list wreg) (wrs : list register)
    (ann : bool) (m1 : M unit) (ors : option regstate) (fn1 : ofence)
    (d1 : dev_state) (oib : option oib32) :
  pstep_hw cpu w2_m rs fn ib d l rds wrs ann m1 ors fn1 d1 oib → rds = [].
Proof.
  by intros [(_ & _ & -> & _)|[(? & ? & ? & ? & _ & _ & -> & _)|(_ & -> & _)]].
Qed.

Lemma w2_m_adm_step (cpu : CPU) (rs : regstate) (fn : ofence) (ib : oib32)
    (d : dev_state) (l : wlabel) (rds : list wreg) (wrs : list register)
    (ann : bool) (m1 : M unit) (ors : option regstate) (fn1 : ofence)
    (d1 : dev_state) (oib : option oib32) :
  lb_admin true l →
  pstep_hw cpu w2_m rs fn ib d l rds wrs ann m1 ors fn1 d1 oib →
  m1 = w2_m ∧ rds = [].
Proof.
  intros Hadm Hst. have Hr : rds = []
    := w2_m_step_rds cpu rs fn ib d l rds wrs ann m1 ors fn1 d1 oib Hst.
  split; [|exact Hr].
  destruct Hst as [(-> & Hn & _)|[(pr & pw & sr & sw & -> & Hn & _)
                                 |(Hp & _)]].
  - exfalso. destruct (w2_m_step_inv rs ib d l m1 ors fn1 d1 oib Hn)
      as (tvs & _ & -> & _). by simpl in Hadm.
  - exfalso. rewrite /pstep_node in Hn. destruct Hn as (-> & _).
    by simpl in Hadm.
  - by destruct Hp as (_ & -> & _).
Qed.

Lemma w2_m_adm_fix (cpu : CPU) (ls : list wlabel) (rds : list wreg)
    (wrs : list register) (ann : bool) (m : M unit) (rs : regstate)
    (fn : ofence) (ib : oib32) (d : dev_state) (m' : M unit)
    (rs' : regstate) (fn' : ofence) (ib' : oib32) (d' : dev_state) :
  phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
  (∀ l0, l0 ∈ ls → lb_admin true l0) →
  m = w2_m → m' = w2_m ∧ rds = [].
Proof.
  intros Hrun. induction Hrun as
    [m0 rs0 fn0 ib0 d0
    |l ls rdsA rdsB wrsA wrsB annA annB m0 rs0 fn0 ib0 d0
     m1 ors fn1 oib d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH];
    intros Hadm Hm; [by split|].
  subst m0.
  have Hl : lb_admin true l by (apply Hadm, elem_of_list_here).
  destruct (w2_m_adm_step cpu rs0 fn0 ib0 d0 l rdsA wrsA annA m1 ors fn1 d1
              oib Hl Hstep) as (Hm1 & ->).
  destruct (IH ltac:(intros l0 Hl0; by apply Hadm, elem_of_list_further) Hm1)
    as (Hm2 & ->).
  by split.
Qed.

(** THE STEP AT ANY ANSWER LIST of the read's own width. *)
Lemma w2_pstep_any (cpu : CPU) (rs : regstate) (ib : oib32) (d : dev_state)
    (tvs : list (nat * bv 8)) :
  length tvs = 4%nat →
  ∃ v : type_of_register w2_rd,
    pstep_ev (PHart cpu w2_m rs None ib) d
      (WeakPromise.LLoad false false (pa_z ev_flag) tvs [])
      (PHart cpu (w2_k1 v) rs None ib) d.
Proof.
  intros Hlen.
  have Hl2 : length tvs.*2 = N.to_nat 4 by rewrite length_fmap Hlen.
  destruct (bv_of_bytes 4 tvs.*2 Hl2) as (w2 & Hw2).
  exists (w2_val (inl (w2, None))).
  rewrite /pstep_ev /w2_m. split; [reflexivity|].
  exists None, None. split_and!; [reflexivity|reflexivity|]. left.
  rewrite /pstep_node /pnode_step /=.
  split; [done|]. left. split; [done|].
  exists w2, tvs. split_and!; try reflexivity; [by rewrite Hlen|].
  intros j Hj. by apply Hw2.
Qed.

(** THE BLOCK, RE-ANSWERED.  Everything the migrated site datum asks at
    this node: the block reads no register, its parked fence is clear at
    the exit, BOTH the emission's successor and every re-answered one lie
    in the instruction's silent tail — and the re-answered block exists. *)
Theorem w2_blk_subst (cpu : CPU) (d0 : dev_state) (ws : wstate) (aq : bool)
    (base : Z) (ts : list nat) (vs : list (bv 8)) (l : wlabel)
    (rds : list wreg) (wrs : list register) (rs : regstate) (fn : ofence)
    (ib : oib32) (m' : M unit) (rs' : regstate) (fn' : ofence)
    (ib' : oib32) (tvs2 : list (nat * bv 8)) :
  length tvs2 = 4%nat →
  cblk cpu d0 ws (WeakAxiomatic.LLoad aq base ts vs) l rds wrs
    w2_m rs fn ib m' rs' fn' ib' →
  rds = [] ∧ fn' = None ∧ (∃ v1 : type_of_register w2_rd, m' = w2_k1 v1) ∧
  ∃ (l2 : wlabel) (rds2 : list wreg) (wrs2 : list register)
    (v2 : type_of_register w2_rd),
    cblk cpu d0 ws
      (WeakAxiomatic.LLoad false (pa_z ev_flag) tvs2.*1 tvs2.*2)
      l2 rds2 wrs2 w2_m rs fn ib (w2_k1 v2) rs' fn' ib'.
Proof.
  intros Hlen2
    (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB & annB
     & Hadm & HA & Hre & HB & -> & ->).
  destruct (w2_m_adm_fix cpu ls rdsA wrsA annA _ rs fn ib d0 ma rsa fna iba
              da HA Hadm eq_refl) as (Hma & ->).
  subst ma.
  have Hst : pstep_ev (PHart cpu w2_m rsa fna iba) da l
               (PHart cpu m' rs' fn' ib') d0.
  { apply pevrun_single_inv. by eapply phrun_pevrun. }
  destruct Hst as (_ & ors & oib & Hrs & Hib & Hhart).
  destruct (hlbl_realizes_load_shape (PHart cpu w2_m rsa fna iba) ws
              aq base ts vs l Hre) as (tvs & Hf & Hs & Hshape).
  have Hnotf : ∀ pr pw sr sw, l ≠ LFence pr pw sr sw.
  { intros pr pw sr sw ->.
    by destruct Hshape as [Hl|(asrc & Hl)]; discriminate Hl. }
  have Hnotd : l ≠ LDev.
  { intros ->. by destruct Hshape as [Hl|(asrc & Hl)]; discriminate Hl. }
  have Hfna : fna = None.
  { destruct fna as [[[[pr pw] sr] sw]|]; [exfalso|reflexivity].
    destruct Hhart as [Hnode|Hplic].
    - rewrite /pstep_node in Hnode. destruct Hnode as (Hl & _).
      by apply (Hnotf pr pw sr sw).
    - destruct Hplic as (Hl & _). by apply Hnotd. }
  subst fna.
  have Hn : pnode_step w2_m rsa iba da l m' ors fn' d0 oib.
  { destruct Hhart as [Hnode|Hplic]; [exact Hnode|exfalso].
    destruct Hplic as (Hl & _). by apply Hnotd. }
  destruct (w2_m_step_inv rsa iba da l m' ors fn' d0 oib Hn)
    as (tvs0 & Hlen0 & Hl0 & Hv1 & Hors & Hfn' & Hda & Hoib).
  destruct (phrun_one cpu l rdsB wrsB annB w2_m rsa None iba da m' rs' fn'
              ib' d0 HB) as (ors2 & oib2 & wrs02 & ann02 & Hhw).
  have HrdsB : rdsB = []
    := w2_m_step_rds cpu rsa None iba da l rdsB wrs02 ann02 m' ors2 fn' d0
         oib2 Hhw.
  subst rdsB ors oib fn' da.
  simpl in Hrs, Hib. subst rs' ib'.
  split_and!; [reflexivity|reflexivity|exact Hv1|].
  destruct (w2_pstep_any cpu rsa iba d0 tvs2 Hlen2) as (v2 & Hst2).
  destruct (pevrun_phrun [WeakPromise.LLoad false false (pa_z ev_flag) tvs2 []]
              _ d0 _ d0
              (pevrun_more _ [] _ d0 _ d0 _ d0 Hst2 (pevrun_nil _ _))
              cpu w2_m rsa None iba (w2_k1 v2) rsa None iba eq_refl eq_refl)
    as (rdsB2 & wrsB2 & annB2 & HB2).
  exists (WeakPromise.LLoad false false (pa_z ev_flag) tvs2 []),
    ([] ++ rdsB2), (wrsA ++ wrsB2), v2.
  exists ls, w2_m, rsa, None, iba, d0, [], wrsA, annA, rdsB2, wrsB2, annB2.
  split_and!; [exact Hadm|exact HA| |exact HB2|reflexivity|reflexivity].
  rewrite /hlbl_realizes. by split_and!.
Qed.

(* ====================================================================== *)
(** * 3c. THE DIVERGED ARM, FIRED BY THE GENERIC SEGMENT ENGINE

    §3b's facts are what the MIGRATED policy interface asks at a site.
    This section runs [WeakRvwmoCert4.seg_step_of_segment] — the generic
    engine the walk itself uses, over [WeakRvwmoCert3.cert_segment''] — on
    a ONE-EVENT row whose event is the REAL spin load, with

      - a NON-EMPTY taint set ([w2_T = [x15]], the loaded value's carrier),
      - the reachability parameter instantiated at [ndreach] from the load
        node, which is what lets the policy pin the node and answer at all,
      - and a policy whose answer is [csync]'s DIVERGED arm: the two runs
        end at DIFFERENT monad nodes ([w2_nodes_differ] when the values
        differ), both inside the instruction's silent tail.

    Nothing is hand-built below the engine: the block, the certified label
    and the appended step are the POLICY's, and the candidate bookkeeping
    is [cert_segment'']'s. *)

Section w2seg.
  Context (cpu : CPU) (d0 : dev_state) (t : nat) (w : bv 32) (ib : oib32).
  Context (rs rs2 : regstate).

  Definition w2_lb : WeakAxiomatic.lbl :=
    WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w).
  Definition w2_Q : nat → WeakAxiomatic.lbl → Prop :=
    λ k lb, k = 0%nat ∧ lb = w2_lb.
  Definition w2_Ctx : nat → cand → Prop :=
    λ _ c, latest_bytes_ok c (pa_z ev_flag) 4.
  Definition w2_Nd : nat → M unit → Prop := ndreach cpu d0 w2_Q 0%nat w2_m.
  Definition w2_pst : nat → list pexv6 := λ _, [PHart cpu w2_m rs2 None ib].
  Definition w2_St : cyc_state := CSt cw_c0 w2_pst (λ _, d0).

  (** THE NODE IS PINNED at row position 0: no block has run, so the
      reachability is an administrative stretch out of the load node, and
      §3b says such a stretch does not move it. *)
  Lemma w2_nd_pin (k : nat) (m : M unit) :
    w2_Nd k m → k = 0%nat → m = w2_m.
  Proof.
    intros Hnd Hk.
    eapply (ndreach_fix cpu d0 w2_Q (λ mm, mm = w2_m) w2_m);
      [reflexivity| |exact Hnd|exact Hk].
    intros m1 m2 rs1' rs2' fn1 fn2 ib1 ib2 ls rds wrs ann Hm1 Hadm Hrun.
    by destruct (w2_m_adm_fix cpu ls rds wrs ann m1 rs1' fn1 ib1 d0 m2 rs2'
                   fn2 ib2 d0 Hrun Hadm Hm1) as (H & _).
  Qed.

  (** THE EMISSION: one block, no administrative stretch, at the REAL load
      request — and it is fabric-quiet. *)
  Lemma w2_hemit :
    hemit (λ _, d0) 0%nat (ms_ws (cand_last_st cw_c0) 0%nat) [w2_lb]
      (w2_p0 cpu rs ib)
      [(WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) [],
        Some 0%nat)]
      (w2_p1 w cpu rs ib).
  Proof.
    apply (HEone (λ _, d0) 0%nat (ms_ws (cand_last_st cw_c0) 0%nat) w2_lb []
             (w2_p0 cpu rs ib) [] (w2_p0 cpu rs ib) d0
             (WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) [])
             (w2_p1 w cpu rs ib) [] (w2_p1 w cpu rs ib)).
    - apply ARnil.
    - apply w2_realizes.
    - apply w2_pstep.
    - apply HEnil.
  Qed.

  Lemma w2_devfree :
    LDev ∉ ([(WeakPromise.LLoad false false (pa_z ev_flag) (ld_tvs t w) [],
              Some 0%nat)] : list eitem).*1.
  Proof.
    intros [H|H]%elem_of_cons; [discriminate|by apply elem_of_nil in H].
  Qed.

  Lemma w2_cst_ok : cst_ok d0 w2_St.
  Proof.
    split_and!; [apply cw_c0_cons| |reflexivity].
    intros k s Hs. rewrite cand_ex_tr in Hs. by destruct k.
  Qed.

  Lemma w2_HQ (i : nat) (lb : WeakAxiomatic.lbl) :
    [w2_lb] !! i = Some lb → w2_Q (0 + i)%nat lb.
  Proof.
    destruct i as [|i]; [|by rewrite /= lookup_nil].
    intros [= <-]. by split.
  Qed.

  Lemma w2_Q_rmwfree (k : nat) (lb : WeakAxiomatic.lbl) :
    w2_Q k lb → lb_rmwfree lb.
  Proof. by intros (_ & ->). Qed.

  Lemma w2_Hpres (k : nat) (c0 : cand) (lb lb' : WeakAxiomatic.lbl) :
    w2_Ctx k c0 → srvwmo_consistent c0 → w2_Q k lb →
    lbl_reidx_w lb lb' → mstep_ok (cand_last_st c0) 0%nat lb' → True →
    w2_Ctx (S k) (cand_snoc c0 (EStep 0%nat lb')).
  Proof.
    intros Hctx Hc (_ & ->) Hri Hok _.
    have Hw' : lb_is_w lb' = false
      by apply (lbl_reidx_w_notw w2_lb lb' Hri eq_refl).
    rewrite /w2_Ctx /latest_bytes_ok cand_snoc_img cd_log_end_snoc
            (es_msg_notw (EStep 0%nat lb') Hw') app_nil_r.
    exact Hctx.
  Qed.

  Lemma w2_Hrds (k : nat) (lb : WeakAxiomatic.lbl) (ws : wstate)
      (l : wlabel) (rds : list wreg) (wrs : list register) (m : M unit)
      (rs1 : regstate) (fn : ofence) (ib1 : oib32) (m' : M unit)
      (rs1' : regstate) (fn' : ofence) (ib1' : oib32) :
    w2_Q k lb → w2_Nd k m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    rds_ok (λ n, n ∉ w2_T) rds.
  Proof.
    intros (Hk & ->) Hnd Hblk.
    rewrite (w2_nd_pin k m Hnd Hk) in Hblk.
    destruct (w2_blk_subst cpu d0 ws false (pa_z ev_flag) (ld_ts t) (ld_vs w)
                l rds wrs rs1 fn ib1 m' rs1' fn' ib1'
                (ld_tvs 0%nat (Z_to_bv 32 0)) eq_refl Hblk) as (-> & _).
    intros n Hn. by apply elem_of_nil in Hn.
  Qed.

  Lemma w2_Hrdsp (k : nat) (lb : WeakAxiomatic.lbl) (ws : wstate)
      (l1 l2 : wlabel) (rds : list wreg) (wrs : list register) (m : M unit)
      (rs1 : regstate) (fn : ofence) (ib1 : oib32) (m' : M unit)
      (rs1' : regstate) (fn' : ofence) (ib1' : oib32) :
    w2_Q k lb → w2_Nd k m →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    rds_ok (λ n, n ∉ w2_T) rds.
  Proof.
    intros (Hk & ->) Hnd Hblk. exfalso.
    exact (cblkp_rmw cpu d0 ws w2_lb l1 l2 rds wrs m rs1 fn ib1 m' rs1' fn'
             ib1' Hblk I).
  Qed.

  (** THE POLICY.  The certified run reads the CANDIDATE's latest bytes;
      the emission read [w].  The two runs therefore leave the memory node
      at DIFFERENT successors — and [csync]'s DIVERGED arm is exactly what
      says that is admissible: both are inside the instruction's silent
      tail, with the register files agreeing off [w2_T]. *)
  Lemma w2_Hpol (k : nat) (c0 : cand) (ws : wstate)
      (lb : WeakAxiomatic.lbl) (l : wlabel) (rds : list wreg)
      (wrs : list register) (m : M unit) (rs1 rs1b : regstate)
      (fn : ofence) (ib1 : oib32) (m' : M unit) (rs1' : regstate)
      (fn' : ofence) (ib1' : oib32) :
    srvwmo_consistent c0 → w2_Ctx k c0 → w2_Q k lb →
    w_relp (ms_ws (cand_last_st c0) 0%nat) = w_relp ws →
    dreg_agree (λ n, n ∉ w2_T) rs1 rs1b →
    w2_Nd k m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    ∃ lb' l' rds' wrs' rs2' (m2' : M unit) (fn2' : ofence) (ib2' : oib32),
      cblk cpu d0 ws lb' l' rds' wrs' m rs1b fn ib1 m2' rs2' fn2' ib2' ∧
      mstep_ok (cand_last_st c0) 0%nat lb' ∧
      lbl_reidx_w lb lb' ∧
      True ∧
      csync w2_T m' rs1' fn' ib1' m2' rs2' fn2' ib2' ∧
      (lb_is_w lb = true →
         clockstep w2_T m' rs1' fn' ib1' m2' rs2' fn2' ib2').
  Proof.
    intros Hc Hctx (Hk & ->) Hrelp Hag Hnd Hblk.
    have Hrds : rds_ok (λ n, n ∉ w2_T) rds
      := w2_Hrds k w2_lb ws l rds wrs m rs1 fn ib1 m' rs1' fn' ib1'
           (conj Hk eq_refl) Hnd Hblk.
    rewrite (w2_nd_pin k m Hnd Hk) in Hblk.
    destruct (w2_blk_subst cpu d0 ws false (pa_z ev_flag) (ld_ts t) (ld_vs w)
                l rds wrs rs1 fn ib1 m' rs1' fn' ib1'
                (ld_tvs 0%nat (Z_to_bv 32 0)) eq_refl Hblk)
      as (Hrn & Hfn' & (v1 & Hm') & _).
    destruct (cert_block_mirror (λ n, n ∉ w2_T) cpu d0 ws w2_lb l rds wrs
                w2_m rs1 fn ib1 m' rs1' fn' ib1' rs1b Hblk Hrds Hag)
      as (rs2b & Hblk2 & Hag2).
    destruct (w2_blk_subst cpu d0 ws false (pa_z ev_flag) (ld_ts t) (ld_vs w)
                l rds wrs rs1b fn ib1 m' rs2b fn' ib1'
                (wit_tvs c0 (pa_z ev_flag) 4)
                (wit_tvs_length c0 (pa_z ev_flag) 4) Hblk2)
      as (_ & _ & _ & (l2 & rds2 & wrs2 & v2 & Hblk3)).
    rewrite (wit_tvs_lbl c0 false (pa_z ev_flag) 4) in Hblk3.
    exists (latest_read_lbl c0 false (pa_z ev_flag) 4), l2, rds2, wrs2, rs2b,
      (w2_k1 v2), fn', ib1'.
    split_and!.
    - rewrite (w2_nd_pin k m Hnd Hk). exact Hblk3.
    - by apply cert_read_witness.
    - right; left. rewrite /latest_read_lbl /=. split_and!;
        [reflexivity|reflexivity|reflexivity| |].
      + reflexivity.
      + reflexivity.
    - exact I.
    - right. split_and!;
        [exact Hfn'|exact Hfn'|rewrite Hm'; apply w2_tail_silent
        |apply w2_tail_silent|exact Hag2].
    - intros H. by simpl in H.
  Qed.

  (** THE INSTANCE.  One [WeakRvwmoCert4.seg_step] of the generic engine,
      at the real load, with the diverged arm at its exit. *)
  Theorem w2_seg_step_diverged :
    dreg_agree (λ n, n ∉ w2_T) rs rs2 →
    ∃ (St' : cyc_state) (tradd : list estep) (m21 : M unit)
      (rs21 : regstate) (fn21 : ofence) (ib21 : oib32),
      seg_step d0 (SegOut 0%nat [w2_lb] 0%nat tradd) w2_St St' ∧
      cst_pst St' (cd_end (cst_c St')) !! 0%nat
        = Some (PHart cpu m21 rs21 fn21 ib21) ∧
      (** the two runs are [csync] at the exit … *)
      csync w2_T (w2_k1 (w2_val (inl (w, None)))) rs None ib
        m21 rs21 fn21 ib21 ∧
      (** … and BOTH are inside the instruction's silent tail, which is
          [csync]'s DIVERGED arm — the emission's own node carries the
          value it read, so no lockstep answer exists here unless the two
          values coincide ([w2_nodes_differ]). *)
      tail_silent w2_T (w2_k1 (w2_val (inl (w, None)))) ∧
      tail_silent w2_T m21.
  Proof.
    intros Hag.
    destruct (seg_step_of_segment 0%nat cpu d0 (λ _ : nat, w2_T) w2_Q w2_Ctx
                (λ _ _, True) w2_Nd (λ _ : nat, reflexivity w2_T)
                w2_Hpres w2_Hrdsp
                (λ k m m' rs' rs'' fn fn' ib' ib'' ls rds wrs ann Hnd Ha Hr,
                   nd_adm cpu d0 w2_Q 0%nat w2_m k m m' rs' rs'' fn fn'
                     ib' ib'' ls rds wrs ann Hnd Ha Hr)
                (λ k m m' ws lb l rds wrs rs' rs'' fn fn' ib' ib'' Hnd Hq Hb,
                   nd_blk cpu d0 w2_Q 0%nat w2_m k m m' ws lb l rds wrs
                     rs' rs'' fn fn' ib' ib'' Hnd Hq Hb)
                (λ k m m' ws lb l1 l2 rds wrs rs' rs'' fn fn' ib' ib''
                   Hnd Hq Hb,
                   nd_blkp cpu d0 w2_Q 0%nat w2_m k m m' ws lb l1 l2 rds wrs
                     rs' rs'' fn fn' ib' ib'' Hnd Hq Hb)
                w2_Hpol
                (cpolpr_of_cpolp 0%nat cpu d0 w2_T w2_Nd w2_Ctx
                   (λ _ _, True) w2_Q
                   (cpolp_of_rmwfree 0%nat cpu d0 w2_T w2_Ctx (λ _ _, True)
                      w2_Q w2_Q_rmwfree))
                0%nat (ms_ws (cand_last_st cw_c0) 0%nat) [w2_lb] _ _
                w2_m rs None ib w2_St w2_m rs2 None ib
                w2_hemit w2_devfree w2_HQ w2_cst_ok cw_bytes0 eq_refl
                (nd_start cpu d0 w2_Q 0%nat w2_m)
                (or_introl (conj eq_refl (conj eq_refl (conj eq_refl Hag))))
                eq_refl)
      as (St' & tradd & Hstep & _ & _ & _ & _ &
          (m1 & rs11 & fn1 & ib1 & m21 & rs21 & fn21 & ib21 &
           Hpfin & Hpx & Hsync & _ & _) & _).
    rewrite /w2_p1 in Hpfin. injection Hpfin as <- <- <- <-.
    exists St', tradd, m21, rs21, fn21, ib21.
    have Hts1 : tail_silent w2_T (w2_k1 (w2_val (inl (w, None))))
      := w2_tail_silent _.
    split_and!; [exact Hstep|exact Hpx|exact Hsync|exact Hts1|].
    destruct Hsync as [(-> & _)|(_ & _ & _ & Hts2 & _)];
      [exact Hts1|exact Hts2].
  Qed.
End w2seg.

(* ====================================================================== *)
(** * 3d. THE POISONED BLOCK — the per-hart-taint migration's own witness

    THE AUDIT'S RULE, at the arm the migration added.  §3c inhabits the
    WITNESS route: a substituted read at [G]'s own footprint.  The POISONED
    route ([WeakRvwmoCert2.lbl_poisoned], [WeakRvwmoWalk.wpois_site]) is a
    different claim — the block's instruction READS A TAINTED CARRIER, so
    the certified run computes a DIFFERENT ADDRESS and no mirror exists —
    and it needs its own inhabitation, at a NON-EMPTY taint, or the whole
    arm is the vacuity the audit is about.

    WHAT IS REAL: the read REQUEST's every field but the address is the
    real [lw a5,0(a4)]'s ([WeakRvwmoCycWit.cy_rreq] over
    [WeakRvwmoConfWit2.ld_reql]); both addresses are real RAM addresses of
    the booted image ([cy_A] = [&started], [cy_B] = [&started+8], with
    [cy_A_ram]/[cy_B_ram]); the carrier read is [a5] = [x15] — the register
    [WeakRvwmoCycWit2] §1's witness load WRITES, so the taint really is the
    one a witness creates; the destination [a4] = [x14] is a carrier too,
    which is how the taint GROWS.

    WHAT IS HAND-BUILT: the block's two-node shape — a [RegRead] of [a5]
    followed by the load, and a one-node tail.  The real nine-node tail of
    [lw] is admitted by [WeakEvProv2.la_tail_par] (see §4(a)); it is not
    wired in here, for the reason §4(b) records.

    WHAT IS PROVED BELOW, and it is exactly the arm's content:
      - the block's READ SET holds the tainted carrier, so
        [WeakRvwmoCert2.cert_block_mirror] does not apply and the policy's
        case split really lands on the poisoned branch ([w3_not_rds_ok]);
      - the two runs' labels are related by [lbl_poisoned] and by NEITHER
        [lbl_reidx] NOR [lbl_reidx_sub] ([w3_poisoned], [w3_not_reidx]) —
        the third arm is necessary, not decorative;
      - the two runs end at DIFFERENT nodes, in [csync]'s DIVERGED arm at
        the GROWN taint ([w3_csync_grown]), and NOT in lockstep
        ([w3_not_clockstep]) — the accumulation is real. *)

Definition w3_src : register := R_bitvector_64 x15.
Definition w3_dst : register := R_bitvector_64 x14.

(** THE TAINT, BEFORE AND AFTER: [x15] is what the witness load of §1
    wrote; [x14] is what THIS load writes. *)
Definition w3_T0 : list wreg := [15%nat].
Definition w3_T1 : list wreg := [15%nat; 14%nat].

Lemma w3_dst_num : ereg_num w3_dst = Some 14%nat.
Proof. by vm_compute. Qed.

Lemma w3_taint_grows : w3_T0 ⊆ w3_T1 ∧ (14%nat ∈ w3_T1) ∧ (14%nat ∉ w3_T0).
Proof.
  split_and!.
  - intros n Hn. apply elem_of_list_singleton in Hn as ->.
    apply elem_of_list_here.
  - apply elem_of_list_further, elem_of_list_here.
  - intros Hn. apply elem_of_list_singleton in Hn. done.
Qed.

Definition w3_val (ans : (bv (8 * 4) * option bool + Arch.abort)%type)
    : type_of_register w3_dst :=
  match ans with
  | inl (w, _) => Z_to_bv 64 (bv_unsigned w)
  | inr _ => Z_to_bv 64 0
  end.

Definition w3_k1 (v : type_of_register w3_dst) : M unit :=
  Interface.Next (Interface.RegWrite w3_dst None v) (fun _ => Interface.Ret tt).

Definition w3_ld (a : Arch.pa) : M unit :=
  Interface.Next (Interface.MemRead 4 (cy_rreq a))
    (fun ans => w3_k1 (w3_val ans)).

(** THE ADDRESS DEPENDS ON THE TAINTED CARRIER — this is what a poisoned
    block IS. *)
Definition w3_addr (v : type_of_register w3_src) : Arch.pa :=
  if bool_decide (bv_unsigned v = 0%Z) then cy_A else cy_B.

Definition w3_m : M unit :=
  Interface.Next (Interface.RegRead w3_src None)
    (fun v => w3_ld (w3_addr v)).

Lemma w3_rds : pnode_rds w3_m = [15%nat].
Proof. by vm_compute. Qed.

(** … so the block's read set MEETS the taint: the mirror is unavailable
    and the policy's case split lands on the poisoned branch. *)
Lemma w3_not_rds_ok : ¬ rds_ok (fun n => n ∉ w3_T0) (pnode_rds w3_m).
Proof.
  intros H. have H15 := H 15%nat ltac:(rewrite w3_rds; apply elem_of_list_here).
  apply H15, elem_of_list_here.
Qed.

Lemma w3_addr_ram (v : type_of_register w3_src) : dev_addr (w3_addr v) = false.
Proof.
  rewrite /w3_addr. case_bool_decide; [apply cy_A_ram|apply cy_B_ram].
Qed.

(** ONE ADMINISTRATIVE STEP: the register read.  It is [LSilent], it moves
    the monad to the address the value determines, and it is what puts the
    carrier into the block's read set. *)
Lemma w3_regread (cpu : CPU) (rs : regstate) (ib : oib32) (d : dev_state) :
  phrun cpu [LSilent] ([15%nat] ++ []) ([] ++ []) (false || false)
    w3_m rs None ib d
    (w3_ld (w3_addr (register_lookup w3_src rs))) rs None (ib_rd ib w3_src) d.
Proof.
  apply (phrun_more cpu LSilent [] [15%nat] [] [] [] false false
           w3_m rs None ib d
           (w3_ld (w3_addr (register_lookup w3_src rs))) None None
           (Some (ib_rd ib w3_src)) d);
    [|apply phrun_nil].
  left. split_and!;
    [reflexivity| |by rewrite w3_rds|reflexivity|reflexivity].
  rewrite /pnode_step /w3_m /=. by split_and!.
Qed.

(** THE LOAD NODE STEPS AT EVERY ANSWER of its own width. *)
Lemma w3_ld_step (cpu : CPU) (rs : regstate) (ib : oib32) (d : dev_state)
    (a : Arch.pa) (tvs : list (nat * bv 8)) :
  dev_addr a = false → length tvs = 4%nat →
  ∃ v : type_of_register w3_dst,
    pstep_ev (PHart cpu (w3_ld a) rs None ib) d
      (WeakPromise.LLoad false false (pa_z a) tvs [])
      (PHart cpu (w3_k1 v) rs None ib) d.
Proof.
  intros Hram Hlen.
  have Hl2 : length tvs.*2 = N.to_nat 4 by rewrite length_fmap Hlen.
  destruct (bv_of_bytes 4 tvs.*2 Hl2) as (w2 & Hw2).
  exists (w3_val (inl (w2, None))).
  rewrite /pstep_ev /w3_ld. split; [reflexivity|].
  exists None, None. split_and!; [reflexivity|reflexivity|]. left.
  rewrite /pstep_node /pnode_step /=. rewrite Hram.
  split; [reflexivity|]. left. split; [reflexivity|].
  exists w2, tvs. split_and!; try reflexivity; [by rewrite Hlen|].
  intros j Hj. by apply Hw2.
Qed.

Lemma w3_realizes (cpu : CPU) (rs : regstate) (ib : oib32) (ws : wstate)
    (a : Arch.pa) (tvs : list (nat * bv 8)) :
  hlbl_realizes (PHart cpu (w3_ld a) rs None ib) ws
    (WeakAxiomatic.LLoad false (pa_z a) tvs.*1 tvs.*2)
    (WeakPromise.LLoad false false (pa_z a) tvs []).
Proof. rewrite /hlbl_realizes. split_and!; [done|done|done|reflexivity]. Qed.

(** THE BLOCK, at whatever the tainted carrier holds. *)
Theorem w3_blk (cpu : CPU) (d0 : dev_state) (ws : wstate) (rs : regstate)
    (ib : oib32) (tvs : list (nat * bv 8)) :
  length tvs = 4%nat →
  ∃ (v : type_of_register w3_dst) (rds : list wreg) (wrs : list register),
    cblk cpu d0 ws
      (WeakAxiomatic.LLoad false
         (pa_z (w3_addr (register_lookup w3_src rs))) tvs.*1 tvs.*2)
      (WeakPromise.LLoad false false
         (pa_z (w3_addr (register_lookup w3_src rs))) tvs [])
      rds wrs w3_m rs None ib (w3_k1 v) rs None (ib_rd ib w3_src) ∧
    (** … and the block's READ SET holds the tainted carrier, which is what
        makes the policy take the POISONED branch. *)
    15%nat ∈ rds.
Proof.
  intros Hlen.
  set a := w3_addr (register_lookup w3_src rs).
  destruct (w3_ld_step cpu rs (ib_rd ib w3_src) d0 a tvs
              (w3_addr_ram _) Hlen) as (v & Hst).
  destruct (pevrun_phrun [WeakPromise.LLoad false false (pa_z a) tvs []]
              _ d0 _ d0
              (pevrun_more _ [] _ d0 _ d0 _ d0 Hst (pevrun_nil _ _))
              cpu (w3_ld a) rs None (ib_rd ib w3_src)
              (w3_k1 v) rs None (ib_rd ib w3_src) eq_refl eq_refl)
    as (rdsB & wrsB & annB & HB).
  exists v, (([15%nat] ++ []) ++ rdsB), (([] ++ []) ++ wrsB).
  split.
  - exists [LSilent], (w3_ld a), rs, None, (ib_rd ib w3_src), d0,
      ([15%nat] ++ []), ([] ++ []), (false || false), rdsB, wrsB, annB.
    split_and!;
      [|apply w3_regread|apply w3_realizes|exact HB|reflexivity|reflexivity].
    intros l0 Hl0. apply elem_of_list_singleton in Hl0 as ->. exact I.
  - apply elem_of_app. left. apply elem_of_app. left. apply elem_of_list_here.
Qed.

(** ** 3d.1 THE TWO RUNS, AND THE THREE FACTS THE ARM RESTS ON

    [rs1] is the emission's register file, [w3_rs2 rs1] the certified run's:
    they agree OFF the taint and differ AT it, which is exactly the state a
    witness leaves behind ([WeakEvProv.taint_closure_load]). *)
Definition w3_rs2 (rs : regstate) : regstate :=
  register_set w3_src (Z_to_bv 64 1) rs.

Lemma w3_agree (rs : regstate) :
  dreg_agree (fun n => n ∉ w3_T0) rs (w3_rs2 rs).
Proof.
  intros r Hr. rewrite /w3_rs2. destruct (decide (r = w3_src)) as [->|Hne].
  - exfalso. apply (Hr 15%nat w2_rd_num), elem_of_list_here.
  - by rewrite register_lookup_set_ne.
Qed.

Lemma w3_lookup2 (rs : regstate) :
  register_lookup w3_src (w3_rs2 rs) = Z_to_bv 64 1.
Proof. apply register_lookup_set. Qed.

(** THE TWO ADDRESSES REALLY DIFFER when the carrier does. *)
Lemma w3_addr0 : w3_addr (Z_to_bv 64 0) = cy_A.
Proof. by vm_compute. Qed.
Lemma w3_addr1 : w3_addr (Z_to_bv 64 1) = cy_B.
Proof. by vm_compute. Qed.
Lemma w3_zA_zB : pa_z cy_A ≠ pa_z cy_B.
Proof. rewrite -/zA -/zB zA_val zB_val. by vm_compute. Qed.

(** (i) THE THIRD ARM IS INHABITED — and it is the ONLY one that relates
    the two labels: their ADDRESSES differ, which both [lbl_reidx] (same
    address AND same values) and [lbl_reidx_sub] (same address) forbid. *)
Theorem w3_poisoned (ts1 ts2 : list nat) (vs1 vs2 : list (bv 8)) :
  length vs2 = length ts2 →
  lbl_poisoned
    (WeakAxiomatic.LLoad false (pa_z cy_A) ts1 vs1)
    (WeakAxiomatic.LLoad false (pa_z cy_B) ts2 vs2).
Proof. by intros H. Qed.

Theorem w3_not_reidx (ts1 ts2 : list nat) (vs1 vs2 : list (bv 8)) :
  ¬ lbl_reidx
      (WeakAxiomatic.LLoad false (pa_z cy_A) ts1 vs1)
      (WeakAxiomatic.LLoad false (pa_z cy_B) ts2 vs2) ∧
  ¬ lbl_reidx_sub
      (WeakAxiomatic.LLoad false (pa_z cy_A) ts1 vs1)
      (WeakAxiomatic.LLoad false (pa_z cy_B) ts2 vs2).
Proof.
  split.
  - intros (_ & Hb & _). by apply w3_zA_zB.
  - intros (_ & _ & Hb & _). by apply w3_zA_zB.
Qed.

(** (ii) THE TAIL IS SILENT AT THE GROWN TAINT — and only at it: the
    block's own destination [x14] is written by the tail, so [w3_T0] does
    NOT admit it and [w3_T1] does.  This is the ACCUMULATION, at the node. *)
Lemma w3_tail_silent (v : type_of_register w3_dst) :
  tail_silent w3_T1 (w3_k1 v).
Proof.
  apply ts_next; [exact I| |intros u; destruct u; apply ts_ret].
  intros r Hr. rewrite /pnode_wrs /= in Hr.
  apply elem_of_list_singleton in Hr. subst r.
  exists 14%nat. split; [exact w3_dst_num|].
  apply elem_of_list_further, elem_of_list_here.
Qed.

(** … and [w3_T0] does NOT admit it: the tail writes a CARRIER the old
    taint does not hold, which is precisely why the taint has to GROW at
    this block rather than stay fixed (the audit's finding). *)
Lemma w3_tail_writes_dst (v : type_of_register w3_dst) :
  pnode_wrs (w3_k1 v) = [w3_dst] ∧ ereg_num w3_dst = Some 14%nat ∧
  (14%nat ∉ w3_T0).
Proof.
  split_and!; [reflexivity|exact w3_dst_num|].
  intros Hn. by apply elem_of_list_singleton in Hn.
Qed.

(** (iii) THE TWO RUNS ARE IN [csync]'s DIVERGED ARM at the GROWN taint …
    and NOT in lockstep: the successor nodes carry the two different loaded
    values ([w2_nodes_differ]'s argument at this node). *)
Theorem w3_csync_grown (v1 v2 : type_of_register w3_dst) (rs1' rs2' : regstate)
    (ib' : oib32) :
  dreg_agree (fun n => n ∉ w3_T1) rs1' rs2' →
  csync w3_T1 (w3_k1 v1) rs1' None ib' (w3_k1 v2) rs2' None ib'.
Proof.
  intros Hag. right.
  split_and!; [reflexivity|reflexivity|apply w3_tail_silent
              |apply w3_tail_silent|exact Hag].
Qed.

Lemma w3_nodes_differ (v1 v2 : type_of_register w3_dst) :
  v1 ≠ v2 → w3_k1 v1 ≠ w3_k1 v2.
Proof.
  intros Hne Heq. apply Hne.
  have Hpr : ∀ v, register_lookup w3_dst (register_set w3_dst v ld_rs0) = v
    by intros v; apply register_lookup_set.
  have Hf : ∀ m : M unit,
      match esil_node_any ld_rs0 m with
      | Some (rs', _) => register_lookup w3_dst rs'
      | None => Z_to_bv 64 0
      end = match esil_node_any ld_rs0 m with
            | Some (rs', _) => register_lookup w3_dst rs'
            | None => Z_to_bv 64 0
            end := λ m, eq_refl.
  have H1 : match esil_node_any ld_rs0 (w3_k1 v1) with
            | Some (rs', _) => register_lookup w3_dst rs'
            | None => Z_to_bv 64 0
            end = v1 by rewrite /w3_k1 /=; apply Hpr.
  have H2 : match esil_node_any ld_rs0 (w3_k1 v2) with
            | Some (rs', _) => register_lookup w3_dst rs'
            | None => Z_to_bv 64 0
            end = v2 by rewrite /w3_k1 /=; apply Hpr.
  by rewrite -H1 -H2 Heq.
Qed.

Theorem w3_not_clockstep (v1 v2 : type_of_register w3_dst)
    (rs1' rs2' : regstate) (ib' : oib32) :
  v1 ≠ v2 →
  ¬ clockstep w3_T1 (w3_k1 v1) rs1' None ib' (w3_k1 v2) rs2' None ib'.
Proof.
  intros Hne (Heq & _ & _ & _).
  exact (w3_nodes_differ v2 v1 (fun H => Hne (eq_sym H)) Heq).
Qed.

(** ** 3d.2 THE WITNESS, ASSEMBLED

    Both blocks exist, at the SAME node, from register files that agree off
    the taint: the emission's reads [cy_A], the certified run's reads
    [cy_B], the two labels are [lbl_poisoned]-related and nothing weaker
    relates them, the block's read set holds the tainted carrier, and the
    exit is [csync]'s DIVERGED arm at the taint the block itself grew.
    This is [WeakRvwmoWalk.poisoned_no_fault]'s and
    [WeakRvwmoWalk.wpois_site]'s content at a concrete node — with the ONE
    residual named there, the fault boundary, discharged HERE by
    construction ([cy_A_ram]/[cy_B_ram]: both addresses are mapped RAM). *)
Theorem w3_pair (cpu : CPU) (d0 : dev_state) (ws : wstate) (rs : regstate)
    (ib : oib32) (tvs1 tvs2 : list (nat * bv 8)) :
  register_lookup w3_src rs = Z_to_bv 64 0 →
  length tvs1 = 4%nat → length tvs2 = 4%nat →
  ∃ (v1 v2 : type_of_register w3_dst)
    (rds1 rds2 : list wreg) (wrs1 wrs2 : list register)
    (l1 l2 : wlabel),
    (* the emission's block: address [cy_A] *)
    cblk cpu d0 ws
      (WeakAxiomatic.LLoad false (pa_z cy_A) tvs1.*1 tvs1.*2) l1 rds1 wrs1
      w3_m rs None ib (w3_k1 v1) rs None (ib_rd ib w3_src) ∧
    (* the certified run's block, from the SAME node: address [cy_B] *)
    cblk cpu d0 ws
      (WeakAxiomatic.LLoad false (pa_z cy_B) tvs2.*1 tvs2.*2) l2 rds2 wrs2
      w3_m (w3_rs2 rs) None ib (w3_k1 v2) (w3_rs2 rs) None (ib_rd ib w3_src) ∧
    (* the register files agree off the taint … *)
    dreg_agree (fun n => n ∉ w3_T0) rs (w3_rs2 rs) ∧
    (* … the block's read set MEETS it, so no mirror exists … *)
    15%nat ∈ rds1 ∧ ¬ rds_ok (fun n => n ∉ w3_T0) rds1 ∧
    (* … the two labels are related by the POISONED arm and by nothing
       weaker … *)
    lbl_poisoned
      (WeakAxiomatic.LLoad false (pa_z cy_A) tvs1.*1 tvs1.*2)
      (WeakAxiomatic.LLoad false (pa_z cy_B) tvs2.*1 tvs2.*2) ∧
    ¬ lbl_reidx
      (WeakAxiomatic.LLoad false (pa_z cy_A) tvs1.*1 tvs1.*2)
      (WeakAxiomatic.LLoad false (pa_z cy_B) tvs2.*1 tvs2.*2) ∧
    ¬ lbl_reidx_sub
      (WeakAxiomatic.LLoad false (pa_z cy_A) tvs1.*1 tvs1.*2)
      (WeakAxiomatic.LLoad false (pa_z cy_B) tvs2.*1 tvs2.*2) ∧
    (* … and the exit is [csync]'s DIVERGED arm at the GROWN taint. *)
    csync w3_T1 (w3_k1 v1) rs None (ib_rd ib w3_src)
      (w3_k1 v2) (w3_rs2 rs) None (ib_rd ib w3_src).
Proof.
  intros Hv Hl1 Hl2.
  have HA : w3_addr (register_lookup w3_src rs) = cy_A
    by rewrite Hv w3_addr0.
  have HB : w3_addr (register_lookup w3_src (w3_rs2 rs)) = cy_B
    by rewrite w3_lookup2 w3_addr1.
  destruct (w3_blk cpu d0 ws rs ib tvs1 Hl1)
    as (v1 & rds1 & wrs1 & Hb1 & Hin1).
  destruct (w3_blk cpu d0 ws (w3_rs2 rs) ib tvs2 Hl2)
    as (v2 & rds2 & wrs2 & Hb2 & Hin2).
  rewrite HA in Hb1. rewrite HB in Hb2.
  exists v1, v2, rds1, rds2, wrs1, wrs2,
    (WeakPromise.LLoad false false (pa_z cy_A) tvs1 []),
    (WeakPromise.LLoad false false (pa_z cy_B) tvs2 []).
  split_and!.
  - exact Hb1.
  - exact Hb2.
  - apply w3_agree.
  - exact Hin1.
  - intros H. exact (H 15%nat Hin1 (elem_of_list_here _ _)).
  - by apply w3_poisoned; rewrite length_fmap length_fmap.
  - apply (proj1 (w3_not_reidx _ _ _ _)).
  - apply (proj2 (w3_not_reidx _ _ _ _)).
  - apply w3_csync_grown.
    eapply dreg_agree_taint_mono; [apply (proj1 w3_taint_grows)|apply w3_agree].
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

    (c) THE POLICY INTERFACE IS NODE-BLIND — DONE, and §3b/§3c are the
        payoff.  [WeakRvwmoCert3.cert_segment''] now carries the
        reachability parameter [Nd] and hands [Nd k m] to the policy (and
        to the read-set side condition), [WeakRvwmoWalk.wwit_vindep] is
        RETIRED in favour of [WeakRvwmoWalk.wwit_nd], and §3c fires the
        DIVERGED arm inside [WeakRvwmoCert4.seg_step_of_segment] — the
        generic engine — at THIS node, with the taint set [w2_T] non-empty
        and the node pinned by [ndreach].

    (d) WHAT §3c DOES NOT REACH, and why.  The engine here PRODUCES the
        diverged arm at a segment's exit; it does not CONSUME it, because
        consuming it ([WeakRvwmoCert3.csync_advance]'s second branch, via
        [witness_instr_tail_silent]) needs a SECOND block of the same
        segment after the witness — and by (b) the node after the boundary
        is the real machine's [RiscvLang.riscv_step], whose next memory
        node is the FETCH reached across [WeakRvwmoAdm]'s 117-node stretch,
        with the real nine-node load tail that (a) rules out.  So a
        [WeakRvwmoWalk.wlk_step'] carrying the diverged arm — the walk's
        segments must END in a write, hence must cross the boundary — waits
        on the paired taint law of (a); everything else is in place. *)

Print Assumptions w2_pstep.
Print Assumptions w2_m_adm_fix.
Print Assumptions w2_blk_subst.
Print Assumptions w2_seg_step_diverged.
Print Assumptions w2_reaches_boundary.
Print Assumptions w2_reconverge.
Print Assumptions w3_blk.
Print Assumptions w3_pair.
