(** * WeakRvwmoCert2.v — B2e-3b SLICE 3b: SEGMENT CERTIFICATION

    Design: [claude-notes/design/weak-memory-route-b.md] §4e, "SLICES 2b/3,
    STATED", "SLICE 3's SHAPE AND ITS ONE OPEN RISK" and its SUB-SLICES
    entry (3b).

    WHAT THIS FILE IS.  Slice 3a ([WeakRvwmoCert]) appends ONE block to a
    candidate; slice 2b ([WeakEvProv]) says a hart's run is a function of
    the registers it READS.  This file joins them: given hart [x]'s
    G-emission ([WeakRvwmoConf.hart_conf]) and a candidate in which [x]'s
    trace is exactly a PREFIX of its G-row, it runs [x] forward through the
    emission's remaining blocks, appending each to the candidate, and
    concludes that the appended labels are the row's own — re-TIMESTAMPED
    to the candidate's log, but with the same addresses, the same data and
    the same classes — for as long as no instruction reads a TAINTED
    carrier.

    THE THREE DELIVERABLES.

    (1) [cert_step] (§3) — one [pstep_ev] of the certified hart mirroring
        one emission step.  Three shapes, because a step is one of three
        things: [cert_step_mirror] (the node is not a memory read, or is one
        whose answers are taken equal — same label, [dreg_agree] off [T]
        preserved, via [WeakEvProv.pstep_ev_dagree]); [cert_step_reindex]
        (a plain load whose G-source IS in the log — the SAME values, the
        candidate's own timestamps, same successor node, via
        [WeakEvInst.pstep_ev_ts_load]); and [cert_step_witness] (a plain
        load whose G-source is NOT in the log — ANY byte list of the right
        width is readable, the successor node DIFFERS, and the taint set
        grows).  The witness case's word is CONSTRUCTED
        ([bv_of_bytes], off [RiscvModelBytes.nth_byte_assemble_len]), not
        assumed: a substituted read is a real step of the real semantics.
        Per the brief, the destination is never the DECODER's [rd] — it is
        the step's own annotation, [WeakEvProv.pstep_hw]'s written set, and
        [WeakEvProv.taint_closure_load] is what consumes it.

    (2) [cert_block] (§4) — one [WeakRvwmoConf.hemit] block appended to the
        candidate.  [cblk] / [cblkp] are the block shapes ([HEone] /
        [HEpair]) with the run's ANNOTATIONS exposed, so that the taint
        hypothesis can be stated where it belongs — on the block's
        accumulated read list.  [cert_block_mirror] / [cert_block_pair]
        transport a block across the register-file change;
        [cert_block_snoc] / [cert_block_snoc_pair] append the result to the
        candidate, [srvwmo_consistent] (from [snoc_consistent] at the
        policy's [mstep_ok]) and [exec_prog_ok'] (from
        [exec_prog_ok'_snoc]) both.

    (3) [cert_segment] (§5) — the iteration from [k0] to the end of the
        emission, by induction on the [hemit] derivation, maintaining
        THE CERTIFICATION INVARIANT ([cert_inv]): the certified hart is at
        the SAME monad node, parked fence and channel as the emission, its
        register file agrees off [T], the candidate's per-agent [w_relp]
        agrees with the emission's wstate, and the supply is in place.  The
        conclusion is [seg_out]: an extended candidate whose new steps are
        ALL [x]'s (solo) and whose appended labels are [lbl_reidx] of the
        row's, so a WRITE (the exit write [row !! kz] in particular) is
        emitted VERBATIM — address, data and class.

    ------------------------------------------------------------------------
    THE BLOCK / INSTRUCTION ALIGNMENT, and how it is resolved.

    The iteration is over BLOCKS (one row event each) while
    [WeakEvProv.instr_dagree] is over INSTRUCTIONS (a [phrun] with no
    [LInstr]), and the two do not align: an instruction spans several
    blocks (the walker's PTE reads, then the access), and a block spans
    several instructions (the administrative run between two row events
    contains whole non-memory instructions).

    THE RESOLUTION taken here: the taint hypothesis is carried on the run's
    ACCUMULATED READ LIST [rds] — [WeakEvProv.phrun_dagree]'s own
    hypothesis, [rds_ok P rds] — and NOT on the channel.  [phrun_dagree]
    needs no [LInstr]-freeness at all: it is [WeakEvProv.instr_dagree] that
    adds it, and only to convert a CHANNEL statement
    ([WeakEvProv.phrun_ib_rds]: away from a boundary the channel accumulates
    exactly the stretch's reads) into the [rds] one.  So the iteration
    carries [rds_ok], each block contributes its own [rds] by
    concatenation, and instruction alignment enters at exactly ONE place —
    [instr_rds_of_channel] (§3.4), the corollary that lets a caller who
    knows an INSTRUCTION's channel read set (which is what §4e's "no
    [row_deps] path from a substituted read to [z]" is a statement about)
    discharge the [rds_ok] of that instruction's stretch.  [T] is carried
    across block boundaries; the channel is not, and does not have to be.

    ------------------------------------------------------------------------
    WHAT IS NARROWED, and where the narrowing is discharged later.

    (N-1) [floor_ok] — [snoc_read_consistent]'s coherence side condition
          ([WeakRvwmoCert.snoc_rd_adm]'s third conjunct: nothing the agent
          has already observed overwrites the named source).  It is an
          explicit hypothesis of [cert_read_in_log] and it is NOT derived
          here.  It is derivable from G's own consistency — the T2-1c
          route: the candidate's log below the frontier is G's rf/co
          restricted to the realized prefix, so a message strictly between
          the source and the reader's floor would be a G-side coherence
          violation.  A later slice.

    (N-2) [src_in_log] / [¬ src_in_log] — the correspondence between a
          G write index (a row label's [ts] entry) and a candidate log
          message.  It is not derived here either: it enters as the
          DATA of the read policy — [cert_read_in_log] takes the
          candidate-side timestamps [ts'] and the admissibility
          [snoc_rd_adm] as hypotheses (that IS "the source is in the log"),
          and [cert_read_witness] takes only [latest_bytes_ok] (that IS
          "the source is not in the log — read the latest").  The
          bookkeeping that produces one or the other from G is B2e-3c's.

    (N-3) The policy is a HYPOTHESIS of [cert_segment], one universally
          quantified clause ([Hpol]) rather than a construction, because
          the choice of certified label depends on the CURRENT candidate,
          which the induction changes at every block.  §4's [cert_block_*]
          are exactly what discharges it at each position; §6 discharges it
          concretely for the write witness.

    Nothing here is [Admitted] or [Axiom]-ed. *)
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
Require Import WeakEvProv.
Require Import WeakRvwmoCert.

Local Open Scope Z_scope.

(** The parked-fence field, abbreviated: it appears in every signature. *)
Notation ofence := (option (bool * bool * bool * bool)).

(* ====================================================================== *)
(** * 1. THE HART-SHAPED PIECES

    Everything below quantifies over a hart state's four components rather
    than over a [pexv6], because the certification's invariant is precisely
    "the same monad node, parked fence and channel; a DIFFERENT register
    file".  These are the lemmas that keep that shape through the run. *)

Lemma pstep_ev_phart (cpu : CPU) (m : M unit) (rs : regstate) (fn : ofence)
    (ib : oib32) (d : dev_state) (l : wlabel) (p' : pexv6) (d' : dev_state) :
  pstep_ev (PHart cpu m rs fn ib) d l p' d' →
  ∃ m' rs' fn' ib', p' = PHart cpu m' rs' fn' ib'.
Proof.
  destruct p' as [cpu' m' rs' fn' ib'|dp']; simpl; [|by intros []].
  intros (-> & ors & oib & -> & -> & _). by eexists _, _, _, _.
Qed.

Lemma adm_run_phart instr (p p' : pexv6) d ls d' :
  adm_run instr p d ls p' d' →
  ∀ cpu m rs fn ib, p = PHart cpu m rs fn ib →
  ∃ m' rs' fn' ib', p' = PHart cpu m' rs' fn' ib'.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH];
    intros cpu m rs fn ib ->.
  - by eexists _, _, _, _.
  - destruct (pstep_ev_phart cpu m rs fn ib d l p1 d1 Hs)
      as (m1 & rs1 & fn1 & ib1 & ->).
    by eapply IH.
Qed.

(** [adm_run] and [pevrun] are the same run with the same labels; the
    administrative alphabet is the only difference. *)
Lemma adm_run_pevrun instr p d ls p' d' :
  adm_run instr p d ls p' d' → pevrun ls p d p' d'.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH];
    [apply pevrun_nil|by eapply pevrun_more].
Qed.

Lemma pevrun_adm_run instr p d ls p' d' :
  pevrun ls p d p' d' → (∀ l, l ∈ ls → lb_admin instr l) →
  adm_run instr p d ls p' d'.
Proof.
  induction 1 as [p d|l ls p d p1 d1 p2 d2 Hs Hr IH]; intros Hadm.
  - apply ARnil.
  - eapply ARcons; [apply Hadm, elem_of_list_here|exact Hs|].
    apply IH. intros l0 Hl0. by apply Hadm, elem_of_list_further.
Qed.

(** THE PROJECTION EQUATION DOES NOT READ THE REGISTER FILE.  [pcls_ev]
    consults only the label, the monad node and the wstate, so the whole of
    [hlbl_realizes] / [hlbl_realizes_pair] transports across a change of
    [rs] (and of [fn], and of the channel). *)
Lemma pcls_ev_rs (cpu : CPU) (m : M unit) (rs rs' : regstate)
    (fn fn' : ofence) (ib ib' : oib32) (l : wlabel) (ws : wstate) :
  pcls_ev (PHart cpu m rs fn ib) l ws = pcls_ev (PHart cpu m rs' fn' ib') l ws.
Proof. by destruct l. Qed.

Lemma hlbl_realizes_rs cpu m rs rs' fn fn' ib ib' ws lb l :
  hlbl_realizes (PHart cpu m rs fn ib) ws lb l →
  hlbl_realizes (PHart cpu m rs' fn' ib') ws lb l.
Proof.
  intros (Hnb & Hlat & Hrf & Hpr). split_and!; [done|done|done|].
  by rewrite (pcls_ev_rs cpu m rs' rs fn' fn ib' ib l ws).
Qed.

Lemma hlbl_realizes_pair_rs cpu m rs rs' fn fn' ib ib'
    cpu2 m2 rsm rsm' fnm fnm' ibm ibm' ws lb l1 l2 :
  hlbl_realizes_pair (PHart cpu m rs fn ib) (PHart cpu2 m2 rsm fnm ibm)
    ws lb l1 l2 →
  hlbl_realizes_pair (PHart cpu m rs' fn' ib') (PHart cpu2 m2 rsm' fnm' ibm')
    ws lb l1 l2.
Proof.
  intros (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
          -> & -> & Hne & Hlen & ->).
  exists aq, rl, base, tvs, data, asrc1, asrc2, vsrc2.
  split_and!; [done|done|done|done|].
  by rewrite (pcls_ev_rs cpu2 m2 rsm' rsm fnm' fnm ibm' ibm).
Qed.

(* ====================================================================== *)
(** * 2. A SUBSTITUTED READ IS A REAL STEP

    [WeakEvInst.pstep_ev_ts_load] retimes a load — same values, different
    timestamps, SAME successor node.  A WITNESS read needs the other
    direction: different VALUES, hence a different successor node.  The
    semantics allows it unconditionally (the RAM arm quantifies the read
    word existentially; [read_ok] is the MACHINE's side, i.e. [elab_ok] of
    the label, not the program's), but the arm is stated over a WORD, so
    the substituted bytes have to be assembled back into one.  They can be:
    that is [RiscvModelBytes.nth_byte_assemble_len]. *)

Lemma bv_of_bytes (n : N) (bs : list (bv 8)) :
  length bs = N.to_nat n →
  ∃ w : bv (8 * n), ∀ j : nat, (j < N.to_nat n)%nat → bs !! j = Some (nth_byte w j).
Proof.
  intros Hlen. exists (Z_to_bv (8 * n) (assemble_bytes bs)).
  intros j Hj.
  have Hjl : (j < length bs)%nat by lia.
  rewrite (nth_byte_assemble_len (8 * n) bs j).
  - by apply list_lookup_lookup_total_lt.
  - rewrite Hlen N_nat_Z N2Z.inj_mul. lia.
  - exact Hjl.
Qed.

(** THE SUBSTITUTION, at the monad node.  ANY byte list of the read's own
    width is readable there, and the register file, the parked fence, the
    fabric and the channel all move exactly as they did — only the
    CONTINUATION differs, which is the whole content of "the runs part
    company at a witness read". *)
Lemma pnode_step_load_subst (m : M unit) (rs : regstate) (ib : oib32)
    (d : dev_state) aq base (tvs tvs2 : list (nat * bv 8)) m' ors fn' d' oib :
  pnode_step m rs ib d (LLoad aq false base tvs []) m' ors fn' d' oib →
  length tvs2 = length tvs →
  ∃ m2, pnode_step m rs ib d (LLoad aq false base tvs2 []) m2 ors fn' d' oib.
Proof.
  rewrite /pnode_step. destruct m as [y|T oc k].
  { by intros (? & ? & _). }
  destruct oc; simpl; try (by intros (? & _));
    try (intros (Hl & _);
         by destruct (erw_of (deps_of_ib (ib_bits ib)) (ib_rds ib) reg));
    try (by intros []).
  - (* MemRead *) destruct (dev_addr _).
    + by intros (w & _ & ? & _).
    + intros (Hcoh & [(Hlat & w & tvs0 & Hlen & Hby & Hl & Hrest)
                     |(_ & w & tvs0 & _ & _ & Hl & _)]) Hts; [|by simplify_eq].
      simplify_eq/=.
      destruct Hrest as (-> & -> & -> & -> & ->).
      have Hl2 : length tvs2.*2 = N.to_nat n by rewrite length_fmap Hts.
      destruct (bv_of_bytes n tvs2.*2 Hl2) as (w2 & Hw2).
      exists (k (inl (w2, None))).
      split; [exact Hcoh|]. left. split; [exact Hlat|].
      exists w2, tvs2. split_and!; first [lia | exact Hw2 | done].
  - (* MemWrite *) destruct (dev_addr _).
    + by intros (? & ? & _).
    + by intros (_ & [(_ & ? & _)|(_ & [(? & _)|(? & _)])]).
  - (* Barrier *) intros (Hl & _). by destruct b.
  - (* Choose *) by intros (ch & ? & _).
Qed.

Lemma pstep_ev_load_subst cpu (m : M unit) (rs : regstate) (fn : ofence)
    (ib : oib32) (d : dev_state) aq base (tvs tvs2 : list (nat * bv 8))
    m' rs' fn' ib' d' :
  pstep_ev (PHart cpu m rs fn ib) d (LLoad aq false base tvs [])
    (PHart cpu m' rs' fn' ib') d' →
  length tvs2 = length tvs →
  ∃ m2, pstep_ev (PHart cpu m rs fn ib) d (LLoad aq false base tvs2 [])
          (PHart cpu m2 rs' fn' ib') d'.
Proof.
  intros (_ & ors & oib & Hrs & Hib & [Hn|(Hl & _)]) Hts; [|done].
  rewrite /pstep_node in Hn. destruct fn as [[[[pr pw] sr] sw]|];
    [by destruct Hn as (? & _)|].
  destruct (pnode_step_load_subst m rs ib d aq base tvs tvs2 m' ors fn' d' oib
              Hn Hts) as (m2 & Hn2).
  exists m2. split; [reflexivity|]. exists ors, oib.
  split_and!; [exact Hrs|exact Hib|]. by left.
Qed.

(* ====================================================================== *)
(** * 3. DELIVERABLE (1): [cert_step]

    ONE [pstep_ev] step of the certified hart mirroring one step of the
    emission.  The three shapes are the three things the emission's node can
    be, from the certification's point of view. *)

(** ** 3.1 The node is not a memory read (or its answers are taken equal)

    Then the certified step emits the SAME label, lands at the SAME node,
    and [dreg_agree] off [T] is preserved.  This is
    [WeakEvProv.pstep_ev_dagree] at the hart shape, and the only hypothesis
    is that the step reads no register the taint set holds. *)
Theorem cert_step_mirror (P : wreg → Prop) cpu (m : M unit) (rs1 rs2 : regstate)
    (fn : ofence) (ib : oib32) (d : dev_state) (l : wlabel)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32) (d' : dev_state) :
  rds_ok P (pnode_rds m) →
  dreg_agree P rs1 rs2 →
  pstep_ev (PHart cpu m rs1 fn ib) d l (PHart cpu m' rs1' fn' ib') d' →
  ∃ rs2', pstep_ev (PHart cpu m rs2 fn ib) d l (PHart cpu m' rs2' fn' ib') d' ∧
          dreg_agree P rs1' rs2'.
Proof. intros Hrds Hag Hst. by eapply pstep_ev_dagree. Qed.

(** ** 3.2 A plain load whose G-source IS in the log ([src_in_log])

    The certified label carries the CANDIDATE's timestamps and the SAME
    values, so the successor node — hence the whole rest of the run — is
    untouched.  [WeakEvInst.pstep_ev_ts_load] is what makes that a theorem
    rather than an assumption. *)
Theorem cert_step_reindex (P : wreg → Prop) cpu (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (d : dev_state)
    aq base (tvs tvs2 : list (nat * bv 8))
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32) (d' : dev_state) :
  rds_ok P (pnode_rds m) →
  dreg_agree P rs1 rs2 →
  pstep_ev (PHart cpu m rs1 fn ib) d (LLoad aq false base tvs [])
    (PHart cpu m' rs1' fn' ib') d' →
  tvs2.*2 = tvs.*2 →
  ∃ rs2', pstep_ev (PHart cpu m rs2 fn ib) d (LLoad aq false base tvs2 [])
            (PHart cpu m' rs2' fn' ib') d' ∧
          dreg_agree P rs1' rs2'.
Proof.
  intros Hrds Hag Hst Hts.
  destruct (pstep_ev_dagree P cpu m rs1 rs2 fn ib d _ m' rs1' fn' ib' d'
              Hrds Hag Hst) as (rs2' & Hst2 & Hag2).
  exists rs2'. split; [|exact Hag2]. by eapply pstep_ev_ts_load.
Qed.

(** ** 3.3 A plain load whose G-source is NOT in the log (a WITNESS)

    The certified label carries DIFFERENT values, so the continuation
    differs: this is where the two runs part company.  The step exists for
    ANY byte list of the read's own width — a substituted read is a real
    step of the real semantics, not a fiction. *)
Theorem cert_step_witness (P : wreg → Prop) cpu (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (d : dev_state)
    aq base (tvs tvs2 : list (nat * bv 8))
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32) (d' : dev_state) :
  rds_ok P (pnode_rds m) →
  dreg_agree P rs1 rs2 →
  pstep_ev (PHart cpu m rs1 fn ib) d (LLoad aq false base tvs [])
    (PHart cpu m' rs1' fn' ib') d' →
  length tvs2 = length tvs →
  ∃ m2 rs2', pstep_ev (PHart cpu m rs2 fn ib) d (LLoad aq false base tvs2 [])
               (PHart cpu m2 rs2' fn' ib') d' ∧
             dreg_agree P rs1' rs2'.
Proof.
  intros Hrds Hag Hst Hlen.
  destruct (pstep_ev_dagree P cpu m rs1 rs2 fn ib d _ m' rs1' fn' ib' d'
              Hrds Hag Hst) as (rs2' & Hst2 & Hag2).
  destruct (pstep_ev_load_subst cpu m rs2 fn ib d aq base tvs tvs2 m' rs2'
              fn' ib' d' Hst2 Hlen) as (m2 & Hst3).
  by exists m2, rs2'.
Qed.

(** ** 3.4 THE BLOCK / INSTRUCTION SEAM

    The iteration's taint hypothesis is [rds_ok P rds] on the run's
    accumulated read list.  A caller who instead knows an INSTRUCTION's
    CHANNEL read set — which is the vocabulary §4e's "no [row_deps] path
    from a substituted read to [z]" speaks — converts it here, and this is
    the ONLY place instruction alignment ([LInstr]-freeness) is used. *)
Theorem instr_rds_of_channel (T : list wreg) cpu ls rds wrs ann
    m rs fn ib d m' rs' fn' ib' d' :
  phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
  LInstr ∉ ls →
  (∀ n, n ∈ ib_rds ib' → n ∉ T) →
  rds_ok (λ n, n ∉ T) rds.
Proof.
  intros Hrun Hni Hib n Hn. apply Hib.
  rewrite (phrun_ib_rds cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' Hrun
             (phrun_no_instr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hni)).
  apply elem_of_app. by right.
Qed.

(** ** 3.5 The taint growth, at the step's OWN annotation

    Not the decoder's [rd]: the written set is [pstep_hw]'s, so a write to a
    non-carrier (the PC) cannot be absorbed.  This is
    [WeakEvProv.taint_closure_load] with both remainders on one hart. *)
Corollary cert_step_taint (T : list wreg) (rd : wreg) cpu
    ls1 rds1 wrs1 ann1 ma1 rsa1 fna1 iba1 da1 mb1 rsb1 fnb1 ibb1 db1
    ls2 rds2 wrs2 ann2 ma2 rsa2 fna2 iba2 da2 mb2 rsb2 fnb2 ibb2 db2 :
  dreg_agree (λ n, n ∉ T) rsa1 rsa2 →
  phrun cpu ls1 rds1 wrs1 ann1 ma1 rsa1 fna1 iba1 da1 mb1 rsb1 fnb1 ibb1 db1 →
  phrun cpu ls2 rds2 wrs2 ann2 ma2 rsa2 fna2 iba2 da2 mb2 rsb2 fnb2 ibb2 db2 →
  (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, ereg_num r = Some n ∧ n ∈ rd :: T) →
  dreg_agree (λ n, n ∉ rd :: T) rsb1 rsb2.
Proof. intros. by eapply taint_closure_load. Qed.

(* ====================================================================== *)
(** * 4. DELIVERABLE (2): [cert_block]

    ONE [WeakRvwmoConf.hemit] block — an [adm_run true] and the realizing
    [pstep_ev] — transported across a change of register file, and then
    appended to the candidate.

    [cblk] IS THAT BLOCK WITH ITS RUN'S ANNOTATIONS EXPOSED.  [hemit] buries
    the block's read and write sets inside an [adm_run]; the taint
    hypothesis is a statement ABOUT them, so they have to be visible.  Both
    halves of the block are [WeakEvProv.phrun]s (the administrative prefix
    and the single realizing step), and [rds]/[wrs] are their
    concatenations. *)

Definition cblk (cpu : CPU) (d0 : dev_state) (ws : wstate) (lb : lbl)
    (l : wlabel) (rds : list wreg) (wrs : list register)
    (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32) : Prop :=
  ∃ ls ma rsa fna iba da rdsA wrsA annA rdsB wrsB annB,
    (∀ l0, l0 ∈ ls → lb_admin true l0) ∧
    phrun cpu ls rdsA wrsA annA m rs fn ib d0 ma rsa fna iba da ∧
    hlbl_realizes (PHart cpu ma rsa fna iba) ws lb l ∧
    phrun cpu [l] rdsB wrsB annB ma rsa fna iba da m' rs' fn' ib' d0 ∧
    rds = rdsA ++ rdsB ∧ wrs = wrsA ++ wrsB.

(** ** 4.1 [cblk] and the [hemit] block are the same object *)

Lemma pevrun_nil_inv p d p' d' : pevrun [] p d p' d' → p' = p ∧ d' = d.
Proof. intros H. by inversion H. Qed.

Lemma pevrun_single_inv l p d p' d' :
  pevrun [l] p d p' d' → pstep_ev p d l p' d'.
Proof.
  intros H. remember [l] as ls eqn:Hls.
  destruct H as [q0 e0|l0 ls0 q0 e0 q1 e1 q2 e2 Hst Hrun];
    [discriminate Hls|].
  injection Hls as -> ->.
  destruct (pevrun_nil_inv q1 e1 q2 e2 Hrun) as (-> & ->). exact Hst.
Qed.

Lemma cblk_intro cpu d0 ws lb l ls pa da m rs fn ib m' rs' fn' ib' :
  adm_run true (PHart cpu m rs fn ib) d0 ls pa da →
  hlbl_realizes pa ws lb l →
  pstep_ev pa da l (PHart cpu m' rs' fn' ib') d0 →
  ∃ rds wrs, cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib'.
Proof.
  intros Har Hre Hst.
  destruct (adm_run_phart true _ _ d0 ls da Har cpu m rs fn ib eq_refl)
    as (ma & rsa & fna & iba & ->).
  destruct (pevrun_phrun ls _ d0 _ da (adm_run_pevrun _ _ _ _ _ _ Har)
              cpu m rs fn ib ma rsa fna iba eq_refl eq_refl)
    as (rdsA & wrsA & annA & HA).
  destruct (pevrun_phrun [l] _ da _ d0
              (pevrun_more l [] _ da _ d0 _ d0 Hst (pevrun_nil _ _))
              cpu ma rsa fna iba m' rs' fn' ib' eq_refl eq_refl)
    as (rdsB & wrsB & annB & HB).
  exists (rdsA ++ rdsB), (wrsA ++ wrsB).
  exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB.
  split_and!; [|exact HA|exact Hre|exact HB|reflexivity|reflexivity].
  by eapply adm_run_admin.
Qed.

Lemma cblk_elim cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' :
  cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
  ∃ ls pa da, adm_run true (PHart cpu m rs fn ib) d0 ls pa da ∧
    hlbl_realizes pa ws lb l ∧
    pstep_ev pa da l (PHart cpu m' rs' fn' ib') d0.
Proof.
  intros (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
          & annB & Hadm & HA & Hre & HB & _ & _).
  exists ls, (PHart cpu ma rsa fna iba), da. split_and!; [|exact Hre|].
  - apply (pevrun_adm_run true _ d0 ls _ da (phrun_pevrun _ _ _ _ _ _ _ _ _ _ _
             _ _ _ _ HA) Hadm).
  - apply pevrun_single_inv. by eapply phrun_pevrun.
Qed.

(** The projection equation inside a block reads the wstate only through
    [w_relp] ([WeakRvwmoSupply.hlbl_realizes_relp]). *)
Lemma cblk_relp cpu d0 ws ws' lb l rds wrs m rs fn ib m' rs' fn' ib' :
  w_relp ws' = w_relp ws →
  cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
  cblk cpu d0 ws' lb l rds wrs m rs fn ib m' rs' fn' ib'.
Proof.
  intros Hr (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
             & annB & Hadm & HA & Hre & HB & -> & ->).
  exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB.
  split_and!; [exact Hadm|exact HA| |exact HB|reflexivity|reflexivity].
  by eapply hlbl_realizes_relp.
Qed.

(** ** 4.2 The block, transported *)

(** THE MIRROR: the block reads no tainted carrier, so the certified hart
    runs it STEP FOR STEP — same administrative labels, same realizing
    label, same axiomatic label, same successor node. *)
Theorem cert_block_mirror (P : wreg → Prop) cpu d0 ws lb l rds wrs
    m rs1 fn ib m' rs1' fn' ib' rs2 :
  cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
  rds_ok P rds →
  dreg_agree P rs1 rs2 →
  ∃ rs2', cblk cpu d0 ws lb l rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
          dreg_agree P rs1' rs2'.
Proof.
  intros (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
          & annB & Hadm & HA & Hre & HB & -> & ->) Hrds Hag.
  apply rds_ok_app in Hrds as [HrdsA HrdsB].
  destruct (phrun_dagree P cpu ls rdsA wrsA annA m rs1 fn ib d0
              ma rsa fna iba da HA HrdsA rs2 Hag) as (rsa2 & HA2 & Haga).
  destruct (phrun_dagree P cpu [l] rdsB wrsB annB ma rsa fna iba da
              m' rs1' fn' ib' d0 HB HrdsB rsa2 Haga) as (rs2' & HB2 & Hag2).
  exists rs2'. split; [|exact Hag2].
  exists ls, ma, rsa2, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB.
  split_and!; [exact Hadm|exact HA2| |exact HB2|reflexivity|reflexivity].
  by eapply hlbl_realizes_rs.
Qed.

(** ** 4.3 The two read policies, at the block

    [lbl_reidx] is the label correspondence the certification delivers: the
    candidate's timestamps are its OWN, everything else — address, data,
    class, width — is the row's.  In particular a plain STORE is related to
    itself, which is why the exit write comes out VERBATIM. *)
Definition lbl_reidx (lb lb' : lbl) : Prop :=
  match lb with
  | WeakAxiomatic.LLoad aq base ts vs =>
      match lb' with
      | WeakAxiomatic.LLoad aq' base' ts' vs' =>
          aq' = aq ∧ base' = base ∧ vs' = vs ∧ length ts' = length ts
      | _ => False
      end
  | WeakAxiomatic.LRmw aq rl base ts rvs wvs kc =>
      match lb' with
      | WeakAxiomatic.LRmw aq' rl' base' ts' rvs' wvs' kc' =>
          aq' = aq ∧ rl' = rl ∧ base' = base ∧ rvs' = rvs ∧ wvs' = wvs ∧
          kc' = kc ∧ length ts' = length ts
      | _ => False
      end
  | _ => lb' = lb
  end.

Lemma lbl_reidx_refl lb : lbl_reidx lb lb.
Proof. destruct lb; simpl; first [done | by split_and!]. Qed.

(** THE EXIT WRITE IS VERBATIM. *)
Lemma lbl_reidx_store rl base vs kc lb' :
  lbl_reidx (WeakAxiomatic.LStore rl base vs kc) lb' →
  lb' = WeakAxiomatic.LStore rl base vs kc.
Proof. done. Qed.

Lemma lbl_reidx_fence pr pw sr sw lb' :
  lbl_reidx (WeakAxiomatic.LFence pr pw sr sw) lb' →
  lb' = WeakAxiomatic.LFence pr pw sr sw.
Proof. done. Qed.

(** ... and it does not move the release-pending bit, which is the only
    thing the projection equation reads of the wstate. *)
Lemma lbl_reidx_relp b lb lb' :
  lbl_reidx lb lb' → lpost_relp b lb' = lpost_relp b lb.
Proof.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc];
    destruct lb' as [aq' base' ts' vs'|rl' base' vs' kc'|pr' pw' sr' sw'|
                     aq' rl' base' ts' rvs' wvs' kc'];
    simpl;
    first [ by intros []
          | by (intros Hc; simplify_eq)
          | by intros (-> & -> & -> & _)
          | by intros (-> & -> & -> & -> & -> & -> & _) ].
Qed.

(** ** 4.3a THE WITNESS-AWARE CORRESPONDENCE

    [lbl_reidx] frees a read's INDICES and nothing else, so a certified
    read must hand back [G]'s own VALUES.  AT A WITNESS THAT IS FALSE.  The
    certified label there is the candidate's LATEST-source read
    ([WeakRvwmoCert.latest_read_lbl]), whose values are the CANDIDATE's own
    bytes and have no reason whatever to be [G]'s: the walk substitutes a
    value, not only a timestamp.  Demanding that they coincide is what made
    [WeakRvwmoWalk.wwit_site] carry [lrd_vs c base n = vs] — a clause no
    graph fact supplies, and one that a witness graph BUILT so the values
    agree does not test.

    [lbl_reidx_sub] is the honest correspondence at a witness, and it is
    exactly [WeakRvwmoCert3.ctrace_prefix]'s own witness arm: the same
    FOOTPRINT (base, width), PLAIN ([aq = false], [witness_not_aq]) and
    ARBITRARY values.

    WHERE THE POSITION-INDEXED PRECISION LIVES.  [lbl_reidx_w] is the
    disjunction of the two, so the row correspondence alone does not say
    WHICH positions were substituted.  It does not have to: the
    classification the policy delivers per step
    ([WeakRvwmoGlue2.cstep_cls], carried into [ctrace_prefix]'s [ctp_step])
    already names the witness set and pins the substituted label to
    [latest_read_lbl] at exactly those positions — that is the
    position-indexed statement, and it was always the one downstream reads.
    A store, a fence and an RMW are unaffected either way ([lbl_reidx_sub]
    is inhabited only at a LOAD), which is why every consumer of the row
    correspondence — the exit write, the write bit, the release-pending
    bit — comes through unchanged. *)
Definition lbl_reidx_sub (lb lb' : lbl) : Prop :=
  match lb with
  | WeakAxiomatic.LLoad aq base ts _ =>
      match lb' with
      | WeakAxiomatic.LLoad aq' base' ts' vs' =>
          aq = false ∧ aq' = false ∧ base' = base ∧
          length ts' = length ts ∧ length vs' = length ts'
      | _ => False
      end
  | _ => False
  end.

Definition lbl_reidx_w (lb lb' : lbl) : Prop :=
  lbl_reidx lb lb' ∨ lbl_reidx_sub lb lb'.

Lemma lbl_reidx_w_refl lb : lbl_reidx_w lb lb.
Proof. left. apply lbl_reidx_refl. Qed.

Lemma lbl_reidx_w_of lb lb' : lbl_reidx lb lb' → lbl_reidx_w lb lb'.
Proof. by left. Qed.

(** THE EXIT WRITE IS STILL VERBATIM — the substituted arm is a load's. *)
Lemma lbl_reidx_w_store rl base vs kc lb' :
  lbl_reidx_w (WeakAxiomatic.LStore rl base vs kc) lb' →
  lb' = WeakAxiomatic.LStore rl base vs kc.
Proof. by intros [H|H]. Qed.

Lemma lbl_reidx_w_fence pr pw sr sw lb' :
  lbl_reidx_w (WeakAxiomatic.LFence pr pw sr sw) lb' →
  lb' = WeakAxiomatic.LFence pr pw sr sw.
Proof. by intros [H|H]. Qed.

Lemma lbl_reidx_sub_relp b lb lb' :
  lbl_reidx_sub lb lb' → lpost_relp b lb' = lpost_relp b lb.
Proof.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc];
    destruct lb' as [aq' base' ts' vs'|rl' base' vs' kc'|pr' pw' sr' sw'|
                     aq' rl' base' ts' rvs' wvs' kc'];
    by intros H.
Qed.

Lemma lbl_reidx_w_relp b lb lb' :
  lbl_reidx_w lb lb' → lpost_relp b lb' = lpost_relp b lb.
Proof.
  intros [H|H]; [by apply lbl_reidx_relp|by apply lbl_reidx_sub_relp].
Qed.

(** … and it moves neither the write bit nor, therefore, the message. *)
Lemma lbl_reidx_w_isw lb lb' : lbl_reidx_w lb lb' → lb_is_w lb' = lb_is_w lb.
Proof.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc];
    destruct lb' as [aq' base' ts' vs'|rl' base' vs' kc'|pr' pw' sr' sw'|
                     aq' rl' base' ts' rvs' wvs' kc'];
    intros [H|H]; try (by simplify_eq); try (by destruct H).
Qed.

Lemma lbl_reidx_w_notw lb lb' :
  lbl_reidx_w lb lb' → lb_is_w lb = false → lb_is_w lb' = false.
Proof. intros H Hw. by rewrite (lbl_reidx_w_isw lb lb' H). Qed.

(** The load block's two ends, computed. *)
Lemma hlbl_realizes_load p ws aq base (tvs : list (nat * bv 8)) :
  hlbl_realizes p ws (WeakAxiomatic.LLoad aq base tvs.*1 tvs.*2)
    (LLoad aq false base tvs []).
Proof.
  rewrite /hlbl_realizes.
  split_and!; [exact I|reflexivity|reflexivity|reflexivity].
Qed.

Lemma hlbl_realizes_load_inv p ws lb aq base (tvs : list (nat * bv 8)) :
  hlbl_realizes p ws lb (LLoad aq false base tvs []) →
  lb = WeakAxiomatic.LLoad aq base tvs.*1 tvs.*2.
Proof. intros (_ & _ & _ & Hpr). simpl in Hpr. by simplify_eq. Qed.

(** RE-TIMESTAMPING a load block: same values, the candidate's indices, and
    NOTHING else moves — same successor node, same register file, same
    channel.  ([WeakEvInst.pstep_ev_ts_load].) *)
Lemma cblk_retime cpu d0 ws lb rds wrs m rs fn ib m' rs' fn' ib'
    aq base (tvs tvs2 : list (nat * bv 8)) :
  cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs
    m rs fn ib m' rs' fn' ib' →
  tvs2.*2 = tvs.*2 →
  ∃ rds2 wrs2,
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2)
      (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m' rs' fn' ib'.
Proof.
  intros (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
          & annB & Hadm & HA & Hre & HB & -> & ->) Hts.
  have Hst : pstep_ev (PHart cpu ma rsa fna iba) da
               (LLoad aq false base tvs2 []) (PHart cpu m' rs' fn' ib') d0.
  { eapply pstep_ev_ts_load; [|exact Hts].
    apply pevrun_single_inv. by eapply phrun_pevrun. }
  destruct (pevrun_phrun [_] _ da _ d0
              (pevrun_more _ [] _ da _ d0 _ d0 Hst (pevrun_nil _ _))
              cpu ma rsa fna iba m' rs' fn' ib' eq_refl eq_refl)
    as (rdsB2 & wrsB2 & annB2 & HB2).
  exists (rdsA ++ rdsB2), (wrsA ++ wrsB2).
  exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2, wrsB2, annB2.
  split_and!; [exact Hadm|exact HA|apply hlbl_realizes_load|exact HB2
              |reflexivity|reflexivity].
Qed.

(** SUBSTITUTING a load block's values (a WITNESS): the successor NODE
    differs — this is where the runs part company — and everything else
    (register file, parked fence, channel, fabric) is untouched. *)
Lemma cblk_subst cpu d0 ws lb rds wrs m rs fn ib m' rs' fn' ib'
    aq base (tvs tvs2 : list (nat * bv 8)) :
  cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs
    m rs fn ib m' rs' fn' ib' →
  length tvs2 = length tvs →
  ∃ m2 rds2 wrs2,
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2)
      (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m2 rs' fn' ib'.
Proof.
  intros (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
          & annB & Hadm & HA & Hre & HB & -> & ->) Hlen.
  have Hst : pstep_ev (PHart cpu ma rsa fna iba) da
               (LLoad aq false base tvs []) (PHart cpu m' rs' fn' ib') d0.
  { apply pevrun_single_inv. by eapply phrun_pevrun. }
  destruct (pstep_ev_load_subst cpu ma rsa fna iba da aq base tvs tvs2
              m' rs' fn' ib' d0 Hst Hlen) as (m2 & Hst2).
  destruct (pevrun_phrun [_] _ da _ d0
              (pevrun_more _ [] _ da _ d0 _ d0 Hst2 (pevrun_nil _ _))
              cpu ma rsa fna iba m2 rs' fn' ib' eq_refl eq_refl)
    as (rdsB2 & wrsB2 & annB2 & HB2).
  exists m2, (rdsA ++ rdsB2), (wrsA ++ wrsB2).
  exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2, wrsB2, annB2.
  split_and!; [exact Hadm|exact HA|apply hlbl_realizes_load|exact HB2
              |reflexivity|reflexivity].
Qed.

(** ** 4.3a THE WLABEL SHAPE OF A LOAD BLOCK, AND THE SHAPE-FREE RETIME

    [WeakPromiseBridge.proj_lbl] sends exactly TWO wlabel constructors to an
    axiomatic [LLoad]: the plain [LLoad] — whose [lat] is [false] by
    [WeakPromiseFact.lat_free] and whose operand list is empty by
    [WeakAxRealize.lb_rfoldfree] — and the exclusive read [LExLoad].  Both
    are re-timestampable at the SAME successor node
    ([WeakEvInst.pstep_ev_ts_load] / [pstep_ev_ts_exload]), so a load block
    can be retimed without the caller knowing which one realizes it.  That
    is what a policy serving a WITNESS position needs: it is handed a
    [cblk] at an arbitrary wlabel. *)
Lemma hlbl_realizes_load_shape p ws aq base ts vs l :
  hlbl_realizes p ws (WeakAxiomatic.LLoad aq base ts vs) l →
  ∃ tvs : list (nat * bv 8),
    tvs.*1 = ts ∧ tvs.*2 = vs ∧
    (l = LLoad aq false base tvs [] ∨ ∃ asrc, l = LExLoad aq base tvs asrc).
Proof.
  intros (Hbx & Hlat & Hrf & Hpr).
  destruct l; simpl in Hpr; try discriminate.
  - (* the plain load *)
    injection Hpr as <- <- <- <-. simpl in Hlat, Hrf. subst.
    eexists. split_and!; [reflexivity|reflexivity|by left].
  - (* the exclusive read *)
    injection Hpr as <- <- <- <-.
    eexists. split_and!; [reflexivity|reflexivity|right; by eexists].
Qed.

Lemma cblk_load_retime cpu d0 ws aq base ts vs l rds wrs
    m rs fn ib m' rs' fn' ib' (tvs2 : list (nat * bv 8)) :
  cblk cpu d0 ws (WeakAxiomatic.LLoad aq base ts vs) l rds wrs
    m rs fn ib m' rs' fn' ib' →
  tvs2.*2 = vs →
  ∃ l2 rds2 wrs2,
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2) l2 rds2 wrs2
      m rs fn ib m' rs' fn' ib'.
Proof.
  intros (ls & ma & rsa & fna & iba & da & rdsA & wrsA & annA & rdsB & wrsB
          & annB & Hadm & HA & Hre & HB & -> & ->) Hts.
  have Hst : pstep_ev (PHart cpu ma rsa fna iba) da l
               (PHart cpu m' rs' fn' ib') d0.
  { apply pevrun_single_inv. by eapply phrun_pevrun. }
  destruct (hlbl_realizes_load_shape (PHart cpu ma rsa fna iba) ws
              aq base ts vs l Hre) as (tvs & Hf & Hs & [Hl|(asrc & Hl)]);
    subst l.
  - have Hts' : tvs2.*2 = tvs.*2 by rewrite Hts Hs.
    have Hst2 : pstep_ev (PHart cpu ma rsa fna iba) da
                  (LLoad aq false base tvs2 []) (PHart cpu m' rs' fn' ib') d0
      := pstep_ev_ts_load _ _ _ _ _ _ _ _ Hst Hts'.
    destruct (pevrun_phrun [_] _ da _ d0
                (pevrun_more _ [] _ da _ d0 _ d0 Hst2 (pevrun_nil _ _))
                cpu ma rsa fna iba m' rs' fn' ib' eq_refl eq_refl)
      as (rdsB2 & wrsB2 & annB2 & HB2).
    exists (LLoad aq false base tvs2 []), (rdsA ++ rdsB2), (wrsA ++ wrsB2).
    exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2, wrsB2, annB2.
    split_and!; [exact Hadm|exact HA|apply hlbl_realizes_load|exact HB2
                |reflexivity|reflexivity].
  - have Hts' : tvs2.*2 = tvs.*2 by rewrite Hts Hs.
    have Hst2 : pstep_ev (PHart cpu ma rsa fna iba) da
                  (LExLoad aq base tvs2 asrc) (PHart cpu m' rs' fn' ib') d0
      := pstep_ev_ts_exload _ _ _ _ _ _ _ _ _ Hst Hts'.
    destruct (pevrun_phrun [_] _ da _ d0
                (pevrun_more _ [] _ da _ d0 _ d0 Hst2 (pevrun_nil _ _))
                cpu ma rsa fna iba m' rs' fn' ib' eq_refl eq_refl)
      as (rdsB2 & wrsB2 & annB2 & HB2).
    exists (LExLoad aq base tvs2 asrc), (rdsA ++ rdsB2), (wrsA ++ wrsB2).
    exists ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2, wrsB2, annB2.
    split_and!; [exact Hadm|exact HA| |exact HB2|reflexivity|reflexivity].
    by rewrite /hlbl_realizes.
Qed.

(** ** 4.3b THE SUBSTITUTION'S MACHINE-SIDE COST, NAMED

    [cblk_subst] substitutes a load block's values but lands at a DIFFERENT
    successor node [m2] — that is the whole content of "the runs part
    company at a witness".  The segment iteration, however, continues from
    the EMISSION's own successor node ([cert_segment]'s invariant: the two
    runs are at the same node), so a witness position is servable only when
    the substituted read re-converges IMMEDIATELY.  [cblk_vfree] is exactly
    that statement — (O-2) in the one form the iteration needs — and making
    it an explicit obligation is what the old value-coincidence clause was
    hiding: with [lrd_vs c base n = vs] the substitution was no
    substitution at all, so [cblk_load_retime] sufficed
    ([cblk_vfree_of_retime] below is precisely that degenerate case). *)
Definition cblk_vfree (cpu : CPU) (d0 : dev_state) (ws : wstate)
    (aq : bool) (base : Z) (ts : list nat) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32) : Prop :=
  ∀ tvs2 : list (nat * bv 8), length tvs2 = length ts →
    ∃ l2 rds2 wrs2,
      cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2) l2 rds2 wrs2
        m rs fn ib m' rs' fn' ib'.

(** THE DEGENERATE CASE: if the substituted values are the ones the block
    already read, [cblk_vfree] is [cblk_load_retime] and costs nothing.
    This is the shape the old [wwit_site] forced, and it is why the
    obligation was invisible. *)
Lemma cblk_vfree_of_retime cpu d0 ws aq base ts vs l rds wrs
    m rs fn ib m' rs' fn' ib' :
  cblk cpu d0 ws (WeakAxiomatic.LLoad aq base ts vs) l rds wrs
    m rs fn ib m' rs' fn' ib' →
  ∀ tvs2 : list (nat * bv 8), tvs2.*2 = vs →
    ∃ l2 rds2 wrs2,
      cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2) l2 rds2 wrs2
        m rs fn ib m' rs' fn' ib'.
Proof.
  intros Hblk tvs2 Hts.
  by apply (cblk_load_retime cpu d0 ws aq base ts vs l rds wrs
              m rs fn ib m' rs' fn' ib' tvs2 Hblk).
Qed.

(** THE IN-LOG READ ([src_in_log]) — the block, transported and retimed. *)
Theorem cert_block_read (P : wreg → Prop) cpu d0 ws lb rds wrs
    m rs1 fn ib m' rs1' fn' ib' rs2 aq base (tvs tvs2 : list (nat * bv 8)) :
  cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  rds_ok P rds → dreg_agree P rs1 rs2 → tvs2.*2 = tvs.*2 →
  ∃ rs2' rds2 wrs2,
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2)
      (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m' rs2' fn' ib' ∧
    lbl_reidx lb (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2) ∧
    dreg_agree P rs1' rs2'.
Proof.
  intros Hblk Hrds Hag Hts.
  have Hlb : lb = WeakAxiomatic.LLoad aq base tvs.*1 tvs.*2.
  { destruct Hblk as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      _ & _ & Hre & _).
    by eapply hlbl_realizes_load_inv. }
  destruct (cert_block_mirror P cpu d0 ws lb _ rds wrs m rs1 fn ib m' rs1'
              fn' ib' rs2 Hblk Hrds Hag) as (rs2' & Hblk2 & Hag2).
  destruct (cblk_retime cpu d0 ws lb rds wrs m rs2 fn ib m' rs2' fn' ib'
              aq base tvs tvs2 Hblk2 Hts) as (rds2 & wrs2 & Hblk3).
  exists rs2', rds2, wrs2. split_and!; [exact Hblk3| |exact Hag2].
  rewrite Hlb /=. split_and!; [done|done|by rewrite Hts|].
  by rewrite !length_fmap -(length_fmap snd tvs2) -(length_fmap snd tvs) Hts.
Qed.

(** THE WITNESS READ (¬ [src_in_log]) — the block, transported and
    SUBSTITUTED.  The successor node is a fresh one, which is exactly the
    divergence [cert_step_taint] then pays for. *)
Theorem cert_block_witness (P : wreg → Prop) cpu d0 ws lb rds wrs
    m rs1 fn ib m' rs1' fn' ib' rs2 aq base (tvs tvs2 : list (nat * bv 8)) :
  cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  rds_ok P rds → dreg_agree P rs1 rs2 → length tvs2 = length tvs →
  ∃ m2 rs2' rds2 wrs2,
    cblk cpu d0 ws (WeakAxiomatic.LLoad aq base tvs2.*1 tvs2.*2)
      (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m2 rs2' fn' ib' ∧
    dreg_agree P rs1' rs2'.
Proof.
  intros Hblk Hrds Hag Hlen.
  destruct (cert_block_mirror P cpu d0 ws lb _ rds wrs m rs1 fn ib m' rs1'
              fn' ib' rs2 Hblk Hrds Hag) as (rs2' & Hblk2 & Hag2).
  destruct (cblk_subst cpu d0 ws lb rds wrs m rs2 fn ib m' rs2' fn' ib'
              aq base tvs tvs2 Hblk2 Hlen) as (m2 & rds2 & wrs2 & Hblk3).
  by exists m2, rs2', rds2, wrs2.
Qed.

(** ** 4.4 The block, APPENDED

    The two halves of [WeakRvwmoCert] at once: [snoc_consistent] for the
    axiomatic side (its ONE local side condition is the policy's
    [mstep_ok]) and [exec_prog_ok'_snoc] for the program side. *)
Theorem cert_block_snoc (c : cand) (x : agent) (pst : nat → list pexv6)
    (dv : nat → dev_state) cpu d0 lb l rds wrs m rs fn ib m' rs' fn' ib' :
  srvwmo_consistent c →
  exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
  pst (cd_end c) !! x = Some (PHart cpu m rs fn ib) →
  dv (cd_end c) = d0 →
  cblk cpu d0 (ms_ws (cand_last_st c) x) lb l rds wrs m rs fn ib m' rs' fn' ib' →
  mstep_ok (cand_last_st c) x lb →
  srvwmo_consistent (cand_snoc c (EStep x lb)) ∧
  exec_prog_ok' pstep_ev pcls_ev
    (pst_snoc c pst x (PHart cpu m' rs' fn' ib')) (dv_snoc c dv d0)
    (cand_exec (cand_snoc c (EStep x lb))).
Proof.
  intros Hc Hpo Hp Hdv Hblk Hok. split; [by apply snoc_consistent|].
  destruct (cblk_elim cpu d0 _ lb l rds wrs m rs fn ib m' rs' fn' ib' Hblk)
    as (ls & pa & da & Har & Hre & Hst).
  eapply (exec_prog_ok'_snoc c x _ pa da ls l lb _ d0);
    [exact Hpo|exact Hp| |exact Hre|exact Hst].
  by rewrite Hdv.
Qed.

(** ** 4.5 THE THREE ADMISSIBILITY ROUTES, as [mstep_ok] providers

    [src_in_log] / [floor_ok] are the brief's two named hypotheses, split
    out of [WeakRvwmoCert.snoc_rd_adm] so that each can be discharged (or
    deferred) on its own.  [floor_ok] is (N-1): it is NOT derived here. *)
Definition src_in_log (c : cand) (base : Z) (ts : list nat)
    (vs : list (bv 8)) : Prop :=
  length vs = length ts ∧
  ∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
     log_byte (cd_img c) (cd_log_end c) t (WeakAxiomatic.acc_addr base j) = Some v.

Definition floor_ok (c : cand) (x : agent) (aq : bool) (base : Z)
    (ts : list nat) : Prop :=
  ∀ (j : nat) t, ts !! j = Some t →
    ¬ writes_in (cd_log_end c) (WeakAxiomatic.acc_addr base j) t
        (cd_floor c x aq (WeakAxiomatic.acc_addr base j)).

Lemma snoc_rd_adm_of c x aq base ts vs :
  src_in_log c base ts vs → floor_ok c x aq base ts →
  snoc_rd_adm c x aq base ts vs.
Proof. intros (Hlen & Hval) Hfl. by split_and!. Qed.

(** (a) THE IN-LOG READ. *)
Theorem cert_read_in_log c x aq base ts vs :
  src_in_log c base ts vs → floor_ok c x aq base ts →
  mstep_ok (cand_last_st c) x (WeakAxiomatic.LLoad aq base ts vs).
Proof. intros H1 H2. by apply snoc_rd_ok, snoc_rd_adm_of. Qed.

(** (b) THE WITNESS READ: the LATEST message of every byte, whose
    admissibility is unconditional ([WeakRvwmoCert]'s answer to (i)) — no
    [floor_ok] is owed, which is why a witness reads the latest. *)
Definition wit_tvs (c : cand) (base : Z) (n : nat) : list (nat * bv 8) :=
  zip (lrd_ts c base n) (lrd_vs c base n).

Lemma wit_tvs_fst c base n : (wit_tvs c base n).*1 = lrd_ts c base n.
Proof. rewrite /wit_tvs fst_zip //. rewrite lrd_length //. Qed.

Lemma wit_tvs_snd c base n : (wit_tvs c base n).*2 = lrd_vs c base n.
Proof. rewrite /wit_tvs snd_zip //. rewrite lrd_length //. Qed.

Lemma wit_tvs_lbl c aq base n :
  WeakAxiomatic.LLoad aq base (wit_tvs c base n).*1 (wit_tvs c base n).*2
  = latest_read_lbl c aq base n.
Proof. by rewrite wit_tvs_fst wit_tvs_snd. Qed.

Lemma wit_tvs_length c base n : length (wit_tvs c base n) = n.
Proof.
  rewrite /wit_tvs length_zip_with lrd_length /lrd_ts length_fmap length_seq.
  lia.
Qed.

Theorem cert_read_witness c x aq base n :
  srvwmo_consistent c → latest_bytes_ok c base n →
  mstep_ok (cand_last_st c) x (latest_read_lbl c aq base n).
Proof. intros Hc Hb. by apply snoc_rd_ok, latest_snoc_rd_adm. Qed.

(** (c) THE WRITE and the FENCE: nothing local to check beyond nonemptiness
    ([WeakRvwmoCert]'s §3). *)
Lemma cert_write_ok c x rl base vs kc :
  vs ≠ [] → mstep_ok (cand_last_st c) x (WeakAxiomatic.LStore rl base vs kc).
Proof. done. Qed.

Lemma cert_fence_ok c x pr pw sr sw :
  mstep_ok (cand_last_st c) x (WeakAxiomatic.LFence pr pw sr sw).
Proof. exact I. Qed.

(** ... and the RMW, whose atomicity forces the LATEST anyway (which is why
    "an RMW witness must read the latest" costs nothing). *)
Lemma cert_rmw_latest_ok c x aq rl base n wvs kc :
  srvwmo_consistent c → latest_bytes_ok c base n →
  wvs ≠ [] → length wvs = n →
  mstep_ok (cand_last_st c) x
    (WeakAxiomatic.LRmw aq rl base (lrd_ts c base n) (lrd_vs c base n) wvs kc).
Proof.
  intros Hc Hb Hne Hlen. split_and!.
  - exact Hne.
  - rewrite /lrd_ts length_fmap length_seq. exact Hlen.
  - by apply snoc_rd_ok, latest_snoc_rd_adm.
  - rewrite cand_last_img cand_last_log.
    intros j t Hj. destruct (lrd_ts_lookup c base n j t Hj) as (Hjn & ->).
    by apply latest_ts_latest, Hb.
Qed.

(* ====================================================================== *)
(** * 5. DELIVERABLE (3): [cert_segment]

    The iteration.  The invariant is stated inline (there is no record: the
    induction is over the [hemit] derivation and every component has to be
    existentially re-produced at each step anyway):

      - the certified hart is at the SAME monad node, parked fence and
        channel as the emission, and its register file agrees off [T];
      - the candidate is [srvwmo_consistent], the supply is in place, and
        the acting agent's program state at [cd_end] is the certified hart;
      - the fabric at [cd_end] is the emission's constant [d0]
        (B1b-1's quiescence, spent here);
      - the candidate's per-agent [w_relp] equals the emission's — the ONLY
        thing the projection equation reads of the wstate
        ([WeakRvwmoConf.pcls_ev_relp]), and what [lbl_reidx_relp] keeps
        true across the re-timestamping.

    THE OUTPUT is a SOLO extension: every appended step is [x]'s, and the
    appended labels are [lbl_reidx] of the row's — verbatim at a store or a
    fence, re-timestamped at a load. *)

Definition lb_rmwfree (lb : lbl) : Prop :=
  match lb with WeakAxiomatic.LRmw _ _ _ _ _ _ _ => False | _ => True end.

(** The candidate's per-agent release-pending bit, one snoc on. *)
Lemma cand_snoc_relp c i lb :
  w_relp (ms_ws (cand_last_st (cand_snoc c (EStep i lb))) i)
  = lpost_relp (w_relp (ms_ws (cand_last_st c) i)) lb.
Proof.
  have H1 : cand_last_st (cand_snoc c (EStep i lb))
          = stt (cand_exec (cand_snoc c (EStep i lb))) (S (cd_end c)).
  { by rewrite {1}/cand_last_st cd_end_snoc. }
  rewrite H1 (cand_next _ (cd_end c) (EStep i lb) (cand_snoc_tr_end c _))
          (cand_snoc_last_st c (EStep i lb)).
  apply mnext_ws_relp.
Qed.

(** THE "OTHER AGENT" TWIN: a snoc of hart [i]'s step does not move hart
    [j]'s release-pending bit.  This is the frame every walk-style chaining
    argument needs — the segment advances one hart, the invariant speaks of
    all of them. *)
Lemma cand_snoc_relp_ne (c : cand) (i j : agent) (lb : WeakAxiomatic.lbl) :
  j ≠ i →
  w_relp (ms_ws (cand_last_st (cand_snoc c (EStep i lb))) j)
  = w_relp (ms_ws (cand_last_st c) j).
Proof.
  intros Hne.
  have H1 : cand_last_st (cand_snoc c (EStep i lb))
          = stt (cand_exec (cand_snoc c (EStep i lb))) (S (cd_end c))
    by rewrite {1}/cand_last_st cd_end_snoc.
  rewrite H1 (cand_next _ (cd_end c) (EStep i lb) (cand_snoc_tr_end c _))
          (cand_snoc_last_st c (EStep i lb)).
  by rewrite (mnext_ws_ne _ _ _ _ Hne).
Qed.

Section segment.
  Context (x : agent) (cpu : CPU) (d0 : dev_state) (T : list wreg).

  (** THE SEGMENT'S LABEL CLASS.  The policy is only ever asked about the
      labels the segment actually carries, so it is parameterized by a
      predicate [Q] the row satisfies — which is what makes the theorem
      instantiable (§6) rather than a statement about all conceivable
      blocks.  [Q] must exclude the fused RMW, whose block is [HEpair] and
      whose certification is the enumerated obligation (O-1). *)
  Context (Q : lbl -> Prop) (HQrmw : forall lb, Q lb -> lb_rmwfree lb).

  (** THE PER-BLOCK POLICY (N-3): at every candidate the iteration reaches,
      the hart's next block can be re-run from the certified register file,
      emitting a label that is [lbl_reidx] of the row's and admissible at
      that candidate.  §4's [cert_block_mirror] / [cert_block_read] /
      [cert_block_witness] with §4.5's [mstep_ok] providers are what
      discharge it; §6 does so concretely. *)
  Context (Hpol : ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
      (rds : list wreg) (wrs : list register)
      (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
      (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
      srvwmo_consistent c0 →
      Q lb →
      w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
      dreg_agree (λ n, n ∉ T) rs1 rs2 →
      cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstep_ok (cand_last_st c0) x lb' ∧
        lbl_reidx lb lb' ∧
        dreg_agree (λ n, n ∉ T) rs1' rs2').

  Theorem cert_segment k0 ws0 rowseg p es pfin :
    hemit (λ _, d0) k0 ws0 rowseg p es pfin →
    Forall Q rowseg →
    ∀ m0 rs10 fn0 ib0, p = PHart cpu m0 rs10 fn0 ib0 →
    ∀ (c : cand) (pst : nat → list pexv6) (dv : nat → dev_state)
      (rs20 : regstate),
      srvwmo_consistent c →
      exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
      pst (cd_end c) !! x = Some (PHart cpu m0 rs20 fn0 ib0) →
      dv (cd_end c) = d0 →
      dreg_agree (λ n, n ∉ T) rs10 rs20 →
      w_relp (ms_ws (cand_last_st c) x) = w_relp ws0 →
      ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
        (tradd : list estep) (m1 : M unit) (rs11 rs21 : regstate)
        (fn1 : ofence) (ib1 : oib32),
        cd_tr c' = cd_tr c ++ tradd ∧
        (∀ s, s ∈ tradd → es_ag s = x) ∧
        Forall2 lbl_reidx_w rowseg ((λ s, es_lb s) <$> tradd) ∧
        srvwmo_consistent c' ∧
        exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
        pst' (cd_end c') !! x = Some (PHart cpu m1 rs21 fn1 ib1) ∧
        dv' (cd_end c') = d0 ∧
        pfin = PHart cpu m1 rs11 fn1 ib1 ∧
        dreg_agree (λ n, n ∉ T) rs11 rs21 ∧
        w_relp (ms_ws (cand_last_st c') x)
        = w_relp (row_ws_aux k0 ws0 rowseg).
  Proof.
    induction 1 as [k ws p
                   |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                   |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                    Har1 Hre Hst1 Har2 Hst2 Hem IH];
      intros Hrf m0 rs10 fn0 ib0 -> c pst dv rs20 Hc Hpo Hp Hdv Hag Hrelp.
    - (* EMPTY SEGMENT *)
      exists c, pst, dv, [], m0, rs10, rs20, fn0, ib0.
      split_and!; [by rewrite app_nil_r| |constructor|exact Hc|exact Hpo
                  |exact Hp|exact Hdv|reflexivity|exact Hag|exact Hrelp].
      intros s Hs. by apply elem_of_nil in Hs.
    - (* ONE BLOCK, then the rest *)
      apply Forall_cons_1 in Hrf as [Hlb Hrf].
      destruct (adm_run_phart true _ _ d0 ls da Har cpu m0 rs10 fn0 ib0 eq_refl)
        as (ma & rsa & fna & iba & Hpa).
      rewrite Hpa in Hst Hre.
      destruct (pstep_ev_phart cpu ma rsa fna iba da l p' d0 Hst)
        as (m1 & rs11 & fn1 & ib1 & Hp').
      rewrite Hp' in Hst.
      rewrite Hpa in Har.
      destruct (cblk_intro cpu d0 ws lb l ls (PHart cpu ma rsa fna iba) da
                  m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 Har Hre Hst)
        as (rds & wrs & Hblk).
      destruct (Hpol c ws lb l rds wrs m0 rs10 rs20 fn0 ib0 m1 rs11 fn1 ib1
                  Hc Hlb Hrelp Hag Hblk)
        as (lb' & l' & rds' & wrs' & rs21 & Hblk2 & Hok & Hri & Hag2).
      destruct (cert_block_snoc c x pst dv cpu d0 lb' l' rds' wrs'
                  m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hc Hpo Hp Hdv
                  (cblk_relp cpu d0 ws (ms_ws (cand_last_st c) x) lb' l'
                     rds' wrs' m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hrelp Hblk2)
                  Hok) as (Hc2 & Hpo2).
      set (c2 := cand_snoc c (EStep x lb')).
      set (pst2 := pst_snoc c pst x (PHart cpu m1 rs21 fn1 ib1)).
      set (dv2 := dv_snoc c dv d0).
      have Hend : cd_end c2 = S (cd_end c) by apply cd_end_snoc.
      have Hp2 : pst2 (cd_end c2) !! x = Some (PHart cpu m1 rs21 fn1 ib1).
      { rewrite Hend /pst2 (pst_snoc_gt c pst x _ (S (cd_end c)) ltac:(lia)).
        apply list_lookup_insert. exact (lookup_lt_Some _ _ _ Hp). }
      have Hdv2 : dv2 (cd_end c2) = d0.
      { rewrite Hend /dv2 (dv_snoc_gt c dv d0 (S (cd_end c)) ltac:(lia)) //. }
      have Hrelp2 : w_relp (ms_ws (cand_last_st c2) x)
                  = w_relp (lbl_post k ws lb).
      { rewrite /c2 cand_snoc_relp Hrelp (lbl_reidx_w_relp _ lb lb' (lbl_reidx_w_of _ _ Hri)).
        by rewrite lbl_post_relp. }
      destruct (IH Hrf m1 rs11 fn1 ib1 Hp' c2 pst2 dv2 rs21
                  Hc2 Hpo2 Hp2 Hdv2 Hag2 Hrelp2)
        as (c' & pst' & dv' & tradd & m2 & rs12 & rs22 & fn2 & ib2 &
            Htr & Hag' & Hf2 & Hc' & Hpo' & Hp'' & Hdv' & Hfin & Hagf & Hrelpf).
      exists c', pst', dv', (EStep x lb' :: tradd), m2, rs12, rs22, fn2, ib2.
      split_and!; [| |constructor; [by left|exact Hf2]|exact Hc'|exact Hpo'|exact Hp''
                   |exact Hdv'|exact Hfin|exact Hagf|exact Hrelpf].
      + rewrite Htr /c2 cand_snoc_tr -app_assoc //.
      + intros s Hs. apply elem_of_cons in Hs as [->|Hs]; [done|by apply Hag'].
    - (* THE FUSED EXCLUSIVE PAIR is excluded by [Forall lb_rmwfree] *)
      exfalso. apply Forall_cons_1 in Hrf as [Hlb _].
      apply HQrmw in Hlb.
      destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                       _ & _ & _ & _ & ->).
      exact Hlb.
  Qed.
End segment.

(** ** 5.1 THE EXIT WRITE, VERBATIM

    The brief's conclusion: at a row position whose label is a plain store —
    the segment's exit write [row !! kz] — the appended step is that store,
    address, data and class included, at the certifying hart. *)
Lemma seg_exit_write (x : agent) (rowseg : list lbl) (tradd : list estep)
    (j : nat) rl base vs kc :
  Forall2 lbl_reidx_w rowseg ((λ s, es_lb s) <$> tradd) →
  (∀ s, s ∈ tradd → es_ag s = x) →
  rowseg !! j = Some (WeakAxiomatic.LStore rl base vs kc) →
  tradd !! j = Some (EStep x (WeakAxiomatic.LStore rl base vs kc)).
Proof.
  intros Hf2 Hag Hj.
  destruct (Forall2_lookup_l _ _ _ _ _ Hf2 Hj) as (y & Hy & Hri).
  rewrite list_lookup_fmap in Hy.
  apply fmap_Some in Hy as (s & Hs & ->).
  have Hlb : es_lb s = WeakAxiomatic.LStore rl base vs kc
    by apply lbl_reidx_w_store.
  have Hx : es_ag s = x by apply Hag, (elem_of_list_lookup_2 _ j).
  rewrite Hs. destruct s as [a b]; simpl in Hlb, Hx. by rewrite Hlb Hx.
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY

    [cert_segment] instantiated on [WeakRvwmoConfWit]'s ONE-BLOCK emission —
    the real [sw &started] store of xv6's [main], at the real machine node —
    with [k0 = 0], the segment reaching the row's only position, and
    [T = []] (the prefix is TRUE, nothing is substituted yet).

    Note what [T = []] does to the taint hypothesis: [rds_ok (λ n, n ∉ [])]
    is VACUOUSLY true, so [cert_block_mirror] applies at every block and the
    policy's whole content is the label's [mstep_ok] — which for a store is
    "the message is nonempty".  That is [pol_store], the concrete policy
    below, and it is the reason the instantiation is a theorem and not
    another hypothesis.  (It is also exactly the shape §4e's segments have
    away from their reads.) *)

(** The label class of the witness segment: a plain store with data. *)
Definition lb_store_ne (lb : lbl) : Prop :=
  match lb with
  | WeakAxiomatic.LStore _ _ vs _ => vs ≠ []
  | _ => False
  end.

Lemma lb_store_ne_rmwfree lb : lb_store_ne lb → lb_rmwfree lb.
Proof. by destruct lb. Qed.

Lemma lb_store_ne_ok (c : cand) (x : agent) lb :
  lb_store_ne lb → mstep_ok (cand_last_st c) x lb.
Proof. by destruct lb. Qed.

(** THE POLICY, discharged: at an empty taint set every block mirrors, and
    a store is admissible at any candidate. *)
Lemma pol_store (x : agent) (cpu : CPU) (d0 : dev_state) :
  ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    lb_store_ne lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ n, n ∉ []) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2',
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx lb lb' ∧
      dreg_agree (λ n, n ∉ []) rs1' rs2'.
Proof.
  intros c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' Hc Hlb Hrelp Hag Hblk.
  destruct (cert_block_mirror (λ n, n ∉ []) cpu d0 ws lb l rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk
              (λ n _, not_elem_of_nil n) Hag) as (rs2' & Hblk2 & Hag2).
  exists lb, l, rds, wrs, rs2'.
  split_and!; [exact Hblk2|by apply lb_store_ne_ok|apply lbl_reidx_refl
              |exact Hag2].
Qed.

Section nonvacuity.
  Context (cpu : CPU) (rs : regstate) (ib : oib32) (d0 : dev_state).

  Notation img0 := (λ _ : Z, @None (bv 8)).

  Lemma nv_hemit :
    hemit (λ _, d0) 0%nat ws_init ev_row (ev_p0 cpu rs ib)
      (em_items (ev_em cpu rs ib)) (em_fin (ev_em cpu rs ib)).
  Proof. exact (ev_hart_conf 0%nat cpu rs ib d0). Qed.

  Lemma nv_row_class : Forall lb_store_ne ev_row.
  Proof.
    apply Forall_singleton. rewrite /lb_store_ne.
    have Hl : length (wbytes 4 WeakLock.lock_one) = 4%nat
      by apply (wbytes_length 4).
    intros H. by rewrite H /= in Hl.
  Qed.

  (** THE INSTANTIATION. *)
  Theorem cert_segment_witness :
    ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
      (tradd : list estep),
      cd_tr c' = tradd ∧
      (∀ s, s ∈ tradd → es_ag s = 0%nat) ∧
      Forall2 lbl_reidx_w ev_row ((λ s, es_lb s) <$> tradd) ∧
      srvwmo_consistent c' ∧
      exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
      tradd !! 0%nat
      = Some (EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                             (wbytes 4 WeakLock.lock_one) WCplain)).
  Proof.
    destruct (cert_segment 0%nat cpu d0 [] lb_store_ne lb_store_ne_rmwfree
                (pol_store 0%nat cpu d0)
                0%nat ws_init ev_row (ev_p0 cpu rs ib) _ _
                nv_hemit nv_row_class
                ev_x2.2 rs None ib eq_refl
                (sm_c img0) (sm_pst cpu rs ib) (sm_dv d0) rs
                (sm_consistent img0) (sm_prog0 img0 cpu rs ib d0)
                eq_refl eq_refl (dreg_agree_refl _ _)
                ltac:(by rewrite (sm_ws img0)))
      as (c' & pst' & dv' & tradd & m1 & rs11 & rs21 & fn1 & ib1 &
          Htr & Hag & Hf2 & Hc' & Hpo' & _ & _ & _ & _ & _).
    exists c', pst', dv', tradd. split_and!;
      [by rewrite Htr|exact Hag|exact Hf2|exact Hc'|exact Hpo'|].
    by apply (seg_exit_write 0%nat ev_row tradd 0%nat).
  Qed.
End nonvacuity.

(** THE POINT, with the objects hidden: the segment certification is
    inhabited at a REAL, nonempty emission, and it delivers the row's own
    write at the certifying hart. *)
Corollary cert_segment_nonvacuous :
  ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
    (tradd : list estep),
    tradd ≠ [] ∧ cd_tr c' = tradd ∧
    (∀ s, s ∈ tradd → es_ag s = 0%nat) ∧
    srvwmo_consistent c' ∧
    exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
    tradd !! 0%nat
    = Some (EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                           (wbytes 4 WeakLock.lock_one) WCplain)).
Proof.
  destruct (cert_segment_witness 0%fin ev_rs0 ib_none dev0_state)
    as (c' & pst' & dv' & tradd & Htr & Hag & _ & Hc' & Hpo' & Hlk).
  exists c', pst', dv', tradd. split_and!;
    [|exact Htr|exact Hag|exact Hc'|exact Hpo'|exact Hlk].
  intros ->. by rewrite lookup_nil in Hlk.
Qed.

(* ====================================================================== *)
(** * 7. WHAT SLICE 3b LEAVES OPEN — the enumerated obligations

    Nothing below is [Admitted]: these are statements this slice does NOT
    make, listed so that B2e-3c knows exactly what it inherits.

    (O-1) THE FUSED EXCLUSIVE PAIR.  [cert_segment]'s [HEpair] case is
          discharged by REFUTATION ([HQrmw]: the segment's label class
          excludes [WeakAxiomatic.LRmw]), so a segment containing an
          [amoswap] acquire is out of its reach today.  Everything the pair
          needs already exists — [WeakRvwmoCert.exec_prog_ok'_snoc_pair] for
          the supply, [WeakRvwmoCert.snoc_rmw_latest_consistent] +
          [cert_rmw_latest_ok] (§4.5) for the consistency, and
          [WeakEvInst.pstep_ev_ts_exload] for the retiming — so the work is
          a [cblkp] twin of [cblk] (an [adm_run true], the exclusive read,
          an [LInstr]-free [adm_run false], the conditional write), a
          [cert_block_pair_mirror] off [hlbl_realizes_pair_rs] (§1, already
          proved here) and a second policy clause.  Priced small; deferred
          only because it doubles the block vocabulary.

    (O-2) RE-CONVERGENCE AFTER A WITNESS.  [cert_step_witness] /
          [cert_block_witness] deliver the substituted read and
          [cert_step_taint] the register-file consequence, but from there
          the two runs are at DIFFERENT monad nodes, and
          [cert_segment]'s invariant ("the same node") does not hold across
          a witness.  The two runs re-converge at the next instruction
          BOUNDARY — [WeakEvInst.pnode_step]'s [Interface.Ret] arm resumes
          both at [riscv_step tick] — but that the certified remainder
          REACHES its boundary is a progress fact about the verified
          program, i.e. the EWPs' content (§4e: "a solo run is a genuine pf
          run of the verified program … 'the substituted value does not
          derail the run before [z]' is the EWPs' content, not a new
          obligation").  So the composition is: [cert_block_witness] at the
          witness position, then [cert_segment] at the GROWN taint set
          [rd :: T] from the re-convergence point on.

    (O-3) [floor_ok] (N-1) and the [src_in_log] bookkeeping (N-2), as
          §0 describes: the T2-1c-style derivation from G's own consistency,
          and the G-write-index ↦ log-message correspondence.

    (O-4) THE POLICY (N-3) is a hypothesis of [cert_segment], not a
          construction.  §4's [cert_block_*] discharge it per position and
          §6 discharges it outright for a store-only segment; the general
          discharge is the same case split B2e-3c makes anyway (write /
          fence / in-log read / witness read). *)

(* ====================================================================== *)
(** * 8. AUDIT *)

Print Assumptions cert_step_mirror.
Print Assumptions cert_step_reindex.
Print Assumptions cert_step_witness.
Print Assumptions cert_step_taint.
Print Assumptions instr_rds_of_channel.
Print Assumptions cert_block_mirror.
Print Assumptions cert_block_read.
Print Assumptions cert_block_witness.
Print Assumptions cert_block_snoc.
Print Assumptions cert_read_in_log.
Print Assumptions cert_read_witness.
Print Assumptions cert_rmw_latest_ok.
Print Assumptions cert_segment.
Print Assumptions cblk_vfree_of_retime.
Print Assumptions seg_exit_write.
Print Assumptions cert_segment_nonvacuous.
