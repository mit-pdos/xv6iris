(** * WeakRvwmoConf.v — THE ROUTE-B CONFORMANCE VOCABULARY (stage B0b-1)

    Design: [claude-notes/design/weak-memory-route-b.md] §2/§4's B0b entry.

    This file bridges the two worlds route B's capstone clause has to speak
    about at once:

      - the GRAPH world — [WeakRvwmoGraph]'s [gexec]/[gdexec], whose per-hart
        ROWS are lists of FUSED axiomatic labels ([WeakAxiomatic.lbl]), and
        [WeakRvwmoNorm]'s renaming [lbl_ren]/[rows_rel];
      - the INSTANCE world — [WeakEvInst.pstep_ev]/[pcls_ev] over
        [WeakEvPf.pexv6], and T1-D's supply vocabulary in [WeakAxRealize]
        ([lb_nobarex]/[lat_free]/[lb_rfoldfree]/[lb_admin]/[adm_star]).

    It is therefore the ONE Rvwmo leaf that imports the instance band.  It is
    still a LEAF: nothing imports it.

    ** WHAT IS HERE

    (1) [row_deps] — the SYNTACTIC REGISTER-DATAFLOW relation of an emitted
        instance label sequence (RVWMO rules 9/10/11, store halves): the
        (source-position, target-position) pairs a hart's own labels induce.
        Positions are ROW positions, i.e. positions in the graph row.

    (2) [hart_conf] — PER-HART ROW EMITTABILITY: the hart's program emits the
        row in po order, one [adm_run]-then-realizing-step block per row
        event, with the exclusive PAIR as the second block shape (mirroring
        [WeakAxRealize.exec_prog_ok']'s per-event disjunction).

    (3) the two STABILITY lemmas — [hart_conf_ren] (the emission survives the
        normalization's ts renaming) and [hart_conf_prefix] (a prefix of an
        emission is an emission).

    (4) [gdexec_conf] — the bundle: every hart's row is emittable and the
        emission's syntactic deps are IN the graph's dep set; plus
        [gdexec_conf_ren], the transport along [rows_rel] that lets B3 apply
        conformance to [normalize]'s output.

    ** FOUR RECORDED SCOPE DECISIONS

    (S-a) TRANSLATION-ORDER EDGES (W-TV, RVWMO rule 13) ARE NOT IN
      [row_deps].  *** REVERSED at [dedges] (route-b §4d.1 F5): they are now
      emitted, from [ds_ld]; the paragraph below records the original
      reasoning. ***  The walker's reads are [asrc = []] loads and their edge
      into the translated store rides the MACHINE's [w_vcap], not the
      syntactic dataflow this fold computes.  Whether the GRAPH-level
      conformance clause needs them as [gd_deps] members is B2e's question
      (the walker kills there consume [w_vcap] at the realized prefix, not
      graph edges).


    (S-a') F5' — TRANSITIVE PROVENANCE THROUGH LOAD ADDRESSES (2026-08-22).
      D-8 (a plain load's LABEL carries no [asrc], because the node cannot
      tell a data read from the walker's PTE read) is UNCHANGED and stays
      unchanged: [read_ok_d]'s vaddr floor is still untripped.  What changed
      is the instance's REGISTER-PROVENANCE annotation: a load's result write
      is now [LRegW rd (DLdRes :: the load's address sources)]
      ([WeakDeps.deps_rd]'s [ORload] arm, via the same [deps_addr] a store's
      [asrc] comes from).  [dstep] needed NOTHING: the [LRegW] arm already
      composes provenance, so [dprov rd] now names the address chain's reads
      as well and every later store inherits them through [dedges].  RVWMO
      rules 9 (into the load) and 10 (out of it) composed — so the dep set
      only GROWS, and it grows within RVWMO.  See [row_deps_addr_chain] and
      its [_before] twin in §9.  Why it is needed: §4d.2(2) certifies a
      cycle-SCC write [z] by a solo run and claims [z]'s label is [G]'s
      because every source of [z] is in [gd_deps] hence gmo-below [z] — with
      no address sources on loads, [r1 ->addr r2 ->data z] left [r1]
      unpinned, so a substituted witness value could change [r2]'s ADDRESS
      and hence [z]'s data.  (An AMO needs no patch: its address sources are
      on the [LRmw] label already, so such a chain is pinned by two dep edges
      and gmo's transitivity.)

    (S-b) AN EMISSION ITEM CARRIES ITS ROW POSITION EXPLICITLY.  [row_deps]
      folds over [list eitem] — labels TAGGED with the row position they
      realize ([None] for an administrative label) — not over a bare
      [list wlabel] with an implicit counter.  It has to: the exclusive PAIR
      puts TWO projecting labels ([LExLoad] and [LExStore], both with a
      [proj_lbl] image) at ONE row position (the fused [LRmw]), while a
      DANGLING [LExLoad] (the walker's abandoned reservation, an [amocas]
      miss — both real xv6 shapes) is a row position of its own.  No function
      of the label alone can tell those apart, so the counter is data.
      [em_labels] recovers the bare sequence for consumers that want it.

    (S-c) [row_deps] EMITS ONLY STRICTLY-INCREASING EDGES.  A fused [LRmw]'s
      write half genuinely depends on its own read half ([LRegW rd [DLdRes]]
      between the two halves of an AMO), but that is an edge (k, k) — INSIDE
      one graph event, where [gdeps_wf] cannot put it (it demands
      [rw.1.2 < rw.2.2]) and where the fused semantics handles the ordering
      anyway.  The fold filters those out; [row_deps_lt] is then by
      construction.

    (S-d) THE FABRIC IS A PER-ROW-POSITION PARAMETER [dv : nat → dev_state].
      [dv k] is the fabric the k-th row event's administrative run starts at
      and [dv (S k)] the one its realizing step ends at — exactly
      [exec_prog_ok']'s [dv] shape, re-indexed from the GLOBAL trace position
      to the HART's own row position.  B0b-2 instantiates it from the global
      witness by composing with "the trace position of hart [i]'s k-th
      event".  Indexing this way is what makes [hart_conf_prefix] carry the
      SAME [dv] (a prefix of the row uses a prefix of the indices), so no
      fabric-truncation operator is needed.

    ** THE CLASS EQUATION IS ts-INDEPENDENT, and that is a theorem here

    The per-hart projection equation is read at [row_ws row k] — a
    REPRESENTATIVE wstate obtained by folding the run-level post functions
    over the row's OWN labels.  That is not the machine's wstate, and it need
    not be: [pcls_ev] reads the wstate only through [w_relp]
    ([pcls_ev_relp], a corollary of [WeakEvInst.pcls_ev_erasable]), and
    [w_relp] of the fold depends only on the labels' fence bits and on
    whether each write event writes a byte — never on a timestamp
    ([row_ws_relp], [lpost_relp_ren]).  That is what makes [hart_conf_ren]
    go through, and it is the design finding the slice was told to check
    for: the class function does NOT read more than [w_relp]. *)
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
Require Import WeakRvwmoNorm.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
(* AFTER the axiomatic band on purpose: [WeakPromise] and [WeakAxiomatic]
   both export [LLoad]/[LStore]/[LFence]/[LRmw], and this file matches on
   WLABELS far more often than on graph labels, so the WLABEL constructors
   are the unqualified ones here and the graph's are written
   [WeakAxiomatic.LLoad] &c.  (This is the opposite convention to
   [WeakAxRealize.v], whose header records the same collision.) *)
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE CLASS FUNCTION READS ONLY [w_relp]

    [WeakEvInst.pcls_ev_erasable] says it, entangled with the erasure's
    label blanking.  This is the same fact with the label held fixed — the
    form every equation below consumes. *)

Lemma pcls_ev_relp p l we wi :
  w_relp we = w_relp wi → pcls_ev p l we = pcls_ev p l wi.
Proof.
  intros H. destruct l; unfold pcls_ev; try reflexivity;
    destruct p as [cpu m rs fn ib|dp];
    solve [ apply (pnode_wclass_relp m we wi H)
          | unfold ddev_class, wm_class_of; rewrite H; reflexivity ].
Qed.

(* ====================================================================== *)
(** * 2. RENAMING A WLABEL'S TIMESTAMP COLUMNS

    [WeakRvwmoNorm.lbl_ren] renames a GRAPH label's [ts] entries.  Its
    instance-side twin renames the [ts] column of a wlabel's [tvs] payload —
    the read halves of [LLoad], [LRmw] and [LExLoad] — and is the IDENTITY
    everywhere else, in particular on every administrative label and on both
    write labels (which carry no timestamp at all). *)

Definition tv_ren (π : nat → nat) (tv : nat * bv 8) : nat * bv 8 :=
  (π tv.1, tv.2).

Definition wlbl_ren (π : nat → nat) (l : wlabel) : wlabel :=
  match l with
  | LLoad aq lat base tvs asrc => LLoad aq lat base (tv_ren π <$> tvs) asrc
  | LRmw aq rl base tvs data asrc vsrc =>
      LRmw aq rl base (tv_ren π <$> tvs) data asrc vsrc
  | LExLoad aq base tvs asrc => LExLoad aq base (tv_ren π <$> tvs) asrc
  | LSilent | LStore _ _ _ _ _ | LFence _ _ _ _ | LDev
  | LRegW _ _ | LCtrl _ | LInstr | LExStore _ _ _ _ _ => l
  end.

Lemma tv_ren_fst π (tvs : list (nat * bv 8)) :
  (tv_ren π <$> tvs).*1 = π <$> tvs.*1.
Proof.
  rewrite -!list_fmap_compose. apply list_fmap_ext. by intros i tv _.
Qed.

Lemma tv_ren_snd π (tvs : list (nat * bv 8)) : (tv_ren π <$> tvs).*2 = tvs.*2.
Proof.
  rewrite -list_fmap_compose. trans (fmap (M:=list) snd tvs); [|done].
  apply list_fmap_ext. by intros i tv _.
Qed.

Lemma tv_ren_length π (tvs : list (nat * bv 8)) :
  length (tv_ren π <$> tvs) = length tvs.
Proof. apply length_fmap. Qed.

(** The renaming is invisible to the three T1-D label gates ... *)
Lemma wlbl_ren_nobarex π l : lb_nobarex (wlbl_ren π l) ↔ lb_nobarex l.
Proof. by destruct l. Qed.
Lemma wlbl_ren_lat_free π l : lat_free (wlbl_ren π l) ↔ lat_free l.
Proof. by destruct l. Qed.
Lemma wlbl_ren_rfoldfree π l : lb_rfoldfree (wlbl_ren π l) ↔ lb_rfoldfree l.
Proof. by destruct l. Qed.

(** ... and to the administrative alphabet, on which it is the identity. *)
Lemma wlbl_ren_admin π instr l : lb_admin instr l → wlbl_ren π l = l.
Proof. by destruct l. Qed.

(** THE PROJECTION SQUARE: renaming a wlabel renames its axiomatic image. *)
Lemma proj_lbl_wren k π l :
  proj_lbl k (wlbl_ren π l) = lbl_ren π <$> proj_lbl k l.
Proof.
  destruct l; simpl; try done; by rewrite tv_ren_fst tv_ren_snd.
Qed.

(** ... and it does not move the class the machine stamps (the class reads
    the label's CONSTRUCTOR and the wstate's [w_relp], neither of which the
    renaming touches). *)
Lemma pcls_ev_wren p π l we wi :
  w_relp we = w_relp wi → pcls_ev p (wlbl_ren π l) we = pcls_ev p l wi.
Proof.
  intros H. transitivity (pcls_ev p l we); [|by apply pcls_ev_relp].
  by destruct l.
Qed.

(** THE TIMESTAMP-OBLIVIOUSNESS OF THE PROGRAM, at the renaming.

    Every arm is one of [WeakEvInst]'s existing [ts_oblivious] exports:
    [pstep_ev_ts_load] (whose [asrc = []]/[lat = false] shape is exactly what
    the two gates supply), [pstep_ev_ts_exload] (at an ARBITRARY [asrc]) and
    [pstep_ev_ts_rmw].  Every other label is renamed to itself.  NO NEW ARM
    VARIANT IS NEEDED. *)
Lemma pstep_ev_wren π p d l p' d' :
  lat_free l → lb_rfoldfree l →
  pstep_ev p d l p' d' → pstep_ev p d (wlbl_ren π l) p' d'.
Proof.
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                 |aq rl base tvs data asrc vsrc|pr pw sr sw| |rd srcs|srcs| |
                 aq base tvs asrc|rl base data asrc vsrc];
    simpl; try (by intros _ _ H).
  - (* LLoad: [lat_free] gives [lat = false], [lb_rfoldfree] gives [asrc = []] *)
    intros -> -> H. by eapply pstep_ev_ts_load; [exact H|apply tv_ren_snd].
  - (* LRmw: no instance arm emits it, but the export is there *)
    intros _ _ H. by eapply pstep_ev_ts_rmw; [exact H|apply tv_ren_snd].
  - (* LExLoad *)
    intros _ _ H. by eapply pstep_ev_ts_exload; [exact H|apply tv_ren_snd].
Qed.

(* ====================================================================== *)
(** * 3. THE ROW'S REPRESENTATIVE WSTATE FOLD

    [row_ws row k] folds [mstep]'s own per-arm post functions over the row's
    first [k] labels, from [ws_init].  It is NOT the machine's wstate (the
    machine's timestamps come from the GLOBAL log length, which a per-hart
    statement has no access to); it is the wstate at which the per-hart
    projection equation is READ, and the only thing that equation needs from
    it is [w_relp] — see [row_ws_relp] and [pcls_ev_relp]. *)

Definition lbl_post (t : nat) (ws : wstate) (l : lbl) : wstate :=
  match l with
  | WeakAxiomatic.LLoad aq base ts _ => load_post_run ws aq base ts
  | WeakAxiomatic.LStore rl base vs _ =>
      store_post_run ws rl base (length vs) (S t)
  | WeakAxiomatic.LFence pr pw sr sw => fence_post ws pr pw sr sw
  | WeakAxiomatic.LRmw aq rl base ts _ wvs _ =>
      store_post_run (load_post_run ws aq base ts) rl base (length wvs) (S t)
  end.

Fixpoint row_ws_aux (t : nat) (ws : wstate) (r : list lbl) : wstate :=
  match r with
  | [] => ws
  | l :: r' => row_ws_aux (S t) (lbl_post t ws l) r'
  end.

Definition row_ws (row : list lbl) (k : nat) : wstate :=
  row_ws_aux 0%nat ws_init (take k row).

(** ** 3.1 [w_relp] of the fold, computed

    A load leaves it alone, a fence sets it iff the fence is [pw ∧ sw], a
    write CLEARS it as soon as it writes a byte (and a zero-byte write —
    which [gwf] excludes — leaves it alone).  NO TIMESTAMP APPEARS. *)

Definition lpost_relp (b : bool) (l : lbl) : bool :=
  match l with
  | WeakAxiomatic.LLoad _ _ _ _ => b
  | WeakAxiomatic.LStore _ _ vs _ => match vs with [] => b | _ => false end
  | WeakAxiomatic.LFence _ pw _ sw => if (pw && sw)%bool then true else b
  | WeakAxiomatic.LRmw _ _ _ _ _ wvs _ =>
      match wvs with [] => b | _ => false end
  end.

Lemma load_post_run_relp ws aq base ts :
  w_relp (load_post_run ws aq base ts) = w_relp ws.
Proof. rewrite -load_post_run_d_0. apply load_post_run_d_relp. Qed.

Lemma store_post_run_relp ws rl base n t :
  w_relp (store_post_run ws rl base n t)
  = match n with 0%nat => w_relp ws | S _ => false end.
Proof.
  destruct n as [|m]; [done|].
  rewrite -store_post_run_d_0. by apply store_post_run_d_relp; lia.
Qed.

Lemma lbl_post_relp t ws l : w_relp (lbl_post t ws l) = lpost_relp (w_relp ws) l.
Proof.
  destruct l as [aq base ts vs|rl base vs k|pr pw sr sw|aq rl base ts rvs wvs k];
    simpl.
  - apply load_post_run_relp.
  - rewrite store_post_run_relp. by destruct vs.
  - by destruct pw, sw.
  - rewrite store_post_run_relp load_post_run_relp. by destruct wvs.
Qed.

Lemma row_ws_aux_relp t ws r :
  w_relp (row_ws_aux t ws r) = foldl lpost_relp (w_relp ws) r.
Proof.
  revert t ws. induction r as [|l r IH]; intros t ws; [done|].
  by rewrite /= IH lbl_post_relp.
Qed.

(** THE CHARACTERIZATION: [row_ws]'s release-pending bit is a fold of the
    row's own labels and NOTHING ELSE. *)
Lemma row_ws_relp row k :
  w_relp (row_ws row k) = foldl lpost_relp false (take k row).
Proof. rewrite /row_ws row_ws_aux_relp //. Qed.

(** ** 3.2 The renaming does not move it *)

Lemma lpost_relp_ren π b l : lpost_relp b (lbl_ren π l) = lpost_relp b l.
Proof. by destruct l. Qed.

Lemma lbl_post_relp_ren π t ws ws' l :
  w_relp ws' = w_relp ws →
  w_relp (lbl_post t ws' (lbl_ren π l)) = w_relp (lbl_post t ws l).
Proof. intros H. by rewrite !lbl_post_relp H lpost_relp_ren. Qed.

Lemma row_ws_aux_relp_ren π t ws ws' r :
  w_relp ws' = w_relp ws →
  w_relp (row_ws_aux t ws' (lbl_ren π <$> r)) = w_relp (row_ws_aux t ws r).
Proof.
  revert t ws ws'. induction r as [|l r IH]; intros t ws ws' H; [done|].
  rewrite fmap_cons /row_ws_aux -/row_ws_aux.
  apply IH. by apply lbl_post_relp_ren.
Qed.

(** THE ts-GENERICITY OF THE PROJECTION EQUATION'S WSTATE — the lemma the
    slice brief names [row_ws_relp_ren]. *)
Lemma row_ws_relp_ren π row k :
  w_relp (row_ws (lbl_ren π <$> row) k) = w_relp (row_ws row k).
Proof.
  rewrite /row_ws -fmap_take. by apply row_ws_aux_relp_ren.
Qed.

(* ====================================================================== *)
(** * 4. THE PER-HART REALIZATION RELATIONS

    [WeakAxRealize.lbl_realizes] / [lbl_realizes_pair] with the AXIOMATIC
    state [σ] replaced by the acting agent's wstate alone — the only part of
    [σ] either of them reads is [ms_ws σ i].  [hlbl_realizes_ax] /
    [hlbl_realizes_pair_ax] are the (definitional) seam back to T1-D's
    vocabulary, which is what B0b-2 consumes. *)

Definition hlbl_realizes (p : pexv6) (ws : wstate) (lb : lbl) (l : wlabel)
    : Prop :=
  lb_nobarex l ∧ lat_free l ∧ lb_rfoldfree l ∧
  proj_lbl (pcls_ev p l ws) l = Some lb.

Definition hlbl_realizes_pair (p pm : pexv6) (ws : wstate) (lb : lbl)
    (l1 l2 : wlabel) : Prop :=
  ∃ aq rl base tvs data asrc1 asrc2 vsrc2,
    l1 = LExLoad aq base tvs asrc1 ∧
    l2 = LExStore rl base data asrc2 vsrc2 ∧
    data ≠ [] ∧ length tvs = length data ∧
    lb = WeakAxiomatic.LRmw aq rl base tvs.*1 tvs.*2 data
           (pcls_ev pm l2 (load_post_run ws aq base tvs.*1)).

Lemma hlbl_realizes_ax p σ i lb l :
  hlbl_realizes p (ms_ws σ i) lb l ↔ lbl_realizes pcls_ev p σ i lb l.
Proof. done. Qed.

Lemma hlbl_realizes_pair_ax p pm σ i lb l1 l2 :
  hlbl_realizes_pair p pm (ms_ws σ i) lb l1 l2
  ↔ lbl_realizes_pair pcls_ev p pm σ i lb l1 l2.
Proof. done. Qed.

(** The realizing wlabel's shape is pinned by its axiomatic image. *)
Lemma hlbl_realizes_notadm p ws lb l instr :
  hlbl_realizes p ws lb l → ¬ lb_admin instr l.
Proof.
  intros (_ & _ & _ & Hpr) Ha. by rewrite (lb_admin_proj _ instr l Ha) in Hpr.
Qed.

(** ** 4.1 ts-genericity of both *)

Lemma hlbl_realizes_ren π p ws ws' lb l :
  w_relp ws' = w_relp ws →
  hlbl_realizes p ws lb l →
  hlbl_realizes p ws' (lbl_ren π lb) (wlbl_ren π l).
Proof.
  intros Hr (Hnb & Hlat & Hrf & Hpr). split_and!.
  - by apply wlbl_ren_nobarex.
  - by apply wlbl_ren_lat_free.
  - by apply wlbl_ren_rfoldfree.
  - rewrite (pcls_ev_wren p π l ws' ws Hr) proj_lbl_wren Hpr //.
Qed.

Lemma hlbl_realizes_pair_ren π p pm ws ws' lb l1 l2 :
  w_relp ws' = w_relp ws →
  hlbl_realizes_pair p pm ws lb l1 l2 →
  hlbl_realizes_pair p pm ws' (lbl_ren π lb) (wlbl_ren π l1) (wlbl_ren π l2).
Proof.
  intros Hr (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
             -> & -> & Hne & Hlen & ->).
  exists aq, rl, base, (tv_ren π <$> tvs), data, asrc1, asrc2, vsrc2.
  split_and!; [done|done|done|by rewrite tv_ren_length|].
  cbn [lbl_ren wlbl_ren]. rewrite tv_ren_fst tv_ren_snd. f_equal.
  apply pcls_ev_relp. by rewrite !load_post_run_relp Hr.
Qed.

(* ====================================================================== *)
(** * 5. THE LABEL-CARRYING ADMINISTRATIVE RUN

    [WeakAxRealize.adm_star] is an [rtc], so its labels are existentially
    buried; [row_deps] needs them (the [LRegW]/[LCtrl]/[LInstr] dataflow
    lives exactly there).  [adm_run] is the same run with its label list
    exposed, and [adm_run_star] is the forgetful map back. *)

Inductive adm_run (instr : bool)
    : pexv6 → dev_state → list wlabel → pexv6 → dev_state → Prop :=
| ARnil p d : adm_run instr p d [] p d
| ARcons p d l p1 d1 ls p' d' :
    lb_admin instr l → pstep_ev p d l p1 d1 →
    adm_run instr p1 d1 ls p' d' →
    adm_run instr p d (l :: ls) p' d'.

Lemma adm_run_star instr p d ls p' d' :
  adm_run instr p d ls p' d' → adm_star pstep_ev instr p d p' d'.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH];
    [apply adm_star_refl|by eapply adm_star_l].
Qed.

Lemma adm_run_admin instr p d ls p' d' :
  adm_run instr p d ls p' d' → ∀ l, l ∈ ls → lb_admin instr l.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH]; intros l0 Hl0.
  - by apply elem_of_nil in Hl0.
  - apply elem_of_cons in Hl0 as [->|Hl0]; [done|by apply IH].
Qed.

Lemma adm_run_mono p d ls p' d' :
  adm_run false p d ls p' d' → ∀ instr, adm_run instr p d ls p' d'.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH]; intros instr.
  - apply ARnil.
  - eapply ARcons; [by apply lb_admin_mono|exact Hs|apply IH].
Qed.

Lemma adm_run_ren π instr p d ls p' d' :
  adm_run instr p d ls p' d' →
  adm_run instr p d (wlbl_ren π <$> ls) p' d'.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH]; [apply ARnil|].
  rewrite /= (wlbl_ren_admin π instr l Ha). by eapply ARcons.
Qed.

(* ====================================================================== *)
(** * 6. EMISSION ITEMS AND [row_deps]

    An ITEM is one instance label together with the ROW POSITION it realizes
    ([None] for an administrative label) — see scope note (S-b). *)

Definition eitem : Type := (wlabel * option nat)%type.

Definition eadm (ls : list wlabel) : list eitem :=
  (λ l, (l, @None nat)) <$> ls.

Definition eitem_ren (π : nat → nat) (it : eitem) : eitem :=
  (wlbl_ren π it.1, it.2).

Lemma eitem_ren_eadm π ls : eitem_ren π <$> eadm ls = eadm (wlbl_ren π <$> ls).
Proof.
  rewrite /eadm -!list_fmap_compose. apply list_fmap_ext. by intros i l _.
Qed.

(** The shape one emission BLOCK has: an administrative stretch, then one
    tagged label.  (Stated as its own equation because [rewrite !fmap_app]
    does not reach the nested block of the exclusive pair.) *)
Lemma eitem_ren_block π ls l k es :
  eitem_ren π <$> (eadm ls ++ (l, Some k) :: es)
  = eadm (wlbl_ren π <$> ls) ++ (wlbl_ren π l, Some k) :: (eitem_ren π <$> es).
Proof. by rewrite fmap_app fmap_cons eitem_ren_eadm. Qed.

(** The label's memory role, at the INSTANCE alphabet.  Both split labels
    count ([LExLoad] reads, [LExStore] writes) — this is [proj_lbl]'s own
    classification of them. *)
Definition elb_is_r (l : wlabel) : bool :=
  match l with
  | LLoad _ _ _ _ _ | LExLoad _ _ _ _ | LRmw _ _ _ _ _ _ _ => true
  | _ => false
  end.

Definition elb_is_w (l : wlabel) : bool :=
  match l with
  | LStore _ _ _ _ _ | LExStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ => true
  | _ => false
  end.

Lemma elb_is_r_ren π l : elb_is_r (wlbl_ren π l) = elb_is_r l.
Proof. by destruct l. Qed.
Lemma elb_is_w_ren π l : elb_is_w (wlbl_ren π l) = elb_is_w l.
Proof. by destruct l. Qed.

(** ** 6.1 The dataflow state

    [ds_prov r] — the row positions of the reads register [r]'s current value
    derives from ([DReg]'s denotation); [ds_ld] — the CURRENT INSTRUCTION's
    load positions ([DLdRes]'s denotation, reset at [LInstr]); [ds_ctl] — the
    accumulated control positions (rule 11, never reset: it taints every
    po-later store).

    Position lists, not [gset]s: [row_deps] is consumed through [∈], and
    duplicates are harmless. *)

Record dstate := DSt {
  ds_prov : gmap wreg (list nat);
  ds_ld   : list nat;
  ds_ctl  : list nat;
}.

Definition ds_init : dstate := DSt ∅ [] [].

Definition dprov (s : dstate) (r : wreg) : list nat :=
  default [] (ds_prov s !! r).

Definition dsrc_pos (s : dstate) (x : dsrc) : list nat :=
  match x with DReg r => dprov s r | DLdRes => ds_ld s end.

Definition dsrcs_pos (s : dstate) (xs : list dsrc) : list nat :=
  mjoin (dsrc_pos s <$> xs).

(** THE EDGES A WRITE AT ROW POSITION [k] EMITS: address operands (rule 9),
    data operands (rule 10), the control set (rule 11) and — see below — the
    current instruction's earlier loads (rule 13), each source position
    paired with [k], minus the self-edges of scope note (S-c).

    SCOPE DECISION (S-a) IS REVERSED HERE (route-b §4d.1 F5): the W-TV
    translation-order edges ARE in [row_deps] now, computed from [ds_ld s] —
    the instruction's own earlier reads, i.e. its translation reads, which
    precede the translated access.  Value-independent: [ds_ld] holds row
    POSITIONS, so the arm is as ts-blind and as renaming-stable as the rest. *)
Definition dedges (s : dstate) (k : nat) (asrc vsrc : list dsrc)
    : list (nat * nat) :=
  (λ j, (j, k)) <$>
    filter (λ j, (j < k)%nat)
      (dsrcs_pos s asrc ++ dsrcs_pos s vsrc ++ ds_ctl s ++ ds_ld s).

Definition dstep (s : dstate) (it : eitem) : dstate * list (nat * nat) :=
  match it.1 with
  | LSilent | LDev | LFence _ _ _ _ => (s, [])
  | LInstr => (DSt (ds_prov s) [] (ds_ctl s), [])
  | LRegW rd srcs =>
      (DSt (<[rd := dsrcs_pos s srcs]> (ds_prov s)) (ds_ld s) (ds_ctl s), [])
  | LCtrl srcs => (DSt (ds_prov s) (ds_ld s) (ds_ctl s ++ dsrcs_pos s srcs), [])
  | LLoad _ _ _ _ _ | LExLoad _ _ _ _ =>
      match it.2 with
      | Some k => (DSt (ds_prov s) (k :: ds_ld s) (ds_ctl s), [])
      | None => (s, [])
      end
  | LStore _ _ _ asrc vsrc | LExStore _ _ _ asrc vsrc =>
      match it.2 with
      | Some k => (s, dedges s k asrc vsrc)
      | None => (s, [])
      end
  | LRmw _ _ _ _ _ asrc vsrc =>
      match it.2 with
      | Some k =>
          (DSt (ds_prov s) (k :: ds_ld s) (ds_ctl s), dedges s k asrc vsrc)
      | None => (s, [])
      end
  end.

Fixpoint row_deps_aux (s : dstate) (es : list eitem) : list (nat * nat) :=
  match es with
  | [] => []
  | it :: es' => (dstep s it).2 ++ row_deps_aux (dstep s it).1 es'
  end.

(** THE REGISTER-DATAFLOW RELATION of an emission. *)
Definition row_deps (es : list eitem) : list (nat * nat) :=
  row_deps_aux ds_init es.

(** ** 6.2 Sanity: every edge runs from a READ position STRICTLY BELOW a
       WRITE position — the [gdeps_wf] shape, at row level *)

Lemma dedges_lt s k asrc vsrc jk :
  jk ∈ dedges s k asrc vsrc → (jk.1 < jk.2)%nat.
Proof.
  rewrite /dedges. intros (j & -> & Hj)%elem_of_list_fmap.
  apply elem_of_list_filter in Hj as [Hlt _]. exact Hlt.
Qed.

Lemma row_deps_aux_lt s es jk :
  jk ∈ row_deps_aux s es → (jk.1 < jk.2)%nat.
Proof.
  revert s. induction es as [|it es IH]; intros s Hjk; simpl in Hjk.
  { by apply elem_of_nil in Hjk. }
  apply elem_of_app in Hjk as [Hjk|Hjk]; [|by eapply IH].
  destruct it as [l [k|]]; destruct l; simpl in Hjk;
    try (by apply elem_of_nil in Hjk); by eapply dedges_lt.
Qed.

Lemma row_deps_lt es jk : jk ∈ row_deps es → (jk.1 < jk.2)%nat.
Proof. apply row_deps_aux_lt. Qed.

(** The TARGET of an edge is the row position of a WRITE item. *)
Lemma row_deps_aux_tgt s es jk :
  jk ∈ row_deps_aux s es →
  ∃ it, it ∈ es ∧ it.2 = Some jk.2 ∧ elb_is_w it.1 = true.
Proof.
  revert s. induction es as [|it es IH]; intros s Hjk; simpl in Hjk.
  { by apply elem_of_nil in Hjk. }
  apply elem_of_app in Hjk as [Hjk|Hjk].
  - destruct it as [l [k|]]; destruct l; simpl in Hjk;
      try (by apply elem_of_nil in Hjk);
      (rewrite /dedges in Hjk;
       apply elem_of_list_fmap in Hjk as (j & -> & _);
       eexists; split_and!; [apply elem_of_list_here|done|done]).
  - destruct (IH _ Hjk) as (it0 & Hin & Hpos & Hw).
    exists it0. split_and!; [by apply elem_of_list_further|done|done].
Qed.

Lemma row_deps_tgt es jk :
  jk ∈ row_deps es →
  ∃ it, it ∈ es ∧ it.2 = Some jk.2 ∧ elb_is_w it.1 = true.
Proof. apply row_deps_aux_tgt. Qed.

(** The SOURCE of an edge is the row position of a READ item.  The induction
    carries a "every position the dataflow state remembers satisfies [P]"
    invariant, with [P] instantiated at the end by "is a read tag of the
    emission". *)

Definition ds_within (P : nat → Prop) (s : dstate) : Prop :=
  (∀ r j, j ∈ dprov s r → P j) ∧
  (∀ j, j ∈ ds_ld s → P j) ∧
  (∀ j, j ∈ ds_ctl s → P j).

Definition eread_ok (P : nat → Prop) (es : list eitem) : Prop :=
  ∀ it k, it ∈ es → it.2 = Some k → elb_is_r it.1 = true → P k.

Lemma ds_within_init P : ds_within P ds_init.
Proof.
  split_and!; intros ** ; rewrite /dprov /ds_init /= ?lookup_empty /= in H |- *;
    by apply elem_of_nil in H.
Qed.

Lemma dsrcs_pos_within P s xs j :
  ds_within P s → j ∈ dsrcs_pos s xs → P j.
Proof.
  intros (Hp & Hl & _) Hj.
  apply elem_of_list_join in Hj as (l & Hj & Hl0).
  apply elem_of_list_fmap in Hl0 as (x & -> & _).
  destruct x as [r|]; [by eapply Hp|by apply Hl].
Qed.

Lemma dstep_within P s it :
  ds_within P s →
  (∀ k, it.2 = Some k → elb_is_r it.1 = true → P k) →
  ds_within P (dstep s it).1 ∧ (∀ jk, jk ∈ (dstep s it).2 → P jk.1).
Proof.
  intros Hs Hr.
  have Hedges : ∀ k asrc vsrc, ∀ jk, jk ∈ dedges s k asrc vsrc → P jk.1.
  { intros k asrc vsrc jk. rewrite /dedges.
    intros (j & -> & Hj)%elem_of_list_fmap.
    apply elem_of_list_filter in Hj as [_ Hj]. simpl.
    apply elem_of_app in Hj as [Hj|Hj]; [by eapply dsrcs_pos_within|].
    apply elem_of_app in Hj as [Hj|Hj]; [by eapply dsrcs_pos_within|].
    apply elem_of_app in Hj as [Hj|Hj];
      [by apply (proj2 (proj2 Hs))|by apply (proj1 (proj2 Hs))]. }
  destruct Hs as (Hp & Hl & Hc).
  destruct it as [l [k|]]; destruct l; simpl in *;
    (split; [|by intros jk Hjk; try (by apply elem_of_nil in Hjk); eauto]).
  (* the state moves *)
  all: try (by split_and!).
  all: try (by split_and!; simpl; auto;
            intros j Hj; apply elem_of_cons in Hj as [->|Hj];
            [by apply Hr|by apply Hl]).
  all: try (by split_and!; simpl; auto;
            intros j Hj; apply elem_of_app in Hj as [Hj|Hj];
            [by apply Hc|by eapply dsrcs_pos_within; [split_and!|]]).
  (* [LRegW]: the destination register's provenance is the sources' *)
  all: try (by split_and!; simpl; auto; intros r0 j Hj;
            rewrite /dprov /= in Hj;
            destruct (decide (r0 = rd)) as [->|Hne];
            [rewrite lookup_insert /= in Hj;
             eapply dsrcs_pos_within; [split_and!|exact Hj]; eauto
            |rewrite lookup_insert_ne // in Hj; by eapply Hp]).
  (* [LInstr]: the load set is emptied *)
  all: try (by split_and!; simpl; auto; intros j Hj;
            by apply elem_of_nil in Hj).
Qed.

Lemma row_deps_aux_within P s es jk :
  ds_within P s → eread_ok P es →
  jk ∈ row_deps_aux s es → P jk.1.
Proof.
  revert s. induction es as [|it es IH]; intros s Hs Hok Hjk; simpl in Hjk.
  { by apply elem_of_nil in Hjk. }
  destruct (dstep_within P s it Hs
              (λ k Hk Hr, Hok it k (elem_of_list_here _ _) Hk Hr))
    as [Hs' He].
  apply elem_of_app in Hjk as [Hjk|Hjk]; [by apply He|].
  eapply IH; [exact Hs'| |exact Hjk].
  intros it0 k Hin. apply Hok. by apply elem_of_list_further.
Qed.

Lemma row_deps_src es jk :
  jk ∈ row_deps es →
  ∃ it, it ∈ es ∧ it.2 = Some jk.1 ∧ elb_is_r it.1 = true.
Proof.
  intros Hjk.
  eapply (row_deps_aux_within
            (λ j, ∃ it, it ∈ es ∧ it.2 = Some j ∧ elb_is_r it.1 = true));
    [apply ds_within_init| |exact Hjk].
  intros it k Hin Hpos Hr. by exists it.
Qed.

(** ** 6.3 [row_deps] IS ts-BLIND

    The fold reads a label's operand lists, its register destination and its
    tag — never a timestamp column — so the renaming is invisible to it. *)

Lemma dstep_ren π s it : dstep s (eitem_ren π it) = dstep s it.
Proof. destruct it as [l k]; by destruct l. Qed.

Lemma row_deps_aux_ren π s es :
  row_deps_aux s (eitem_ren π <$> es) = row_deps_aux s es.
Proof.
  revert s. induction es as [|it es IH]; intros s; [done|].
  by rewrite /= dstep_ren IH.
Qed.

Lemma row_deps_ren π es : row_deps (eitem_ren π <$> es) = row_deps es.
Proof. apply row_deps_aux_ren. Qed.

(* ====================================================================== *)
(** * 7. [hart_conf]: PER-HART ROW EMITTABILITY

    One block per row event: an [adm_run true] and then either the realizing
    step, or — for a row event that is a fused [LRmw] — the exclusive PAIR
    with its [LInstr]-FREE interior run.  This is [exec_prog_ok']'s per-event
    disjunction, per hart, with the axiomatic [mstate] replaced by the
    representative wstate fold (which the relation threads: the [wstate]
    index of [hemit] at row position [k] IS [row_ws row k], see
    [hemit_row_ws]). *)

Inductive hemit (dv : nat → dev_state)
    : nat → wstate → list lbl → pexv6 → list eitem → pexv6 → Prop :=
| HEnil k ws p : hemit dv k ws [] p [] p
| HEone k ws lb row p ls pa da l p' es pfin :
    adm_run true p (dv k) ls pa da →
    hlbl_realizes pa ws lb l →
    pstep_ev pa da l p' (dv (S k)) →
    hemit dv (S k) (lbl_post k ws lb) row p' es pfin →
    hemit dv k ws (lb :: row) p (eadm ls ++ (l, Some k) :: es) pfin
| HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin :
    adm_run true p (dv k) ls1 pa da →
    hlbl_realizes_pair pa pm2 ws lb l1 l2 →
    pstep_ev pa da l1 pm dm →
    adm_run false pm dm ls2 pm2 dm2 →
    pstep_ev pm2 dm2 l2 p' (dv (S k)) →
    hemit dv (S k) (lbl_post k ws lb) row p' es pfin →
    hemit dv k ws (lb :: row) p
      (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es) pfin.

(** THE EMISSION: the item sequence and the program state it ends at.
    B2e projects the steps out of [hart_conf]'s derivation; B3 transports
    the whole thing along the normalization orbit. *)
Record hemission := HEm {
  em_items : list eitem;
  em_fin   : pexv6;
}.

Definition em_labels (em : hemission) : list wlabel := (em_items em).*1.

Definition em_ren (π : nat → nat) (em : hemission) : hemission :=
  HEm (eitem_ren π <$> em_items em) (em_fin em).

Lemma em_labels_ren π em : em_labels (em_ren π em) = wlbl_ren π <$> em_labels em.
Proof.
  rewrite /em_labels /em_ren /= -!list_fmap_compose.
  apply list_fmap_ext. by intros i it _.
Qed.

(** [i] is carried for the caller's benefit (it is the hart the row belongs
    to, and [gdexec_conf] pairs it with the row positions to make [geid]s);
    the emission itself does not need it — the hart's identity is inside
    [p0]'s [PHart cpu] field. *)
Definition hart_conf (i : agent) (row : list lbl) (p0 : pexv6)
    (dv : nat → dev_state) (em : hemission) : Prop :=
  hemit dv 0%nat ws_init row p0 (em_items em) (em_fin em).

(** THE WSTATE INDEX OF [hemit] IS THE FOLD: [HEone]/[HEpair] advance it by
    [lbl_post k ws lb] at row position [k], which is exactly how [row_ws]
    steps ([row_ws_step] below).  So the block at row position [n] of a
    [hart_conf] derivation reads its projection equation at [row_ws row n]. *)
Lemma row_ws_aux_snoc t ws r n l :
  r !! n = Some l →
  row_ws_aux t ws (take (S n) r)
  = lbl_post (t + n) (row_ws_aux t ws (take n r)) l.
Proof.
  revert t ws n. induction r as [|l0 r IH]; intros t ws n Hn; [done|].
  destruct n as [|n]; simpl in Hn |- *.
  - simplify_eq. by rewrite Nat.add_0_r.
  - rewrite (IH (S t) (lbl_post t ws l0) n Hn).
    by replace (t + S n)%nat with (S t + n)%nat by lia.
Qed.

Lemma row_ws_step row n l :
  row !! n = Some l → row_ws row (S n) = lbl_post n (row_ws row n) l.
Proof. intros Hn. rewrite /row_ws (row_ws_aux_snoc 0%nat _ row n l Hn) //. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.1 The row events' kinds, read off the emission

    Every tagged item's label is a read/write exactly where the row label at
    that position is — which is what turns [row_deps]' §6.2 sanity lemmas
    into [gdeps_wf]'s conjuncts. *)

Lemma hlbl_realizes_kind p ws lb l :
  hlbl_realizes p ws lb l →
  (elb_is_r l = true → lb_is_r lb = true) ∧
  (elb_is_w l = true → lb_is_w lb = true).
Proof.
  intros (Hnb & _ & _ & Hpr). destruct l; simplify_eq/=; split; done.
Qed.

Lemma hemit_tag_lbl dv k ws row p es pfin it j :
  hemit dv k ws row p es pfin → it ∈ es → it.2 = Some j →
  ∃ lb, (k ≤ j)%nat ∧ row !! (j - k)%nat = Some lb ∧
        (elb_is_r it.1 = true → lb_is_r lb = true) ∧
        (elb_is_w it.1 = true → lb_is_w lb = true).
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros Hit Hj.
  - by apply elem_of_nil in Hit.
  - apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. exists lb.
      rewrite Nat.sub_diag. destruct (hlbl_realizes_kind pa ws lb l Hre).
      split_and!; [lia|done|done|done]. }
    destruct (IH Hit Hj) as (lb0 & Hle & Hlk & Hr & Hw).
    exists lb0. split_and!; [lia| |done|done].
    replace (j - k)%nat with (S (j - S k))%nat by lia. done.
  - apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. exists lb. rewrite Nat.sub_diag.
      destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                       -> & -> & _ & _ & ->).
      split_and!; [lia|done|done|done]. }
    apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. exists lb. rewrite Nat.sub_diag.
      destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                       -> & -> & _ & _ & ->).
      split_and!; [lia|done|done|done]. }
    destruct (IH Hit Hj) as (lb0 & Hle & Hlk & Hr & Hw).
    exists lb0. split_and!; [lia| |done|done].
    replace (j - k)%nat with (S (j - S k))%nat by lia. done.
Qed.

Lemma hart_conf_tag_lbl i row p0 dv em it j :
  hart_conf i row p0 dv em → it ∈ em_items em → it.2 = Some j →
  ∃ lb, row !! j = Some lb ∧
        (elb_is_r it.1 = true → lb_is_r lb = true) ∧
        (elb_is_w it.1 = true → lb_is_w lb = true).
Proof.
  intros Hem Hit Hj.
  destruct (hemit_tag_lbl _ _ _ _ _ _ _ _ _ Hem Hit Hj)
    as (lb & _ & Hlk & Hr & Hw).
  rewrite Nat.sub_0_r in Hlk. by exists lb.
Qed.

(** THE [gdeps_wf] SHAPE, at row level: every [row_deps] edge of an emission
    of [row] runs from a READ position of [row] strictly below a WRITE
    position of [row]. *)
Lemma hart_conf_row_deps_wf i row p0 dv em jk :
  hart_conf i row p0 dv em → jk ∈ row_deps (em_items em) →
  (jk.1 < jk.2)%nat ∧
  (∃ lb, row !! jk.1 = Some lb ∧ lb_is_r lb = true) ∧
  (∃ lb, row !! jk.2 = Some lb ∧ lb_is_w lb = true).
Proof.
  intros Hem Hjk. split_and!.
  - by eapply row_deps_lt.
  - destruct (row_deps_src _ _ Hjk) as (it & Hit & Hpos & Hr).
    destruct (hart_conf_tag_lbl i row p0 dv em it jk.1 Hem Hit Hpos)
      as (lb & Hlk & Hrr & _).
    exists lb. split; [done|by apply Hrr].
  - destruct (row_deps_tgt _ _ Hjk) as (it & Hit & Hpos & Hw).
    destruct (hart_conf_tag_lbl i row p0 dv em it jk.2 Hem Hit Hpos)
      as (lb & Hlk & _ & Hww).
    exists lb. split; [done|by apply Hww].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.2 STABILITY (1): the normalization orbit

    The emission's instance labels change only their ts columns, which
    [pstep_ev] accepts by [WeakEvInst]'s [ts_oblivious] family; the
    projection equation transports because the class reads only [w_relp] and
    the fold's [w_relp] is ts-blind (§3.2); and [row_deps] is unchanged
    (§6.3).  NO SIDE CONDITION ON [π] IS NEEDED — not injectivity, not
    [π 0 = 0]. *)

Lemma hemit_ren π dv k ws row p es pfin :
  hemit dv k ws row p es pfin →
  ∀ ws', w_relp ws' = w_relp ws →
  hemit dv k ws' (lbl_ren π <$> row) p (eitem_ren π <$> es) pfin.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros ws' Hrelp.
  - apply HEnil.
  - rewrite eitem_ren_block.
    eapply HEone.
    + by apply adm_run_ren.
    + by eapply hlbl_realizes_ren.
    + destruct Hre as (_ & Hlat & Hrf & _). by apply pstep_ev_wren.
    + apply IH. by apply lbl_post_relp_ren.
  - rewrite eitem_ren_block eitem_ren_block.
    have Hshape := Hre.
    destruct Hshape as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                        -> & -> & Hne & Hlen & Hlb).
    eapply HEpair.
    + by apply adm_run_ren.
    + by eapply hlbl_realizes_pair_ren.
    + eapply (pstep_ev_wren π); [done|done|exact Hst1].
    + by apply adm_run_ren.
    + eapply (pstep_ev_wren π); [done|done|exact Hst2].
    + apply IH. by apply lbl_post_relp_ren.
Qed.

Lemma hart_conf_ren π i row p0 dv em :
  hart_conf i row p0 dv em →
  hart_conf i (lbl_ren π <$> row) p0 dv (em_ren π em).
Proof. intros Hem. by eapply hemit_ren. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.3 STABILITY (2): prefix restriction

    An emission of a row restricts to an emission of every prefix of it — cut
    at the [n]-th row event's realizing step.  The fabric parameter is
    UNCHANGED (scope note (S-d)): row-position indexing makes a row prefix
    use an index prefix. *)

(** A prefix inside one emission BLOCK. *)
Lemma prefix_block {A} (a : list A) (x : A) (b c : list A) :
  b `prefix_of` c → a ++ x :: b `prefix_of` a ++ x :: c.
Proof. intros [t ->]. exists t. by rewrite -app_assoc. Qed.

Lemma hemit_prefix dv k ws row p es pfin :
  hemit dv k ws row p es pfin →
  ∀ n, ∃ es' pfin', es' `prefix_of` es ∧
       hemit dv k ws (take n row) p es' pfin'.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros n.
  - exists [], p. split; [apply prefix_nil|]. rewrite take_nil. apply HEnil.
  - destruct n as [|n].
    { exists [], p. split; [apply prefix_nil|]. apply HEnil. }
    destruct (IH n) as (es' & pfin' & Hpre & Hem').
    exists (eadm ls ++ (l, Some k) :: es'), pfin'. split.
    + by apply prefix_block.
    + rewrite firstn_cons. by eapply HEone.
  - destruct n as [|n].
    { exists [], p. split; [apply prefix_nil|]. apply HEnil. }
    destruct (IH n) as (es' & pfin' & Hpre & Hem').
    exists (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es'),
      pfin'. split.
    + by apply prefix_block, prefix_block.
    + rewrite firstn_cons. by eapply HEpair.
Qed.

Lemma hart_conf_prefix i row p0 dv em n :
  hart_conf i row p0 dv em →
  ∃ em', hart_conf i (take n row) p0 dv em' ∧
         em_items em' `prefix_of` em_items em.
Proof.
  intros Hem. destruct (hemit_prefix _ _ _ _ _ _ _ Hem n)
    as (es' & pfin' & Hpre & Hem').
  by exists (HEm es' pfin').
Qed.

(* ====================================================================== *)
(** * 8. THE CONFORMANCE BUNDLE

    Every hart's row is EMITTABLE from its boot state, and the emission's
    SYNTACTIC dependency edges are contained in the graph's declared dep
    set.  This is the tier-2 capstone's conformance hypothesis, stated
    entirely through tier-1's own vocabulary (route-b §2a resolution (α)). *)

Definition gdexec_conf (boot : agent → pexv6) (dvp : agent → nat → dev_state)
    (GD : gdexec) : Prop :=
  ∀ i row, gx_prog (gd_g GD) !! i = Some row →
    ∃ em, hart_conf i row (boot i) (dvp i) em ∧
          (∀ jk, jk ∈ row_deps (em_items em) →
                 ((i, jk.1), (i, jk.2)) ∈ gd_deps GD).

(** THE CONFORMANCE EDGES SATISFY [gdeps_wf]'s clause — so a conformant
    [gdexec] whose dep set is EXACTLY its conformance edges is dep-wf for
    free.  (Stated per-edge; B2e wants it in that form.) *)
Lemma gdexec_conf_deps_wf boot dvp GD i row em jk :
  gx_prog (gd_g GD) !! i = Some row →
  hart_conf i row (boot i) (dvp i) em →
  jk ∈ row_deps (em_items em) →
  (i, jk.1).1 = (i, jk.2).1 ∧ ((i, jk.1).2 < (i, jk.2).2)%nat ∧
  glbl_is (gd_g GD) (i, jk.1) lb_is_r ∧ glbl_is (gd_g GD) (i, jk.2) lb_is_w.
Proof.
  intros Hrow Hem Hjk.
  destruct (hart_conf_row_deps_wf i row (boot i) (dvp i) em jk Hem Hjk)
    as (Hlt & (lb1 & Hl1 & Hr1) & (lb2 & Hl2 & Hw2)).
  split_and!; [done|done| |].
  - exists lb1. split; [|done]. rewrite /gx_lbl /= Hrow //.
  - exists lb2. split; [|done]. rewrite /gx_lbl /= Hrow //.
Qed.

(** THE ORBIT TRANSPORT — what lets B3 apply conformance to [normalize]'s
    output.  [rows_rel] renames the rows' ts columns and leaves the dep set
    (which names EVENTS, not timestamps) alone. *)
Lemma gdexec_conf_ren π boot dvp GD GD' :
  rows_rel π (gd_g GD) (gd_g GD') →
  gd_deps GD' = gd_deps GD →
  gdexec_conf boot dvp GD → gdexec_conf boot dvp GD'.
Proof.
  intros Hrr Hdeps Hconf i row' Hrow'.
  destruct Hrr as (_ & Hprog & _).
  rewrite Hprog list_lookup_fmap in Hrow'.
  apply fmap_Some in Hrow' as (row & Hrow & ->).
  destruct (Hconf i row Hrow) as (em & Hem & Hdep).
  exists (em_ren π em). split; [by apply hart_conf_ren|].
  intros jk Hjk. rewrite Hdeps. apply Hdep.
  by rewrite /em_ren /= row_deps_ren in Hjk.
Qed.

(* ====================================================================== *)
(** * 9. SMOKE TESTS

    Closed checks that the definitions are not vacuous and that the fold
    computes what the design says. *)

(** The load;regw;store chain of RVWMO rule 10: the store's data operand
    names the register the load wrote, so the load's row position is a dep
    source of the store's.  (The [LInstr]s are the instruction boundaries —
    the second one RESETS [DLdRes], which is why the store's edge has to
    come through [DReg 5], not through the load set.) *)
Example row_deps_chain :
  row_deps [ (LInstr, None);
             (WeakPromise.LLoad false false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (LRegW 5%nat [DLdRes], None);
             (LInstr, None);
             (WeakPromise.LStore false 8 [bv_0 8] [DReg 5%nat] [], Some 1%nat) ]
  = [(0%nat, 1%nat)].
Proof. vm_compute. reflexivity. Qed.

(** F5' (route-b §4d.1) — TRANSITIVE PROVENANCE THROUGH LOAD ADDRESSES.
    The pointer chase [ld r1 <- [x]; ld r2 <- [r1]; st [q] := r2]: the second
    load's ADDRESS comes from the first load's result, so the store depends
    on the FIRST load too (RVWMO rules 9 and 10 composed).  D-8 keeps the
    address sources off the [LLoad] LABEL, so what carries the composition is
    the instance's register write, [LRegW r2 (DLdRes :: DReg r1)]
    ([WeakDeps.deps_rd]'s [ORload] arm) — and the fold then yields BOTH
    (1,2) and (0,2).  The edge (0,2) is the new one.  ([r9] is the first
    load's own base register, written by nobody in this row, so its
    provenance is empty and it contributes nothing — the emission is
    nonetheless the shape the instance now produces.) *)
Example row_deps_addr_chain :
  row_deps [ (LInstr, None);
             (WeakPromise.LLoad false false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (LRegW 1%nat [DLdRes; DReg 9%nat], None);
             (LInstr, None);
             (WeakPromise.LLoad false false 8 [(1%nat, bv_0 8)] [], Some 1%nat);
             (LRegW 2%nat [DLdRes; DReg 1%nat], None);
             (LInstr, None);
             (WeakPromise.LStore false 16 [bv_0 8] [] [DReg 2%nat], Some 2%nat) ]
  = [(1%nat, 2%nat); (0%nat, 2%nat)].
Proof. vm_compute. reflexivity. Qed.

(** THE "BEFORE", kept as a live check: with the PRE-F5' emission — the
    second load's result write naming only [DLdRes] — the first load is NOT
    in the store's dependency set, and nothing else in the row changes.  That
    absence is exactly the hole §4d.1 F5' names (a witness read above the
    certified write could redirect the second load's address, hence the
    store's data, with no dep edge to forbid it). *)
Example row_deps_addr_chain_before :
  row_deps [ (LInstr, None);
             (WeakPromise.LLoad false false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (LRegW 1%nat [DLdRes], None);
             (LInstr, None);
             (WeakPromise.LLoad false false 8 [(1%nat, bv_0 8)] [], Some 1%nat);
             (LRegW 2%nat [DLdRes], None);
             (LInstr, None);
             (WeakPromise.LStore false 16 [bv_0 8] [] [DReg 2%nat], Some 2%nat) ]
  = [(1%nat, 2%nat)].
Proof. vm_compute. reflexivity. Qed.

(** Scope note (S-c) in action: the exclusive pair's INTERNAL read→write
    dependency is at ONE row position and is filtered out. *)
Example row_deps_amo_selfedge :
  row_deps [ (LExLoad false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (LRegW 5%nat [DLdRes], None);
             (LExStore false 0 [bv_0 8] [] [DReg 5%nat], Some 0%nat) ]
  = [].
Proof. vm_compute. reflexivity. Qed.

(** THE W-TV ARM (rule 13) in action: within ONE instruction — no [LInstr]
    between them — the load's row position feeds the store's, with NO
    register dataflow at all ([asrc] and [vsrc] both empty).  This is the
    edge scope decision (S-a) used to omit; the [LInstr] boundary is what
    keeps it from leaking into the NEXT instruction's stores (contrast
    [row_deps_chain], where the reset forces the edge through [DReg 5]). *)
Example row_deps_wtv :
  row_deps [ (LInstr, None);
             (WeakPromise.LLoad false false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (WeakPromise.LStore false 8 [bv_0 8] [] [], Some 1%nat) ]
  = [(0%nat, 1%nat)].
Proof. vm_compute. reflexivity. Qed.

(** … and the reset really does cut it: with an [LInstr] between, the load
    is no longer the store's translation read. *)
Example row_deps_wtv_reset :
  row_deps [ (LInstr, None);
             (WeakPromise.LLoad false false 0 [(0%nat, bv_0 8)] [], Some 0%nat);
             (LInstr, None);
             (WeakPromise.LStore false 8 [bv_0 8] [] [], Some 1%nat) ]
  = [].
Proof. vm_compute. reflexivity. Qed.

(** The empty row is emittable. *)
Example hart_conf_nil i p0 dv : hart_conf i [] p0 dv (HEm [] p0).
Proof. apply HEnil. Qed.
