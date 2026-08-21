(** * WeakEvFunnel.v — THE EVENT-TIER INSTRUCTION FUNNEL (M4-1, first slice)

    Plan: [claude-notes/projects/weak-memory-m4-retarget.md] (stage M4-1, "the
    funnel twin"); the bridge it stands on is [WeakEvExecEff] (stage M4-S1);
    the language is [WeakEvLang] ([claude-notes/design/
    weak-memory-event-granular.md]).

    WHAT THIS FILE IS.  [WeakFunnel.wwp_instr] is the instruction-atomic
    tier's funnel: a leaf hands in the text resource, the M-mode config and
    ONE [execute] fact, and gets [WWP Loop] back.  This file is its EVENT-TIER
    twin: a leaf hands in the text resource, its register frame and ONE
    whole-instruction RUN fact, and gets [EWP (ELoop gen c)] back — with the
    fetch, the decode, the [try_step] wrapper, [minstret], the clock tick and
    all the register plumbing consumed inside the rule, exactly as before.

    ================== THE FOUR PIECES ==================

    §1  [erun Dr Dw m t] — [WeakEvExecEff.epurew] with the READ and WRITE
        footprints SEPARATED (see the dfrac finding below), plus its
        composition kit ([erun_bind], [erun_bind0], [erun_read_reg],
        [erun_write_reg], [erun_read] — the RAM-read arm — and [erun_mono]).
        A successful [erun] IS an [exec_eff] run with the same value, state
        and trace ([erun_exec_eff]), so the two never disagree.
    §2  [ereg_fr c rs Dr q] — the register frame with the FRACTION A FUNCTION
        OF THE REGISTER — and its one-node rule [ewp_ev_node2] / batched walk
        [ewp_ev_walk] ([WeakEvLift] §4's twins).
    §3  [erun_split_read] — a run whose whole trace is ONE read IS: a silent
        stretch, the read node, a silent stretch.  This is the whole content
        of "a register-only instruction is a fetch and nothing else".
    §4  [ewp_ev_one_fetch] (mid-cycle) and [ewp_instr_pure] (at the
        instruction boundary, both ticks) — THE RULES.
    §5  the leaf-facing packaging: [winstr_bytes_etext_word] (the funnel's
        fetch obligation, discharged from the resource every existing leaf
        already holds), the frame adapters, and [epure_erun] (every [epure]
        mirror of [WeakEvExecEff] feeds these rules unchanged).
    §6  the demonstration: a real boot-cone certificate fragment through the
        kit, and [WeakLeafUtypeShift.wwp_lui_leaf] restated at the event tier.

    ================== FINDING 1: THE MIRROR GAP (the headline) ==================

    THE RULE SIDE OF M4-1 IS CHEAP; THE CERTIFICATE SIDE IS NOT FREE, and the
    retarget plan's cost estimate has to absorb that.  The tree's existing
    whole-instruction certificates ([WeakCert.wstep_conf_eff], produced by
    [WeakFetchEff.wP_eff_of_leaf_base] / [WeakLeafRegOnly.wP_eff_of_leaf_regonly])
    give [exec_eff (riscv_step tick) t = Some (tt, t', es)].  They do NOT
    transfer to [erun]:

      - [erun] guards the register arms by the footprint, and
      - [erun] is STUCK at a device access, where [exec_eff] consults
        [dev_read] / [dev_write] and RECORDS NOTHING IN THE TRACE.

    So an [exec_eff] success cannot witness device-freedom, and M4-S1's
    finding (ii) — no [dev_state] makes every device access fail, because
    [uart_read] answers in every state — says no semantic detector can be
    built either.  Device-freedom is a property of the RUN, and the only way
    to have it is to re-run the mirror in a predicate that carries it.
    CONSEQUENCE: the [try_step] spine has to be re-mirrored at [erun] —
    [WeakEffSkel]'s [execR_eff] kit (the [catch_early_return] monad),
    [WeakPmpEff], [WeakFetchEff] §§1–5 and [WeakTickEff], ~2 800 lines of
    [exec_eff] script.  M4-S1 measured what that conversion costs per lemma
    (the [epure] mirror is the [exec_eff] mirror with the combinator names
    changed and ONE membership side condition added per register node), so it
    is mechanical — but it is NOT zero, and it is the residual input of §6's
    leaf (premise (i)) and of every other leaf.  §1's kit and §5's
    [epure_erun] exist to make that port a rename.

    ================== FINDING 2: [ereg_frame] IS TOO STRONG (B2) ==================

    [WeakEvLift.ereg_frame c rs D] owns EVERY register of [D] at
    [DfracOwn 1].  The registers [try_step] reads include [misa], [mseccfg],
    [pma_regions], [htif_tohost_base] and [elp] — held PERSISTENTLY
    ([DfracDiscarded]) by [InstrBytes.hw_config] inside [mmode_config] — and
    [cur_privilege] / [mstatus] / [hart_state], held at a client-chosen
    fraction [dq].  A leaf can therefore NEVER hand [ereg_frame] over its own
    footprint, and the spike's rule cannot be the leaf-facing one.  THE FIX,
    delivered here: [ereg_fr c rs Dr q] takes the fraction as a function of
    the register, and the run predicate takes TWO footprints — reads are
    answered on [Dr] (any fraction), writes are guarded by [Dw] (where
    [q r = DfracOwn 1] is required).  [ereg_fr c rs D (fun _ => DfracOwn 1)]
    IS [ereg_frame c rs D] ([ereg_fr_frame]), so nothing in [WeakEvLift] is
    invalidated.

    ================== FINDING 3: B1, AND WHY IT IS NOT A PROBLEM ==================

    [WeakFunnel.wwp_instr] holds [minstret_inv] (and [clock_inv] on the tick
    branch) OPEN ACROSS THE WHOLE INSTRUCTION.  The event tier cannot do
    that: an instruction is many language steps and an invariant may only be
    held across one.  It does not need to: [minstret], [minstret_increment],
    [mcycle], [mtime], [mtimecmp] and [mip] are HART-LOCAL cells, so the hart
    may simply own them ([Dw]), and the whole-instruction hold disappears.
    (For a cell that is genuinely shared, the per-node opening is available —
    [WeakEvWire.ewp_ev_reg_read_inv] is that rule.)  The tick branch is then
    an ordinary register stretch, which is why [ewp_instr_pure] takes the
    certificate for BOTH ticks and costs nothing extra for the tick one.

    ================== THE LATER COUNT ==================

    [ewp_ev_one_fetch] is ▷-FREE (its continuation is later-free, which is
    strictly stronger); [ewp_instr_pure] carries exactly ONE ▷, the one
    [WeakEvLift.ewp_eloop] spends on the instruction boundary — the same
    single ▷ [WeakFunnel.wwp_cb] gives its leaf.

    ================== MEASUREMENTS ==================

    Whole file, [coqc -time]: 6.4 s cold (of which ~3 s is the [Require]
    chain, which includes the instruction-atomic tier for §5's packaging
    only).  No [vm_compute] anywhere; no [Admitted]; the file's theorems rest
    on the tree's five standard [rv64d] axioms and nothing else. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WeakCert.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.
Require Import WeakEvLift.
Require Import WeakEvExecEff.
(* the instruction-atomic tier, for the LEAF-FACING packaging of §5 only:
   [winstr_bytes] (the text resource every leaf already holds) and
   [wak_plain] / [regonly_es] (the trace shape every register-only leaf's
   [exec_eff] certificate carries).  No rule of §§1-4 depends on them. *)
Require Import WeakBridge.
Require Import WeakFunnel.
Require Import WeakFetchEff.
Require Import WeakLeafRegOnly.
Require Import WpGpr WpMmodeLeafBase.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. [erun]: [epurew] with the READ and WRITE footprints SEPARATED *)

Fixpoint erun {X} (Dr Dw : gset register) (m : M X) (t : mstate) {struct m}
    : option (X * mstate * list weff) :=
  match m with
  | Interface.Ret y => Some (y, t, [])
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * mstate * list weff) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ Dr)
           then erun Dr Dw (k (register_lookup r t.(sregs))) t
           else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ Dw) then erun Dr Dw (k tt) (set_reg t r v) else None
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then None
           else
             match read_bytes t.(mem) (Interface.ReadReq.pa req) n with
             | Some w =>
                 match erun Dr Dw (k (inl (w, None))) t with
                 | Some (y, t', es) =>
                     Some (y, t',
                           WEread (classify (Interface.ReadReq.access_kind req))
                                  (Interface.ReadReq.pa req) n :: es)
                 | None => None
                 end
             | None => None
             end
       | Interface.InstrAnnounce _   => fun k => erun Dr Dw (k tt) t
       | Interface.BranchAnnounce _ _=> fun k => erun Dr Dw (k tt) t
       | Interface.CacheOp _         => fun k => erun Dr Dw (k tt) t
       | Interface.TlbOp _           => fun k => erun Dr Dw (k tt) t
       | Interface.TakeException _   => fun k => erun Dr Dw (k tt) t
       | Interface.ReturnException _ => fun k => erun Dr Dw (k tt) t
       | Interface.TranslationStart _=> fun k => erun Dr Dw (k tt) t
       | Interface.TranslationEnd _  => fun k => erun Dr Dw (k tt) t
       | Interface.CycleCount        => fun k => erun Dr Dw (k tt) t
       | Interface.Message _         => fun k => erun Dr Dw (k tt) t
       | Interface.GetCycleCount     => fun k => erun Dr Dw (k 0%Z) t
       (* MemWrite / Barrier / Choose / GenericFail / … : STUCK. *)
       | _ => fun _ => None
       end) k
  end.

(** THE COMPOSITION KIT ([WeakEvExecEff] §1's twin, one arm richer). *)

Lemma erun_returnm {X} (Dr Dw : gset register) (x : X) t :
  erun Dr Dw (Defs.returnm x) t = Some (x, t, []).
Proof. reflexivity. Qed.

Lemma erun_read_reg (Dr Dw : gset register) (r : register) t :
  r ∈ Dr ->
  erun Dr Dw (Defs.read_reg r : M _) t
    = Some (register_lookup r t.(sregs), t, []).
Proof. intros HD. simpl. by case_decide. Qed.

Lemma erun_write_reg (Dr Dw : gset register) (r : register)
    (v : type_of_register r) t :
  r ∈ Dw -> erun Dr Dw (Defs.write_reg r v : M _) t = Some (tt, set_reg t r v, []).
Proof. intros HD. simpl. by case_decide. Qed.

(** The one memory arm: a RAM read, answered by the run's own byte map. *)
Lemma erun_read {X} (Dr Dw : gset register) (n : N)
    (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M X)
    (t : mstate) (w : bv (8 * n)) (y : X) (t' : mstate) (es : list weff) :
  dev_addr (Interface.ReadReq.pa req) = false ->
  read_bytes t.(mem) (Interface.ReadReq.pa req) n = Some w ->
  erun Dr Dw (K (inl (w, None))) t = Some (y, t', es) ->
  erun Dr Dw (Interface.Next (Interface.MemRead n req) K) t
    = Some (y, t', WEread (classify (Interface.ReadReq.access_kind req))
                          (Interface.ReadReq.pa req) n :: es).
Proof. intros Hdev Hrd Hk. simpl. rewrite Hdev Hrd Hk. reflexivity. Qed.

Lemma erun_bind {X Y} (Dr Dw : gset register) (m : M X) (f : X -> M Y) :
  forall t v t' es, erun Dr Dw m t = Some (v, t', es) ->
    forall y t'' es', erun Dr Dw (f v) t' = Some (y, t'', es') ->
      erun Dr Dw (Defs.bind m f) t = Some (y, t'', (es ++ es')%list).
Proof.
  induction m as [y0 | T oc k IH]; intros t v t' es Hm y t'' es' Hf.
  - rewrite bind_Ret. simpl in Hm. by injection Hm as <- <- <-.
  - rewrite bind_Next. destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hm _ _ _ Hf));
      [ (case_decide; [|discriminate Hm]); exact (IH _ _ _ _ _ Hm _ _ _ Hf)
      | (case_decide; [|discriminate Hm]); exact (IH _ _ _ _ _ Hm _ _ _ Hf)
      | ].
    (* MemRead *)
    destruct (dev_addr _); [discriminate Hm|].
    destruct (read_bytes _ _ _) as [wA|]; [|discriminate Hm].
    destruct (erun Dr Dw (k _) t) as [[[xA tA] esA]|] eqn:Hep; [|discriminate Hm].
    injection Hm as <- <- <-.
    rewrite (IH _ _ _ _ _ Hep _ _ _ Hf). reflexivity.
Qed.

Lemma erun_bind0 {Y} (Dr Dw : gset register) (m : M unit) (n : M Y) t u t' es :
  erun Dr Dw m t = Some (u, t', es) ->
  forall y t'' es', erun Dr Dw n t' = Some (y, t'', es') ->
    erun Dr Dw (Defs.bind0 m n) t = Some (y, t'', (es ++ es')%list).
Proof.
  intros Hm y t'' es' Hn. unfold Defs.bind0.
  apply (erun_bind Dr Dw m _ t u t' es Hm). by destruct u.
Qed.

(** MONOTONE in both footprints. *)
Lemma erun_mono {X} (Dr Dr' Dw Dw' : gset register) (m : M X) :
  Dr ⊆ Dr' -> Dw ⊆ Dw' ->
  forall t r, erun Dr Dw m t = Some r -> erun Dr' Dw' m t = Some r.
Proof.
  intros Hsr Hsw. induction m as [y0 | T oc k IH]; intros t r Hm; [exact Hm|].
  destruct oc; simpl in Hm |- *; try discriminate;
    try (exact (IH _ _ _ Hm)).
  - (* RegRead *)
    case_decide as Hin; [|discriminate Hm].
    case_decide as Hin'; [exact (IH _ _ _ Hm)|by destruct (Hin' (Hsr _ Hin))].
  - (* RegWrite *)
    case_decide as Hin; [|discriminate Hm].
    case_decide as Hin'; [exact (IH _ _ _ Hm)|by destruct (Hin' (Hsw _ Hin))].
  - (* MemRead *)
    destruct (dev_addr _); [discriminate Hm|].
    destruct (read_bytes _ _ _) as [wA|]; [|discriminate Hm].
    destruct (erun Dr Dw (k _) t) as [[[xA tA] esA]|] eqn:Hep; [|discriminate Hm].
    by rewrite (IH _ _ _ Hep).
Qed.

(** [erun] IS [epurew] at a common footprint, hence IS [exec_eff]: the two
    predicates never disagree, and a client may hand in either. *)
Lemma erun_epurew {X} (Dr Dw : gset register) (m : M X) :
  Dw ⊆ Dr ->
  forall t r, erun Dr Dw m t = Some r -> epurew Dr m t = Some r.
Proof.
  intros Hsub. induction m as [y0 | T oc k IH]; intros t r Hm; [exact Hm|].
  destruct oc; simpl in Hm |- *; try discriminate;
    try (exact (IH _ _ _ Hm)).
  - case_decide; [exact (IH _ _ _ Hm)|discriminate Hm].
  - case_decide as Hin; [|discriminate Hm].
    case_decide as Hin'; [exact (IH _ _ _ Hm)|by destruct (Hin' (Hsub _ Hin))].
  - destruct (dev_addr _); [discriminate Hm|].
    destruct (read_bytes _ _ _) as [wA|]; [|discriminate Hm].
    destruct (erun Dr Dw (k _) t) as [[[xA tA] esA]|] eqn:Hep; [|discriminate Hm].
    by rewrite (IH _ _ _ Hep).
Qed.

Corollary erun_exec_eff {X} (Dr Dw : gset register) (m : M X) t y t' es :
  Dw ⊆ Dr -> erun Dr Dw m t = Some (y, t', es) ->
  exec_eff m t = Some (y, t', es) /\ mdev t' = mdev t.
Proof.
  intros Hsub Hm.
  exact (epurew_exec_eff Dr m t y t' es (erun_epurew Dr Dw m Hsub t _ Hm)).
Qed.

(* ====================================================================== *)
(** ** 2. THE REGISTER FRAME, DFRAC-INDEXED, AND ITS ONE-NODE RULE *)

(** [WeakEvLift.esil_node] with the WRITE guard moved to [Dw]. *)
Definition esil_node2 (Dr Dw : gset register) (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ Dr) then Some (rs, k (register_lookup r rs)) else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ Dw) then Some (register_set r v rs, k tt) else None
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Definition esil2D (Dr Dw : gset register) (x y : M unit * regstate) : Prop :=
  esil_node2 Dr Dw x.2 x.1 = Some (y.2, y.1).

(** The machine does not know about footprints: at [Dw ⊆ Dr] the two node
    functions agree, which is what lets §2's rule reuse [WeakEvLift]'s
    semantic bridge lemmas verbatim. *)
Lemma esil_node2_node (Dr Dw : gset register) (rs : regstate) (m : M unit) p :
  Dw ⊆ Dr -> esil_node2 Dr Dw rs m = Some p -> esil_node Dr rs m = Some p.
Proof.
  intros Hsub. destruct m as [y|T oc k]; [done|].
  destruct oc; simpl; try discriminate; try done;
    (case_decide as Hin; [|discriminate]);
    (case_decide as Hin'; [done|by destruct (Hin' (Hsub _ Hin))]).
Qed.

Section frame.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE FRAME.  [WeakEvLift.ereg_frame] with the fraction a FUNCTION of the
      register: the config registers a real instruction reads are held
      [DfracDiscarded] (persistently) or at a share by [mmode_config], and
      only the registers the instruction WRITES need [DfracOwn 1]. *)
  Definition ereg_fr (c : CPU) (rs : regstate) (Dr : gset register)
      (q : register -> dfrac) : iProp Σ :=
    ([∗ set] r ∈ Dr, reg_pointsto_at c r (q r) (register_lookup r rs))%I.

  Lemma ereg_fr_frame c rs D :
    ereg_fr c rs D (fun _ => DfracOwn 1) ⊣⊢ ereg_frame c rs D.
  Proof. by rewrite /ereg_fr /ereg_frame. Qed.

  Lemma ereg_fr_ext c rs rs' D q :
    reg_agree_on D rs rs' -> ereg_fr c rs D q ⊣⊢ ereg_fr c rs' D q.
  Proof.
    intros Hag. rewrite /ereg_fr. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  Lemma ereg_fr_agree c rs D q (rs0 : regstate) :
    reg_interp_at (cpu_reg_name c) rs0 -∗ ereg_fr c rs D q -∗
    ⌜reg_agree_on D rs rs0⌝.
  Proof.
    rewrite /ereg_fr. iIntros "Hi Hf".
    rewrite bi.pure_forall. iIntros (r). rewrite bi.pure_impl. iIntros (Hr).
    iDestruct (big_sepS_elem_of _ _ r Hr with "Hf") as "Hr".
    iDestruct (reg_valid_at c rs0 r (q r) (register_lookup r rs)
                 with "Hi Hr") as %Hv.
    iPureIntro. by symmetry.
  Qed.

  Lemma ereg_fr_update c rs D q (r : register) (v : type_of_register r) rs0 :
    r ∈ D -> q r = DfracOwn 1 ->
    reg_interp_at (cpu_reg_name c) rs0 -∗ ereg_fr c rs D q ==∗
    reg_interp_at (cpu_reg_name c) (register_set r v rs0) ∗
    ereg_fr c (register_set r v rs) D q.
  Proof.
    intros HrD Hq. rewrite /ereg_fr. iIntros "Hi Hf".
    iDestruct (big_sepS_delete _ _ r HrD with "Hf") as "[Hr Hrest]".
    rewrite Hq.
    iMod (reg_update_at c rs0 r (register_lookup r rs) v with "Hi Hr")
      as "[Hi Hr]".
    iModIntro. iFrame "Hi".
    iApply (big_sepS_delete _ _ r HrD).
    rewrite register_lookup_set Hq. iFrame "Hr".
    iApply (big_sepS_mono with "Hrest").
    intros r' Hr'. apply elem_of_difference in Hr' as [_ Hne].
    assert (Hne' : r' <> r)
      by (intros ->; apply Hne, elem_of_singleton; reflexivity).
    by rewrite (irrelevant_register_set r' r rs v (register_beq_false r' r Hne')).
  Qed.

  (** [WeakEvLift.esil_node_agree]'s twin: the stretch the CLIENT computed at
      its own register file is the stretch the MACHINE takes. *)
  Lemma esil_node2_agree Dr Dw rs1 rs2 m m1 rs1' :
    reg_agree_on Dr rs1 rs2 -> esil_node2 Dr Dw rs1 m = Some (rs1', m1) ->
    exists rs2', esil_node2 Dr Dw rs2 m = Some (rs2', m1) /\
                 reg_agree_on Dr rs1' rs2'.
  Proof.
    intros Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
    destruct oc; simpl in Hnode |- *; try discriminate Hnode;
      first
        [ (* RegRead *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; rewrite (Hag _ HrD); exists rs2; by split
        | (* RegWrite *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; eexists; (split; [done|]);
          intros r' Hr'; destruct (decide (r' = reg)) as [->|Hne];
          [ by rewrite !register_lookup_set
          | rewrite !(irrelevant_register_set r' reg _ regval
                        (register_beq_false r' reg Hne)); by apply Hag ]
        | injection Hnode as <- <-; exists rs2; by split ].
  Qed.

  (** ONE silent node, at the split footprint. *)
  (** D3-2: like [WeakEvLift.ewp_ev_sil_node], this rule now owns the hart's
      view — a silent node may be PARM's [step_assign] / [step_if] / the
      instruction start.  What comes back is [ws_depmove], nothing weaker. *)
  Lemma ewp_ev_node2 (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac) (rs : regstate) (m m1 : M unit) (rs1 : regstate)
      (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    esil_node2 Dr Dw rs m = Some (rs1, m1) ->
    hart_ws c ws -∗ ereg_fr c rs Dr q -∗
    ▷ (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
         ereg_fr c rs1 Dr q -∗ EWP (ECycle gen c m1 None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hsub Hq Hnode) "Hws Hrf H".
    iApply (ewp_ecycle gen c m None Hgen).
    iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_rmw σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hri & Hlog & Hlat & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iDestruct (ereg_fr_agree c rs Dr q (wgregs σ c) with "Hri Hrf") as %Hag.
    destruct (esil_node2_agree Dr Dw rs (wgregs σ c) m m1 rs1 Hag Hnode)
      as (rs2 & Hnode2 & Hag2).
    pose proof (esil_node2_node Dr Dw (wgregs σ c) m (rs2, m1) Hsub Hnode2)
      as Hnode2'.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro.
      destruct (esil_node_ecycle gen σ c Dr m m1 rs2 Hnode2') as (σ1 & Hc & _).
      by do 2 eexists. }
    iNext. iIntros (e' σ') "%Hcy". iMod "Hmask" as "_".
    destruct (esil_node_ecycle_inv gen σ c Dr rs2 m1 m e' σ' Hnode2' Hcy)
      as (-> & Hσ').
    iAssert (|==> reg_interp_at (cpu_reg_name c) rs2 ∗ ereg_fr c rs1 Dr q)%I
      with "[Hri Hrf]" as ">[Hri Hrf]".
    { destruct m as [y|T oc k]; [by simpl in Hnode|].
      destruct oc; simpl in Hnode; try discriminate Hnode;
        first
          [ (* RegWrite *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iMod (ereg_fr_update c rs Dr q _ regval (wgregs σ c) (Hsub _ HrD)
                    (Hq _ HrD) with "Hri Hrf") as "[Hri Hrf]";
            iModIntro; by iFrame "Hri Hrf"
          | (* RegRead *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (ereg_fr_ext c rs rs Dr q)
          | injection Hnode as Hq1 Hq2; simpl in Hnode2;
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (ereg_fr_ext c rs rs Dr q) ]. }
    have Hrg := esil_sigma_regs σ c rs2 σ' Hσ'.
    iAssert (|==> ∃ ws' : wstate, ⌜ws_depmove (wgws σ c) ws'⌝ ∗
                    weak_state_interp σ' ∗ hart_ws c ws')%I
      with "[Hri Hlog Hlat Hwsa Hws Hcl]" as ">(%ws' & %Hdm' & Hσ & Hws)".
    { destruct Hσ' as [(k0 & ->)|[(Hr & (v & ->))|(Hr & ->)]].
      - iMod (hart_ws_update c (wgws σ c) (wgws σ c) (erw_ws (wgws σ c) k0)
                with "Hwsa Hws") as "[Hwsa Hws]".
        iDestruct ("Hcl" $! rs2 (erw_ws (wgws σ c) k0) (wglog σ)
                     with "[%] [%] [%] [%] [%] Hri Hlog Hlat Hwsa") as "Hσ0".
        { lia. }
        { destruct k0; simpl;
            [exact (Hbnd c)
            |apply regw_post_bounded;
               [exact (Hbnd c)|by apply srcs_view_bounded]
            |apply ctrl_post_bounded;
               [exact (Hbnd c)|by apply srcs_view_bounded]]. }
        { apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
            [exact (no_violation_hart _ _ c Hnv)|].
          intros a Hlt. exfalso.
          rewrite (ws_depmove_coh _ _ a (erw_ws_depmove (wgws σ c) k0)) in Hlt.
          lia. }
        { exists []. rewrite app_nil_r. split; [reflexivity|].
          intros mm Hmm. by apply elem_of_nil in Hmm. }
        { exact Hwf. }
        iModIntro. iExists (erw_ws (wgws σ c) k0). iFrame "Hws".
        iSplitR; [iPureIntro; apply erw_ws_depmove|].
        destruct k0;
          [iApply (weak_state_interp_ptwise
                     (ewg_regwslog σ c rs2 (wgws σ c) (wglog σ))
                     (<[c := rs2]> (wgregs σ)) (wgws σ) (wgib σ) with "[Hσ0]")
          |by rewrite /ewg_regwslog /ewg_regws /=..].
        + reflexivity.
        + intros c0. rewrite /ewg_regwslog /=.
          destruct (decide (c0 = c)) as [->|Hne];
            [by rewrite gws_insert_eq|by rewrite gws_insert_ne].
        + iExact "Hσ0".
      - iMod (hart_ws_update c (wgws σ c) (wgws σ c) (instr_post (wgws σ c))
                with "Hwsa Hws") as "[Hwsa Hws]".
        iDestruct ("Hcl" $! rs2 (instr_post (wgws σ c)) (wglog σ)
                     with "[%] [%] [%] [%] [%] Hri Hlog Hlat Hwsa") as "Hσ0".
        { lia. }
        { by apply instr_post_bounded, (Hbnd c). }
        { apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
            [exact (no_violation_hart _ _ c Hnv)|].
          intros a Hlt. exfalso.
          rewrite (ws_depmove_coh _ _ a (instr_post_depmove (wgws σ c)))
            in Hlt. lia. }
        { exists []. rewrite app_nil_r. split; [reflexivity|].
          intros mm Hmm. by apply elem_of_nil in Hmm. }
        { exact Hwf. }
        iModIntro. iExists (instr_post (wgws σ c)). iFrame "Hws".
        iSplitR; [iPureIntro; apply instr_post_depmove|].
        rewrite /ewg_ibws.
        iApply (weak_state_interp_ptwise
                  (ewg_regwslog σ c rs2 (instr_post (wgws σ c)) (wglog σ))
                  (wgregs σ) (<[c := instr_post (wgws σ c)]> (wgws σ))
                  (<[c := v]> (wgib σ)) with "[Hσ0]").
        + intros c0. rewrite /ewg_regwslog /= Hr.
          destruct (decide (c0 = c)) as [->|Hne];
            [by rewrite greg_insert_eq|by rewrite greg_insert_ne].
        + reflexivity.
        + iExact "Hσ0".
      - iMod (hart_ws_update c (wgws σ c) (wgws σ c) (wgws σ c)
                with "Hwsa Hws") as "[Hwsa Hws]".
        iDestruct ("Hcl" $! rs2 (wgws σ c) (wglog σ)
                     with "[%] [%] [%] [%] [%] Hri Hlog Hlat Hwsa") as "Hσ0".
        { lia. }
        { exact (Hbnd c). }
        { exact (no_violation_hart _ _ c Hnv). }
        { exists []. rewrite app_nil_r. split; [reflexivity|].
          intros mm Hmm. by apply elem_of_nil in Hmm. }
        { exact Hwf. }
        iModIntro. iExists (wgws σ c). iFrame "Hws".
        iSplitR; [iPureIntro; reflexivity|].
        destruct σ as [gr img lg f dv gn pw ib0]. simpl in Hr.
        iApply (weak_state_interp_ptwise
                  (ewg_regwslog (WGState gr img lg f dv gn pw ib0) c rs2 (f c) lg)
                  gr f ib0 with "[Hσ0]").
        + intros c0. rewrite /ewg_regwslog /= Hr.
          destruct (decide (c0 = c)) as [->|Hne];
            [by rewrite greg_insert_eq|by rewrite greg_insert_ne].
        + intros c0. rewrite /ewg_regwslog /=.
          destruct (decide (c0 = c)) as [->|Hne];
            [by rewrite gws_insert_eq|by rewrite gws_insert_ne].
        + iExact "Hσ0". }
    iModIntro. iSplitL "Hσ"; [iExact "Hσ"|].
    by iApply ("H" $! ws' with "[//] Hws Hrf").
  Qed.

  (** THE BATCHED WALK — the induction, once. *)
  Lemma ewp_ev_walk (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac) (x y : M unit * regstate) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    rtc (esil2D Dr Dw) x y ->
    hart_ws c ws -∗ ereg_fr c x.2 Dr q -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_fr c y.2 Dr q -∗ EWP (ECycle gen c y.1 None) @ ⊤) -∗
    EWP (ECycle gen c x.1 None) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hrtc. revert ws.
    induction Hrtc as [x|x y0 z Hxy _ IH]; intros ws.
    - iIntros "Hws Hrf H". iApply ("H" $! ws with "[%] Hws Hrf"). reflexivity.
    - destruct x as [m0 rs0], y0 as [m1 rs1]. simpl in Hxy |- *.
      iIntros "Hws Hrf H".
      iApply (ewp_ev_node2 gen c Dr Dw q rs0 m0 m1 rs1 ws Hgen Hsub Hq Hxy
                with "Hws Hrf").
      iNext. iIntros (ws1) "%Hd1 Hws Hrf".
      iApply (IH ws1 with "Hws Hrf"). iIntros (ws2) "%Hd2 Hws Hrf".
      iApply ("H" $! ws2 with "[%] Hws Hrf"). by etrans.
  Qed.

End frame.

(* ====================================================================== *)
(** ** 3. THE SPLIT: a one-fetch run IS silent / read / silent *)

(** The trace-free fragment: a silent stretch of the language, with the byte
    map untouched. *)
Lemma erun_nil_walk (Dr Dw : gset register) (m : M unit) :
  forall t y t', erun Dr Dw m t = Some (y, t', []) ->
    rtc (esil2D Dr Dw) (m, sregs t) (Interface.Ret y, sregs t') /\
    mem t' = mem t /\ mdev t' = mdev t.
Proof.
  induction m as [y0 | T oc k IH]; intros t y t' Hm.
  - simpl in Hm. injection Hm as <- <-. split_and!; [apply rtc_refl|done|done].
  - destruct oc; simpl in Hm; try discriminate Hm;
      first
        [ (* RegRead *)
          case_decide as HD; [|discriminate Hm];
          destruct (IH _ _ _ _ Hm) as (Hr & Hmm & Hmd);
          (split_and!; [|exact Hmm|exact Hmd]);
          refine (rtc_l (esil2D Dr Dw) _
                    (k (register_lookup reg (sregs t)), sregs t) _ _ Hr);
          rewrite /esil2D /=; by case_decide
        | (* RegWrite *)
          case_decide as HD; [|discriminate Hm];
          destruct (IH _ _ _ _ Hm) as (Hr & Hmm & Hmd);
          (split_and!; [|exact Hmm|exact Hmd]);
          refine (rtc_l (esil2D Dr Dw) _
                    (k tt, register_set reg regval (sregs t)) _ _ Hr);
          rewrite /esil2D /=; by case_decide
        | (* MemRead: the trace is a cons, not [] *)
          destruct (dev_addr _); [discriminate Hm|];
          destruct (read_bytes _ _ _) as [w0|]; [|discriminate Hm];
          destruct (erun Dr Dw (k (inl (w0, None))) t) as [r0|];
          [destruct r0 as [[y0 t0'] es0]|]; discriminate Hm
        | (* GetCycleCount *)
          destruct (IH _ _ _ _ Hm) as (Hr & Hmm & Hmd);
          (split_and!; [|exact Hmm|exact Hmd]);
          refine (rtc_l (esil2D Dr Dw) _ (k 0%Z, sregs t) _ _ Hr);
          by rewrite /esil2D /=
        | (* every other silent node *)
          destruct (IH _ _ _ _ Hm) as (Hr & Hmm & Hmd);
          (split_and!; [|exact Hmm|exact Hmd]);
          refine (rtc_l (esil2D Dr Dw) _ (k tt, sregs t) _ _ Hr);
          by rewrite /esil2D /= ].
Qed.

(** THE SPLIT.  A run whose whole trace is ONE read decomposes into: a silent
    stretch, the read NODE (with its request, its continuation and the state
    it is reached at), and a silent stretch to the monad's [Ret].  Nothing
    but the read is a language event, which is why the funnel below can be
    stated with the fetch as its only obligation. *)
Lemma erun_split_read (Dr Dw : gset register) (m : M unit) (t : mstate)
    (y : unit) (t' : mstate) (ak : akinfo) (pa : Arch.pa) (n : N) :
  erun Dr Dw m t = Some (y, t', [WEread ak pa n]) ->
  exists (req : Interface.ReadReq.t n)
         (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
         (t1 : mstate) (w : bv (8 * n)),
    rtc (esil2D Dr Dw) (m, sregs t)
        (Interface.Next (Interface.MemRead n req) K, sregs t1) /\
    mem t1 = mem t /\ mdev t1 = mdev t /\
    Interface.ReadReq.pa req = pa /\
    classify (Interface.ReadReq.access_kind req) = ak /\
    dev_addr pa = false /\
    read_bytes (mem t) pa n = Some w /\
    rtc (esil2D Dr Dw) (K (inl (w, None)), sregs t1)
        (Interface.Ret y, sregs t') /\
    mem t' = mem t /\ mdev t' = mdev t.
Proof.
  revert t. induction m as [y0 | T oc k IH]; intros t Hm; [by simpl in Hm|].
  destruct oc; simpl in Hm; try discriminate Hm.
  (* --- the MemRead arm: the fetch itself --- *)
  all: try (match goal with
            | |- context[Interface.MemRead ?nn ?rq] =>
                destruct (dev_addr (Interface.ReadReq.pa rq)) eqn:Hdev;
                  [discriminate Hm|];
                destruct (read_bytes (mem t) (Interface.ReadReq.pa rq) nn)
                  as [w0|] eqn:Hrd; [|discriminate Hm];
                destruct (erun Dr Dw (k (inl (w0, None))) t) as [r0|] eqn:Htl;
                  [|discriminate Hm];
                destruct r0 as [[y1 t1] es1];
                injection Hm as <- <- Hak Hpa Hn Hes; subst es1; subst n;
                destruct (erun_nil_walk Dr Dw (k (inl (w0, None))) t y1 t1 Htl)
                  as (Hpost & Hmm & Hmd);
                rewrite Hpa in Hdev; rewrite Hpa in Hrd;
                exists rq, k, t, w0;
                split_and!; first [done | apply rtc_refl]
            end).
  (* --- every other arm is a register node or a silent node --- *)
  all: first
    [ (* RegRead *)
      case_decide as HD; [|discriminate Hm];
      destruct (IH _ _ Hm) as (req & K & t1 & w & Hpre & Hm1 & Hd1 & Hpa & Hak
                               & Hdev & Hrd & Hpost & Hmm & Hmd);
      exists req, K, t1, w; split_and!; try done;
      refine (rtc_l (esil2D Dr Dw) _
                (k (register_lookup reg (sregs t)), sregs t) _ _ Hpre);
      rewrite /esil2D /=; by case_decide
    | (* RegWrite *)
      case_decide as HD; [|discriminate Hm];
      destruct (IH _ _ Hm) as (req & K & t1 & w & Hpre & Hm1 & Hd1 & Hpa & Hak
                               & Hdev & Hrd & Hpost & Hmm & Hmd);
      exists req, K, t1, w; split_and!; try done;
      refine (rtc_l (esil2D Dr Dw) _
                (k tt, register_set reg regval (sregs t)) _ _ Hpre);
      rewrite /esil2D /=; by case_decide
    | (* GetCycleCount *)
      destruct (IH _ _ Hm) as (req & K & t1 & w & Hpre & Hm1 & Hd1 & Hpa & Hak
                               & Hdev & Hrd & Hpost & Hmm & Hmd);
      exists req, K, t1, w; split_and!; try done;
      refine (rtc_l (esil2D Dr Dw) _ (k 0%Z, sregs t) _ _ Hpre);
      by rewrite /esil2D /=
    | (* every other silent node *)
      destruct (IH _ _ Hm) as (req & K & t1 & w & Hpre & Hm1 & Hd1 & Hpa & Hak
                               & Hdev & Hrd & Hpost & Hmm & Hmd);
      exists req, K, t1, w; split_and!; try done;
      refine (rtc_l (esil2D Dr Dw) _ (k tt, sregs t) _ _ Hpre);
      by rewrite /esil2D /= ].
Qed.

(* ====================================================================== *)
(** ** 4. THE DERIVED RULE: ONE INSTRUCTION, ONE FETCH, NO OTHER EVENT *)

Section rule.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** The mid-cycle form: the run starts at an arbitrary monad [m] and ends at
      the instruction boundary.  The ONLY event obligation is the fetch, and
      it is discharged INSIDE the rule from the pinned text
      ([WeakEvLift.ewp_ev_fetch]): no callback, no [read_ok], no φ payment. *)
  Theorem ewp_ev_one_fetch (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac) (m : M unit) (t t' : mstate) (y : unit)
      (ak : akinfo) (pa : Arch.pa) (n : N) (w : bv (8 * n)) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    erun Dr Dw m t = Some (y, t', [WEread ak pa n]) ->
    read_bytes (mem t) pa n = Some w ->
    ak_coh ak = false -> ak_latest ak = false ->
    etext_word (pa_z pa) n w -∗
    ereg_fr c (sregs t) Dr q -∗
    hart_ws c ws -∗
    (* D3-2: the successor view is no longer NAMED — the two silent stretches
       around the fetch may carry PARM's [step_assign]/[step_if]/instruction
       start.  [ws_le] is all a client of this rule ever used it for. *)
    (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗
     ereg_fr c (sregs t') Dr q -∗ hart_ws c ws' -∗
     EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hrun Hw Hcoh Hlat.
    destruct (erun_split_read Dr Dw m t y t' ak pa n Hrun)
      as (req & K & t1 & w0 & Hpre & Hm1 & Hd1 & Hpa & Hak & Hdev & Hrd
          & Hpost & Hmm & Hmd).
    assert (Hww : w0 = w) by (rewrite Hw in Hrd; by injection Hrd).
    subst w0.
    iIntros "#Ht Hrf Hws H".
    (* ---- the silent stretch before the fetch ---- *)
    iApply (ewp_ev_walk gen c Dr Dw q (m, sregs t)
              (Interface.Next (Interface.MemRead n req) K, sregs t1) ws
              Hgen Hsub Hq Hpre with "Hws Hrf").
    simpl. iIntros (ws1) "%Hd1' Hws Hrf".
    (* ---- THE FETCH ---- *)
    iApply (ewp_ev_fetch gen c n req K w ws1 Hgen
              ltac:(by rewrite Hpa) ltac:(by rewrite Hak)
              ltac:(by rewrite Hak) with "[Ht] Hws").
    { by rewrite Hpa. }
    iNext. iIntros "Hws". rewrite Hpa Hak.
    (* ---- the silent stretch after it, and the boundary ---- *)
    iApply (ewp_ev_walk gen c Dr Dw q (K (inl (w, None)), sregs t1)
              (Interface.Ret y, sregs t')
              (efetch_ws ws1 (ak_sync ak) (pa_z pa) n)
              Hgen Hsub Hq Hpost with "Hws Hrf").
    simpl. iIntros (ws2) "%Hd2' Hws Hrf". iApply (ewp_ev_ret gen c y Hgen).
    iApply ("H" $! ws2 with "[%] Hrf Hws").
    etrans; [by apply ws_depmove_le|].
    etrans; [apply efetch_ws_le|by apply ws_depmove_le].
  Qed.

  (** THE FUNNEL TWIN, at the instruction boundary: [WeakFunnel.wwp_instr]'s
      shape with [WWP Loop] re-bound to [EWP (ELoop gen c)].  The certificate
      is owed for BOTH ticks — the clock branch is an ordinary register
      stretch here, so it costs nothing beyond having the clock cells in the
      footprint (B1, discharged locally). *)
  Theorem ewp_instr_pure (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac) (t : mstate) (tp : bool -> mstate)
      (ak : akinfo) (pa : Arch.pa) (n : N) (w : bv (8 * n)) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    (forall tick : bool,
       erun Dr Dw (riscv_step tick) t = Some (tt, tp tick, [WEread ak pa n])) ->
    read_bytes (mem t) pa n = Some w ->
    ak_coh ak = false -> ak_latest ak = false ->
    etext_word (pa_z pa) n w -∗
    ereg_fr c (sregs t) Dr q -∗
    hart_ws c ws -∗
    ▷ (∀ (tick : bool) (ws' : wstate), ⌜ws_le ws ws'⌝ -∗
         ereg_fr c (sregs (tp tick)) Dr q -∗
         hart_ws c ws' -∗
         EWP (ELoop gen c) @ ⊤) -∗
    EWP (ELoop gen c) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hcert Hw Hcoh Hlat.
    iIntros "#Ht Hrf Hws H". iApply (ewp_eloop gen c ws Hgen with "Hws").
    (* W2b condition 1: the boundary IS the reset point, so the fetch that
       follows runs at [instr_post ws]. *)
    iNext. iIntros (tick) "Hws".
    iApply (ewp_ev_one_fetch gen c Dr Dw q (riscv_step tick) t (tp tick) tt
              ak pa n w (instr_post ws) Hgen Hsub Hq (Hcert tick) Hw Hcoh Hlat
              with "Ht Hrf Hws").
    iIntros (ws') "%Hle Hrf Hws". iApply ("H" $! tick ws' with "[%] Hrf Hws").
    etrans; [apply instr_post_le|exact Hle].
  Qed.

End rule.

(* ====================================================================== *)
(** ** 5. THE LEAF-FACING PACKAGING (B2's adapter, as far as it goes)

    WHAT IS HERE: the TEXT bridge (complete — [winstr_bytes] serves
    [WeakFunnel.winstr] and [WeakLeafM.winstr_m] alike, both being
    [winstr_bytes] plus pure decode facts), the frame's peel/insensitivity
    adapters, and the [epure] → [erun] embedding.

    WHAT IS NOT, and is the next concrete item: the [mmode_config dq] ADAPTER
    ([mmode_config dq -∗ ereg_fr c rs Dcfg qcfg ∗ (ereg_fr … -∗ mmode_config
    dq)] for the config subset, with [qcfg] mapping [InstrBytes.hw_config]'s
    five registers to [DfracDiscarded] and [cur_privilege]/[mstatus]/
    [hart_state] to [DfracOwn dq]).  It is EXPRESSIBLE only because §2's frame
    is dfrac-indexed (header, finding 2); it needs [hw_config]'s unbundling
    and the value-agreement plumbing, and it is what [WeakLeafO.whart_run]
    ([= mmode_config ∗ wrunning]) will go through.  [WeakLeafO.leaf_hide]
    itself needs NO adapter: its [∀ ws, … ⌜ws_le ws ws'⌝ … hart_ws] shape is
    exactly the shape §6's leaf delivers, so it re-checks with [WWP Loop]
    re-bound and [c := cpu_id]. *)

Section pack.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE TEXT.  [WeakFunnel.winstr_bytes] — what every existing leaf holds,
      and what [WeakFunnel.winstr] wraps — IS [etext_word] at the fetch
      window: both are the big-op of [wlat_pointsto _ DfracDiscarded 0 _] over
      the four bytes, and the only difference is the address spelling
      ([pa_add] vs the log's [Z] keys), which [WeakBridge.acc_wf_byte]
      settles.  So the funnel's fetch obligation is discharged from the
      leaf's EXISTING resource, with no restatement. *)
  Lemma winstr_bytes_etext_word (pc : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 32) :
    winstr_bytes pc (F_Base w) -∗ etext_word (pa_z pc) 4 w.
  Proof.
    iIntros "#Hbs".
    iDestruct "Hbs" as "(%Hal & %Hacc & %Hram & Hb)".
    iDestruct "Hb" as (w0) "[%Hr #Hb]". destruct Hr as [<- Hrvc].
    rewrite /etext_word. iApply big_sepL_intro. iIntros "!>" (i j Hj).
    apply lookup_seq in Hj as [-> Hlt].
    assert (Hi : (0 + i)%nat = i) by lia. rewrite Hi.
    rewrite /etext -/(acc_addr pc i)
            -(acc_wf_byte pc 4 i Hacc ltac:(simpl; lia)).
    iDestruct (big_sepL_lookup _ (seq 0 4) i i with "Hb") as "H".
    { by apply lookup_seq_lt. }
    iExact "H".
  Qed.

  (** The [winstr] wrapper, for a caller that holds the funnel's own resource
      (the [F_Base] arm — the 4-aligned 32-bit instruction, which is the arm
      [WeakFetchEff] mirrors). *)
  Lemma winstr_etext_word (pc : SailStdpp.Values.mword 64) (i : instruction)
      (w : SailStdpp.Values.mword 32) :
    winstr pc false i -∗
    ∃ w' : SailStdpp.Values.mword 32, etext_word (pa_z pc) 4 w'.
  Proof.
    iIntros "[_ Hi]". iDestruct "Hi" as (r) "(%Hrvc & Hb & _)".
    destruct r as [e|w'|h|e].
    - iDestruct "Hb" as "(_ & _ & _ & Hb)".
      iDestruct "Hb" as (w0) "[%HF _]". done.
    - iExists w'. by iApply winstr_bytes_etext_word.
    - by simpl in Hrvc.
    - iDestruct "Hb" as "(_ & _ & _ & Hb)".
      iDestruct "Hb" as (w0) "[%HF _]". done.
  Qed.

  (** THE REGISTER ADAPTER.  A named points-to peels out of the frame and back
      in — which is how a leaf keeps stating [PC ↦ᵣ pc] (or any other cell it
      wants to name) while the rule consumes the whole frame. *)
  Lemma ereg_fr_peel c rs Dr q (r : register) :
    r ∈ Dr ->
    ereg_fr c rs Dr q ⊣⊢
      reg_pointsto_at c r (q r) (register_lookup r rs) ∗
      ereg_fr c rs (Dr ∖ {[r]}) q.
  Proof. intros Hr. by rewrite /ereg_fr (big_sepS_delete _ _ r Hr). Qed.

  (** ... and the frame is INSENSITIVE to registers outside it, which is what
      lets a client state the post-state with [set_reg]s it does not own. *)
  Lemma ereg_fr_set_ne c rs Dr q (r : register) (v : type_of_register r) :
    r ∉ Dr -> ereg_fr c (register_set r v rs) Dr q ⊣⊢ ereg_fr c rs Dr q.
  Proof.
    intros Hr. apply ereg_fr_ext. intros r' Hr'.
    assert (Hne : r' <> r) by (intros ->; done).
    exact (irrelevant_register_set r' r rs v (register_beq_false r' r Hne)).
  Qed.

End pack.

(** THE CERTIFICATE BRIDGE: [WeakEvExecEff]'s memory-free [epure] IS an
    [erun] with an empty trace, so the composition kit of that file (and every
    [epure] mirror written against it) feeds this file's rule unchanged. *)
Lemma epure_erun {X} (D : gset register) (m : M X) :
  forall t y t', epure D m t = Some (y, t') -> erun D D m t = Some (y, t', []).
Proof.
  induction m as [y0 | T oc k IH]; intros t y t' Hm.
  - simpl in Hm. by injection Hm as <- <-.
  - destruct oc; simpl in Hm |- *; try discriminate;
      try (exact (IH _ _ _ _ Hm));
      (case_decide; [|discriminate Hm]); exact (IH _ _ _ _ Hm).
Qed.

(* ====================================================================== *)
(** ** 6. THE DEMONSTRATION — a real boot-cone leaf, at the event tier *)

Import Defs.

(** *** 6a.  A REAL certificate fragment, through the kit.  The LUI leaf's
    post-fetch tail ([WeakEvExecEff] §6, the [execute]-then-[tick_pc] run of
    the GENERATED model at an arbitrary register bank) is an [erun] with an
    empty trace, by ONE application of [epure_erun].  This is the evidence
    that the §1 kit and the [epure] mirrors are the same interface. *)
Lemma erun_lui_tail (D : gset register) (rd : mword 5) (imm : mword 20)
    (s : mstate) :
  (forall n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D) ->
  (PC : register) ∈ D -> (nextPC : register) ∈ D ->
  erun D D (Defs.bind (execute (UTYPE (imm, Regidx rd, LUI)))
              (fun _ => tick_pc tt)) s
  = Some (tt,
          (let s1 := if Z.eqb (uint rd) 0 then s
                     else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                            (regval_into_reg (luival imm)) in
           set_reg s1 PC (register_lookup nextPC s1.(sregs))), []).
Proof.
  intros HD HPC HnPC.
  exact (epure_erun D _ s tt _ (epure_lui_tail D rd imm s HD HPC HnPC)).
Qed.

(** *** 6b.  THE LEAF.  [WeakLeafUtypeShift.wwp_lui_leaf] at the event tier:
    the SAME instruction, the SAME text resource, the SAME weak-memory
    interface, with [WWP Loop] re-bound to [EWP (ELoop gen c)].

    THE STATEMENT DELTA, item by item (this is the B2 answer, measured rather
    than guessed):

      - SURVIVES VERBATIM: [winstr_bytes pc (F_Base w)] (the text), [hart_ws
        c ws] and the [ws_le]-monotone successor view (the weak-memory
        interface), the [gen = 0] premise, and the conclusion modulo
        [WWP Loop ↦ EWP (ELoop gen c)].
      - REPLACED: [mmode_config dq ∗ pmpcfg_n ↦ᵣ{dq} pmpcfg0 ∗ PC ↦ᵣ pc ∗
        nextPC ↦ᵣ npc0 ∗ gpr_file m] become ONE [ereg_fr c (sregs t) Dr q].
        That is not a re-packaging of the same ownership: [mmode_config]'s
        [hw_config] half is PERSISTENT and its three cells are FRACTIONAL, so
        the frame HAD to become dfrac-indexed (header, finding 2); [gpr_file]
        is a [regfile]-indexed big-op with an x0 special case, which
        [ereg_fr] flattens into membership side conditions on [Dr].  A leaf
        that wants [PC ↦ᵣ pc] back peels it with [ereg_fr_peel] (§5).
      - ABSORBED INTO PREMISE (i): [pmp_allows_all], the two alignment facts,
        [uint rd <> 0], and all five decode premises ([Hdecf], the [D]-agree
        fact, [D (R_bool minstret_increment) = false], [goodb0], the
        [ext_decode] fact).  They are exactly the inputs
        [WeakFetchEff.wP_eff_of_leaf_base] consumes to build the
        whole-instruction run, so at the event tier they are consumed by the
        [erun] mirror rather than by the funnel.
      - ADDED: the footprint side conditions ([Dw ⊆ Dr], full ownership on
        [Dw]) and — the residual — premise (i) itself, the whole-instruction
        [erun] mirror the header's finding 1 explains.  [WeakEvWire.ewp_instr]
        removes [sig_seip]/[sig_meip] from [Dr] and is otherwise identical.
      - LATERS: one, on the continuation, exactly as in [wwp_cb]. *)
Section demo.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma ewp_lui_leaf_ev (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rd : mword 5) (imm : mword 20)
      (t : mstate) (tp : bool -> mstate) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    (* --- the fetch window, as [wwp_lui_leaf] has it --- *)
    read_bytes (mem t) pc 4 = Some w ->
    (* --- (i) THE WHOLE-INSTRUCTION CERTIFICATE, at the register-only
           trace the leaf's [exec_eff] certificate already carries --- *)
    (forall tick : bool,
       erun Dr Dw (riscv_step tick) t = Some (tt, tp tick, regonly_es true pc)) ->
    (* --- (ii) what the leaf's postcondition says about the result --- *)
    (forall tick : bool,
       register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) (sregs (tp tick))
         = regval_into_reg (luival imm)) ->
    (forall tick : bool,
       register_lookup PC (sregs (tp tick)) = add_vec_int pc 4) ->
    winstr_bytes pc (F_Base w) -∗
    ereg_fr c (sregs t) Dr q -∗
    hart_ws c ws -∗
    ▷ (∀ (tick : bool) (ws' : wstate),
         ⌜ws_le ws ws'⌝ -∗
         ⌜register_lookup (R_bitvector_64 (gpr_of_Z (uint rd)))
            (sregs (tp tick)) = regval_into_reg (luival imm)⌝ -∗
         ⌜register_lookup PC (sregs (tp tick)) = add_vec_int pc 4⌝ -∗
         ereg_fr c (sregs (tp tick)) Dr q -∗
         hart_ws c ws' -∗
         EWP (ELoop gen c) @ ⊤) -∗
    EWP (ELoop gen c) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hw Hcert Hrd Hpc.
    iIntros "#Hbs Hrf Hws H".
    iDestruct (winstr_bytes_etext_word pc w with "Hbs") as "#Ht".
    iApply (ewp_instr_pure gen c Dr Dw q t tp wak_plain pc 4 w ws
              Hgen Hsub Hq Hcert Hw eq_refl eq_refl with "Ht Hrf Hws").
    iNext. iIntros (tick ws') "%Hle Hrf Hws".
    iApply ("H" $! tick ws' with "[%] [%] [%] Hrf Hws").
    - exact Hle.
    - apply Hrd.
    - apply Hpc.
  Qed.

End demo.
