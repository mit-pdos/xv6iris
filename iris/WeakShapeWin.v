(** * WeakShapeWin.v — [gwpx], the VALUE-AND-WINDOW mode, and finding (O10)

    Stage C7.  Two things live here.

    §1  (O10) — THE FINDING, and it is the seventh instance of the
        over-quantified-∀ genre: [∀ b, sail_shaped (riscv_step b)] is
        REFUTABLE AGAIN, this time by the model's own A/D-bit update path.
        [rv64d.update_and_write_pte] issues an EXCLUSIVE read of the PTE and
        then, on the arm where the RE-READ entry needs no update, returns
        SUCCESSFULLY WITHOUT a conditional write — after which the
        instruction performs its ordinary data access, i.e. a [MemRead] (or a
        [MemWrite] at a different address) inside an open exclusive window,
        which [WeakSailLTS.amo_tail] forbids outright.  The leaves are
        machine-checked below; the reachability is a source argument of the
        same kind as (O4)'s, (O6)'s and (O9)'s.  See the section for the
        specified fix.

    §2  [gwpx Q P w m] — the mode stage C6 asked C7 for ("[gwalk] WITH A RET
        POSTCONDITION"), in the form the consumers actually forced:

          [Q : E → Prop]          the exception postcondition;
          [P : A → win → Prop]    the RETURN postcondition, over the value
                                  AND THE WINDOW THAT IS OPEN AT THE RETURN.

        THE WINDOW ARGUMENT OF [P] IS NOT A GENERALISATION FOR ITS OWN SAKE —
        it is what makes ONE fixpoint serve the whole kit.  [WeakShape.gwalk]
        is the instance [P := λ _ w, w = None] (the closed reading),
        [WeakShapeOverrides.gwalkx] is [P := λ _ _, True] (the abandoning
        reading) up to the [ExtraOutcome] arm, and the mode
        [rv64d.run_hart_active] needs is neither: "if [execute] returns an
        [ExecuteAs] redirection then no window is open AND the payload is
        [ast_wf]" — a JOINT value/window postcondition, which is exactly what
        lets the redirection arm call [execute] again while the abandoning
        arms ([execute_LOADRES]) still go through.  A [P] without the window
        argument cannot state it, and the [gwalkx]/[gsilent] split cannot
        either (the redirection arm is not silent).

        The [Interface.ExtraOutcome] arm follows [gwalk]'s KIT-SIDE
        STRENGTHENING ([False] under an open window, [Q e] with the window
        closed) rather than [gwalkx]'s [True]: it is what makes
        [gwpx_try_catch] able to hand the handler over at a CLOSED window,
        and every handler the model builds ([liftR], [catch_early_return])
        closes nothing.  As the durable note says: a kit may be strictly
        stronger than the specification where that buys compositionality —
        but say so at the arm.

    §3  the combinator kit, §4 the solver [gwx_solve], §5 the transfers
        ([gwalk] in, [gwalkx]/[sail_shaped] out) and the two bind rules that
        make the EXISTING 294-lemma tower reusable for every prefix:
        [gwpx_bind_walk] (prefix from `gshape`) and [gwpx_bind_pure] (prefix
        from [WeakShapeAst]'s [gpureP], i.e. the decoder postcondition).

    ------------------------------------------------------------------------
    §1  (O10): AN ABANDONED EXCLUSIVE WINDOW IS NOT THE END OF THE
        INSTRUCTION — [∀ b, sail_shaped (riscv_step b)] IS FALSE

    THE PATH, read off [model-xv6iris/rv64d.v]:

      rv64d.update_and_write_pte sv vpn pteAddr pte level access …
        match update_PTE_Bits pte access with
        | None   => returnM (Ok (None, ext_ptw))          (* no read at all *)
        | Some _ =>
            (Svadu ∧ menvcfg.ADUE = 1) ∨ (¬Svadu ∧ ¬Svade) ⇒
              read_pte_exclusive pteAddr pte_width >>= λ w,
              match w with
              | Err _ => returnM (Err (PTW_No_Access, ext_ptw))
              | Ok pte' =>                       (* pte' is ∀-QUANTIFIED *)
                  check_leaf_pte … pte' … >>= λ c,
                  match c with
                  | Err (e, x) => returnM (Err (e, x))
                  | Ok (_, _, x) =>
                      match update_PTE_Bits pte' access with
                      | None      => returnM (Ok (Some pte', x))   (* ←—— *)
                      | Some pte'' => write_pte_conditional …      (* closes *)

    [read_pte_exclusive] is [mem_read_priv (Load PageTableEntry) … (res :=
    true)], so [read_kind_of_flags false false true = Read_RISCV_reserved],
    which [WeakInterp.classify] maps to [AV_exclusive], i.e. [ak_latest =
    true] — the read OPENS a window ([sail_shaped]'s [MemRead] arm hands the
    continuation to [amo_tail]).  The marked arm then RETURNS
    [Ok (Some pte', …)], i.e. a SUCCESSFUL A/D update with NO conditional
    write; [translate_TLB_hit]/[translate_TLB_miss] treat that as success,
    [translate]/[translateAddr] return [Ok], and the [execute_*] clause goes
    on to do the instruction's OWN data access.  That access is a [MemRead]
    (a load, or an AMO's read) or a [MemWrite] at the DATA address, and
    [amo_tail]'s arms are [MemRead ↦ False] and "any [MemWrite] must be at
    the window's own [pa]/[n]".  Both leaves are machine-checked below.

    WHY THE ARM IS REACHED, in the ∀-quantified sense every shape predicate
    is stated in: [pte'] is the value of a [MemRead], which
    [sail_shaped]/[gwalk] quantify over UNIVERSALLY, so the walk must hold at
    every [pte'] — including one whose A/D bits are already set
    ([update_PTE_Bits pte' access = None]) and whose permissions pass
    [check_leaf_pte].  The enclosing gate is satisfiable at ordinary register
    states: [hartSupports Ext_Svadu = true] in this configuration
    ([rv64d.v]), [currentlyEnabled Ext_Svadu = hartSupports Ext_Svadu], and
    [menvcfg.ADUE] is a REGISTER, universally quantified by the [RegRead]
    arm.  (The per-IMAGE story is different — xv6 never sets [menvcfg.ADUE]
    — and that is exactly the shape of the fix.)

    THIS IS THE SAME GENRE AS (O2) AND (O4), NOT A NEW ONE.  (O2) found an
    exclusive READ with no conditional write and C2 fixed it by BRACKETING
    the abandoned window in [sail_mstep] — [silent_run … (Interface.Ret y,
    rs1)] — i.e. by assuming the abandoned tail is SILENT.  (O10) is the case
    where it is NOT: the tail of an abandoned PTE reservation is the rest of
    the instruction, memory accesses included.  So the bracket does not
    apply, the LTS is stuck, and the shape predicate is false.

    THE SPECIFIED FIX (the C2/C4 pattern, third time; NOT implemented in C7):

      (i)   [WeakSailLTS.sail_shaped]'s [MemRead] arm DROPS the window
            entirely: an exclusive read is shaped exactly like a plain one
            ([∀ w, sail_shaped (k …)]).  [amo_tail] then survives only as the
            hypothesis of [sail_mstep]'s FUSED rmw arm and of
            [WeakSailComplete.amo_reach] — it stops being a claim [sail_shaped]
            makes.
      (ii)  [sail_mstep]'s BARE exclusive-read arm becomes ONE STEP instead of
            a bracket, exactly as C4's standalone conditional write did.  C2
            rejected the one-step form because "it leaves the hart in window
            mode, where [sail_shaped] is not preserved"; with (i) there is no
            window mode, so [sail_shaped_res_step] and [tail_complete] go
            through unchanged.  The machine only GAINS behaviours — the safe
            direction.
      (iii) the ⇐ cost goes where (O2)'s and (O4)'s went: into
            [WeakSailLTS2.pf_solo_f]/[fused_blk], the target-indexed
            run-local side condition, whose reading stays "every exclusive
            access of the block is part of a fused rmw".  Per-image discharge:
            xv6 runs with [menvcfg.ADUE = 0], so the A/D update path is never
            taken and every exclusive access in a kernel block is an AMO.

      AND THE KIT COLLAPSES: with (i), [gwalk]'s window index disappears,
      [gwalkx] becomes [gwalk], the exclusive-window obligation stage C6
      recorded ("EVERY memory instruction pays it") EVAPORATES, and the
      memory cone loses its hardest semantic obligation (the read/write
      address-and-width agreement across [checked_mem_read] /
      [checked_mem_write]).  [gwpx] survives unchanged — its [P]'s window
      argument simply becomes constantly [None].

    UNTIL THAT LANDS, the twelve residual facts of
    [WeakShapeTop.riscv_step_shaped_residue] are FALSE (all twelve: every one
    of them translates, and translation is where the abandoned window is),
    and so is the capstones' [∀ b, sail_shaped (riscv_step b)] premise.  C7
    therefore does NOT swap it: swapping a false premise for another false
    premise buys nothing and hides the vacuity. *)

From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
From xv6iris Require Import WeakSailComplete WeakShape WeakShapeOverrides.
From xv6iris Require Import WeakShapeOverrides2 WeakShapeAst.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

Local Ltac mred :=
  cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind].

(* ====================================================================== *)
(** ** 1. (O10) at its leaves *)

(** LEAF ONE: inside an open exclusive window a RAM read of ANY kind is
    refuted — [amo_tail]'s [Interface.MemRead] arm is [False].  This is what
    the instruction's own load runs into after the PTE reservation was
    abandoned. *)
Lemma amo_tail_read_ram_False pa n rk addr width meta (k : _ → M unit) :
  rk = Read_plain ∨ rk = Read_RISCV_reserved ∨ rk = Read_RISCV_reserved_acquire →
  amo_tail pa n (Defs.bind (read_ram rk (Physaddr addr) width meta) k) → False.
Proof.
  intros Hrk. destruct Hrk as [->|[->| ->]];
    cbv [read_ram]; mred; cbv [Defs.sail_mem_read]; mred; done.
Qed.

(** …and the same in the kit's vocabulary, which is what a compositional
    proof of the memory cone actually hits. *)
Lemma gwalkx_read_ram_in_window_False {B} pa n rk addr width meta (k : _ → M B) :
  rk = Read_plain ∨ rk = Read_RISCV_reserved ∨ rk = Read_RISCV_reserved_acquire →
  gwalkx (Some (pa, n))
         (Defs.bind (read_ram rk (Physaddr addr) width meta) k) → False.
Proof.
  intros Hrk. destruct Hrk as [->|[->| ->]];
    cbv [read_ram]; mred; cbv [Defs.sail_mem_read]; mred; done.
Qed.

(** LEAF TWO: a window may be ABANDONED at a return — that is C2's (O2) fix
    ([amo_tail]'s [Interface.Ret] arm is [True]) — so nothing at
    [update_and_write_pte]'s exit refutes the abandonment locally.  The
    refutation only appears at the NEXT memory event, i.e. after the value
    has been carried through [translate] into the [execute_*] clause.  That
    is why (O10) could not be seen from the leaves alone and needed the
    whole path. *)
Lemma amo_tail_returnm_abandon pa n (x : unit) :
  amo_tail pa n (Defs.returnm x).
Proof. done. Qed.

(** LEAF THREE: the read that opens the window really is exclusive.
    [read_pte_exclusive] passes [(aq, rl, res) = (false, false, true)], and
    that is [Read_RISCV_reserved], whose [WeakInterp.classify] has
    [ak_latest = true] ([WeakShape.classify_excl_normal]). *)
Lemma read_kind_of_flags_res : read_kind_of_flags false false true
                               = Defs.returnm Read_RISCV_reserved.
Proof. reflexivity. Qed.

(** LEAF FOUR, THE COMPOSITE, and it is (O10)'s shape in one statement: an
    exclusive RAM read whose continuation issues ANOTHER RAM read is not
    walkable — the window is still open at the second node.  Between the two
    reads sits, in the model, the whole of [check_leaf_pte], the abandoning
    return of [update_and_write_pte], [translate], [translateAddr] and the
    [execute_*] clause's own prologue; none of that closes a window. *)
Lemma gwalk_excl_read_then_read_False {B} addr width meta
    rk2 addr2 width2 meta2 (k : _ → M B)
    (v : bv (8 * Z.to_N width)) :
  rk2 = Read_plain ∨ rk2 = Read_RISCV_reserved ∨ rk2 = Read_RISCV_reserved_acquire →
  dev_addr addr = false →
  gwalk None
    (Defs.bind (read_ram Read_RISCV_reserved (Physaddr addr) width meta)
       (λ _, Defs.bind (read_ram rk2 (Physaddr addr2) width2 meta2) k)) →
  False.
Proof.
  intros Hrk2 Hd. cbv [read_ram]; mred; cbv [Defs.sail_mem_read]; mred.
  simpl. rewrite Hd. intros [_ Hk]. specialize (Hk v). revert Hk. mred.
  destruct Hrk2 as [->|[->| ->]];
    cbv [read_ram]; mred; cbv [Defs.sail_mem_read]; mred; done.
Qed.

(* ====================================================================== *)
(** ** 2. [gwpx]: the value-and-window mode *)

Section Wpx.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gwpx (Q : E → Prop) (P : A → win → Prop) (w : win) (m : mon)
    {struct m} : Prop :=
  match m with
  | Interface.Ret x => P x w
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead n req => λ k,
           match w with
           | Some _ => False
           | None =>
               if dev_addr (Interface.ReadReq.pa req)
               then ∀ v : bv (8 * n), gwpx Q P None (k (inl (v, None)))
               else
                 ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
                 (if ak_latest (classify (Interface.ReadReq.access_kind req))
                  then ∀ v : bv (8 * n),
                         gwpx Q P (Some (Interface.ReadReq.pa req, n))
                              (k (inl (v, None)))
                  else ∀ v : bv (8 * n), gwpx Q P None (k (inl (v, None))))
           end
       | Interface.MemWrite n' req' => λ k,
           match w with
           | Some (pa, n) =>
               dev_addr (Interface.WriteReq.pa req') = false ∧
               Interface.WriteReq.pa req' = pa ∧ n' = n ∧ n' ≠ 0%N ∧
               ak_latest (classify (Interface.WriteReq.access_kind req')) = true ∧
               gwpx Q P None (k (inl None))
           | None =>
               (if dev_addr (Interface.WriteReq.pa req') then True
                else n' ≠ 0%N) ∧
               gwpx Q P None (k (inl None))
           end
       | Interface.Barrier _ => λ k,
           match w with
           | Some _ => False
           | None => ∀ r, gwpx Q P None (k r)
           end
       | Interface.ExtraOutcome e => λ _,
           (* the KIT-SIDE strengthening [gwalk] carries, not a claim of the
              specification: [False] under an open window is what lets
              [gwpx_try_catch] hand the handler over at a closed one. *)
           match w with Some _ => False | None => Q e end
       | _ => λ k, ∀ r, gwpx Q P w (k r)
       end) k
  end.

End Wpx.

Arguments gwpx {E A} Q P w m.

(** The two postconditions that make [gwpx] the modes the kit already had.
    [gwalk] is an EXACT instance; [gwalkx] differs only at the [ExtraOutcome]
    arm, and only in the direction that costs nothing (§5). *)
Lemma gwalk_gwpx {E A} (Q : E → Prop) w (m : Defs.monad E A) :
  (∀ e, Q e) → gwalk w m → gwpx Q (λ _ w', w' = None) w m.
Proof.
  intros HQ. revert w. induction m as [x|T oc k IH]; intros w Hm.
  { by destruct w. }
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. apply HQ.
Qed.

Lemma gwpx_gwalk {E A} (Q : E → Prop) w (m : Defs.monad E A) :
  gwpx Q (λ _ w', w' = None) w m → gwalk w m.
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm.
  { by destruct w. }
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - by destruct w as [[pa0 n0]|].
Qed.

Lemma gwpx_gwalkx {E A} (Q : E → Prop) (P : A → win → Prop) w
    (m : Defs.monad E A) :
  gwpx Q P w m → gwalkx w m.
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm; [done|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - done.
Qed.

(** …hence the specification, for the [M unit] instance. *)
Lemma gwpx_shaped (Q : exception → Prop) (P : unit → win → Prop) (m : M unit) :
  gwpx Q P None m → sail_shaped m.
Proof. intros H. by apply gwalkx_shaped, (gwpx_gwalkx Q P). Qed.

Lemma gwpx_mono {E A} (Q Q' : E → Prop) (P P' : A → win → Prop) w
    (m : Defs.monad E A) :
  (∀ e, Q e → Q' e) → (∀ x w', P x w' → P' x w') →
  gwpx Q P w m → gwpx Q' P' w m.
Proof.
  intros HQ HP. revert w. induction m as [x|T oc k IH]; intros w Hm.
  { by apply HP. }
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. by apply HQ.
Qed.

(** A silent prefix satisfies every mode, at every window — the leaf the
    solver falls back on. *)
Lemma gsilent_gwpx {E A} (Q : E → Prop) (P : A → win → Prop) w
    (m : Defs.monad E A) :
  (∀ x w', P x w') → gsilent m → gwpx Q P w m.
Proof.
  intros HP. revert w. induction m as [x|T oc k IH]; intros w Hm; [by apply HP|].
  destruct oc; simpl in Hm |- *; try done; try (intros r; by apply IH).
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(* ====================================================================== *)
(** [exres_wf]: the postcondition [rv64d.run_hart_active] consumes.  It is
    the ONE thing the redirection arm needs — "if [execute] hands back an
    [ExecuteAs], its payload is a well-formed instruction" — and nothing
    else about an [ExecutionResult] is ever asked.  Note that it says
    NOTHING about the window, deliberately: the window half of the
    postcondition is supplied separately by [P]'s second argument, so that
    the abandoning clauses ([execute_LOADRES]) stay covered. *)
Definition exres_wf (r : ExecutionResult) : Prop :=
  match r with ExecuteAs i => ast_wf i | _ => True end.

(** …and the sweep's own postcondition: [exres_wf] AND the window closed.
    The two are separate facts and the sweep proves both — every
    [ExecutionResult]-returning function OUTSIDE the memory cone is
    window-free — but [execute] itself only exports the weaker
    [exres_wf_win] below, because its memory clauses ([execute_LOADRES] and
    the abandoning arms of [execute_AMO]) DO leave a window open.  That
    asymmetry is the whole reason [P] takes the window. *)
Definition exres_ok (r : ExecutionResult) (w : win) : Prop :=
  exres_wf r ∧ w = None.

(** What [rv64d.run_hart_active] actually needs of [execute]: a redirection
    carries a well-formed instruction AND arrives with no window open (so the
    arm may call [execute] again); any other result is unconstrained (so an
    abandoning clause is covered). *)
Definition exres_wf_win (r : ExecutionResult) (w : win) : Prop :=
  match r with ExecuteAs i => ast_wf i ∧ w = None | _ => True end.

Lemma exres_ok_wf_win r w : exres_ok r w → exres_wf_win r w.
Proof. intros [Hr ->]. by destruct r. Qed.

Lemma exres_wf_wf_win r : exres_wf r → exres_wf_win r None.
Proof. destruct r; cbn; auto. Qed.

(** The sweep's mode, in one notation. *)
Notation gwx m := (gwpx (λ _ : exception, True) exres_ok None m).

Lemma gwx_wfwin (m : M ExecutionResult) :
  gwx m → gwpx (λ _ : exception, True) exres_wf_win None m.
Proof. apply gwpx_mono; [done|apply exres_ok_wf_win]. Qed.

(** ** 3. The combinator kit *)

(** THE BIND, in its general form: the postcondition of [m] — value AND
    window — is the hypothesis of [k]'s obligation, AT THAT WINDOW.  Every
    other bind rule of this file, and [WeakShape.gwalk_bind] /
    [WeakShapeOverrides.gwalkx_bind] / [gwalkx_bind_silent], is this lemma
    with a particular [P]. *)
Lemma gwpx_bind {E A B} (Q : E → Prop) (P : A → win → Prop)
    (P' : B → win → Prop) w (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwpx Q P w m → (∀ x w', P x w' → gwpx Q P' w' (k x)) →
  gwpx Q P' w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - by destruct w as [[pa0 n0]|].
Qed.

(** THE FORM THE SOLVER RUNS ON — and the form that makes the EXISTING
    294-lemma tower reusable for every prefix.  The prefix obligation is
    [gwpx] AT THE CLOSED POSTCONDITION, which an atomic call discharges out
    of `gshape` in one step ([gwalk_gwpx]) and a compound prefix (an [if], a
    [match] with an [early_return] arm, a [liftR]) is walked into.  Stating
    it with a bare [gwalk] prefix instead would be WRONG inside a
    [catch_early_return]: there an [early_return r] node carries a value the
    postcondition constrains, and [gwalk] says nothing about it. *)
Lemma gwpx_bind_closed {E A B} (Q : E → Prop) (P' : B → win → Prop) w
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwpx Q (λ _ w', w' = None) w m → (∀ x, gwpx Q P' None (k x)) →
  gwpx Q P' w (Defs.bind m k).
Proof.
  intros Hm Hk. apply (gwpx_bind Q (λ _ w', w' = None)); [done|].
  by intros x w' ->.
Qed.

Lemma gwpx_bind0_closed {E A} (Q : E → Prop) (P' : A → win → Prop) w
    (m : Defs.monad E unit) (n : Defs.monad E A) :
  gwpx Q (λ _ w', w' = None) w m → gwpx Q P' None n →
  gwpx Q P' w (Defs.bind0 m n).
Proof. intros ??. rewrite /Defs.bind0. by apply gwpx_bind_closed. Qed.

(** …and the ONE value-carrying prefix rule the sweep needs, for the
    [ExecutionResult]-valued calls whose result the continuation matches on. *)
Lemma gwpx_bind_exres {E B} (Q : E → Prop) (P' : B → win → Prop) w
    (m : Defs.monad E ExecutionResult) (k : ExecutionResult → Defs.monad E B) :
  gwpx Q exres_ok w m → (∀ x, exres_wf x → gwpx Q P' None (k x)) →
  gwpx Q P' w (Defs.bind m k).
Proof.
  intros Hm Hk. apply (gwpx_bind Q exres_ok); [done|].
  by intros x w' [Hx ->]; apply Hk.
Qed.

(** …and the form the DECODER POSTCONDITION feeds ([WeakShapeAst.gpureP]):
    a prefix that issues no memory event, raises whatever it likes, and
    whose returned values satisfy [Pm]. *)
Lemma gwpx_bind_pure {E A B} (Q : E → Prop) (Pm : A → Prop)
    (P' : B → win → Prop) (m : Defs.monad E A) (k : A → Defs.monad E B) :
  (∀ e, Q e) → gpureP Pm m → (∀ x, Pm x → gwpx Q P' None (k x)) →
  gwpx Q P' None (Defs.bind m k).
Proof.
  intros HQ. revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done; try (by apply HQ);
    try (destruct ty; simpl in Hm |- *; intros r; by apply IH).
Qed.

(** THE CONSUMERS: a [gwpx] fact crossing back into an ordinary shape
    obligation.  [gwalkx] is the one the peel needs (an [execute] clause may
    abandon a window); [gwalk] the one an escape-free site needs. *)
Lemma gwalkx_bind_wpx {E A B} (Q : E → Prop) (P : A → win → Prop) w
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwpx Q P w m → (∀ x w', P x w' → gwalkx w' (k x)) →
  gwalkx w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - done.
Qed.

Lemma gwalk_bind_wpx {E A B} (Q : E → Prop) (P : A → win → Prop) w
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwpx Q P w m → (∀ x w', P x w' → gwalk w' (k x)) → gwalk w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - by destruct w as [[pa0 n0]|].
Qed.

(** THE HANDLER RULE.  The [ExtraOutcome] arm is [False] under an open
    window, so the handler is only ever entered at a CLOSED one — which is
    exactly what makes this rule usable at [liftR] and
    [catch_early_return], whose handlers close nothing. *)
Lemma gwpx_try_catch {A E1 E2} (Q1 : E1 → Prop) (Q2 : E2 → Prop)
    (P : A → win → Prop) w (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  (∀ e, Q1 e → gwpx Q2 P None (h e)) →
  gwpx Q1 P w m → gwpx Q2 P w (Defs.try_catch m h).
Proof.
  intros Hh. revert w. induction m as [x|T oc k IH]; intros w Hm; [done|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. by apply Hh.
Qed.

(** The leaves. *)
Lemma gwpx_ret {E A} (Q : E → Prop) (P : A → win → Prop) w (x : A) :
  P x w → gwpx Q P w (Interface.Ret x).
Proof. done. Qed.

Lemma gwpx_returnm {E A} (Q : E → Prop) (P : A → win → Prop) w (x : A) :
  P x w → gwpx Q P w (Defs.returnm (E := E) x).
Proof. done. Qed.

Lemma gwpx_throw {E A} (Q : E → Prop) (P : A → win → Prop) (e : E) :
  Q e → gwpx Q P None (Defs.throw (A := A) e).
Proof. done. Qed.

Lemma gwpx_early_return {A R E} (Q : R + E → Prop) (P : A → win → Prop) (r : R) :
  Q (inl r) → gwpx Q P None (Defs.early_return (A := A) (E := E) r).
Proof. done. Qed.

Lemma gwpx_fail {E A} (Q : E → Prop) (P : A → win → Prop) w msg :
  gwpx Q P w (Defs.fail (A := A) (E := E) msg).
Proof. rewrite /Defs.fail /=. by intros []. Qed.

Lemma gwpx_exit {E A} (Q : E → Prop) (P : A → win → Prop) w :
  gwpx Q P w (Defs.exit (A := A) (E := E) tt).
Proof. apply gwpx_fail. Qed.

Lemma gwpx_assert_exp' {E} (Q : E → Prop) (b : bool)
    (P : (b = true) → win → Prop) w msg :
  (∀ h w', P h w') → gwpx Q P w (Defs.assert_exp' (E := E) b msg).
Proof.
  intros HP. rewrite /Defs.assert_exp'. destruct b; [apply HP|apply gwpx_fail].
Qed.

Lemma gwpx_assert_exp {E} (Q : E → Prop) (P : unit → win → Prop) w b msg :
  (∀ w', P tt w') → gwpx Q P w (Defs.assert_exp (E := E) b msg).
Proof.
  intros HP. rewrite /Defs.assert_exp. destruct b; [apply HP|apply gwpx_fail].
Qed.

(** [liftR] and [catch_early_return], the model's only two handlers. *)
Lemma gwpx_liftR {A R E} (Q : R + E → Prop) (P : A → win → Prop) w
    (m : Defs.monad E A) :
  (∀ e, Q (inr e)) → gwpx (λ _ : E, True) P w m →
  gwpx Q P w (Defs.liftR (R := R) m).
Proof.
  intros HQ Hm. rewrite /Defs.liftR. apply (gwpx_try_catch (λ _, True)); [|done].
  intros e _. by apply gwpx_throw.
Qed.

Lemma gwpx_catch_early_return {A E} (Q : E → Prop) (P : A → win → Prop) w
    (m : Defs.monadR A E A) :
  gwpx (λ ea, match ea with inl a => P a None | inr e => Q e end) P w m →
  gwpx Q P w (Defs.catch_early_return m).
Proof.
  intros Hm. rewrite /Defs.catch_early_return.
  apply (gwpx_try_catch
           (λ ea, match ea with inl a => P a None | inr e => Q e end) Q P);
    [|done].
  intros [a|e] He; [by apply gwpx_returnm|by apply gwpx_throw].
Qed.

Lemma gwpx_try_catchR {A R E} (Q : R + E → Prop) (P : A → win → Prop) w
    (m : Defs.monadR R E A) (h : E → Defs.monadR R E A) :
  (∀ e, gwpx Q P None (h e)) →
  gwpx (λ ea, match ea with inl r => Q (inl r) | inr _ => True end) P w m →
  gwpx Q P w (Defs.try_catchR m h).
Proof.
  intros Hh Hm. rewrite /Defs.try_catchR.
  apply (gwpx_try_catch
           (λ ea, match ea with inl r => Q (inl r) | inr _ => True end) Q P);
    [|done].
  intros [r|e] He; [by apply gwpx_throw|by apply Hh].
Qed.

(** The boolean short-circuits and the structural loops: the LEFT operand /
    the loop body may open no window that escapes it, so their obligation is
    the tower's [gwalk None]. *)
Lemma gwpx_and_boolM {E} (Q : E → Prop) (P : bool → win → Prop) w
    (l r : Defs.monad E bool) :
  gwpx Q (λ _ w', w' = None) w l → gwpx Q P None r → P false None →
  gwpx Q P w (Defs.and_boolM l r).
Proof.
  intros Hl Hr HP. rewrite /Defs.and_boolM.
  apply gwpx_bind_closed; [done|]. by intros [|].
Qed.

Lemma gwpx_or_boolM {E} (Q : E → Prop) (P : bool → win → Prop) w
    (l r : Defs.monad E bool) :
  gwpx Q (λ _ w', w' = None) w l → gwpx Q P None r → P true None →
  gwpx Q P w (Defs.or_boolM l r).
Proof.
  intros Hl Hr HP. rewrite /Defs.or_boolM.
  apply gwpx_bind_closed; [done|]. by intros [|].
Qed.

Lemma gwpx_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (Q : E → Prop) (P : T n → win → Prop) (x : Defs.monad E (T m)) :
  gwpx Q (λ _ w', w' = None) None x → (∀ v, P v None) →
  gwpx Q P None (Defs.autocast_m (n := n) x).
Proof.
  intros Hx HP. rewrite /Defs.autocast_m.
  apply gwpx_bind_closed; [done|]. intros v. by apply gwpx_returnm.
Qed.

(** The structural loops appear only as bind PREFIXES in the [execute_*]
    clauses, where the CLOSED postcondition is all that is needed and
    `gshape` supplies it through [gwalk_gwpx].  A tail-position loop would
    need a loop invariant in the [P] position; no site asks for one. *)
Lemma gwpx_foreachM_closed {E a Vars} (Q : E → Prop)
    (l : list a) (vars : Vars) (body : a → Vars → Defs.monad E Vars) :
  (∀ e, Q e) → (∀ x v, gwalk None (body x v)) →
  gwpx Q (λ _ w', w' = None) None (Defs.foreachM l vars body).
Proof.
  intros HQ Hb. apply gwalk_gwpx; [done|]. by apply gwalk_foreachM.
Qed.

(* ====================================================================== *)
(** ** 4. [gwx_solve] — the solver, under the (O8) discipline

    Same three rules as [gw_solve]: the LEAF IS GATED on the goal being
    atomic (a leaf tactic runs at every node, not only at leaves), the
    hint-database lookup goes first and is premise-free, and the model's
    constants stay OPAQUE to the database (a `discriminated` DB prunes by
    head constant only if it cannot delta-unfold them).

    ONE THING IS DIFFERENT, and it is the point of the mode: at a [bind] the
    PREFIX obligation is [gwalk None], which is exactly what the 294-lemma
    tower proves — so the prefix is discharged by [gw_solve] and only the
    CONTINUATION is walked in this mode.  That is what keeps a [gwpx] sweep
    the size of the clause bodies rather than the size of their cones.

    The postcondition side-goals ([P x w] / [Q e]) are left to `gwpost`,
    which the consumer populates ([WeakShapeExec]'s [exres_wf]). *)


Create HintDb gwpost discriminated.
#[export] Hint Constants Opaque : gwpost.

(** …and the database of the sweep's own conclusions, so that a TAIL call to
    an already-proven [ExecutionResult]-returning function is one
    premise-free lookup ([doCSR] in [execute_CSRReg], [trap] in
    [execute_ECALL], …).  Prefix calls do not go here: they are
    value-irrelevant and the 294-lemma `gshape` tower already covers them. *)
Create HintDb gwexec discriminated.
#[export] Hint Constants Opaque : gwexec.

(** The PURE [ExecutionResult] producers — the ~54 compressed expansions —
    are closed by computation: every [ExecuteAs] payload they build has a
    LITERAL width. *)
(** ONE STEP OF THE PURE DRIVER.  A [match] on a VARIABLE is destructed
    first (Sail's pure clauses dispatch on their own arguments); only if no
    occurrence has a variable scrutinee is a computed one taken (an [if] over
    a [generic_eq]).  Taking them in the other order would [destruct] the
    [ExecutionResult] a clause returns and leave an [ExecuteAs ?i] goal with
    nothing known about [?i]. *)
Ltac ew_dstep :=
  cbn beta iota;
  match goal with
  | |- context [match ?x with _ => _ end] => is_var x; destruct x
  | |- context [match ?x with _ => _ end] => destruct x
  end.

Ltac ew_solve :=
  first
    [ exact I
    | solve [ simpl; first [ exact I | lia ] ]
    | solve [ repeat ew_dstep; simpl; first [ exact I | lia ] ] ].

(** [∀ e, Q e] where [Q] is the SUM postcondition a [catch_early_return]
    installs does NOT reduce until the sum is destructed, so [by intros]
    leaves a stuck [match] and every rule carrying that premise silently
    falls through.  (It cost an hour: the decoder rule in [WeakShapeExec]
    fell through to the [gwalk] route, which walks the decoder happily and
    DROPS its postcondition.) *)
Ltac qtriv :=
  first [ solve [by intros]
        | solve [intros e; destruct e; first [exact I | reflexivity | done]] ].

Ltac gwx_wf :=
  first [ exact I | assumption | solve [eauto 3 with gwpost]
        | solve [ simpl; first [ exact I | lia ] ]
        | solve [ repeat ew_dstep; simpl;
                  first [ exact I | lia | solve [eauto 2 with gwpost] ] ] ].

Ltac gwx_val :=
  first [ exact I | reflexivity | assumption
        | apply exres_wf_wf_win; solve [gwx_wf]
        | cbv [exres_ok exres_wf_win];
          first [ exact I | split; [solve [gwx_wf]|reflexivity]
                | solve [gwx_wf] ]
        | solve [gwx_wf] ].

Ltac gwx_step :=
  match goal with
  (* THE PREFIX'S TYPE DECIDES THE RULE, and it is the only place the sweep
     needs to look at a type: an [ExecutionResult]-valued prefix is a call
     whose VALUE the continuation matches on ([jump_to] in [execute_JALR],
     [doCSR] in [execute_CSRReg]), so its postcondition has to travel; every
     other prefix is value-irrelevant and the `gshape` tower covers it. *)
  | |- gwpx _ _ _ (@Defs.bind ExecutionResult _ _ _ _) => apply gwpx_bind_exres
  | |- gwpx _ _ _ (Defs.bind _ _) => apply gwpx_bind_closed
  | |- gwpx _ _ _ (Defs.bind0 _ _) => apply gwpx_bind0_closed
  | |- gwpx _ _ _ (Defs.try_catch _ _) => eapply gwpx_try_catch
  | |- gwpx _ _ _ (Defs.liftR _) => apply gwpx_liftR; [qtriv|]
  | |- gwpx _ _ _ (Defs.catch_early_return _) => apply gwpx_catch_early_return
  | |- gwpx _ _ _ (Defs.try_catchR _ _) => apply gwpx_try_catchR
  | |- gwpx _ _ _ (Defs.and_boolM _ _) =>
      apply gwpx_and_boolM; [| |solve [gwx_val]]
  | |- gwpx _ _ _ (Defs.or_boolM _ _) =>
      apply gwpx_or_boolM; [| |solve [gwx_val]]
  | |- gwpx _ _ _ (Defs.autocast_m _) =>
      apply gwpx_autocast_m; [|solve [gwx_val]]
  | |- gwpx _ _ _ (if ?b then _ else _) => destruct b
  | |- gwpx _ _ _ (match ?x with _ => _ end) => destruct x
  | |- gwpx _ _ _ (match ?x with _ => _ end _) => destruct x
  | |- gwpx _ _ _ (match ?x with _ => _ end _ _) => destruct x
  end.

Ltac gwx_atomic :=
  lazymatch goal with
  | |- gwpx _ _ _ (Defs.bind _ _) => fail
  | |- gwpx _ _ _ (Defs.bind0 _ _) => fail
  | |- gwpx _ _ _ (Defs.try_catch _ _) => fail
  | |- gwpx _ _ _ (Defs.liftR _) => fail
  | |- gwpx _ _ _ (Defs.catch_early_return _) => fail
  | |- gwpx _ _ _ (Defs.try_catchR _ _) => fail
  | |- gwpx _ _ _ (Defs.and_boolM _ _) => fail
  | |- gwpx _ _ _ (Defs.or_boolM _ _) => fail
  | |- gwpx _ _ _ (Defs.autocast_m _) => fail
  | |- gwpx _ _ _ (if _ then _ else _) => fail
  | |- gwpx _ _ _ (match _ with _ => _ end) => fail
  | |- gwpx _ _ _ (match _ with _ => _ end _) => fail
  | |- gwpx _ _ _ (match _ with _ => _ end _ _) => fail
  | _ => idtac
  end.

(** A goal whose postcondition is the CLOSED one is just a [gwalk] goal, and
    the 294-lemma tower is what proves those — so try that route first, at
    every node.  It costs nothing where it does not apply: [P] fails to
    unify syntactically, and the [∀ e, Q e] premise fails immediately inside
    a [catch_early_return] (where an [early_return] node DOES carry a
    constrained value), both before [gw_solve] is ever entered. *)
Ltac gwx_closed :=
  apply gwalk_gwpx; [qtriv | solve [gw_solve]].

Ltac gwx_leaf :=
  first
    [ exact I | assumption
    | gwx_closed
    | gwx_atomic;
      first
        [ solve [eauto 1 with gwexec nocore]
        (* the same conclusion, WEAKENED to the window-permissive
           postcondition [execute] itself exports *)
        | apply gwx_wfwin; solve [eauto 1 with gwexec nocore]
        | apply gwpx_fail | apply gwpx_exit
        | apply gwpx_ret; solve [gwx_val]
        | apply gwpx_returnm; solve [gwx_val]
        | apply gwpx_throw; solve [gwx_val]
        | apply gwpx_early_return; solve [gwx_val]
        | apply gwpx_assert_exp'; solve [gwx_val]
        | apply gwpx_assert_exp; solve [gwx_val]
        (* THE COMMON LEAF, AND IT GOES THROUGH THE TOWER: an atomic call in
           bind-prefix position, at the closed postcondition, out of `gshape`
           in one premise-free lookup. *)
        | apply gwalk_gwpx; [qtriv|solve [gw_solve]]
        | apply gsilent_gwpx; [solve [gwx_val] | solve [gsl_leaf]]
        | solve [gwx_val] ] ].

Ltac gwx_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gwx_leaf]
    | gwx_step ].
