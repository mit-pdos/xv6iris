(** * WeakShapeMem.v — THE MEMORY CONE'S SHAPE LEMMAS (stage C8)

    [WeakShapeGen01..15.v] prove [gwalk] for the 294 monadic definitions of
    [Riscv.rv64d] whose cone touches NEITHER of the model's two memory leaves
    ([read_ram]/[write_ram]) NOR one of its three opaque monadic axioms.  THIS
    file is the rest: the 51-function residue, minus what
    [WeakShapeOverrides2] already did ([_rec_pt_walk]/[pt_walk]) and minus the
    eleven [execute_*] clauses (which take their [0 < width] from the decoder
    postcondition and live in [WeakShapeExec]).  With it, stage C8 can close
    [riscv_step_shaped_ax].

    ------------------------------------------------------------------------
    WHAT (O10)'s FIX REMOVED, AND WHY THIS FILE IS SMALL.

    Through stage C7 [gwalk] carried a WINDOW index and an exclusive read
    OPENED it, so a memory access owed, on top of its own shape, a
    cross-function agreement: the exclusive read's [(pa, n)] had to equal the
    closing conditional write's, which needed [pmaCheck] answering
    [CannotSplit], [split_misaligned] returning [N = 1], an [untilMT]
    unfolding at [N = 1] and [add_vec_int … 0] reasoning — and it needed all
    of that in a VALUE mode the [gwalk] tower does not have.  Stage C8's
    (O10) fix deleted the index: an exclusive read is walked exactly like a
    plain read, a conditional write exactly like a plain write.  What is left
    at a memory node is

      [MemRead ]  [ak_coh (classify …) = false]   off device addresses
      [MemWrite]  [n' ≠ 0%N]                      off device addresses

    i.e. NOTHING on the read side that the [read_kind] does not decide, and
    on the write side ONLY the width.  So this whole cone is width-only, and
    the file's obligations are exactly:

    (a) THE READ KIND.  [read_ram] is unwalkable at exactly ONE of its seven
        kinds, [Read_ifetch] — it emits [AK_ifetch], whose [classify] has
        [ak_coh = true].  Two of the other six ([Read_RISCV_acquire],
        [Read_RISCV_strong_acquire]) are [internal_error] nodes, which the
        walk crosses vacuously since (O9); the remaining four are
        [AK_explicit]/[AK_arch] with [ak_coh = false].  §1's
        [gwalk_read_ram_any]/[_solo] take [rk ≠ Read_ifetch] as a hypothesis,
        and §3 discharges it at the ONE call site ([checked_mem_read]) out of
        [read_kind_of_flags]'s postcondition — that function's eight arms
        produce four kinds and four [internal_error]s, and [Read_ifetch] is
        not among them.

    (b) THE WIDTH, [0 < width], ON THE WRITE SIDE ONLY.  It travels
        [checked_mem_write] → [mem_write_value*] → [write_pte_conditional] /
        [translate_and_write_value] → [vmem_write_addr] → [vmem_write], and
        is consumed at the [MemWrite] node through
        [WeakShapeOverrides2.gpost_split_misaligned] ([0 < width →
        0 < split_width]).  Every lemma that needs it says so; the eleven
        [execute_*] clauses get it from [WeakShapeAst.ast_wf].  TWO PLACES
        NEED MORE THAN A SUBSTITUTION, and both are inside [vmem_write_addr],
        whose accesses go out at DERIVED widths:

          - [access_width = if do_split_access then in_page_bytes else width],
            so a write's width can be [in_page_bytes], the FIRST component of
            what [split_on_page_boundary] returned.  §6's
            [gpost_split_on_page_boundary] is the missing fact
            ([0 < width → 0 < in_page_bytes]); on the split path it is
            [0 < 8 - uint (addr[2:0])], i.e. [Operators_mwords.uint_range],
            and that is the only arithmetic in this file.
          - the page-crossing arm writes [next_page_bytes] bytes and is
            guarded by [do_split_access], whose own definition
            ([and_boolM _ (returnm (next_page_bytes >? 0))]) is where
            [0 < next_page_bytes] comes from.  §1's [gwalk_bind_and_boolM]
            peels that [and_boolM] WITHOUT a value mode, by leaving the RIGHT
            operand's [bind] intact so that the bound boolean stays the
            syntactic [Z.gtb next_page_bytes 0] and an ordinary [destruct]
            recovers the fact.  (A [gpost] of the left operand would need
            [gpost] lemmas for a cone the [gwalk] tower does not cover —
            finding (O7).)

        NO OTHER SIDE CONDITION IS USED ANYWHERE IN THIS FILE.  In particular
        [update_and_write_pte] needs none: its conditional write goes out at
        [pte_width = if sv_width =? 32 then 4 else 8], a literal.

    (c) THE THREE AXIOM FACTS.  [rv64d] declares [load_reservation],
        [cancel_reservation] and [plat_term_write] as [Axiom]s of monad type,
        so no shape fact about them is provable or refutable.  §2 holds
        [rv64d_axiom_shapes], the [Record] (NOT [Axiom]s — so nothing here
        enters [Print Assumptions]) that states what must be assumed, and its
        [gw_*]/[gsilent_*] corollaries.  IT MOVED HERE FROM [WeakShapeTop.v]
        together with [gw_htif_store]/[gw_mmio_write], because the cone
        CONSUMES it: [checked_mem_write] calls [mmio_write] → [htif_store] →
        [plat_term_write], and [vmem_read_addr] calls [load_reservation].
        [WeakShapeTop] re-exports the record by [Require Import]ing this file.

    ------------------------------------------------------------------------
    LAYERING (each layer needs only the one below it, plus the tower):

      §1  kit: the two memory leaves at an arbitrary kind, the value-fact
          consumers ([gwalk_bind_postQ], [gwalk_bind_bind],
          [gwalk_bind_and_boolM]) and the sweep tactic [gwm_solve];
      §2  the axiom record, [htif_store], [mmio_write];
      §3  [checked_mem_read] + its wrappers → [read_pte], [read_pte_exclusive];
      §4  [checked_mem_write] + its wrappers → [write_pte_conditional];
      §5  the page-table layer: [check_leaf_pte], [pt_walk],
          [update_and_write_pte], [translate_TLB_hit]/[_miss], [translate],
          [translateAddr];
      §6  the access layer: [translate_and_read_value]/[_write_value],
          [vmem_read_addr]/[vmem_write_addr], [vmem_read]/[vmem_write],
          [process_clean_inval];
      §7  the fetch layer: [fetch_bytes], [rvfi_fetch], [fetch];
      §8  the SEVEN functions of §6 that return (or carry) an
          [ExecutionResult], again in [WeakShapeWin]'s VALUE mode — what
          [WeakShapeExec]'s eleven clauses consume on their fault paths.
          It is cheap for the reason (O7)'s corollary gives: [gwp]'s bind
          rule takes plain [gwalk] for the PREFIX, so §§3–7 discharge every
          prefix and only those seven are re-walked.

    TACTIC DISCIPLINE — finding (O8) applies verbatim.  [gw_solve] runs its
    LEAF at every node, so every alternative added to the leaf is paid once
    per node of every proof; [gwm_leaf] therefore keeps the [gw_atomic] gate
    and adds exactly two alternatives.  The two big functions
    ([checked_mem_read], [checked_mem_write]) get a HAND-STRUCTURED script —
    stage C5 measured the generic solver exploding at one step inside the
    misaligned-split [untilMT] body — which peels [catch_early_return], the
    [check_pma]/[split_misaligned]/[read_kind_of_flags] binds and the loop
    explicitly and runs the solver only on the loop body.  The OTHER
    recurring device is cheaper and used everywhere: when a callee's width
    hypothesis is discharged by a fact already in context, [pose proof] the
    SPECIALISED instance before running the solver, so that the leaf can
    close it with a premise-free hypothesis lookup instead of a search. *)

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
From xv6iris Require Import WeakShapeOverrides2 WeakShapeAst WeakShapeWin.
From xv6iris Require Import WeakShapeGen01 WeakShapeGen02 WeakShapeGen03
  WeakShapeGen04 WeakShapeGen05 WeakShapeGen06 WeakShapeGen07 WeakShapeGen08
  WeakShapeGen09 WeakShapeGen10 WeakShapeGen11 WeakShapeGen12 WeakShapeGen13
  WeakShapeGen14 WeakShapeGen15.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(** A failing tactic over a Sail term prints the whole term with the error,
    and the [checked_mem_*] goals are tens of thousands of nodes wide. *)
Local Set Printing Depth 40.

(** [Defs.returnR] is [Defs.returnm] at the early-return monad, and the
    generated code uses it at EVERY join of a fault match.  [gw_solve]'s own
    [cbn] list omits it (a fresh variable at the join costs the sweep
    nothing), but a hand script that has to keep a value's IDENTITY across the
    join must reduce it — otherwise the next [intros] names the join's fresh
    variable rather than the pair the script is after. *)
Local Ltac mred :=
  cbn [Defs.bind Defs.bind0 Defs.returnm Defs.returnR returnM
       Interface.iMon_bind].

(* ====================================================================== *)
(** ** 1. Kit: the memory leaves at an arbitrary kind, and three consumers *)

(** *** 1a. [read_ram] AT ANY KIND BUT [Read_ifetch]

    The mirror of [WeakShapeOverrides2.gwalk_write_ram_any].  Since (O10)'s
    fix the read arm constrains only [ak_coh], which the KIND decides. *)
Lemma gwalk_read_ram_any {B} rk addr width meta (k : _ → M B) :
  rk ≠ Read_ifetch →
  (∀ r, gwalk (k r)) →
  gwalk (Defs.bind (read_ram rk (Physaddr addr) width meta) k).
Proof.
  intros Hrk Hk. cbv [read_ram]. destruct rk;
    first
      [ exfalso; by apply Hrk
      | (mred; cbv [Defs.sail_mem_read]; mred;
         apply gwalk_MemRead_plain; [done|intros v; mred; apply Hk])
      | exact I ].
Qed.

Lemma gwalk_read_ram_solo rk addr width meta :
  rk ≠ Read_ifetch → gwalk (read_ram rk (Physaddr addr) width meta).
Proof.
  intros Hrk. cbv [read_ram]. destruct rk;
    first
      [ exfalso; by apply Hrk
      | (mred; cbv [Defs.sail_mem_read]; mred;
         apply gwalk_MemRead_plain; [done|intros v; mred; apply gwalk_ret])
      | exact I ].
Qed.

(** *** 1b. Value facts crossing into a shape obligation

    [WeakShapeOverrides2.gwalk_bind_post] takes the THROW-FREE [gpost0].  The
    memory cone's prefixes are not throw-free — every one of them runs under
    a [liftR], whose handler re-throws, and [read_kind_of_flags]'s four
    [internal_error] arms are throws outright.  The generalisation is free:
    since (O9) [gwalk] asks NOTHING of a throw's continuation, so the
    exception postcondition [Q] is simply unused. *)
Lemma gwalk_bind_postQ {E A B} (Q : E → Prop) (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpost Q P m → (∀ x, P x → gwalk (k x)) → gwalk (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(** [liftR] with BOTH postconditions carried.  [WeakShapeOverrides2.gpost_liftR]
    demands a throw-free argument; this form lets a throw through into the
    [inr] half of the sum, which is what [read_kind_of_flags] needs. *)
Lemma gpost_liftR_any {A R E} (Q1 : E → Prop) (Q : R + E → Prop) (P : A → Prop)
    (m : Defs.monad E A) :
  (∀ e, Q1 e → Q (inr e)) → gpost Q1 P m → gpost Q P (Defs.liftR (R := R) m).
Proof. intros HQ. apply gpost_try_catch. intros e He. by apply HQ. Qed.

(** A [bind] whose PREFIX is itself a [bind] — stated at the walk level
    rather than as an associativity EQUATION, because the equation needs
    functional extensionality (an axiom this tree does not use) and the walk
    does not. *)
Lemma gwalk_bind_bind {E A B C} (m : Defs.monad E A) (f : A → Defs.monad E B)
    (g : B → Defs.monad E C) :
  gwalk m → (∀ x, gwalk (Defs.bind (f x) g)) →
  gwalk (Defs.bind (Defs.bind m f) g).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|intros v; by apply IH].
  - destruct Hm as [Hn Hm]. split; [done|by apply IH].
  - done.
Qed.

(** …and the instance that matters: an [and_boolM] whose bound boolean the
    CONTINUATION has to know something about. *)
Lemma gwalk_bind_and_boolM {E B} (l r : Defs.monad E bool)
    (k : bool → Defs.monad E B) :
  gwalk l → gwalk (Defs.bind r k) → gwalk (k false) →
  gwalk (Defs.bind (Defs.and_boolM l r) k).
Proof.
  intros Hl Hr Hf. rewrite /Defs.and_boolM.
  apply gwalk_bind_bind; [done|]. by intros [|].
Qed.

(** *** 1c. The sweep tactic

    [gw_solve] plus the two memory leaves, BEHIND THE [gw_atomic] GATE
    (finding (O8): a leaf tactic runs at every node, and [read_ram] /
    [write_ram] are transparent, so an ungated [apply] of either would
    delta-unfold two large terms at every [bind] of every proof).  The side
    conditions are discharged by [assumption] out of the enclosing proof's
    context — [rk ≠ Read_ifetch] and [0 < split_width] respectively. *)
Ltac gwm_leaf :=
  first
    [ gw_leaf
    | gw_atomic;
      first [ apply gwalk_read_ram_solo; assumption
            | apply gwalk_write_ram_solo; assumption ] ].

Ltac gwm_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gwm_leaf]
    | gw_step ].

(* ====================================================================== *)
(** ** 2. The three opaque monadic axioms, and the HTIF store path

    MOVED HERE FROM [WeakShapeTop.v] (stage C8), because §4 CONSUMES it:
    [checked_mem_write] calls [mmio_write] on every MMIO-writable address.

    (O5) [rv64d] declares [load_reservation], [cancel_reservation] and
    [plat_term_write] as [Axiom]s of monad type, and all three are reachable
    from [try_step] ([vmem_read_addr], [execute_STORECON], [htif_store]).  An
    opaque constant of monad type has no shape: nothing about it is provable
    OR refutable.  [rv64d_axiom_shapes] is the honest statement of what must
    be assumed instead — a [Record], NOT a set of [Axiom]s, so that the
    capstones' [Print Assumptions] stays at the five rv64d axioms it already
    reports.  [gquiet] (not merely [gwalk]) is the right strength: these are
    extern hooks that touch no memory and raise nothing. *)
Record rv64d_axiom_shapes : Prop := {
  ax_load_reservation :
    ∀ (a : Values.mword (if 64 =? 32 then 34 else 64)%Z) (n : Z),
      gquiet (load_reservation a n);
  ax_cancel_reservation : ∀ u, gquiet (cancel_reservation u);
  ax_plat_term_write : ∀ (b : Values.mword 8), gquiet (plat_term_write b);
}.

(** …and what they buy at the leaves, in the sweep's own vocabulary. *)
Lemma gw_load_reservation (H : rv64d_axiom_shapes) a n :
  gwalk (load_reservation a n).
Proof. by apply gwalk_quiet, (ax_load_reservation H). Qed.

Lemma gw_cancel_reservation (H : rv64d_axiom_shapes) u :
  gwalk (cancel_reservation u).
Proof. by apply gwalk_quiet, (ax_cancel_reservation H). Qed.

Lemma gw_plat_term_write (H : rv64d_axiom_shapes) b :
  gwalk (plat_term_write b).
Proof. by apply gwalk_quiet, (ax_plat_term_write H). Qed.

(** The [gsilent] forms, for a caller that needs the stronger mode. *)
Lemma gsilent_cancel_reservation (H : rv64d_axiom_shapes) u :
  gsilent (cancel_reservation u).
Proof. by apply gquiet_gsilent, (ax_cancel_reservation H). Qed.

Lemma gsilent_load_reservation (H : rv64d_axiom_shapes) a n :
  gsilent (load_reservation a n).
Proof. by apply gquiet_gsilent, (ax_load_reservation H). Qed.

Lemma gsilent_plat_term_write (H : rv64d_axiom_shapes) b :
  gsilent (plat_term_write b).
Proof. by apply gquiet_gsilent, (ax_plat_term_write H). Qed.

(** [htif_store] is [plat_term_write]'s single call site and [mmio_write] is
    [htif_store]'s only caller, so the record is the whole of what they need
    — every other leaf of theirs is in the generated tower. *)
Lemma gw_htif_store (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwalk (@htif_store a0 a1 a2).
Proof.
  pose proof (gw_plat_term_write H) as Hterm.
  intros; destruct a0; cbv [htif_store]; gw_solve.
Qed.

Lemma gw_mmio_write (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwalk (@mmio_write a0 a1 a2).
Proof.
  pose proof (gw_htif_store H) as Hh.
  intros; cbv [mmio_write]; gw_solve.
Qed.

(* ====================================================================== *)
(** ** 3. THE READ SIDE

    No width obligation anywhere: since (O10)'s fix the [MemRead] arm asks
    only [ak_coh = false], which the [read_kind] decides.  The one thing that
    has to travel is [rk ≠ Read_ifetch]. *)

(** [read_kind_of_flags]'s eight arms produce four kinds and four
    [internal_error]s, and [Read_ifetch] is not among them.  Stated through
    the [liftR] that [checked_mem_read] wraps the call in, so the four throws
    land in the [inr] half of the early-return sum where the exception
    postcondition is [True]. *)
Lemma gpost_liftR_read_kind_of_flags {R} (aq rl res : bool) :
  gpost (λ _ : R + exception, True) (λ rk, rk ≠ Read_ifetch)
        (Defs.liftR (read_kind_of_flags aq rl res)).
Proof.
  destruct aq, rl, res; cbv [read_kind_of_flags internal_error];
    first
      [ apply gpost_liftR; apply gpost_returnm; discriminate
      | apply (gpost_liftR_any (λ _ : exception, True));
        [done|apply gpost_throw; exact I] ].
Qed.

(** THE BIG ONE, HAND-STRUCTURED (finding (O8)/stage C5): peel
    [catch_early_return], the [check_pma] bind, the [split_misaligned] bind,
    the [read_kind_of_flags] bind and the [untilMT] explicitly, and run the
    solver only on the loop's condition and body. *)
Lemma gw_checked_mem_read :
  ∀ access pbmt priv paddr width aq rl res meta,
    gwalk (@checked_mem_read access pbmt priv paddr width aq rl res meta).
Proof.
  intros. cbv [checked_mem_read].
  apply gwalk_catch_early_return.
  apply gwalk_bind; [apply gwalk_liftR, gw_check_pma_with_pmp_priority|].
  intros [ai|e]; mred; [|exact I].
  apply gwalk_bind; [apply gwalk_liftR, gw_split_misaligned|].
  intros [N sw]; mred.
  destruct (misaligned_order N) as [[first last] step]; mred.
  apply (gwalk_bind_postQ (λ _, True) (λ rk, rk ≠ Read_ifetch));
    [apply gpost_liftR_read_kind_of_flags|].
  intros rk Hrk.
  apply gwalk_bind; [|intros [[d f] i]; by gwm_solve].
  apply gwalk_untilMT; [intros v; by gwm_solve|].
  (* THE LOOP BODY, likewise by hand, and EVERY CALLEE NAMED.  [gw_solve]'s
     leaf begins with an UNGATED [exact I], i.e. a [whnf] of the goal, and
     inside this body the arguments are no longer variables but concrete
     address/width arithmetic — so a computing callee ([mmio_read],
     [within_mmio_readable]) gets fully evaluated once per visit.  MEASURED
     in this proof: [by gwm_solve] on [gwalk (liftR (mmio_read …))] is
     216 s and on [within_mmio_readable] 76 s, against ~0 s for the named
     [apply]; the whole loop body under the generic solver was 288 s and its
     [checked_mem_write] twin did not finish at all.  This is finding (O8)
     one layer down: the gate is on the DATABASE LOOKUP, not on [exact I]. *)
  intros [[d f] i]. mred.
  apply gwalk_bind; [apply gwalk_liftR, gwalk_assert_exp'|]. intros _. mred.
  apply gwalk_bind; [apply gwalk_liftR, gw_pmpCheck|].
  intros [e|]; mred; [exact I|].
  apply gwalk_bind; [apply gwalk_liftR, gw_within_mmio_readable|].
  intros [|]; mred.
  - (* MMIO *)
    apply gwalk_bind.
    + apply gwalk_bind; [apply gwalk_liftR, gw_mmio_read|].
      intros [md|e]; mred; exact I.
    + intros sd. mred. by destruct (Z.eqb i last).
  - (* RAM: the read leaf, at the kind [read_kind_of_flags] produced *)
    apply gwalk_bind.
    + apply gwalk_bind; [by apply gwalk_liftR, gwalk_read_ram_solo|].
      intros [rd mt]. exact I.
    + intros sd. mred. by destruct (Z.eqb i last).
Qed.
#[export] Hint Resolve gw_checked_mem_read : gshape.

Lemma gw_mem_read_priv_meta :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8,
    gwalk (@mem_read_priv_meta a0 a1 a2 a3 a4 a5 a6 a7 a8).
Proof. intros; cbv [mem_read_priv_meta]; gwm_solve. Qed.
#[export] Hint Resolve gw_mem_read_priv_meta : gshape.

Lemma gw_mem_read_priv :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7, gwalk (@mem_read_priv a0 a1 a2 a3 a4 a5 a6 a7).
Proof. intros; cbv [mem_read_priv]; gwm_solve. Qed.
#[export] Hint Resolve gw_mem_read_priv : gshape.

Lemma gw_mem_read :
  ∀ a0 a1 a2 a3 a4 a5 a6, gwalk (@mem_read a0 a1 a2 a3 a4 a5 a6).
Proof. intros; cbv [mem_read]; gwm_solve. Qed.
#[export] Hint Resolve gw_mem_read : gshape.

Lemma gw_read_pte : ∀ a0 a1, gwalk (@read_pte a0 a1).
Proof. intros; cbv [read_pte]; gwm_solve. Qed.
#[export] Hint Resolve gw_read_pte : gshape.

Lemma gw_read_pte_exclusive : ∀ a0 a1, gwalk (@read_pte_exclusive a0 a1).
Proof. intros; cbv [read_pte_exclusive]; gwm_solve. Qed.
#[export] Hint Resolve gw_read_pte_exclusive : gshape.

(* ====================================================================== *)
(** ** 4. THE WRITE SIDE

    Here [0 < width] is real, and it is the ONLY side condition: it is what
    [WeakShapeOverrides2.gpost_split_misaligned] turns into the
    [0 < split_width] the [MemWrite] node demands. *)

Lemma gw_checked_mem_write (H : rv64d_axiom_shapes) :
  ∀ paddr width data access pbmt priv meta aq rl con,
    (0 < width)%Z →
    gwalk (@checked_mem_write paddr width data access pbmt priv meta aq rl con).
Proof.
  pose proof (gw_mmio_write H) as Hmmio.
  intros paddr width data access pbmt priv meta aq rl con Hw.
  cbv [checked_mem_write].
  apply gwalk_catch_early_return.
  apply gwalk_bind; [apply gwalk_liftR, gw_check_pma_with_pmp_priority|].
  intros [ai|e]; mred; [|exact I].
  apply (gwalk_bind_postQ (λ _, True) (λ p, (0 < snd p)%Z));
    [by apply gpost_liftR_split_misaligned|].
  intros [N sw] Hsw. cbn [snd] in Hsw. mred.
  destruct (misaligned_order N) as [[first last] step]; mred.
  apply gwalk_bind; [apply gwalk_liftR, gw_write_kind_of_flags|]. intros wk.
  apply gwalk_bind; [|intros [[f i] ws]; by gwm_solve].
  apply gwalk_untilMT; [intros v; by gwm_solve|].
  intros [[f i] ws]. mred.
  apply gwalk_bind; [apply gwalk_liftR, gwalk_assert_exp'|]. intros _. mred.
  apply gwalk_bind; [apply gwalk_liftR, gw_pmpCheck|].
  intros [e|]; mred; [exact I|].
  apply gwalk_bind; [apply gwalk_liftR, gw_within_mmio_writable|].
  intros [|]; mred.
  - (* MMIO: [mmio_write], hence the axiom record *)
    apply gwalk_bind.
    + apply gwalk_bind; [apply gwalk_liftR, Hmmio|].
      intros [v|e]; mred; exact I.
    + intros ws'. mred. by destruct (Z.eqb i last).
  - (* RAM: the write leaf, at the width [split_misaligned] returned *)
    apply gwalk_bind.
    + apply gwalk_bind; [by apply gwalk_liftR, gwalk_write_ram_solo|].
      intros v. exact I.
    + intros ws'. mred. by destruct (Z.eqb i last).
Qed.

Lemma gw_mem_write_value_priv_meta (H : rv64d_axiom_shapes) :
  ∀ paddr width value access pbmt priv meta aq rl con,
    (0 < width)%Z →
    gwalk (@mem_write_value_priv_meta paddr width value access pbmt priv meta
             aq rl con).
Proof.
  intros paddr width value access pbmt priv meta aq rl con Hw.
  pose proof (fun a b c d e f g h i =>
                gw_checked_mem_write H a width b c d e f g h i Hw) as Hc.
  cbv [mem_write_value_priv_meta]; gwm_solve.
Qed.

Lemma gw_mem_write_value_priv (H : rv64d_axiom_shapes) :
  ∀ paddr width value priv access pbmt aq rl con,
    (0 < width)%Z →
    gwalk (@mem_write_value_priv paddr width value priv access pbmt aq rl con).
Proof.
  intros. cbv [mem_write_value_priv].
  apply gw_mem_write_value_priv_meta; assumption.
Qed.

Lemma gw_mem_write_value_meta (H : rv64d_axiom_shapes) :
  ∀ paddr width value access pbmt meta aq rl con,
    (0 < width)%Z →
    gwalk (@mem_write_value_meta paddr width value access pbmt meta aq rl con).
Proof.
  intros paddr width value access pbmt meta aq rl con Hw.
  pose proof (fun a b c d e f g h i =>
                gw_mem_write_value_priv_meta H a width b c d e f g h i Hw)
    as Hc.
  cbv [mem_write_value_meta]; gwm_solve.
Qed.

Lemma gw_mem_write_value (H : rv64d_axiom_shapes) :
  ∀ paddr width value access pbmt aq rl con,
    (0 < width)%Z →
    gwalk (@mem_write_value paddr width value access pbmt aq rl con).
Proof.
  intros. cbv [mem_write_value]. apply gw_mem_write_value_meta; assumption.
Qed.

(** [write_pte_conditional]'s width is [pte_size], and its ONE call site
    ([update_and_write_pte]) passes the literal [if sv_width =? 32 then 4
    else 8] — so the hypothesis is discharged there without any decoder
    input.  The second form is the one the call site's leaf matches. *)
Lemma gw_write_pte_conditional (H : rv64d_axiom_shapes) :
  ∀ paddr pte_size pte,
    (0 < pte_size)%Z → gwalk (@write_pte_conditional paddr pte_size pte).
Proof.
  intros. cbv [write_pte_conditional]. apply gw_mem_write_value_priv; assumption.
Qed.

Lemma gw_write_pte_conditional_lit (H : rv64d_axiom_shapes) :
  ∀ paddr (sv_width : Z) pte,
    gwalk (@write_pte_conditional paddr
             (if Z.eqb sv_width 32 then 4 else 8) pte).
Proof.
  intros. apply gw_write_pte_conditional; [done|by destruct (Z.eqb sv_width 32)].
Qed.

(* ====================================================================== *)
(** ** 5. THE PAGE-TABLE LAYER *)

(** No memory of its own: [check_leaf_pte]'s callees ([pte_is_invalid],
    [check_PTE_permission], [currentlyEnabled],
    [page_based_mem_type_forwards]) are all in the generated tower.  It is in
    the residue only because [tools/gen_shape.py]'s [is_monadic] test used to
    miss a wrapped signature (fixed in C5; the function stays in the
    generator's [SKIP] set so the built shards remain byte-identical). *)
Lemma gw_check_leaf_pte :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9,
    gwalk (@check_leaf_pte a0 a1 a2 a3 a4 a5 a6 a7 a8 a9).
Proof. intros; cbv [check_leaf_pte]; gwm_solve. Qed.
#[export] Hint Resolve gw_check_leaf_pte : gshape.

(** [_rec_pt_walk] is the [Acc]-fuelled walker; [WeakShapeOverrides2] §3 did
    it modulo its three monadic callees, all of which are now available. *)
Lemma gw_pt_walk_full :
  ∀ a0 a1 a2 a3 a4 a5 a6 level a8 a9,
    gwalk (@pt_walk a0 a1 a2 a3 a4 a5 a6 level a8 a9).
Proof.
  apply gw_pt_walk;
    solve [ intros; apply gw_read_pte
          | intros; apply gw_pte_is_invalid
          | intros; apply gw_check_leaf_pte ].
Qed.
#[export] Hint Resolve gw_pt_walk_full : gshape.

Lemma gw_update_and_write_pte (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9,
    gwalk (@update_and_write_pte a0 a1 a2 a3 a4 a5 a6 a7 a8 a9).
Proof.
  pose proof (gw_write_pte_conditional_lit H) as Hwp.
  intros; cbv [update_and_write_pte]; gwm_solve.
Qed.

Lemma gw_translate_TLB_hit (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9,
    gwalk (@translate_TLB_hit a0 a1 a2 a3 a4 a5 a6 a7 a8 a9).
Proof.
  pose proof (gw_update_and_write_pte H) as Hu.
  intros; cbv [translate_TLB_hit]; gwm_solve.
Qed.

Lemma gw_translate_TLB_miss (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8,
    gwalk (@translate_TLB_miss a0 a1 a2 a3 a4 a5 a6 a7 a8).
Proof.
  pose proof (gw_update_and_write_pte H) as Hu.
  intros; cbv [translate_TLB_miss]; gwm_solve.
Qed.

Lemma gw_translate (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8,
    gwalk (@translate a0 a1 a2 a3 a4 a5 a6 a7 a8).
Proof.
  pose proof (gw_translate_TLB_hit H) as Hh.
  pose proof (gw_translate_TLB_miss H) as Hm.
  intros; cbv [translate]; gwm_solve.
Qed.

Lemma gw_translateAddr (H : rv64d_axiom_shapes) :
  ∀ a0 a1, gwalk (@translateAddr a0 a1).
Proof.
  pose proof (gw_translate H) as Ht.
  intros; cbv [translateAddr]; gwm_solve.
Qed.

(* ====================================================================== *)
(** ** 6. THE ACCESS LAYER *)

Lemma gw_translate_and_read_value (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5, gwalk (@translate_and_read_value a0 a1 a2 a3 a4 a5).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; cbv [translate_and_read_value]; gwm_solve.
Qed.

Lemma gw_translate_and_write_value (H : rv64d_axiom_shapes) :
  ∀ vaddr width value access aq rl res,
    (0 < width)%Z →
    gwalk (@translate_and_write_value vaddr width value access aq rl res).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros vaddr width value access aq rl res Hw.
  pose proof (fun a b c d e f g =>
                gw_mem_write_value H a width b c d e f g Hw) as Hmv.
  cbv [translate_and_write_value]; gwm_solve.
Qed.

(** THE FIRST-COMPONENT POSTCONDITION OF [split_on_page_boundary], and the
    only arithmetic in this file.  On the intra-page path the answer is
    [(width, 0)]; on the split path it is [(8 - uint addr[2:0], …)], and
    [Operators_mwords.uint_range] bounds the subtrahend by 7. *)
Lemma gpost_split_on_page_boundary {n} (addr : Values.mword n) (width : Z) :
  (0 < width)%Z →
  gpost0 (λ p, (0 < fst p)%Z) (split_on_page_boundary addr width).
Proof.
  intros Hw. cbv [split_on_page_boundary].
  destruct (eq_vec _ _); [by apply gpost_returnm|].
  apply (gpost_bind _ (λ _, True)); [apply gpost_assert_exp'|].
  intros _ _. apply gpost_returnm. cbn [fst].
  match goal with
  | |- context [uint ?x] => pose proof (uint_range x) as Hr
  end.
  cbv [Values.pow2 Values.pow] in Hr |- *. cbn in Hr. lia.
Qed.

(** [vmem_read_addr] needs NO width fact (the read arm constrains nothing but
    the kind) — but it is [load_reservation]'s call site, hence the record. *)
Lemma gw_vmem_read_addr (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5, gwalk (@vmem_read_addr a0 a1 a2 a3 a4 a5).
Proof.
  pose proof (gw_translate_and_read_value H) as Ht.
  pose proof (gw_load_reservation H) as Hl.
  intros; cbv [vmem_read_addr]; gwm_solve.
Qed.

Lemma gw_vmem_read (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6, gwalk (@vmem_read a0 a1 a2 a3 a4 a5 a6).
Proof.
  pose proof (gw_vmem_read_addr H) as Hv.
  intros; cbv [vmem_read]; gwm_solve.
Qed.

(** THE ONE PLACE WHERE [0 < width] IS NOT A SUBSTITUTION — see the header's
    (b).  [sys_misaligned_order_decreasing] is reduced away so that the
    model's DECREASING-order page-crossing arm (dead in this configuration)
    does not have to be walked at all. *)
Lemma gw_vmem_write_addr (H : rv64d_axiom_shapes) :
  ∀ vaddr width data access aq rl res,
    (0 < width)%Z →
    gwalk (@vmem_write_addr vaddr width data access aq rl res).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros vaddr width data access aq rl res Hw.
  cbv [vmem_write_addr sys_misaligned_order_decreasing].
  apply gwalk_catch_early_return.
  apply gwalk_bind0; [by gwm_solve|]. mred.
  apply (gwalk_bind_postQ (λ _, True) (λ p, (0 < fst p)%Z));
    [by apply gpost_liftR, gpost_split_on_page_boundary|].
  intros [ipb npb] Hipb. cbn [fst] in Hipb. mred.
  apply gwalk_bind; [by gwm_solve|]. intros w2. mred.
  apply gwalk_bind; [by gwm_solve|]. intros w3. mred.
  apply gwalk_bind; [by gwm_solve|]. intros effPriv. mred.
  apply gwalk_bind_and_boolM; [by gwm_solve| |].
  - (* the right operand: [do_split_access] IS [npb >? 0] *)
    mred. destruct (Z.gtb npb 0) eqn:Hnpb.
    + have Hnpb' : (0 < npb)%Z by (apply Z.gtb_lt in Hnpb; lia).
      pose proof (fun a b c d e f g =>
                    gw_mem_write_value H a ipb b c d e f g Hipb) as Hmv.
      pose proof (fun a b c d e f =>
                    gw_translate_and_write_value H a npb b c d e f Hnpb')
        as Htw.
      gwm_solve.
    + pose proof (fun a b c d e f g =>
                    gw_mem_write_value H a width b c d e f g Hw) as Hmv.
      gwm_solve.
  - (* [do_split_access = false]: every derived width is [width] *)
    pose proof (fun a b c d e f g =>
                  gw_mem_write_value H a width b c d e f g Hw) as Hmv.
    gwm_solve.
Qed.

Lemma gw_vmem_write (H : rv64d_axiom_shapes) :
  ∀ rs_addr offset width data access aq rl res,
    (0 < width)%Z →
    gwalk (@vmem_write rs_addr offset width data access aq rl res).
Proof.
  intros rs_addr offset width data access aq rl res Hw.
  pose proof (fun a b c d e f =>
                gw_vmem_write_addr H a width b c d e f Hw) as Hv.
  cbv [vmem_write]; gwm_solve.
Qed.

Lemma gw_process_clean_inval (H : rv64d_axiom_shapes) :
  ∀ a0 a1, gwalk (@process_clean_inval a0 a1).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; cbv [process_clean_inval]; gwm_solve.
Qed.

(* ====================================================================== *)
(** ** 7. THE FETCH LAYER

    A fetch translates and then reads, at a literal width — so, since (O10)'s
    fix, there is nothing to say beyond the two callees.  (The read goes out
    at [Read_plain]: the model passes [(aq, rl, res) = (false, false, false)]
    to [mem_read], and [read_ram]'s [Read_ifetch] arm is dead in the whole
    model.) *)

Lemma gw_fetch_bytes (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwalk (@fetch_bytes a0 a1 a2).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; cbv [fetch_bytes]; gwm_solve.
Qed.

Lemma gw_rvfi_fetch (H : rv64d_axiom_shapes) : ∀ a0, gwalk (@rvfi_fetch a0).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; destruct a0; cbv [rvfi_fetch]; gwm_solve.
Qed.

Lemma gw_fetch (H : rv64d_axiom_shapes) : ∀ a0, gwalk (@fetch a0).
Proof.
  pose proof (gw_rvfi_fetch H) as Hr.
  pose proof (gw_fetch_bytes H) as Hb.
  intros; destruct a0; cbv [fetch]; gwm_solve.
Qed.

(* ====================================================================== *)
(** ** 8. THE SAME CONE IN THE VALUE MODE

    [WeakShapeExec]'s eleven memory clauses are stated in [WeakShapeWin]'s
    [gwx] mode ([gwp] at the return postcondition [exres_wf] = "a redirection
    carries a well-formed instruction"), because that is what
    [run_hart_active]'s [ExecuteAs] arm consumes.  Ten of the eleven end in

        vmem_read … >>= λ w, match w with Ok d => … | Err e => returnM e end

    and [vmem_read : M (result _ ExecutionResult)] — so the value returned on
    the fault path is an [ExecutionResult] THIS CONE PRODUCED, and [gwx]
    demands [exres_wf] of it.  [gwalk] cannot say that (it is value-blind),
    which is finding (O7) once more.

    WHAT IT COSTS IS SMALL, and for the reason [WeakShapeWin] §3 records:
    [gwp]'s bind rule takes plain [gwalk] for the PREFIX, so §§3–7 discharge
    every prefix out of `gshape` and only the seven functions whose RESULT is
    (or carries) an [ExecutionResult] are re-walked.  Those are exactly:
    [translate_and_read_value], [translate_and_write_value],
    [vmem_read_addr], [vmem_write_addr], [vmem_read], [vmem_write] and
    [process_clean_inval].

    THE ONE PLACE THE MODE COSTS A SECOND PROOF is [vmem_write_addr], whose
    two derived widths (§6's (b)) have to be established again — the value
    mode changes the conclusion, not the arithmetic.  Its script below is
    §6's, with [gwp] rules in place of the [gwalk] ones; the three that
    [WeakShapeWin] does not already have are stated first. *)

(** [gwalk_bind_postQ] / [gwalk_bind_bind] / [gwalk_bind_and_boolM] of §1, in
    the value mode.  Each is proved exactly as its §1 twin, with the two
    extra arms ([Interface.Ret] carrying [P'], [Interface.ExtraOutcome]
    carrying [Q]) discharged from the corresponding arm of the hypothesis. *)
Lemma gwp_bind_postQ {E A B} (Q : E → Prop) (P : A → Prop) (P' : B → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpost Q P m → (∀ x, P x → gwp Q P' (k x)) → gwp Q P' (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gwp_bind_bind {E A B C} (Q : E → Prop) (P' : C → Prop)
    (m : Defs.monad E A) (f : A → Defs.monad E B) (g : B → Defs.monad E C) :
  gwp Q (λ _, True) m → (∀ x, gwp Q P' (Defs.bind (f x) g)) →
  gwp Q P' (Defs.bind (Defs.bind m f) g).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|intros v; by apply IH].
  - destruct Hm as [Hn Hm]. split; [done|by apply IH].
  - done.
Qed.

Lemma gwp_bind_and_boolM {E B} (Q : E → Prop) (P' : B → Prop)
    (l r : Defs.monad E bool) (k : bool → Defs.monad E B) :
  gwp Q (λ _, True) l → gwp Q P' (Defs.bind r k) → gwp Q P' (k false) →
  gwp Q P' (Defs.bind (Defs.and_boolM l r) k).
Proof.
  intros Hl Hr Hf. rewrite /Defs.and_boolM.
  apply gwp_bind_bind; [done|]. by intros [|].
Qed.

(** The postcondition of an [access]-layer call: the fault payload is an
    [ExecutionResult] and it is never a redirection.  (Every one of them is
    built by [memory_exception] — i.e. [trap] — or is a literal
    [Ext_DataAddr_Check_Failure], so [exres_wf] holds; but that is a fact
    about the proof, not about the statement.) *)
Definition exres_err {A} (r : Values.result A ExecutionResult) : Prop :=
  match r with Values.Ok _ => True | Values.Err e => exres_wf e end.

Notation gxr m := (gwp (λ _ : exception, True) exres_err m).

(** THE ONE STEP [gwx_solve] DOES NOT HAVE, and the reason it does not:
    [gwx_step] carries a prefix's postcondition only when the prefix's type
    is literally [ExecutionResult] ([gwp_bind_exres]), which is right for the
    ~130 [execute_*] clauses; here the fault-carrying prefixes have type
    [result _ ExecutionResult], so the generic rule takes the
    VALUE-IRRELEVANT route and DROPS the fact — after which the [early_return
    (Err e)] four lines below has nothing to close [exres_wf e] with.  (The
    symptom is two stranded [gwp _ _ (Defs.early_return (Values.Err e))]
    goals, i.e. the (O8)-family trap [WeakShapeWin] §4 records as (ii): a
    rule that silently falls through to a weaker one.)  [gxr_step] is that
    rule, keyed on a NAMED prefix fact so that it fails immediately on every
    other bind. *)
Ltac gxr_step Hx :=
  lazymatch goal with
  | |- gwp ?Q _ (Defs.bind (Defs.liftR _) _) =>
      apply (gwp_bind Q exres_err); [apply gwp_liftR; [qtriv|apply Hx]|]
  | |- gwp ?Q _ (Defs.bind _ _) =>
      apply (gwp_bind Q exres_err); [apply Hx|]
  end.

(** UNPACK THE POSTCONDITION ONLY ONCE ITS SUBJECT IS A CONSTRUCTOR — the
    third of [WeakShapeExec]'s tactic traps, and the same fix.  Left folded,
    [exres_err (Values.Err e)] is not [exres_wf e] to [assumption] under
    every reduction strategy a leaf might use; unfolded too early (while the
    subject is still a variable) it is a stuck [match] that helps nobody. *)
Ltac gxr_clean :=
  match goal with
  | Hx : exres_err (Values.Ok _) |- _ => clear Hx
  | Hx : exres_err (Values.Err _) |- _ =>
      cbv [exres_err] in Hx; cbn beta iota in Hx
  end.

Ltac gxm_solve Hx :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | progress gxr_clean
    | solve [gwx_leaf]
    | gxr_step Hx
    | gwx_step ].

Lemma gx_translate_and_read_value (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5, gxr (@translate_and_read_value a0 a1 a2 a3 a4 a5).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; cbv [translate_and_read_value]; gwx_solve.
Qed.

Lemma gx_translate_and_write_value (H : rv64d_axiom_shapes) :
  ∀ vaddr width value access aq rl res,
    (0 < width)%Z →
    gxr (@translate_and_write_value vaddr width value access aq rl res).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros vaddr width value access aq rl res Hw.
  pose proof (fun a b c d e f g =>
                gw_mem_write_value H a width b c d e f g Hw) as Hmv.
  cbv [translate_and_write_value]; gwx_solve.
Qed.

Lemma gx_vmem_read_addr (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5, gxr (@vmem_read_addr a0 a1 a2 a3 a4 a5).
Proof.
  pose proof (gw_translate_and_read_value H) as Ht.
  pose proof (gx_translate_and_read_value H) as Htx.
  pose proof (gw_load_reservation H) as Hl.
  intros; cbv [vmem_read_addr]; gxm_solve Htx.
Qed.

Lemma gx_vmem_read (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 a5 a6, gxr (@vmem_read a0 a1 a2 a3 a4 a5 a6).
Proof.
  pose proof (gw_vmem_read_addr H) as Hv.
  pose proof (gx_vmem_read_addr H) as Hvx.
  intros; cbv [vmem_read]; gxm_solve Hvx.
Qed.

(** §6's script, in the value mode.  The two derived widths are established
    exactly as there; what changes is only which bind rule carries them. *)
Lemma gx_vmem_write_addr (H : rv64d_axiom_shapes) :
  ∀ vaddr width data access aq rl res,
    (0 < width)%Z →
    gxr (@vmem_write_addr vaddr width data access aq rl res).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros vaddr width data access aq rl res Hw.
  cbv [vmem_write_addr sys_misaligned_order_decreasing].
  apply gwp_catch_early_return.
  apply gwp_bind0_closed; [by gwx_solve|]. mred.
  apply (gwp_bind_postQ _ (λ p, (0 < fst p)%Z));
    [by apply gpost_liftR, gpost_split_on_page_boundary|].
  intros [ipb npb] Hipb. cbn [fst] in Hipb. mred.
  apply gwp_bind_closed; [by gwx_solve|]. intros w2. mred.
  apply gwp_bind_closed; [by gwx_solve|]. intros w3. mred.
  apply gwp_bind_closed; [by gwx_solve|]. intros effPriv. mred.
  apply gwp_bind_and_boolM; [by gwx_solve| |].
  - mred. destruct (Z.gtb npb 0) eqn:Hnpb.
    + have Hnpb' : (0 < npb)%Z by (apply Z.gtb_lt in Hnpb; lia).
      pose proof (fun a b c d e f g =>
                    gw_mem_write_value H a ipb b c d e f g Hipb) as Hmv.
      pose proof (fun a b c d e f =>
                    gw_translate_and_write_value H a npb b c d e f Hnpb')
        as Htw.
      pose proof (fun a b c d e f =>
                    gx_translate_and_write_value H a npb b c d e f Hnpb')
        as Htwx.
      gxm_solve Htwx.
    + pose proof (fun a b c d e f g =>
                    gw_mem_write_value H a width b c d e f g Hw) as Hmv.
      gxm_solve Hmv.
  - pose proof (fun a b c d e f g =>
                  gw_mem_write_value H a width b c d e f g Hw) as Hmv.
    gxm_solve Hmv.
Qed.

Lemma gx_vmem_write (H : rv64d_axiom_shapes) :
  ∀ rs_addr offset width data access aq rl res,
    (0 < width)%Z →
    gxr (@vmem_write rs_addr offset width data access aq rl res).
Proof.
  intros rs_addr offset width data access aq rl res Hw.
  pose proof (fun a b c d e f =>
                gw_vmem_write_addr H a width b c d e f Hw) as Hv.
  pose proof (fun a b c d e f =>
                gx_vmem_write_addr H a width b c d e f Hw) as Hvx.
  cbv [vmem_write]; gxm_solve Hvx.
Qed.

Lemma gx_process_clean_inval (H : rv64d_axiom_shapes) :
  ∀ a0 a1, gwx (@process_clean_inval a0 a1).
Proof.
  pose proof (gw_translateAddr H) as Ht.
  intros; cbv [process_clean_inval]; gwx_solve.
Qed.
