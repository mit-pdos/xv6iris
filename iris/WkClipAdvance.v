(** * WkClipAdvance.v — STEP-0 PROTOTYPE: the ADVANCING install cut

    THE EXPERIMENT (claude-notes/projects/weak-memory.md, the CHECKPOINT's
    NEXT item 2 — "the USER page tables").  The user-table invariant cannot
    be the kernel table's: a user leaf slot is OVERWRITTEN by software
    ([mappages] installs a PTE, [uvmunmap] stores [*pte = 0], [uvmalloc]
    grows the mapping), so there is no single canonical word every message
    is an A/D variant of.  The shape the worklist proposes instead is

        "every message AT OR ABOVE THE LATEST INSTALL writes a variant of
         the CURRENT word",

    i.e. exactly [WeakKpt] §1's CLIPPED layer ([wlog_variants_from T0],
    [wfresh_from T0], [wwin_install log T0]) with the cut [T0] ADVANCING at
    every software store rather than pinned at kvmmake's boot install.

    THE DESIGN RISK the worklist flags, and the only thing this file tests:
    can the clipped vocabulary be RE-ESTABLISHED at a new cut after a
    NON-VARIANT software store — a store whose value is unrelated to the
    old canonical word?  Nothing here is about the walk, the WP layer or
    the Iris invariant; this is the pure log-level core, so that a negative
    answer is cheap to learn.

    WHAT IS PROVED, all with the EXISTING vocabulary UNCHANGED (no new
    axioms, no edits to any other file):

      1. [wclip_reinstall] — THE RE-INSTALL RULE.  Appending an arbitrary
         8-byte window write [wwrite_msg tid k la 8 w'] to ANY log
         re-establishes all three clipped conjuncts at the FRESH cut
         [T0 := S (length log)], with the NEW word [w'] as the canonical
         one.  The old history — and any old canonical word — drops out,
         because the closure at that cut quantifies over messages of index
         [≥ length log], i.e. over the appended message alone.

         NOTE ON THE CUT'S ARITHMETIC.  The cut is a TIMESTAMP, and the
         timestamp of index [i] is [S i] ([WeakMem.log_byte]); the appended
         message sits at index [length log], so its timestamp — and hence
         the new cut — is [S (length log)], not [length log].  (At the cut
         [length log] the closure would still be forced to cover the LAST
         PRE-EXISTING message, which is precisely the message an advancing
         cut must be allowed to forget.)

      2. [wclip_unmap_collapse] — THE COLLAPSE AT THE NEW CUT, at the
         [uvmunmap] word [w' = 0], via the EXISTING [wadm_variant_from],
         used verbatim: every admissible (weak, racy, byte-wise) read of
         the window is [pte_set_ad 0 a d] for some A/D bits.  Reusing that
         lemma unchanged IS the experiment's claim.  [_ext] is the same
         statement under any further extension of the log that does not
         write the window (the [wwin_install_prefix] /
         [wlog_variants_from_ext] kit, also unchanged).

      3. [pte_set_ad_zero_invalid] — A/D variants of the zero word are
         still INVALID PTEs, in the [exec_eff] spelling
         [WeakWalkEff.wpte_invalid] — the one the walk's fault arm actually
         consumes ([WeakWalkEff.exec_eff_check_leaf_pte_invalid], which
         returns [Err (PTW_Invalid_PTE tt)] from [check_leaf_pte]).  This
         is what turns 2. into "the walker faults on an unmapped slot no
         matter which racy value it observes".

    VERDICT (see the report): the clipped layer supports an advancing cut
    with NOTHING added.  The re-install rule needs no geometry, no
    well-formedness and no fact about the pre-existing log — see the
    comment on [wclip_reinstall]. *)

(* the import block is [WeakKpt]'s / [WeakVariant]'s, trimmed to what this
   file names *)
From Stdlib.ssr Require Import ssreflect.
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakCert WeakEff WeakLeafEffCommon.
Require Import WeakRacy.
Require Import PtAdBits PtTree.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. The re-install rule

    The three clipped conjuncts, each at the fresh cut, proved separately
    so that the report can say exactly which premises each one costs.  The
    answer is: NONE of them costs anything — no [wlog_wf], no [acc_wf], no
    hypothesis whatsoever about [log].  [wclip_reinstall] below packages
    them in the shape the worklist asked for. *)

(** The appended message is the one at the new cut, and it writes every
    byte of the window. *)
Lemma wreinstall_install (tid : option nat) (kcls : wm_class) (la : Arch.pa)
    (log : list wmsg) (w' : bv (8 * 8)%N) :
  wwin_install (log ++ [wwrite_msg tid kcls la 8 w']) (S (length log)) la.
Proof.
  split; [lia|].
  exists (wwrite_msg tid kcls la 8 w'). split.
  - replace (S (length log) - 1)%nat with (length log) by lia.
    rewrite (lookup_app_r log _ (length log) (Nat.le_refl _)) Nat.sub_diag //.
  - intros j Hj. eexists.
    exact (wwrite_msg_byte tid kcls la 8 w' j ltac:(vm_compute; lia)).
Qed.

(** THE POINT OF THE WHOLE FILE: the closure at the fresh cut sees ONLY the
    appended message, so the new word [w'] — arbitrary, in particular NOT a
    variant of whatever the window held before — is a legitimate canonical
    word.  The old history is quantified away by the cut, not reasoned
    about. *)
Lemma wreinstall_variants (tid : option nat) (kcls : wm_class) (la : Arch.pa)
    (log : list wmsg) (w' : bv (8 * 8)%N) :
  wlog_variants_from (S (length log)) (log ++ [wwrite_msg tid kcls la 8 w'])
    (pa_z la) (w' : mword 64).
Proof.
  intros i m Hi Hge.
  assert (Hlen : (i < length log + 1)%nat).
  { apply lookup_lt_Some in Hi. rewrite length_app /= in Hi. lia. }
  assert (Hieq : i = length log) by lia. subst i.
  rewrite (lookup_app_r log _ (length log) (Nat.le_refl _)) Nat.sub_diag /= in Hi.
  injection Hi as <-.
  apply (wmsg_variant_write tid kcls la w' (pa_z la) (w' : mword 64) eq_refl).
  exact (pte_set_ad_refl (w' : mword 64)).
Qed.

(** The CAS discipline at the fresh cut is VACUOUS: [wfresh_from T0]
    constrains messages STRICTLY above [T0] (the install itself is exempt —
    it is allowed to overwrite whatever was there), and at [T0 = S (length
    log)] the appended install is the last index, so there is nothing above
    it.  This is where a boot-cut assumption baked into [wfresh_from] would
    have shown up; there is none — the definition is stated relative to its
    [T0] argument and the image only ever enters through [log_byte] at
    timestamps below the cut, which the [T0 < S i] guard excludes.  Hence
    the [forall img]. *)
Lemma wreinstall_fresh (tid : option nat) (kcls : wm_class) (la : Arch.pa)
    (log : list wmsg) (w' : bv (8 * 8)%N) (img : image) :
  wfresh_from (S (length log)) img (log ++ [wwrite_msg tid kcls la 8 w'])
    (pa_z la).
Proof.
  intros i m b Hi Hgt _.
  exfalso. apply lookup_lt_Some in Hi. rewrite length_app /= in Hi. lia.
Qed.

(** THE RE-INSTALL RULE, packaged.  [wlog_wf log] and [acc_wf la 8] are
    carried because they are what the surrounding cone will have in hand at
    a real store site (they are needed to keep [wflat] describing the log —
    [WeakBridge.acc_wf_msg] — and are free there); NEITHER IS CONSUMED
    HERE, which is itself part of the finding: re-installing the clipped
    invariant at a new cut is a pure index computation. *)
Lemma wclip_reinstall (tid : option nat) (kcls : wm_class) (la : Arch.pa)
    (log : list wmsg) (w' : bv (8 * 8)%N) :
  wlog_wf log ->
  acc_wf la 8 ->
  wwin_install (log ++ [wwrite_msg tid kcls la 8 w']) (S (length log)) la /\
  wlog_variants_from (S (length log)) (log ++ [wwrite_msg tid kcls la 8 w'])
    (pa_z la) (w' : mword 64) /\
  (forall img : image,
     wfresh_from (S (length log)) img (log ++ [wwrite_msg tid kcls la 8 w'])
       (pa_z la)).
Proof.
  intros _ _. split_and!.
  - exact (wreinstall_install tid kcls la log w').
  - exact (wreinstall_variants tid kcls la log w').
  - intro img. exact (wreinstall_fresh tid kcls la log w' img).
Qed.

(* ====================================================================== *)
(** ** 2. The collapse at the new cut, at the [uvmunmap] word

    [wadm_variant_from] is used EXACTLY as it stands in [WeakKpt] §1d; the
    only new inputs are §1's two facts at the advancing cut.  The zero word
    is taken as a hypothesis on the message's value rather than written
    into the message, so the statement types at [bv (8 * 8)] (the width the
    log's 8-byte writes carry) without any cast gymnastics. *)

Lemma wclip_unmap_collapse (σ : wmstate) (rak : akinfo) (la : Arch.pa)
    (log : list wmsg) (tid : option nat) (kcls : wm_class)
    (z w : bv (8 * 8)%N) :
  (z : mword 64) = mword_of_int 0 ->
  wm_log σ = (log ++ [wwrite_msg tid kcls la 8 z])%list ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  wadm σ rak la 8 w ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad (mword_of_int 0) a d.
Proof.
  intros Hz Hlog Hcov Hadm.
  destruct (wadm_variant_from σ rak la (z : mword 64) (S (length log)) w
              ltac:(rewrite Hlog; exact (wreinstall_variants tid kcls la log z))
              ltac:(rewrite Hlog; exact (wreinstall_install tid kcls la log z))
              Hcov Hadm) as (a & d & Hw).
  exists a, d. by rewrite Hw Hz.
Qed.

(** ... and the same under any further extension of the log that does not
    touch the window (the shape a real [uvmunmap] proof needs: other harts
    and the same hart go on appending messages elsewhere between the store
    and the read).  [wwin_install_prefix] and [wlog_variants_from_ext] are
    the existing kit, unchanged. *)
Lemma wclip_unmap_collapse_ext (σ : wmstate) (rak : akinfo) (la : Arch.pa)
    (log rest : list wmsg) (tid : option nat) (kcls : wm_class)
    (z w : bv (8 * 8)%N) :
  (z : mword 64) = mword_of_int 0 ->
  wm_log σ = ((log ++ [wwrite_msg tid kcls la 8 z]) ++ rest)%list ->
  (forall (i : nat) (m : wmsg),
     wm_log σ !! i = Some m -> (length log + 1 <= i)%nat ->
     forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None) ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  wadm σ rak la 8 w ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad (mword_of_int 0) a d.
Proof.
  intros Hz Hlog Hno Hcov Hadm.
  set (log0 := (log ++ [wwrite_msg tid kcls la 8 z])%list).
  assert (Hlen0 : length log0 = (length log + 1)%nat)
    by (rewrite /log0 length_app /=; lia).
  assert (Hpref : log0 `prefix_of` wm_log σ) by (rewrite Hlog; by exists rest).
  assert (Hvar : wlog_variants_from (S (length log)) (wm_log σ) (pa_z la)
                   (z : mword 64)).
  { refine (wlog_variants_from_ext (S (length log)) log0 (wm_log σ) (pa_z la)
              (z : mword 64) (wreinstall_variants tid kcls la log z) Hpref _).
    intros i m Hi Hge j Hj.
    exact (Hno i m Hi ltac:(lia) j Hj). }
  assert (Hinst : wwin_install (wm_log σ) (S (length log)) la)
    by exact (wwin_install_prefix log0 (wm_log σ) (S (length log)) la
                (wreinstall_install tid kcls la log z) Hpref).
  destruct (wadm_variant_from σ rak la (z : mword 64) (S (length log)) w
              Hvar Hinst Hcov Hadm) as (a & d & Hw).
  exists a, d. by rewrite Hw Hz.
Qed.

(* ====================================================================== *)
(** ** 3. A/D variants of the zero word still fault

    The walk's fault arm consumes [WeakWalkEff.wpte_invalid] — see
    [WeakWalkEff.exec_eff_check_leaf_pte_invalid], which turns it into
    [exec_eff (check_leaf_pte ...) s = Some (Err (PTW_Invalid_PTE tt, tt),
    s, [])], the level-0 [PTW_Invalid_PTE] arm of the three walk heads.  So
    that is the spelling proved here ([PtTree.pte_invalid], the SC twin,
    follows by [wpte_invalid_pte_invalid] — [pte_set_ad_zero_pte_invalid]).

    [PtBuild.pte_invalid_bit0] is the [exec] version of the bit-0 test; the
    [exec_eff] twin is one lemma, and A/D-stability of bit 0 is
    [PtAdBits.pte_set_ad_testbit] at [k = 0] (bit 0 is V, and [pte_set_ad]
    only ever touches bits 6 and 7 — the [pte_set_ad_flag_*] laws are the
    same fact stated per flag). *)

(** A word with V clear is eff-invalid: the first [pte_is_invalid] disjunct
    fires and short-circuits, so no register (in particular [menvcfg]) is
    read and the trace is empty. *)
Lemma wpte_invalid_bit0 (w : SailStdpp.Values.mword 64) :
  Z.testbit (bv_unsigned w) 0 = false -> wpte_invalid w.
Proof.
  intros Hb s.
  unfold pte_is_invalid.
  rewrite (pte_flags_V_bit0 w Hb).
  rewrite (exec_eff_or_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (eq_vec ('b"0" : mword 1) ('b"0")) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** THE UNMAPPED-SLOT FAULT FACT: every A/D variant of the zero word is an
    invalid PTE.  Combined with §2 this says: after [uvmunmap]'s store, no
    matter which of the racily observable values the walker's leaf read
    returns, it takes the fault arm. *)
Lemma pte_set_ad_zero_invalid (a d : mword 1) :
  wpte_invalid (pte_set_ad (mword_of_int 0) a d).
Proof.
  apply wpte_invalid_bit0.
  rewrite (pte_set_ad_testbit (mword_of_int 0) a d 0 ltac:(lia)).
  vm_compute. reflexivity.
Qed.

(** the SC projection, free *)
Lemma pte_set_ad_zero_pte_invalid (a d : mword 1) :
  pte_invalid (pte_set_ad (mword_of_int 0) a d).
Proof. apply wpte_invalid_pte_invalid, pte_set_ad_zero_invalid. Qed.

(* ====================================================================== *)
(** ** 4. The headline, end to end

    Everything above, composed: after a software store of the zero word,
    every admissible read of the slot is an invalid PTE. *)

Lemma wclip_unmap_faults (σ : wmstate) (rak : akinfo) (la : Arch.pa)
    (log : list wmsg) (tid : option nat) (kcls : wm_class)
    (z w : bv (8 * 8)%N) :
  (z : mword 64) = mword_of_int 0 ->
  wm_log σ = (log ++ [wwrite_msg tid kcls la 8 z])%list ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  wadm σ rak la 8 w ->
  wpte_invalid (w : mword 64).
Proof.
  intros Hz Hlog Hcov Hadm.
  destruct (wclip_unmap_collapse σ rak la log tid kcls z w Hz Hlog Hcov Hadm)
    as (a & d & Hw).
  rewrite Hw. exact (pte_set_ad_zero_invalid a d).
Qed.

Print Assumptions wclip_reinstall.
Print Assumptions wclip_unmap_collapse.
Print Assumptions wclip_unmap_collapse_ext.
Print Assumptions pte_set_ad_zero_invalid.
Print Assumptions wclip_unmap_faults.
