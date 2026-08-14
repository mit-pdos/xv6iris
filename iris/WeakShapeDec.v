(** * WeakShapeDec.v — the decoder's cone in the [gpure] mode, and the
    DECODER POSTCONDITION [∀ w, gpureP ast_wf (ext_decode w)].

    [WeakShapeAst] §3 says what the postcondition is FOR (it is the only
    thing that makes [∀ ast, gwalk (execute ast)] — stage C5's (O6) —
    a statable obligation) and §4 gives the mode.  This file supplies the
    two things §3 leaves open:

      §1  the THIRTY-FIVE monadic definitions [rv64d.encdec_backwards] and
          [rv64d.encdec_compressed_backwards] reach, each in [gpure].  This
          is the second mode finding (O7) asked for, restricted to the one
          cone that needs it: the generated tower proves [gwalk], which
          permits memory events and therefore implies neither [gpost] nor
          [gpureP].  The cone is small enough (35 of the model's 345 monadic
          definitions) that it is written out here rather than generated —
          [tools/gen_shape.py] should grow a [--mode] flag before a THIRD
          mode is ever needed.
      §2  the traversal itself.

    RELATION TO [DecodeSetU].  That file already walks both decoders with a
    leaf predicate ([goodbP D P m s]) and gets the COMPLETE decode image
    ([decodable_u]/[decodable_c], hence [width_ok1248] on every memory
    clause).  It is VALUE-PINNED at the U-mode reference state [dstateU]:
    its [Interface.RegRead] arm answers from a concrete register file, which
    is what lets [dtp_pin] cut disabled extension families out by
    [vm_compute].  The fetch in [run_hart_active] runs at an ARBITRARY
    register state (any privilege, any CSR), so the postcondition this file
    needs is the ∀-quantified one — which is exactly [gpost]'s [RegRead] arm.
    What is reused is therefore the METHOD and not the theorems: the clause
    spine rule ([DecodeSetU.goodbP_spine] ⇝ [WeakShapeAst.gpureP_spine]), the
    driver's shape ([dtp_core] ⇝ [dp_core]) and the observation that the
    width fields are gate-INDEPENDENT (they come from [width_enc_backwards] /
    [width_enc_wide_backwards] applied to a funct3/funct2 slice), which is
    why dropping the pinning costs only extra dead branches and never a
    width. *)

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

(* ====================================================================== *)
(** ** 1. The cone, bottom-up *)

(** *** 1a. The two fuel recursions.

    Same recipe as [tools/gen_shape.py]'s [OVERRIDE_PROOFS] and
    [WeakShapeOverrides2.gw__rec_pt_walk]: [fix] on the ACCESSIBILITY
    argument, with the induction hypothesis asserted at the accessibility
    SUBTERM (anywhere else breaks the guard condition, and [eauto] cannot
    invent the instance or project a conjunction). *)

Lemma gp__rec_hartSupports : ∀ a0 a1 a2, gpure (_rec_hartSupports a0 a1 a2).
Proof.
  fix IH 3. intros a0 a1 a2. destruct a2 as [a2].
  cbv [_rec_hartSupports]. gpu_solve.
Qed.
#[export] Hint Resolve gp__rec_hartSupports : gpure.

Lemma gp_hartSupports : ∀ a0, gpure (hartSupports a0).
Proof. intros; cbv [hartSupports]; gpu_solve. Qed.
#[export] Hint Resolve gp_hartSupports : gpure.

Lemma gp_internal_error : ∀ (a : Type) f l s, gpure (@internal_error a f l s).
Proof. intros; cbv [internal_error]; gpu_solve. Qed.
#[export] Hint Resolve gp_internal_error : gpure.

Lemma gp_reserved_behavior : ∀ (a : Type) m, gpure (@reserved_behavior a m).
Proof. intros; cbv [reserved_behavior]; gpu_solve. Qed.
#[export] Hint Resolve gp_reserved_behavior : gpure.

Lemma gp_is_mstateen_accessible : ∀ a0, gpure (is_mstateen_accessible a0).
Proof. intros; cbv [is_mstateen_accessible]; gpu_solve. Qed.
#[export] Hint Resolve gp_is_mstateen_accessible : gpure.

Lemma gp_get_mstateen : ∀ a0, gpure (get_mstateen a0).
Proof. intros; cbv [get_mstateen]; gpu_solve. Qed.
#[export] Hint Resolve gp_get_mstateen : gpure.

Lemma gp_read_senvcfg : ∀ a0, gpure (read_senvcfg a0).
Proof. intros; cbv [read_senvcfg]; gpu_solve. Qed.
#[export] Hint Resolve gp_read_senvcfg : gpure.

(** THE NINE-WAY MUTUAL BLOCK.  One [fix] on the shared [Acc] proves all nine
    at once; the [K]s are the per-member instances of the IH at the
    accessibility subterms.  Note that THREE of the nine throw
    ([_rec_get_xLPE] at [VirtualSupervisor]/[VirtualUser], and
    [_rec_virtual_memory_supported] through it) — which is precisely why the
    mode here is [gpure] and not [gsilent]. *)
Lemma gp__rec_stateen_group :
  ∀ l acc,
    (∀ p b s, gpure (_rec_check_stateen_bit p b s l acc)) ∧
    (∀ e, gpure (_rec_currentlyEnabled e l acc)) ∧
    (∀ i, gpure (_rec_get_hstateen i l acc)) ∧
    (∀ i, gpure (_rec_get_sstateen i l acc)) ∧
    (∀ p, gpure (_rec_get_xLPE p l acc)) ∧
    (∀ u, gpure (_rec_is_hstateen_accessible u l acc)) ∧
    (∀ u, gpure (_rec_is_sstateen_accessible u l acc)) ∧
    (∀ u, gpure (_rec_is_zfinx_enabled_by_stateen u l acc)) ∧
    (∀ u, gpure (_rec_virtual_memory_supported u l acc)).
Proof.
  fix IH 2. intros l acc. destruct acc as [acc].
  assert (K1 : ∀ y H p b s, gpure (_rec_check_stateen_bit p b s y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K2 : ∀ y H e, gpure (_rec_currentlyEnabled e y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K3 : ∀ y H i, gpure (_rec_get_hstateen i y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K4 : ∀ y H i, gpure (_rec_get_sstateen i y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K5 : ∀ y H p, gpure (_rec_get_xLPE p y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K6 : ∀ y H u, gpure (_rec_is_hstateen_accessible u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K7 : ∀ y H u, gpure (_rec_is_sstateen_accessible u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K8 : ∀ y H u, gpure (_rec_is_zfinx_enabled_by_stateen u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K9 : ∀ y H u, gpure (_rec_virtual_memory_supported u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  clear IH.
  repeat apply conj.
  - intros p b s. cbv [_rec_check_stateen_bit]. gpu_solve.
  - intros e. cbv [_rec_currentlyEnabled]. gpu_solve.
  - intros i. cbv [_rec_get_hstateen]. gpu_solve.
  - intros i. cbv [_rec_get_sstateen]. gpu_solve.
  - intros p. cbv [_rec_get_xLPE]. gpu_solve.
  - intros u. cbv [_rec_is_hstateen_accessible]. gpu_solve.
  - intros u. cbv [_rec_is_sstateen_accessible]. gpu_solve.
  - intros u. cbv [_rec_is_zfinx_enabled_by_stateen]. gpu_solve.
  - intros u. cbv [_rec_virtual_memory_supported]. gpu_solve.
Qed.

Lemma gp__rec_currentlyEnabled : ∀ e l acc,
  gpure (_rec_currentlyEnabled e l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_get_xLPE : ∀ p l acc, gpure (_rec_get_xLPE p l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_virtual_memory_supported : ∀ u l acc,
  gpure (_rec_virtual_memory_supported u l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_check_stateen_bit : ∀ p b s l acc,
  gpure (_rec_check_stateen_bit p b s l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_get_hstateen : ∀ i l acc, gpure (_rec_get_hstateen i l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_get_sstateen : ∀ i l acc, gpure (_rec_get_sstateen i l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_is_hstateen_accessible : ∀ u l acc,
  gpure (_rec_is_hstateen_accessible u l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_is_sstateen_accessible : ∀ u l acc,
  gpure (_rec_is_sstateen_accessible u l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.
Lemma gp__rec_is_zfinx_enabled_by_stateen : ∀ u l acc,
  gpure (_rec_is_zfinx_enabled_by_stateen u l acc).
Proof. intros; apply gp__rec_stateen_group. Qed.

#[export] Hint Resolve
  gp__rec_check_stateen_bit gp__rec_currentlyEnabled gp__rec_get_hstateen
  gp__rec_get_sstateen gp__rec_get_xLPE gp__rec_is_hstateen_accessible
  gp__rec_is_sstateen_accessible gp__rec_is_zfinx_enabled_by_stateen
  gp__rec_virtual_memory_supported : gpure.

(** *** 1b. The rest of the cone, in topological order *)

Lemma gp_currentlyEnabled : ∀ a0, gpure (currentlyEnabled a0).
Proof. intros; cbv [currentlyEnabled]; gpu_solve. Qed.
#[export] Hint Resolve gp_currentlyEnabled : gpure.

Lemma gp_virtual_memory_supported : ∀ a0, gpure (virtual_memory_supported a0).
Proof. intros; cbv [virtual_memory_supported]; gpu_solve. Qed.
#[export] Hint Resolve gp_virtual_memory_supported : gpure.

Lemma gp_zicfiss_xSSE : ∀ a0, gpure (zicfiss_xSSE a0).
Proof. intros; cbv [zicfiss_xSSE]; gpu_solve. Qed.
#[export] Hint Resolve gp_zicfiss_xSSE : gpure.

Lemma gp_amo_encoding_valid : ∀ a0 a1 a2 a3, gpure (@amo_encoding_valid a0 a1 a2 a3).
Proof.
  intros a0 a1 a2 a3. destruct a2 as [a2], a3 as [a3].
  cbv [amo_encoding_valid]; gpu_solve.
Qed.
#[export] Hint Resolve gp_amo_encoding_valid : gpure.

Lemma gp_width_enc_wide_backwards : ∀ a0, gpure (width_enc_wide_backwards a0).
Proof. intros; cbv [width_enc_wide_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_width_enc_wide_backwards : gpure.

Lemma gp_encdec_reg_backwards : ∀ a0, gpure (encdec_reg_backwards a0).
Proof. intros; cbv [encdec_reg_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_reg_backwards : gpure.

Lemma gp_encdec_amoop_backwards : ∀ a0, gpure (encdec_amoop_backwards a0).
Proof. intros; cbv [encdec_amoop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_amoop_backwards : gpure.

Lemma gp_encdec_bop_backwards : ∀ a0, gpure (encdec_bop_backwards a0).
Proof. intros; cbv [encdec_bop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_bop_backwards : gpure.

Lemma gp_encdec_cbop_backwards : ∀ a0, gpure (encdec_cbop_backwards a0).
Proof. intros; cbv [encdec_cbop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_cbop_backwards : gpure.

Lemma gp_encdec_cbop_zicbop_backwards : ∀ a0,
  gpure (encdec_cbop_zicbop_backwards a0).
Proof. intros; cbv [encdec_cbop_zicbop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_cbop_zicbop_backwards : gpure.

Lemma gp_encdec_csrop_backwards : ∀ a0, gpure (encdec_csrop_backwards a0).
Proof. intros; cbv [encdec_csrop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_csrop_backwards : gpure.

Lemma gp_encdec_iop_backwards : ∀ a0, gpure (encdec_iop_backwards a0).
Proof. intros; cbv [encdec_iop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_iop_backwards : gpure.

Lemma gp_encdec_mul_op_backwards : ∀ a0, gpure (encdec_mul_op_backwards a0).
Proof. intros; cbv [encdec_mul_op_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_mul_op_backwards : gpure.

Lemma gp_encdec_ntl_backwards : ∀ a0, gpure (encdec_ntl_backwards a0).
Proof. intros; cbv [encdec_ntl_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_ntl_backwards : gpure.

Lemma gp_encdec_uop_backwards : ∀ a0, gpure (encdec_uop_backwards a0).
Proof. intros; cbv [encdec_uop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_uop_backwards : gpure.

Lemma gp_encdec_wrsop_backwards : ∀ a0, gpure (encdec_wrsop_backwards a0).
Proof. intros; cbv [encdec_wrsop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_wrsop_backwards : gpure.

Lemma gp_encdec_zicondop_backwards : ∀ a0, gpure (encdec_zicondop_backwards a0).
Proof. intros; cbv [encdec_zicondop_backwards]; gpu_solve. Qed.
#[export] Hint Resolve gp_encdec_zicondop_backwards : gpure.

(* ====================================================================== *)
(** ** 2. The traversal: every instruction either decoder produces is
    [ast_wf]

    The driver is [DecodeSetU]'s [dtp_core] with the value-pinning arm
    REMOVED and the spine/bind rules replaced by their [gpost] twins.
    Dropping the pinning is what makes the result state-generic: a gate whose
    concrete value is [false] at [dstateU] is simply traversed on both
    branches here, which costs dead arms and never a width — the width fields
    come from [width_enc_backwards] / [width_enc_wide_backwards] on a
    funct3/funct2 slice and no extension gate touches them. *)

Ltac dp_leaf :=
  lazymatch goal with
  | |- gpost _ ?P (Defs.returnm ?v) =>
      change (P v); cbv beta iota delta [optW ast_wf]
  | |- gpost _ ?P (returnM ?v) =>
      change (P v); cbv beta iota delta [optW ast_wf]
  | |- gpost _ ?P (Interface.Ret ?v) =>
      change (P v); cbv beta iota delta [optW ast_wf]
  end.

(** The WIDE (AMO) width is a MONADIC mapping, so the plain forall-bind rule
    would abstract it to a fresh unconstrained [Z] and lose positivity; carry
    it as a Q-rule hypothesis into the leaf instead ([DecodeSetU]'s
    [dtp_width_wide], same reason). *)
Ltac dp_width_wide :=
  lazymatch goal with
  | |- gpost ?Q ?P (Defs.bind (width_enc_wide_backwards ?X) ?k) =>
      apply (gpost_bind Q (λ w : Z, (0 < w)%Z));
        [ apply gpost_width_enc_wide_backwards
        | let wd := fresh "wd" in let Hwd := fresh "Hwd" in intros wd Hwd ]
  end.

Ltac dp_spine :=
  lazymatch goal with
  | |- gpost _ _ (Defs.bind _ _) =>
      first [ apply gpureP_spine | apply gpureP_spine_pure ]
  end.

Ltac dp_bind :=
  lazymatch goal with
  | |- gpost _ _ (Defs.bind _ _) =>
      apply gpureP_bind; [ solve [gpu_solve] | let x := fresh "x" in intros x ]
  end.

Ltac dp_if :=
  lazymatch goal with
  | |- gpost _ _ (if ?g then _ else _) =>
      tryif constr_eq g true then cbv iota
      else tryif constr_eq g false then cbv iota
      else (let E := fresh "E" in destruct g eqn:E)
  end.

Ltac dp_let :=
  lazymatch goal with
  | |- gpost _ _ (let _ := _ in _) => cbv zeta
  end.

Ltac dp_match :=
  lazymatch goal with
  | |- gpost _ _ (match ?x with _ => _ end) =>
      tryif is_var x then destruct x
      else first [ progress (cbv beta iota) | let E := fresh "E" in destruct x eqn:E ]
  end.

(** The pure leaf goals: [optW ast_wf] of a [Some]/[None] built by an [if]
    chain over the instruction bits. *)
Ltac dp_pure :=
  lazymatch goal with
  | |- gpost _ _ _ => fail
  | _ =>
      first [ exact I
            | assumption
            | apply width_enc_backwards_pos
            | progress (cbv beta iota delta [optW ast_wf width_enc_backwards])
            | match goal with
              | |- context[if ?g then _ else _] =>
                  let E := fresh "E" in destruct g eqn:E
              end
            | match goal with
              | |- context[match ?x with _ => _ end] =>
                  tryif is_var x then destruct x else fail
              end
            | lia ]
  end.

Ltac dp_core :=
  first [ dp_leaf | dp_width_wide | dp_spine | dp_bind
        | dp_if | dp_let | dp_match | dp_pure ].

Theorem gpureP_ext_decode (w : Values.mword 32) :
  gpureP ast_wf (ext_decode w).
Proof.
  cbv [ext_decode encdec_backwards]. cbv beta zeta.
  repeat dp_core.
Qed.

Theorem gpureP_ext_decode_compressed (h : Values.mword 16) :
  gpureP ast_wf (ext_decode_compressed h).
Proof.
  cbv [ext_decode_compressed encdec_compressed_backwards]. cbv beta zeta.
  repeat dp_core.
Qed.
