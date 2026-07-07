(* One-shot compressed-instruction decode.

   The RVC decoder [ext_decode_compressed] contains a [currentlyEnabled
   Ext_Zca] gate on the taken path.  That gate is an [Acc]-guarded recursion
   that [vm_compute] cannot evaluate, which is why the concrete-word decode
   proofs originally walked the ~55-clause match by hand, paying
   ~2s per instruction (that hand-walk machinery has since been removed).

   This file proves ONCE, symbolically in the word, that the decoder is
   exec-equivalent (on any state with misa.C set) to a read-free variant
   [decode_c_pure] in which [currentlyEnabled Ext_Zca] is replaced by
   [returnM true].  [decode_c_pure] has no [Acc]-recursion on its taken path,
   so [vm_compute] decodes it directly.  Each site then becomes

       rewrite (rvc_bridge _ s Hmisa); vm_compute; reflexivity      (~0.01s)

   The equivalence is a plain congruence [Rb] over the Sail free monad, with
   the single non-reflexive leaf being the Zca gate ([Rb_leaf], via
   [exec_currentlyEnabled_Zca]).  Every other leaf is handled by [Rb_refl],
   which needs only that the leaf is state-preserving; those obligations are
   discharged by the [ro] ("read-only") development below.  No axioms. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvExec RiscvFetchExec.
Local Open Scope Z_scope.
Import Defs.

(* ===== state-preservation ([ro]) development ===== *)
Definition ro {T} (m : M T) : Prop := forall s v s', exec m s = Some (v, s') -> s' = s.

Lemma ro_returnM {T} (x : T) : ro (returnM x).
Proof. intros s v s' H. rewrite exec_returnm in H. inversion H. reflexivity. Qed.
Lemma ro_read_reg (r : register) : ro (Defs.read_reg r : M _).
Proof. intros s v s' H. rewrite exec_read_reg in H. inversion H. reflexivity. Qed.
Lemma ro_bind {T U} (m : M T) (k : T -> M U) :
  ro m -> (forall a, ro (k a)) -> ro (Defs.bind m k).
Proof. intros Hm Hk s v s' H. rewrite exec_bind in H.
  destruct (exec m s) as [[a s1]|] eqn:E; [|discriminate].
  specialize (Hm _ _ _ E). subst s1. specialize (Hk a _ _ _ H). exact Hk. Qed.
Lemma ro_and_boolM (l r : M bool) : ro l -> ro r -> ro (and_boolM l r).
Proof. intros Hl Hr. unfold and_boolM. apply ro_bind; [exact Hl| intro a; destruct a; [exact Hr|apply ro_returnM]]. Qed.
Lemma ro_or_boolM (l r : M bool) : ro l -> ro r -> ro (or_boolM l r).
Proof. intros Hl Hr. unfold or_boolM. apply ro_bind; [exact Hl| intro a; destruct a; [apply ro_returnM|exact Hr]]. Qed.
Lemma ro_assert_exp' (b : bool) (msg : string) : ro (assert_exp' b msg).
Proof. intros s v s' H. destruct b; cbn in H; [inversion H; reflexivity | discriminate]. Qed.
Lemma ro_if {T} (b:bool) (x y : M T) : ro x -> ro y -> ro (if b then x else y).
Proof. intros Hx Hy; destruct b; assumption. Qed.
Lemma ro_exit {T} (x : unit) : ro (exit x : M T).
Proof. intros s v s' H. cbn in H. discriminate. Qed.
Lemma ro_read_senvcfg : ro (read_senvcfg tt).
Proof. unfold read_senvcfg. cbn match. repeat first [apply ro_bind|apply ro_read_reg|apply ro_returnM|intro]. Qed.
Lemma ro_internal_error {T} f l m : ro (internal_error (a:=T) f l m).
Proof. intros s v s' H. cbn in H. discriminate. Qed.

(* [hartSupports] is a well-founded recursion; induct on the fuel. *)
Lemma ro_rec_hartSupports : forall k (acc : Acc (Zwf 0) k) e, ro (_rec_hartSupports e k acc).
Proof.
  intro k. revert k.
  apply (well_founded_ind (Zwf_well_founded 0)
           (fun k => forall (acc : Acc (Zwf 0) k) e, ro (_rec_hartSupports e k acc))).
  intros k IH acc e. destruct acc. cbn [_rec_hartSupports].
  apply ro_bind; [apply ro_assert_exp' | intros Hk; pose proof (proj1 (Z.geb_le k 0) Hk) as Hle].
  destruct e;
    repeat first
      [ apply ro_returnM | apply ro_and_boolM | apply ro_or_boolM
      | apply ro_bind | apply ro_read_reg | apply ro_if
      | (apply IH; unfold Zwf; lia) | intro ].
Qed.
Lemma ro_hartSupports e : ro (hartSupports e).
Proof. unfold hartSupports. apply ro_rec_hartSupports. Qed.

Ltac ro_step aux :=
  repeat first
    [ apply ro_returnM | apply ro_read_reg | apply ro_assert_exp'
    | apply ro_hartSupports | apply ro_read_senvcfg | apply ro_internal_error
    | apply ro_exit
    | apply ro_and_boolM | apply ro_or_boolM | apply ro_if | apply ro_bind
    | aux | intro ].
(* unfold one level of a [_rec_currentlyEnabled] recursor *)
Ltac cE1 := match goal with a : Acc _ _ |- _ => destruct a end; cbn [_rec_currentlyEnabled].

(* [currentlyEnabled e] for the extensions reachable from the RVC decoder.
   Each arm either bottoms out in [hartSupports]/[read_reg] (base cases) or
   recurses to a strictly lower extension (handled by [apply]ing that
   extension's lemma, NOT by re-unfolding -- the fuel is symbolic, so a
   destruct loop would never terminate). *)
Lemma ro_rec_cE_Zicsr k acc : ro (_rec_currentlyEnabled Ext_Zicsr k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_C k acc : ro (_rec_currentlyEnabled Ext_C k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_M k acc : ro (_rec_currentlyEnabled Ext_M k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_B k acc : ro (_rec_currentlyEnabled Ext_B k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_A k acc : ro (_rec_currentlyEnabled Ext_A k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_Zimop k acc : ro (_rec_currentlyEnabled Ext_Zimop k acc).
Proof. cE1. ro_step ltac:(fail). Qed.
Lemma ro_rec_cE_U k acc : ro (_rec_currentlyEnabled Ext_U k acc).
Proof. cE1. ro_step ltac:(apply ro_rec_cE_Zicsr). Qed.
Lemma ro_rec_cE_S k acc : ro (_rec_currentlyEnabled Ext_S k acc).
Proof. cE1. ro_step ltac:(apply ro_rec_cE_Zicsr). Qed.
Lemma ro_rec_cE_Zca k acc : ro (_rec_currentlyEnabled Ext_Zca k acc).
Proof. cE1. ro_step ltac:(apply ro_rec_cE_C). Qed.
Lemma ro_rec_cE_Zaamo k acc : ro (_rec_currentlyEnabled Ext_Zaamo k acc).
Proof. cE1. ro_step ltac:(apply ro_rec_cE_A). Qed.

Ltac ro_cE_aux := first
  [ apply ro_rec_cE_Zicsr | apply ro_rec_cE_C | apply ro_rec_cE_M
  | apply ro_rec_cE_B | apply ro_rec_cE_U | apply ro_rec_cE_S | apply ro_rec_cE_Zca
  | apply ro_rec_cE_A | apply ro_rec_cE_Zimop | apply ro_rec_cE_Zaamo ].
Ltac ro_cE := unfold currentlyEnabled; destruct (Defs.Zwf_guarded _); cbn [_rec_currentlyEnabled]; ro_step ro_cE_aux.

Lemma ro_cE_Zcb : ro (currentlyEnabled Ext_Zcb).             Proof. ro_cE. Qed.
Lemma ro_cE_Zcmop : ro (currentlyEnabled Ext_Zcmop).         Proof. ro_cE. Qed.
Lemma ro_cE_Zbb : ro (currentlyEnabled Ext_Zbb).             Proof. ro_cE. Qed.
Lemma ro_cE_Zicfiss : ro (currentlyEnabled Ext_Zicfiss).     Proof. ro_cE. Qed.
Lemma ro_cE_Zmmul : ro (currentlyEnabled Ext_Zmmul).         Proof. ro_cE. Qed.
Lemma ro_cE_Zihintntl : ro (currentlyEnabled Ext_Zihintntl). Proof. ro_cE. Qed.
Lemma ro_cE_Zba : ro (currentlyEnabled Ext_Zba).             Proof. ro_cE. Qed.
Lemma ro_cE_M : ro (currentlyEnabled Ext_M).                 Proof. ro_cE. Qed.
Lemma ro_cE_S : ro (currentlyEnabled Ext_S).
Proof. unfold currentlyEnabled. apply ro_rec_cE_S. Qed.

Lemma ro_zicfiss_xSSE p : ro (zicfiss_xSSE p).
Proof.
  unfold zicfiss_xSSE. apply ro_and_boolM; [apply ro_cE_S|].
  destruct p; repeat first [apply ro_returnM|apply ro_bind|apply ro_read_reg|apply ro_read_senvcfg|apply ro_internal_error|intro].
Qed.
Lemma ro_encdec_reg w : ro (encdec_reg_backwards w).
Proof. unfold encdec_reg_backwards. cbn zeta. apply ro_if; [apply ro_returnM | apply ro_bind; [apply ro_assert_exp'|intro; apply ro_exit]]. Qed.
Lemma ro_encdec_ntl w : ro (encdec_ntl_backwards w).
Proof. unfold encdec_ntl_backwards. cbn zeta. repeat (apply ro_if; [apply ro_returnM|]). apply ro_bind; [apply ro_assert_exp'|intro; apply ro_exit]. Qed.

(* dispatch [ro <leaf>] for every leaf the RVC decoder produces.  Matches on
   the head symbol so a mismatched [apply] never unfolds [ro] over [exec] of a
   large term (that is quadratically slow across the ~2000-node decoder). *)
Ltac ro_leaf :=
  lazymatch goal with
  | |- ro (returnM _) => apply ro_returnM
  | |- ro (Defs.read_reg _) => apply ro_read_reg
  | |- ro (read_reg _) => apply ro_read_reg
  | |- ro (assert_exp' _ _) => apply ro_assert_exp'
  | |- ro (exit _) => apply ro_exit
  | |- ro (zicfiss_xSSE _) => apply ro_zicfiss_xSSE
  | |- ro (encdec_reg_backwards _) => apply ro_encdec_reg
  | |- ro (encdec_ntl_backwards _) => apply ro_encdec_ntl
  | |- ro (currentlyEnabled Ext_Zcb) => apply ro_cE_Zcb
  | |- ro (currentlyEnabled Ext_Zcmop) => apply ro_cE_Zcmop
  | |- ro (currentlyEnabled Ext_Zbb) => apply ro_cE_Zbb
  | |- ro (currentlyEnabled Ext_Zicfiss) => apply ro_cE_Zicfiss
  | |- ro (currentlyEnabled Ext_Zmmul) => apply ro_cE_Zmmul
  | |- ro (currentlyEnabled Ext_Zihintntl) => apply ro_cE_Zihintntl
  | |- ro (currentlyEnabled Ext_Zba) => apply ro_cE_Zba
  | |- ro (currentlyEnabled Ext_M) => apply ro_cE_M
  end.

(* ===== the [Rb] bridge congruence ===== *)
(* [Rb m m']: on any misa.C state, m and m' exec-agree and m preserves misa.C. *)
Definition Rb {T} (m m' : M T) : Prop :=
  forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec m s = exec m' s /\
    (forall v s', exec m s = Some (v, s') ->
        eq_vec (_get_Misa_C (register_lookup misa s'.(sregs))) ('b"1") = true).
Lemma Rb_exec {T} (m m' : M T) s :
  Rb m m' -> eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true -> exec m s = exec m' s.
Proof. intros H Hm. apply (proj1 (H s Hm)). Qed.
Lemma Rb_refl {T} (m : M T) : ro m -> Rb m m.
Proof. intros Hro s Hm. split; [reflexivity|]. intros v s' Hex. rewrite (Hro s v s' Hex). exact Hm. Qed.
Lemma Rb_returnM {T} (x : T) : Rb (returnM x) (returnM x).
Proof. apply Rb_refl, ro_returnM. Qed.
Lemma Rb_leaf : Rb (currentlyEnabled Ext_Zca) (returnM true).
Proof.
  intros s Hm. rewrite (exec_currentlyEnabled_Zca s Hm). split; [reflexivity|].
  intros v s' Heq. inversion Heq. subst. exact Hm.
Qed.
Lemma Rb_bind {T U} (m m' : M T) (k k' : T -> M U) :
  Rb m m' -> (forall a, Rb (k a) (k' a)) -> Rb (Defs.bind m k) (Defs.bind m' k').
Proof.
  intros Hm Hk s Hs. rewrite !exec_bind.
  destruct (Hm s Hs) as [Heq Hpres]. rewrite Heq.
  destruct (exec m' s) as [[a s1]|] eqn:E'.
  - specialize (Hpres a s1 Heq). destruct (Hk a s1 Hpres) as [Heqk Hpresk]. split.
    + exact Heqk. + intros v s2 Hex. eapply Hpresk; exact Hex.
  - split; [reflexivity|]. intros v s2 Hc. discriminate Hc.
Qed.
Lemma Rb_if {T} (b : bool) (x x' y y' : M T) : Rb x x' -> Rb y y' -> Rb (if b then x else y) (if b then x' else y').
Proof. intros Hx Hy. destruct b; assumption. Qed.
Lemma Rb_and_boolM (l l' r r' : M bool) : Rb l l' -> Rb r r' -> Rb (and_boolM l r) (and_boolM l' r').
Proof. intros Hl Hr. unfold and_boolM. apply Rb_bind; [exact Hl|]. intro a. destruct a; [exact Hr | apply Rb_returnM]. Qed.
Lemma Rb_or_boolM (l l' r r' : M bool) : Rb l l' -> Rb r r' -> Rb (or_boolM l r) (or_boolM l' r').
Proof. intros Hl Hr. unfold or_boolM. apply Rb_bind; [exact Hl|]. intro a. destruct a; [apply Rb_returnM | exact Hr]. Qed.
Lemma Rb_match_opt {T U} (w : option T) (f f' : T -> M U) (n n' : M U) :
  (forall a, Rb (f a) (f' a)) -> Rb n n' ->
  Rb (match w with Some a => f a | None => n end) (match w with Some a => f' a | None => n' end).
Proof. intros Hf Hn. destruct w; [apply Hf | exact Hn]. Qed.

(* [Opaque Rb] so the [if] case below matches the model's bool-[match]-compiled
   conditionals rather than unfolding [Rb]. *)
Opaque Rb.
Ltac cong :=
  match goal with
  | |- Rb (currentlyEnabled Ext_Zca) _ => apply Rb_leaf
  | |- Rb (returnM _) _ => apply Rb_returnM
  | |- Rb (and_boolM _ _) _ => apply Rb_and_boolM; [cong|cong]
  | |- Rb (or_boolM _ _) _ => apply Rb_or_boolM; [cong|cong]
  | |- Rb (Defs.bind _ _) _ => apply Rb_bind; [cong| intro; cong]
  | |- Rb (match ?w with Some _ => _ | None => _ end) _ => apply Rb_match_opt; [intro; cong|cong]
  | |- Rb (if _ then _ else _) _ => apply Rb_if; [cong|cong]
  | |- Rb _ _ => apply Rb_refl; ro_leaf
  end.

(* [decode_c_pure w]: the Sail RVC decoder with [currentlyEnabled Ext_Zca]
   replaced by [returnM true], built by abstracting the gate out of the
   decoder body and re-applying it to [returnM true]. *)
Definition decode_c_pure (w : mword 16) : M instruction :=
  ltac:(
    let t := constr:(ext_decode_compressed w) in
    let t := eval unfold ext_decode_compressed, encdec_compressed_backwards in t in
    let t := eval cbv beta in t in
    let t := eval cbn zeta in t in
    let p := eval pattern (currentlyEnabled Ext_Zca) in t in
    match p with ?f _ => exact (f (returnM true)) end).

(* proven ONCE, symbolic in [w]: the decoder is exec-equivalent to the
   read-free variant on any misa.C state. *)
Lemma rvc_bridge (w : mword 16) s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed w) s = exec (decode_c_pure w) s.
Proof.
  intro Hm. apply (Rb_exec _ _ s); [| exact Hm].
  unfold decode_c_pure, ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta.
  cong.
Qed.

(* one-shot concrete-word decode (the only remaining compressed-decode path):
   rewrite through the bridge, then [vm_compute] the read-free decoder (~0.01s). *)
(* After [vm_compute] both sides are canonical up to the well-formedness proof
   carried by each [bv]; close constructor-by-constructor, discharging each [bv]
   leaf with [bv_eq] (unsigned equality) BEFORE [f_equal] would peel into its
   proof term. *)
Ltac rvc_oneshot s Hmisa :=
  rewrite (rvc_bridge _ s Hmisa);
  vm_compute;
  repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].
