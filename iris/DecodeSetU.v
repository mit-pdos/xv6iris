(* DecodeSetU.v -- the COMPLETE decode image at the U-mode reference state.

   DecodeTotalU proved that every 32-bit word decodes ([decode_total_u]);
   this file pins down WHICH instructions can come out: [goodbP D P m s]
   refines [goodb] with a leaf predicate P that must hold at every
   reachable [Ret] leaf, so one linear traversal of the decoder yields

       goodbP D_u decodable_u (ext_decode w) dstateU = true

   and hence [decode_total_u_set]: every word decodes to an instruction
   in the EXPLICIT set [decodable_u] -- the complete set of instructions
   that can execute in user mode under the xv6 configuration.

   Tightness: extension gates are VALUE-PINNED at the concrete dstateU
   ([goodbP_bind_val] + vm_compute on the closed probe), so families whose
   gate is off (Zba/Zbb-only/Zbs, Zicfilp's LPAD, the senvcfg.SSE-gated
   shadow-stack ops) never reach a Some leaf and stay OUT of the set.
   The classification flows through the clause spine
   via [goodbP_bind_Q]: the head's leaf predicate becomes a hypothesis for
   the continuation, so `match o with Some r => returnM r | None => rest`
   turns "every clause leaf satisfies optP P" into "the decoder's leaves
   satisfy P".                                                            *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec.
Require Import WpDecodeBridge DecodeTotalU UserBits.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 goodbP: goodb refined with a leaf predicate.                        *)
(* ===================================================================== *)

Fixpoint goodbP (D : register -> bool) {X} (P : X -> bool) (m : M X) (s : mstate)
    {struct m} : bool :=
  match m with
  | Interface.Ret y => P y
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> bool with
       | Interface.RegRead r _ => fun k => andb (D r) (goodbP D P (k (register_lookup r s.(sregs))) s)
       | Interface.InstrAnnounce _   => fun k => goodbP D P (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => goodbP D P (k tt) s
       | Interface.Barrier _         => fun k => goodbP D P (k tt) s
       | Interface.CacheOp _         => fun k => goodbP D P (k tt) s
       | Interface.TlbOp _           => fun k => goodbP D P (k tt) s
       | Interface.TakeException _   => fun k => goodbP D P (k tt) s
       | Interface.ReturnException _ => fun k => goodbP D P (k tt) s
       | Interface.TranslationStart _=> fun k => goodbP D P (k tt) s
       | Interface.TranslationEnd _  => fun k => goodbP D P (k tt) s
       | Interface.CycleCount        => fun k => goodbP D P (k tt) s
       | Interface.Message _         => fun k => goodbP D P (k tt) s
       | Interface.GetCycleCount     => fun k => goodbP D P (k 0%Z) s
       | _ => fun _ => false
       end) k
  end.

(* The one soundness lemma: goodbP gives exec success, state preservation,
   result transport to every D-agreeing state, AND P of the result.       *)
Lemma goodbP_exec (D : register -> bool) {X} (P : X -> bool) (m : M X) (s1 s2 : mstate) :
  (forall r, D r = true -> register_lookup r s1.(sregs) = register_lookup r s2.(sregs)) ->
  goodbP D P m s1 = true ->
  exists x, exec m s1 = Some (x, s1) /\ exec m s2 = Some (x, s2) /\ P x = true.
Proof.
  intros Hagree; revert s2 Hagree.
  induction m as [y|T oc k IH]; intros s2 Hagree Hgood.
  - exists y. cbn in Hgood. auto.
  - destruct oc; cbn [goodbP exec] in Hgood |- *; try discriminate Hgood;
      try (apply (IH _ s2 Hagree Hgood)).
    apply andb_prop in Hgood as [HDr Hgood'].
    match goal with
    | HDr : D ?rr = true |- _ =>
      pose proof (Hagree _ HDr) as Hr; rewrite <- Hr;
      apply (IH (register_lookup rr s1.(sregs)) s2 Hagree Hgood')
    end.
Qed.

(* goodb is goodbP at the trivial predicate.                              *)
Lemma goodbP_top (D : register -> bool) {X} (m : M X) (s : mstate) :
  goodb D m s = true -> goodbP D (fun _ => true) m s = true.
Proof.
  induction m as [y|T oc k IH]; intros Hm.
  - reflexivity.
  - destruct oc; cbn [goodb goodbP] in Hm |- *; try discriminate Hm;
      try (apply IH; exact Hm).
    apply andb_prop in Hm as [HD Hk]. rewrite HD. cbn. apply IH; exact Hk.
Qed.

(* ===================================================================== *)
(* §2 The structural rules.                                               *)
(* ===================================================================== *)

(* The Q-rule: the head's leaf predicate becomes a HYPOTHESIS for the
   continuation -- how classification flows through the clause spine.     *)
Lemma goodbP_bind_Q (D : register -> bool) {X Y} (Q : X -> bool) (P : Y -> bool)
      (m : M X) (f : X -> M Y) (s : mstate) :
  goodbP D Q m s = true ->
  (forall x, Q x = true -> goodbP D P (f x) s = true) ->
  goodbP D P (Defs.bind m f) s = true.
Proof.
  intros Hm Hf; revert Hm.
  induction m as [y|T oc k IH]; intros Hm.
  - rewrite bind_Ret. apply Hf. exact Hm.
  - rewrite bind_Next.
    destruct oc; cbn [goodbP] in Hm |- *; try discriminate Hm;
      try (apply IH; exact Hm).
    apply andb_prop in Hm as [HD Hk]. rewrite HD. cbn. apply IH; exact Hk.
Qed.

Lemma goodbP_bind_forall (D : register -> bool) {X Y} (P : Y -> bool)
      (m : M X) (f : X -> M Y) (s : mstate) :
  goodbP D (fun _ => true) m s = true ->
  (forall x, goodbP D P (f x) s = true) ->
  goodbP D P (Defs.bind m f) s = true.
Proof.
  intros Hm Hf. apply (goodbP_bind_Q D (fun _ => true) P m f s Hm).
  intros x _. apply Hf.
Qed.

(* Value-pinning: when the head's exec value at s is KNOWN (closed config
   probes at the concrete dstateU), only that continuation is traversed --
   this is what keeps disabled-extension families out of the image.       *)
Lemma goodbP_bind_val (D : register -> bool) {X Y} (P : Y -> bool)
      (m : M X) (f : X -> M Y) (s : mstate) (v : X) :
  exec m s = Some (v, s) ->
  goodbP D (fun _ => true) m s = true ->
  goodbP D P (f v) s = true ->
  goodbP D P (Defs.bind m f) s = true.
Proof.
  intros He Hm Hf; revert He Hm.
  induction m as [y|T oc k IH]; intros He Hm.
  - rewrite bind_Ret. cbn [exec] in He.
    assert (y = v) as -> by congruence. exact Hf.
  - rewrite bind_Next.
    destruct oc; cbn [exec] in He; cbn [goodbP] in Hm |- *; try discriminate Hm;
      try (apply IH; assumption).
    apply andb_prop in Hm as [HD Hk]. rewrite HD. cbn. apply IH; assumption.
Qed.

Lemma goodbP_read_reg (D : register -> bool) {X} (P : X -> bool) (r : register)
      (f : type_of_register r -> M X) (s : mstate) :
  D r = true ->
  goodbP D P (f (register_lookup r s.(sregs))) s = true ->
  goodbP D P (Defs.bind (Defs.read_reg r) f) s = true.
Proof.
  intros HD Hf.
  change (goodbP D P (Defs.bind (Defs.read_reg r) f) s)
    with (andb (D r) (goodbP D P (f (register_lookup r s.(sregs))) s)).
  rewrite HD, Hf. reflexivity.
Qed.

(* Value pinning needs an exec VALUE at the concrete dstateU, but a
   vm_compute'd exec equation reads back the (huge) normalized register
   file in the Some(_, state) result.  [bval] is the value-only mirror of
   exec along read-only paths: its readback is just Some v.               *)
Fixpoint bval {X} (m : M X) (s : mstate) {struct m} : option X :=
  match m with
  | Interface.Ret y => Some y
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option X with
       | Interface.RegRead r _ => fun k => bval (k (register_lookup r s.(sregs))) s
       | Interface.InstrAnnounce _   => fun k => bval (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => bval (k tt) s
       | Interface.Barrier _         => fun k => bval (k tt) s
       | Interface.CacheOp _         => fun k => bval (k tt) s
       | Interface.TlbOp _           => fun k => bval (k tt) s
       | Interface.TakeException _   => fun k => bval (k tt) s
       | Interface.ReturnException _ => fun k => bval (k tt) s
       | Interface.TranslationStart _=> fun k => bval (k tt) s
       | Interface.TranslationEnd _  => fun k => bval (k tt) s
       | Interface.CycleCount        => fun k => bval (k tt) s
       | Interface.Message _         => fun k => bval (k tt) s
       | Interface.GetCycleCount     => fun k => bval (k 0%Z) s
       | _ => fun _ => None
       end) k
  end.

Lemma bval_exec {X} (m : M X) (s : mstate) (v : X) :
  bval m s = Some v -> exec m s = Some (v, s).
Proof.
  induction m as [y|T oc k IH]; intros Hb.
  - cbn in Hb. injection Hb as <-. reflexivity.
  - destruct oc; cbn [bval exec] in Hb |- *; try discriminate Hb; apply IH; exact Hb.
Qed.

Lemma goodbP_bind_bval (D : register -> bool) {X Y} (P : Y -> bool)
      (m : M X) (f : X -> M Y) (s : mstate) (v : X) :
  bval m s = Some v ->
  goodbP D (fun _ => true) m s = true ->
  goodbP D P (f v) s = true ->
  goodbP D P (Defs.bind m f) s = true.
Proof.
  intros Hb. apply (goodbP_bind_val D P m f s v (bval_exec m s v Hb)).
Qed.

(* and_boolM whose LEFT side is concretely false: short-circuits without
   ever running the right side.                                           *)
Lemma exec_and_lfalse (l r : M bool) (s : mstate) :
  exec l s = Some (false, s) ->
  exec (and_boolM l r) s = Some (false, s).
Proof.
  intros Hl. unfold and_boolM. rewrite exec_bind, Hl. apply exec_returnm.
Qed.

(* and_boolM whose RIGHT side is concretely false (its left side may
   depend on symbolic instruction bits): the conjunction is false however
   the left side evaluates.                                               *)
Lemma exec_and_rfalse (D : register -> bool) (l r : M bool) (s : mstate) :
  goodb D l s = true ->
  exec r s = Some (false, s) ->
  exec (and_boolM l r) s = Some (false, s).
Proof.
  intros Hl Hr.
  destruct (goodb_exec_total D l s Hl) as [lb Hlb].
  unfold and_boolM. rewrite exec_bind, Hlb.
  destruct lb; [exact Hr | apply exec_returnm].
Qed.

(* The clause-spine rule.                                                 *)
Definition optP {X} (P : X -> bool) (o : option X) : bool :=
  match o with Some x => P x | None => true end.

Lemma goodbP_spine (D : register -> bool) {X} (P : X -> bool)
      (c : M (option X)) (rest : M X) (s : mstate) :
  goodbP D (optP P) c s = true ->
  goodbP D P rest s = true ->
  goodbP D P (Defs.bind c (fun o => match o with Some r => returnM r | None => rest end)) s = true.
Proof.
  intros Hc Hrest. apply (goodbP_bind_Q D (optP P) P c _ s Hc).
  intros [i|] HQ; [exact HQ | exact Hrest].
Qed.

(* The decoder's LAST clause chains through a pure match instead (the
   [let w := match o with Some r => r | None => ILLEGAL _ end in returnM w]
   tail) -- same transport, default leaf instead of a rest chain.         *)
Lemma goodbP_spine_pure (D : register -> bool) {X} (P : X -> bool)
      (c : M (option X)) (dflt : X) (s : mstate) :
  goodbP D (optP P) c s = true ->
  P dflt = true ->
  goodbP D P (Defs.bind c (fun o => returnM (match o with Some r => r | None => dflt end))) s = true.
Proof.
  intros Hc Hd. apply (goodbP_bind_Q D (optP P) P c _ s Hc).
  intros [i|] HQ; [exact HQ | exact Hd].
Qed.

(* ===================================================================== *)
(* §3 The traversal driver.                                               *)
(* ===================================================================== *)

Ltac dtp_leaf :=
  lazymatch goal with
  | |- goodbP ?D ?P (returnM ?v) ?s = true =>
      first [ reflexivity
            | change (goodbP D P (returnM v) s) with (P v);
              cbv beta iota delta [optP] ]
  end.

(* Pin a probe head to its concrete boolean at dstateU.

   COST DISCIPLINE: [eval vm_compute in] is only ever run on CLOSED
   probes (currentlyEnabled/virtual_memory_supported/zicfiss chains) --
   their readback is a literal [Some b].  Never vm-eval a term containing
   instruction bits: if its value is stuck, the readback of the stuck
   vm-normal-form is enormous (this, not the evaluation, is what made the
   naive pin arm take minutes).  Goal-level [vm_compute; reflexivity]
   equations are fine even when a DEAD branch mentions the word: the dead
   branch is discarded during evaluation and never read back.            *)
Ltac dtp_pin_here D P h f s b :=
  apply (goodbP_bind_bval D P h f s b);
  [ vm_compute; reflexivity | vm_compute; reflexivity | cbv beta ].

Ltac dtp_pin_closed D P h f s :=
  let r := eval vm_compute in (bval h s) in
  lazymatch r with
  | Some true => dtp_pin_here D P h f s true
  | Some false => dtp_pin_here D P h f s false
  end.

(* and_boolM whose left side is symbolic (instruction bits) but whose
   right side is a concretely-false closed probe chain (the shadow-stack
   pattern): the conjunction is false however the left side evaluates.    *)
Ltac dtp_pin_rfalse D P l r f s :=
  let rv := eval vm_compute in (bval r s) in
  lazymatch rv with
  | Some false =>
      apply (goodbP_bind_val D P (and_boolM l r) f s false);
      [ apply (exec_and_rfalse D l r s);
          [ solve [repeat dt_step]
          | apply bval_exec; vm_compute; reflexivity ]
      | apply goodbP_top; apply (goodb_and_boolM D l r s);
          [ solve [repeat dt_step] | solve [repeat dt_step] ]
      | cbv beta ]
  end.

Ltac dtp_pin :=
  lazymatch goal with
  | |- goodbP ?D ?P (Defs.bind ?h ?f) ?s = true =>
      lazymatch h with
      | currentlyEnabled _ => dtp_pin_closed D P h f s
      | virtual_memory_supported _ => dtp_pin_closed D P h f s
      | zicfiss_xSSE _ => dtp_pin_closed D P h f s
      | and_boolM (currentlyEnabled ?e) ?r =>
          (* decide by the (closed) gate alone; when the gate is ON the
             conjunction is only pinnable if the right side is itself a
             closed probe (chain): plain gate (C_SEXT_B), gate-disjunction
             (C_MUL), privilege-read chain (SSRDP), or a nested gated
             chain (C_SSPUSH) -- never a word-dependent returnM.          *)
          let ev := eval vm_compute in (bval (currentlyEnabled e) s) in
          lazymatch ev with
          | Some false => dtp_pin_here D P h f s false
          | Some true =>
              lazymatch r with
              | Defs.bind (Defs.read_reg _) _ => dtp_pin_closed D P h f s
              | zicfiss_xSSE _ => dtp_pin_closed D P h f s
              | currentlyEnabled _ => dtp_pin_closed D P h f s
              | or_boolM (currentlyEnabled _) (currentlyEnabled _) =>
                  dtp_pin_closed D P h f s
              | and_boolM (currentlyEnabled ?e2) ?r2 =>
                  let ev2 := eval vm_compute in (bval (currentlyEnabled e2) s) in
                  lazymatch ev2 with
                  | Some false => dtp_pin_here D P h f s false
                  | Some true =>
                      lazymatch r2 with
                      | Defs.bind (Defs.read_reg _) _ => dtp_pin_closed D P h f s
                      | currentlyEnabled _ => dtp_pin_closed D P h f s
                      end
                  end
              end
          end
      | and_boolM (and_boolM (currentlyEnabled ?e0) ?l2) ?r =>
          (* closed gated chain on the LEFT, word test on the right (the
             compressed shadow-stack shape): pin when the chain is false *)
          lazymatch l2 with
          | returnM _ => fail
          | _ =>
              let lv := eval vm_compute in (bval (and_boolM (currentlyEnabled e0) l2) s) in
              lazymatch lv with
              | Some false =>
                  apply (goodbP_bind_val D P h f s false);
                  [ apply exec_and_lfalse; apply bval_exec; vm_compute; reflexivity
                  | vm_compute; reflexivity
                  | cbv beta ]
              end
          end
      | and_boolM (returnM ?x) (currentlyEnabled ?e) =>
          (* symbolic left, closed gate right (the ZBA_RTYPE shape) *)
          let ev := eval vm_compute in (bval (currentlyEnabled e) s) in
          lazymatch ev with
          | Some false => dtp_pin_rfalse D P (returnM x) (currentlyEnabled e) f s
          end
      | and_boolM (returnM ?x) (and_boolM (currentlyEnabled ?e2) ?r2) =>
          lazymatch r2 with
          | returnM _ => fail  (* word-dependent right: no pin *)
          | _ => dtp_pin_rfalse D P (returnM x) (and_boolM (currentlyEnabled e2) r2) f s
          end
      end
  end.

Ltac dtp_spine :=
  lazymatch goal with
  | |- goodbP _ _ (Defs.bind _ ?f) _ = true =>
      (* The decoder's clause spine is either syntactically immediate or one
         bind-association below a boolean feature gate.  Dispatch on those
         shapes before asking unification to convert the polymorphic spine
         lemmas; trying both lemmas at every generic bind dominates this
         thousand-goal traversal. *)
      lazymatch f with
      | (fun o => match o with
                  | Some r => returnM r
                  | None => _
                  end) => apply goodbP_spine
      | (fun _ => Defs.bind _
                    (fun o => match o with
                              | Some r => returnM r
                              | None => _
                              end)) => apply goodbP_spine
      | (fun o => returnM (match o with
                           | Some r => r
                           | None => _
                           end)) => apply goodbP_spine_pure
      | (fun _ => Defs.bind _
                    (fun o => returnM (match o with
                                       | Some r => r
                                       | None => _
                                       end))) => apply goodbP_spine_pure
      end
  end.

Ltac dtp_readreg :=
  lazymatch goal with
  | |- goodbP _ _ (Defs.bind (Defs.read_reg _) _) _ = true =>
      apply goodbP_read_reg; [ vm_compute; reflexivity | cbv beta ]
  end.

Ltac dtp_if :=
  lazymatch goal with
  | |- goodbP _ _ (if ?g then _ else _) _ = true =>
      tryif constr_eq g true then cbv iota
      else tryif constr_eq g false then cbv iota
      else (let E := fresh "E" in destruct g eqn:E)
  end.

Ltac dtp_let :=
  lazymatch goal with
  | |- goodbP _ _ (let x := _ in _) _ = true => cbv zeta
  end.

Ltac dtp_match :=
  lazymatch goal with
  | |- goodbP _ _ (match ?x with _ => _ end) _ = true =>
      tryif is_var x then destruct x
      else first [ progress (cbv beta iota) | let E := fresh "E" in destruct x eqn:E ]
  end.

(* generic bind: head is value-irrelevant, solved in goodb-world by the
   DecodeTotalU driver (probes, mappers, and_boolM, nested binds).        *)
Ltac dtp_bind :=
  lazymatch goal with
  | |- goodbP _ _ (Defs.bind _ _) _ = true =>
      apply goodbP_bind_forall;
      [ apply goodbP_top; solve [repeat dt_step]
      | let x := fresh "x" in intros x ]
  end.

(* pure boolean leaf goals (P applied to an if/match over symbolic bits)  *)
Ltac dtp_pure :=
  lazymatch goal with
  | |- goodbP _ _ _ _ = true => fail
  | |- _ = true =>
      first [ reflexivity
            | apply bit0_concat0_20
            | apply bit0_concat0_12
            | match goal with |- context[if ?g then _ else _] =>
                let E := fresh "E" in destruct g eqn:E end
            | match goal with |- context[match ?x with _ => _ end] =>
                tryif is_var x then destruct x else fail end ]
  end.

Ltac dtp_core :=
  first [ dtp_leaf | dtp_pin | dtp_readreg | dtp_spine
        | dtp_if | dtp_let | dtp_match | dtp_bind | dtp_pure ].

(* The LR/SC decode gate: [and_boolM (currentlyEnabled Ext_Zalrsc)
   (returnM (lrsc_width_valid width))].  Zalrsc is ON, so its value is
   [lrsc_width_valid width]; carry that as a Q-rule hypothesis into the
   Some-leaf so the classified set can pin LR/SC to widths {4,8} rather
   than the over-approximating {1,2,4,8} (the analog of goodbP_width_wide
   for the wide AMO width). *)
Lemma goodbP_zalrsc_gate (width : Z) :
  goodbP D_u (fun b => implb b (lrsc_width_valid width))
    (and_boolM (currentlyEnabled Ext_Zalrsc) (returnM (lrsc_width_valid width))) dstateU = true.
Proof.
  unfold and_boolM.
  apply (goodbP_bind_val D_u (fun b => implb b (lrsc_width_valid width))
           (currentlyEnabled Ext_Zalrsc)
           (fun l => if l then returnM (lrsc_width_valid width) else returnM false)
           dstateU true).
  - apply bval_exec. vm_compute. reflexivity.
  - apply goodbP_top. solve [repeat dt_step].
  - cbn match.
    change (goodbP D_u (fun b => implb b (lrsc_width_valid width)) (returnM (lrsc_width_valid width)) dstateU)
      with (implb (lrsc_width_valid width) (lrsc_width_valid width)).
    destruct (lrsc_width_valid width); reflexivity.
Qed.

(* ===================================================================== *)
(* §4 decodable_u: the COMPLETE set of instructions reachable by 32-bit   *)
(*    decode in the xv6 user-mode configuration (discovered by running    *)
(*    the traversal with an opaque predicate: exactly these 54            *)
(*    constructors reach a leaf; notably absent: all Zba/Zbb-only/Zbs     *)
(*    families, SLLIUW, LPAD (Zicfilp off), SSPUSH/SSPOPCHK/SSRDP         *)
(*    (senvcfg.SSE = 0), vector/compressed/hypervisor.  REV8/RORI/RORIW/  *)
(*    ZBB_RTYPE/ZBB_RTYPEW stay: their gate is Zbb OR Zbkb, and Zbkb is   *)
(*    on.  SSAMOSWAP stays: its decode gate checks only width+Zicfiss;    *)
(*    the xSSE check happens at execute.)                                 *)
(* ===================================================================== *)

Definition width_ok1248 (width : Z) : bool :=
  (width =? 1) || (width =? 2) || (width =? 4) || (width =? 8).

(* AMO's width comes through the WIDE mapping (word_width_wide), whose image
   is {1,2,4,8,16}. *)
Definition awidth_ok (width : Z) : bool :=
  (width =? 1) || (width =? 2) || (width =? 4) || (width =? 8) || (width =? 16).

Definition decodable_u (i : instruction) : bool :=
  match i with
  | ADDIW _ => true
  | AMO (_,_,_,_,_,width,_) => awidth_ok width
  (* JAL / BTYPE record the PAYLOAD invariant the decoder guarantees:
     the immediate's bit 0 is 0 (encdec appends '0').  [jump_to] ASSERTS
     target bit-0 (a false assert is STUCK, not a trap), so the
     classification needs this to run the control-flow arms. *)
  | BTYPE (imm, _, _, _) => eq_vec (access_vec_dec imm 0) ('b"0")
  | CLMUL _ => true | CLMULH _ => true | CLMULR _ => true
  | CSRImm _ => true | CSRReg _ => true
  | DIV _ => true | DIVW _ => true
  | EBREAK _ => true | ECALL _ => true
  | FENCE _ => true | FENCEI _ => true | FENCE_TSO _ => true
  | ILLEGAL _ => true | ITYPE _ => true
  | JAL (imm, _) => eq_vec (access_vec_dec imm 0) ('b"0")
  | JALR _ => true
  | LOAD (_,_,_,_,width) => width_ok1248 width
  | LOADRES (_,_,_,width,_) => lrsc_width_valid width
  | MRET _ => true | MUL _ => true | MULW _ => true
  | NTL _ => true | PAUSE _ => true
  | REM _ => true | REMW _ => true
  | REV8 _ => true | RORI _ => true | RORIW _ => true
  | RTYPE _ => true | RTYPEW _ => true
  | SFENCE_INVAL_IR _ => true | SFENCE_VMA _ => true | SFENCE_W_INVAL _ => true
  | SHIFTIOP _ => true | SHIFTIWOP _ => true | SINVAL_VMA _ => true
  | SRET _ => true | SSAMOSWAP _ => true
  | STORE (_,_,_,width) => width_ok1248 width
  | STORECON (_,_,_,_,width,_) => lrsc_width_valid width
  | UTYPE _ => true | WFI _ => true | WRS _ => true
  | ZBB_RTYPE _ => true | ZBB_RTYPEW _ => true
  | ZICBOM _ => true | ZICBOP _ => true | ZICBOZ _ => true
  | ZICOND_RTYPE _ => true
  | ZIMOP_MOP_R _ => true | ZIMOP_MOP_RR _ => true
  | _ => false
  end.

(* ===================================================================== *)
(* §5 The classified totality theorem.                                    *)
(* ===================================================================== *)

(* The WIDE (AMO) width comes through a MONADIC mapping [width_enc_wide_
   backwards X : M Z] whose image is {1,2,4,8,16} whenever the decode gate
   [width_enc_wide_backwards_matches X] holds.  The plain forall-bind rule
   ([dtp_bind]) would abstract the width to a fresh unconstrained [Z] and
   lose membership; instead carry it as a Q-rule hypothesis into the leaf. *)
Lemma goodbP_width_wide (X : mword 3) (s : mstate) :
  width_enc_wide_backwards_matches X = true ->
  goodbP D_u awidth_ok (width_enc_wide_backwards X) s = true.
Proof.
  unfold width_enc_wide_backwards_matches, width_enc_wide_backwards, awidth_ok.
  intro H.
  repeat match goal with
         | |- context[if ?g then _ else _] => let E := fresh "E" in destruct g eqn:E
         end;
    try discriminate H; reflexivity.
Qed.

Ltac dtp_width_wide :=
  lazymatch goal with
  | |- goodbP ?D ?P (Defs.bind (width_enc_wide_backwards ?X) ?k) ?s = true =>
      apply (goodbP_bind_Q D awidth_ok P (width_enc_wide_backwards X) k s);
      [ apply goodbP_width_wide;
        repeat match goal with
               | H : (let _ := _ in _) = true |- _ => cbv zeta in H
               | H : andb _ _ = true |- _ => apply andb_prop in H; destruct H
               end; assumption
      | let wd := fresh "wd" in let Hwd := fresh "Hwd" in
        intros wd Hwd; cbv [awidth_ok] in Hwd; cbv beta ]
  end.

(* The memory-width leaf: after [dtp_leaf] the goal is
   [decodable_u (LOAD/STORE/LOADRES/STORECON (..., width_enc_backwards X)) = true]
   (pure width, closed by case-splitting the eq_vec chain), or the AMO leaf
   [decodable_u (AMO (..., wd)) = true] with [wd] carried by [dtp_width_wide]
   (closed by the introduced membership hypothesis). *)
Ltac dtp_width :=
  lazymatch goal with
  | |- _ = true =>
      cbv [decodable_u awidth_ok width_ok1248 width_enc_backwards];
      first [ assumption
            | reflexivity
            | solve [ repeat (match goal with
                              | |- context[if ?g then _ else _] =>
                                  let E := fresh "E" in destruct g eqn:E
                              end);
                      first [ reflexivity | vm_compute; reflexivity ] ] ]
  end.

Ltac dtp_lrsc :=
  lazymatch goal with
  | |- goodbP ?D ?P (Defs.bind (and_boolM (currentlyEnabled Ext_Zalrsc) (returnM (lrsc_width_valid ?w))) ?k) ?s = true =>
      apply (goodbP_bind_Q D (fun b => implb b (lrsc_width_valid w)) P
               (and_boolM (currentlyEnabled Ext_Zalrsc) (returnM (lrsc_width_valid w))) k s);
      [ apply goodbP_zalrsc_gate
      | let b := fresh "b" in let Hb := fresh "Hb" in
        intros b Hb; cbv zeta; destruct b; cbn [implb] in Hb;
        [ dtp_leaf; cbv [decodable_u]; exact Hb | dtp_leaf ] ]
  end.

Lemma goodbP_encdec_u (w : mword 32) :
  goodbP D_u decodable_u (ext_decode w) dstateU = true.
Proof.
  unfold ext_decode, encdec_backwards. cbv beta zeta.
  repeat (first [ dtp_lrsc | dtp_width_wide | dtp_core | dtp_width ]).
Qed.

(* Every 32-bit word decodes -- to a SINGLE instruction, shared by every
   state agreeing with the U-mode reference on the decode read set, and
   that instruction lies in the explicit set [decodable_u].               *)
Theorem decode_total_u_set (w : mword 32) :
  exists i, decodable_u i = true /\
    forall s, agree_on D_u s dstateU -> exec (ext_decode w) s = Some (i, s).
Proof.
  destruct (goodbP_exec D_u decodable_u (ext_decode w) dstateU dstateU
              (fun r _ => eq_refl) (goodbP_encdec_u w)) as (i & Hi & _ & HP).
  exists i. split; [exact HP|]. intros s Hag.
  destruct (goodbP_exec D_u decodable_u (ext_decode w) dstateU s
              (fun r HD => eq_sym (Hag r HD)) (goodbP_encdec_u w)) as (x & Hx & Hs & _).
  assert (i = x) as -> by congruence.
  exact Hs.
Qed.

(* ===================================================================== *)
(* §6 The compressed (16-bit) decoder: same machinery, second image.      *)
(*    MISA_C has C enabled, so user code CAN execute compressed           *)
(*    instructions; this is the decode-side completion for that path.     *)
(*    The discovered image is the Zca base set + the Zcb subset that      *)
(*    needs no Zba/Zbb (C_LBU/C_LH/C_LHU/C_SB/C_SH/C_ZEXT_B/C_NOT/C_MUL)  *)
(*    + hints (C_NTL, ZCMOP, C_NOP) + the C_ILLEGAL fallback.  Excluded:  *)
(*    C_JAL (RV32-only), C_SEXT_B/C_SEXT_H/C_ZEXT_H (need Zbb, off),      *)
(*    C_ZEXT_W (needs Zba, off), C_SSPUSH/C_SSPOPCHK (senvcfg.SSE = 0;    *)
(*    their gate is the left-nested closed chain handled by the           *)
(*    exec_and_lfalse pin).  No FP: this model build generates no         *)
(*    FLD/FSD clauses in either decoder.                                  *)
(* ===================================================================== *)

Definition decodable_c (i : instruction) : bool :=
  match i with
  | C_ADD _ => true | C_ADDI _ => true | C_ADDI16SP _ => true
  | C_ADDI4SPN _ => true | C_ADDIW _ => true | C_ADDW _ => true
  | C_AND _ => true | C_ANDI _ => true
  | C_BEQZ _ => true | C_BNEZ _ => true
  | C_EBREAK _ => true | C_ILLEGAL _ => true
  | C_J _ => true | C_JALR _ => true | C_JR _ => true
  | C_LBU _ => true | C_LD _ => true | C_LDSP _ => true
  | C_LH _ => true | C_LHU _ => true
  | C_LI _ => true | C_LUI _ => true
  | C_LW _ => true | C_LWSP _ => true
  | C_MUL _ => true | C_MV _ => true
  | C_NOP _ => true | C_NOT _ => true | C_NTL _ => true
  | C_OR _ => true
  | C_SB _ => true | C_SD _ => true | C_SDSP _ => true
  | C_SH _ => true
  | C_SLLI _ => true | C_SRAI _ => true | C_SRLI _ => true
  | C_SUB _ => true | C_SUBW _ => true
  | C_SW _ => true | C_SWSP _ => true
  | C_XOR _ => true | C_ZEXT_B _ => true
  | ZCMOP _ => true
  | _ => false
  end.

Lemma goodbP_encdec_c (w : mword 16) :
  goodbP D_u decodable_c (ext_decode_compressed w) dstateU = true.
Proof.
  unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta zeta.
  repeat dtp_core.
Qed.

(* Every 16-bit halfword decodes -- to a SINGLE instruction in the
   explicit compressed set, shared by every D_u-agreeing state.           *)
Theorem decode_total_c_set (w : mword 16) :
  exists i, decodable_c i = true /\
    forall s, agree_on D_u s dstateU ->
      exec (ext_decode_compressed w) s = Some (i, s).
Proof.
  destruct (goodbP_exec D_u decodable_c (ext_decode_compressed w) dstateU dstateU
              (fun r _ => eq_refl) (goodbP_encdec_c w)) as (i & Hi & _ & HP).
  exists i. split; [exact HP|]. intros s Hag.
  destruct (goodbP_exec D_u decodable_c (ext_decode_compressed w) dstateU s
              (fun r HD => eq_sym (Hag r HD)) (goodbP_encdec_c w)) as (x & Hx & Hs & _).
  assert (i = x) as -> by congruence.
  exact Hs.
Qed.
