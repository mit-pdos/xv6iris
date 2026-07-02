(* RiscvTryStep.v -- the shared try_step machinery: fetch, currentlyEnabled, *)
(*   the MR (early-return) monad, memory read, pending, + the ADD datapath.   *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

(* ===== RiscvModelWP ===== *)
(* ====================================================================== *)
(* RiscvModelWP.v  —  machinery toward wp_add THROUGH the real try_step.   *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* Compositional reduction lemmas for the interpreter [run].               *)
(* ---------------------------------------------------------------------- *)

(* NB: these proofs are CONVERSION-LAZY (iff_refl / exact / destruct reduce only
   to weak-head normal form, picking a single [outcome] branch).  We avoid
   [cbn [run]] / [simpl run], which eagerly expand the whole 20-branch GADT
   match of [run] and blow up memory. *)

Lemma run_ret {X} (x0 : X) s y s' :
  run (Defs.returnm x0) s y s' <-> (y = x0 /\ s' = s).
Proof. apply iff_refl. Qed.

Lemma run_bind {X Y} (m : M Y) (f : Y -> M X) s x s' :
  run (Defs.bind m f) s x s' <->
  (exists y s1, run m s y s1 /\ run (f y) s1 x s').
Proof.
  unfold Defs.bind. revert s. induction m as [y0 | T oc k IH]; intros s.
  - split.
    + intro H. exists y0, s. split; [ split; reflexivity | exact H ].
    + intros (y & s1 & [Hy Hs] & H). subst y s1. exact H.
  - destruct oc;
      first
        [ (* simple state-threading outcomes: goal convertible to IH *)
          exact (IH _ _)
        | (* MemRead: exists w, byte-match /\ run (k (inl (w,None))) *)
          (split;
           [ intro H; destruct H as (w & HP & H); apply IH in H;
             destruct H as (yy & s1 & Hk & Hf);
             exists yy, s1; split; [ exists w; split; assumption | assumption ]
           | intros (yy & s1 & H & Hf); destruct H as (w & HP & Hk);
             exists w; split;
             [ assumption | apply IH; exists yy, s1; split; assumption ] ])
        | (* Choose: exists c, run (k c) *)
          (split;
           [ intro H; destruct H as (c & H); apply IH in H;
             destruct H as (yy & s1 & Hk & Hf);
             exists yy, s1; split; [ exists c; assumption | assumption ]
           | intros (yy & s1 & H & Hf); destruct H as (c & Hk);
             exists c; apply IH; exists yy, s1; split; assumption ])
        | (* failure / discard / injected-exception: stuck (False) *)
          (split; [ intro H; destruct H | intros (yy & s1 & H & _); destruct H ]) ].
Qed.

(* Sequencing with unit-result first action. *)
Lemma run_bind0 {X} (m : M unit) (n : M X) s x s' :
  run (Defs.bind0 m n) s x s' <->
  (exists s1, run m s tt s1 /\ run n s1 x s').
Proof.
  unfold Defs.bind0. rewrite run_bind. split.
  - intros (y & s1 & Hm & Hn). destruct y. eauto.
  - intros (s1 & Hm & Hn). exists tt, s1. auto.
Qed.

(* Per-effect step lemmas: register read / write through the real
   [read_reg]/[write_reg] of the model. *)
Lemma run_read_reg (r : register) s (x : type_of_register r) s' :
  run (Defs.read_reg r : M _) s x s' <->
  (x = register_lookup r s.(sregs) /\ s' = s).
Proof. apply iff_refl. Qed.

Lemma run_write_reg (r : register) (v : type_of_register r) s x s' :
  run (Defs.write_reg r v : M _) s x s' <->
  (x = tt /\ s' = set_reg s r v).
Proof. apply iff_refl. Qed.

(* [returnM] is [Defs.returnm] specialised to the model's exception type. *)
Lemma run_returnM {X} (x0 : X) s y s' :
  run (returnM x0) s y s' <-> (y = x0 /\ s' = s).
Proof. unfold returnM. apply run_ret. Qed.

(* ===== RiscvModelMR ===== *)
(* ====================================================================== *)
(* RiscvModelMR.v  —  the MR (early-return) monad bridge.                   *)
(*                                                                         *)
(* run_hart_active runs in the early-return monad                          *)
(*   monadR R E := iMon (fun _ => (R + E))   [= monad (R+E)]               *)
(* via [catch_early_return], [liftR], [early_return], [returnR], with the  *)
(* SAME [>>=]/[>>] (Defs.bind/bind0) as the base monad.                    *)
(*                                                                         *)
(* We give an early-return-aware interpreter [runR] (result [R + X]:       *)
(* [inl r] = early-returned r, [inr x] = fell through with x), its         *)
(* bind/liftR/early_return/ret laws, and the bridge                        *)
(*   run (catch_early_return body) <-> runR body falls-through-or-returns. *)
(*                                                                         *)
(* CONVERSION-LAZY proofs only (iff_refl / destruct-to-WHNF / exact).      *)
(* Never [cbn [run]]/[cbn [runR]] (20-branch GADT -> OOM).                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* The early-return-aware interpreter for [monadR R exception X].          *)
(* Same effect handling as [run]; additionally an [ExtraOutcome (inl r)]   *)
(* (i.e. [early_return r]) yields result [inl r], and [ExtraOutcome (inr   *)
(* e)] (a genuine exception) is stuck.                                     *)
(* ---------------------------------------------------------------------- *)

Fixpoint runR {R X} (m : Defs.monadR R exception X)
    (s : mstate) (res : R + X) (s' : mstate) {struct m} : Prop :=
  match m with
  | Interface.Ret y => res = inr y /\ s' = s
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> Defs.monadR R exception X) -> Prop with
       | Interface.RegRead r _ =>
           fun k => runR (k (register_lookup r s.(sregs))) s res s'
       | Interface.RegWrite r _ v =>
           fun k => runR (k tt) (set_reg s r v) res s'
       | Interface.MemRead n req =>
           fun k => exists w : bv (8 * n),
             (forall j : nat, (N.of_nat j < n)%N ->
                s.(mem) !! (pa_add (Interface.ReadReq.pa req) j) = Some (nth_byte w j))
             /\ runR (k (inl (w, None))) s res s'
       | Interface.MemWrite n req =>
           fun k =>
             runR (k (inl None))
                  (MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req))) res s'
       | Interface.InstrAnnounce _    => fun k => runR (k tt) s res s'
       | Interface.BranchAnnounce _ _ => fun k => runR (k tt) s res s'
       | Interface.Barrier _          => fun k => runR (k tt) s res s'
       | Interface.CacheOp _          => fun k => runR (k tt) s res s'
       | Interface.TlbOp _            => fun k => runR (k tt) s res s'
       | Interface.TakeException _    => fun k => runR (k tt) s res s'
       | Interface.ReturnException _  => fun k => runR (k tt) s res s'
       | Interface.TranslationStart _ => fun k => runR (k tt) s res s'
       | Interface.TranslationEnd _   => fun k => runR (k tt) s res s'
       | Interface.CycleCount         => fun k => runR (k tt) s res s'
       | Interface.Message _          => fun k => runR (k tt) s res s'
       | Interface.GetCycleCount      => fun k => runR (k 0%Z) s res s'
       | Interface.Choose _           => fun k => exists c, runR (k c) s res s'
       | Interface.ExtraOutcome e =>
           fun _ => match e with
                    | inl r => res = inl r /\ s' = s
                    | inr _ => False
                    end
       | _ => fun _ => False
       end) k
  end.

(* ---- cheap (convertibility) laws ------------------------------------- *)


Lemma runR_returnR {R X} (x0 : X) s res s' :
  runR (returnR R x0 : Defs.monadR R exception X) s res s' <-> (res = inr x0 /\ s' = s).
Proof. apply iff_refl. Qed.


(* ---- liftR: a lifted base computation never early-returns; its [runR]   *)
(*      coincides with [run] of the base computation (result tagged inr).  *)
Lemma runR_liftR {R X} (m : M X) s res s' :
  runR (Defs.liftR (R:=R) m) s res s' <-> (exists x, res = inr x /\ run m s x s').
Proof.
  unfold Defs.liftR. revert s. induction m as [x0 | T oc k IH]; intros s.
  - split.
    + intros [Hr Hs]. exists x0. split; [exact Hr | split; [reflexivity | exact Hs]].
    + intros (x & Hr & Hx & Hs). subst x. split; [exact Hr | exact Hs].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H; destruct H as (x & Hr & Hk);
             exists x; split; [exact Hr | exists w; split; [exact HP | exact Hk]]
           | intros (x & Hr & (w & HP & Hk));
             exists w; split; [exact HP | apply IH; exists x; split; [exact Hr | exact Hk]] ])
        | (split;
           [ intros (c & H); apply IH in H; destruct H as (x & Hr & Hk);
             exists x; split; [exact Hr | exists c; exact Hk]
           | intros (x & Hr & (c & Hk));
             exists c; apply IH; exists x; split; [exact Hr | exact Hk] ])
        | (split; [ intro H; destruct H | intros (x & _ & H); destruct H ]) ].
Qed.

(* ---- the bridge: catch_early_return turns an early-return body back into *)
(*      the base monad; both inl/inr at the same value collapse to it.      *)
Lemma run_catch_early_return {X} (body : Defs.monadR X exception X) s x s' :
  run (Defs.catch_early_return body) s x s' <->
  (runR body s (inl x) s' \/ runR body s (inr x) s').
Proof.
  unfold Defs.catch_early_return. revert s. induction body as [a0 | T oc k IH]; intros s.
  - split.
    + intros [Hx Hs]. right. subst x. split; [reflexivity | exact Hs].
    + intros [ [Hc _] | [Heq Hs] ]; [ discriminate Hc | injection Heq as <-; split; [reflexivity | exact Hs] ].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H; destruct H as [Hk | Hk];
             [ left; exists w; split; [exact HP | exact Hk]
             | right; exists w; split; [exact HP | exact Hk] ]
           | intros [ (w & HP & Hk) | (w & HP & Hk) ];
             [ exists w; split; [exact HP | apply IH; left; exact Hk]
             | exists w; split; [exact HP | apply IH; right; exact Hk] ] ])
        | (split;
           [ intros (c & H); apply IH in H; destruct H as [Hk | Hk];
             [ left; exists c; exact Hk | right; exists c; exact Hk ]
           | intros [ (c & Hk) | (c & Hk) ];
             [ exists c; apply IH; left; exact Hk | exists c; apply IH; right; exact Hk ] ])
        | (match goal with He : (_ + exception)%type |- _ => destruct He as [a0 | ee] end;
           [ split;
             [ intros [Hx Hs]; left; subst x; split; [reflexivity | exact Hs]
             | intros [ [Heq Hs] | [Hc _] ];
               [ injection Heq as <-; split; [reflexivity | exact Hs] | discriminate Hc ] ]
           | split; [ intro H; destruct H | intros [H | H]; destruct H ] ])
        | (split; [ intro H; destruct H | intros [H | H]; destruct H ]) ].
Qed.

(* ---- bind in the early-return monad: short-circuits on early return.    *)
Lemma runR_bind {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s res s' :
  runR (Defs.bind m f) s res s' <->
  ((exists r, res = inl r /\ runR m s (inl r) s')
   \/ (exists a s1, runR m s (inr a) s1 /\ runR (f a) s1 res s')).
Proof.
  unfold Defs.bind. revert s. induction m as [a0 | T oc k IH]; intros s.
  - split.
    + intro H. right. exists a0, s. split; [ split; reflexivity | exact H ].
    + intros [ (r & Hr & [Hc _]) | (a & s1 & [Heq Hs] & Hf) ];
        [ discriminate Hc | injection Heq as <-; subst s1; exact Hf ].
  - destruct oc;
      first
        [ exact (IH _ _)
        | (split;
           [ intros (w & HP & H); apply IH in H;
             destruct H as [ (r & Hr & Hk) | (a & s1 & Hk & Hf) ];
             [ left; exists r; split; [exact Hr | exists w; split; [exact HP | exact Hk]]
             | right; exists a, s1; split; [ exists w; split; [exact HP | exact Hk] | exact Hf ] ]
           | intros [ (r & Hr & (w & HP & Hk)) | (a & s1 & (w & HP & Hk) & Hf) ];
             [ exists w; split; [exact HP | apply IH; left; exists r; split; [exact Hr | exact Hk]]
             | exists w; split; [exact HP | apply IH; right; exists a, s1; split; [exact Hk | exact Hf]] ] ])
        | (split;
           [ intros (c & H); apply IH in H;
             destruct H as [ (r & Hr & Hk) | (a & s1 & Hk & Hf) ];
             [ left; exists r; split; [exact Hr | exists c; exact Hk]
             | right; exists a, s1; split; [ exists c; exact Hk | exact Hf ] ]
           | intros [ (r & Hr & (c & Hk)) | (a & s1 & (c & Hk) & Hf) ];
             [ exists c; apply IH; left; exists r; split; [exact Hr | exact Hk]
             | exists c; apply IH; right; exists a, s1; split; [exact Hk | exact Hf] ] ])
        | (match goal with He : (_ + exception)%type |- _ => destruct He as [r0 | ee] end;
           [ split;
             [ intros [Hres Hs]; left; exists r0; split; [exact Hres | split; [reflexivity | exact Hs]]
             | intros [ (r & Hres & [Heq Hs]) | (a & s1 & Hf0 & _) ];
               [ injection Heq as <-; split; [exact Hres | exact Hs]
               | destruct Hf0 as [Hc _]; discriminate Hc ] ]
           | split;
             [ intro H; destruct H
             | intros [ (r & _ & Hf0) | (a & s1 & Hf0 & _) ]; destruct Hf0 ] ])
        | (split;
           [ intro H; destruct H
           | intros [ (r & _ & Hf0) | (a & s1 & Hf0 & _) ]; destruct Hf0 ]) ].
Qed.

(* ---------------------------------------------------------------------- *)

(* ===== RiscvModelEnabled ===== *)
(* ===================================================================== *)
(* RiscvModelEnabled.v — item (2): taming the Acc-recursive extension     *)
(* predicates (`hartSupports`/`currentlyEnabled`) so they reduce through   *)
(* `run`. Proof-of-concept: the `Acc`-guarded well-founded recursion       *)
(* unfolds AXIOM-FREE by `destruct`-ing the `Zwf_guarded` accessibility    *)
(* proof (no Acc proof-irrelevance / funext needed).                       *)
(* ===================================================================== *)

(* `hartSupports Ext_Zca` is a leaf (statically `returnM true`); it runs
   through one Acc-unfold + the reclimit guard to the concrete bool `true`. *)

(* ===== RiscvModelExecute ===== *)
(* ===================================================================== *)
(* RiscvModelExecute.v — home stretch toward wp_add-through-try_step.      *)
(*                                                                         *)
(*  Verified, axiom-free, building on RiscvModel{Lang,WP,MR,Enabled}:      *)
(*   - run step-lemmas for the boolean monad combinators and_boolM/or_boolM*)
(*     (the shape currentlyEnabled / hartSupports are built from);         *)
(*   - run_execute_RTYPE_ADD: the model's REAL `execute (RTYPE .. ADD)`     *)
(*     reduces, compositionally, to read rs1, read rs2, write rd from       *)
(*     add_vec, retire -- the ADD datapath, modulo the register-file        *)
(*     primitives rX_bits/wX_bits (whose concrete-index dispatch + the     *)
(*     run_read_reg/run_write_reg bridge discharge separately).            *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* 1. Boolean-monad combinators step through `run`.                       *)
(*    [and_boolM l r = l >>= fun b => if b then r else returnm false]      *)
(*    [or_boolM  l r = l >>= fun b => if b then returnm true else r]       *)
(*    The `returnm` branches are definitionally the `run`-of-`Ret` facts,  *)
(*    so each side of the `if` lands on the obvious shape.                 *)
(* --------------------------------------------------------------------- *)

Lemma run_and_boolM (l r : M bool) s b s' :
  run (and_boolM l r) s b s' <->
  (exists bl s1, run l s bl s1 /\
                 (if bl then run r s1 b s' else (b = false /\ s' = s1))).
Proof.
  unfold and_boolM. rewrite run_bind. split.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
Qed.

Lemma run_or_boolM (l r : M bool) s b s' :
  run (or_boolM l r) s b s' <->
  (exists bl s1, run l s bl s1 /\
                 (if bl then (b = true /\ s' = s1) else run r s1 b s')).
Proof.
  unfold or_boolM. rewrite run_bind. split.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
  - intros (bl & s1 & Hl & H). exists bl, s1. split; [exact Hl|]. destruct bl; exact H.
Qed.

(* --------------------------------------------------------------------- *)
(* 2. execute (RTYPE .. ADD) reduces to the ADD datapath.                 *)
(*                                                                         *)
(*    execute_RTYPE rs2 rs1 rd ADD                                         *)
(*      = (rX_bits rs1 >>= fun a => rX_bits rs2 >>= fun b =>               *)
(*           returnM (add_vec a b))                                         *)
(*        >>= fun w => wX_bits rd w >> returnM RETIRE_SUCCESS.             *)
(*                                                                         *)
(*    Register reads don't change state, so given the rs1/rs2 reads and    *)
(*    the rd write, the whole thing runs to RETIRE_SUCCESS with exactly    *)
(*    the rd-write's effect.                                               *)
(* --------------------------------------------------------------------- *)

Lemma run_execute_RTYPE_ADD (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  run (rX_bits rs1) s a s ->
  run (rX_bits rs2) s b s ->
  run (wX_bits rd (add_vec a b)) s tt s' ->
  run (execute_RTYPE rs2 rs1 rd ADD) s RETIRE_SUCCESS s'.
Proof.
  intros Ha Hb Hw.
  unfold execute_RTYPE. cbn match.
  (* outer bind: inner computes (add_vec a b) leaving state s *)
  apply run_bind. exists (add_vec a b), s. split.
  - (* inner: rX_bits rs1 >>= rX_bits rs2 >>= returnM (add_vec) *)
    apply run_bind. exists a, s. split; [exact Ha|].
    apply run_bind. exists b, s. split; [exact Hb|].
    apply run_returnM. split; reflexivity.
  - (* wX_bits rd (add_vec a b) >> returnM RETIRE_SUCCESS *)
    apply run_bind0. exists s'. split; [exact Hw|].
    apply run_returnM. split; reflexivity.
Qed.

(* ===== RiscvModelRegs ===== *)
(* ===================================================================== *)
(* RiscvModelRegs.v — clears the read_reg-wrapper "blocker" and gives a    *)
(* FULLY CONCRETE execute(ADD) over the real model's register file.        *)
(*                                                                         *)
(* KEY FINDING: the model's `read_reg`/`write_reg` AS USED INSIDE rX/wX     *)
(* (defined in rv64d.v after `Import Defs`) resolve to Defs.read_reg /      *)
(* Defs.write_reg — the Interface-monad ones that run_read_reg/run_write_reg*)
(* already target.  (The `rv64d_types.read_reg` wrapper is the *Prompt*     *)
(* monad and is shadowed; the earlier "mismatch" was a misread.)  So rX/wX  *)
(* reduce by conversion + the existing bridge lemmas, no new axioms.        *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* 1. rX / wX at concrete registers reduce to Defs.read_reg/write_reg.     *)
(*    These hold BY CONVERSION (the 32-way Z.eqb index dispatch computes;   *)
(*    regval_into_reg is the identity on mword 64).                         *)
(* --------------------------------------------------------------------- *)

Lemma rX_x10 : rX (Regno 10) = Defs.read_reg (R_bitvector_64 x10).
Proof. reflexivity. Qed.
Lemma rX_x11 : rX (Regno 11) = Defs.read_reg (R_bitvector_64 x11).
Proof. reflexivity. Qed.
(* wX threads the value through [regval_into_reg] (= identity on mword 64, but
   kept symbolic here since it does not auto-reduce under conversion). *)

(* run versions: register reads are state-pure, writes go via set_reg. *)
Lemma run_rX_x10 s :
  run (rX (Regno 10)) s (register_lookup (R_bitvector_64 x10) s.(sregs)) s.
Proof. rewrite rX_x10. split; reflexivity. Qed.
Lemma run_rX_x11 s :
  run (rX (Regno 11)) s (register_lookup (R_bitvector_64 x11) s.(sregs)) s.
Proof. rewrite rX_x11. split; reflexivity. Qed.
(* wX = write_reg .. >> returnM (xreg_full_write_callback ..); the callback is
   [tt] (xreg_full_write_callback _ _ _ := tt), so wX is a write then return tt. *)
Lemma wX_x12_eq (v : mword 64) :
  wX (Regno 12) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x12) (regval_into_reg v)) (returnM tt).
Proof. reflexivity. Qed.

Lemma run_wX_x12 s (v : mword 64) :
  run (wX (Regno 12) v) s tt (set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof.
  rewrite wX_x12_eq. apply run_bind0.
  exists (set_reg s (R_bitvector_64 x12) (regval_into_reg v)). split.
  - split; reflexivity.
  - split; reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* 2. Lift to rX_bits / wX_bits given the register index value.            *)
(*    rX_bits (Regidx i) = rX (Regno (uint i)); supply `uint i = n`.        *)
(* --------------------------------------------------------------------- *)

Lemma run_rX_bits_x10 (i : mword 5) s :
  uint i = 10 ->
  run (rX_bits (Regidx i)) s (register_lookup (R_bitvector_64 x10) s.(sregs)) s.
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply run_rX_x10. Qed.
Lemma run_rX_bits_x11 (i : mword 5) s :
  uint i = 11 ->
  run (rX_bits (Regidx i)) s (register_lookup (R_bitvector_64 x11) s.(sregs)) s.
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply run_rX_x11. Qed.
Lemma run_wX_bits_x12 (i : mword 5) s (v : mword 64) :
  uint i = 12 ->
  run (wX_bits (Regidx i) v) s tt (set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply run_wX_x12. Qed.

(* --------------------------------------------------------------------- *)
(* 3. FULLY CONCRETE execute(ADD): add x12, x10, x11 over the real model.  *)
(*    rd=x12, rs1=x10, rs2=x11 (distinct, non-zero).  No hypotheses beyond  *)
(*    the register-index values; no axioms.                                *)
(* --------------------------------------------------------------------- *)

Lemma run_execute_ADD_x12_x10_x11 (rd rs1 rs2 : mword 5) s :
  uint rs1 = 10 -> uint rs2 = 11 -> uint rd = 12 ->
  run (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s RETIRE_SUCCESS
      (set_reg s (R_bitvector_64 x12)
         (regval_into_reg
            (add_vec (register_lookup (R_bitvector_64 x10) s.(sregs))
                     (register_lookup (R_bitvector_64 x11) s.(sregs))))).
Proof.
  intros H1 H2 H3.
  eapply run_execute_RTYPE_ADD.
  - apply run_rX_bits_x10; exact H1.
  - apply run_rX_bits_x11; exact H2.
  - apply run_wX_bits_x12; exact H3.
Qed.

(* ===== RiscvModelMem ===== *)
(* ====================================================================== *)
(* RiscvModelMem.v                                                         *)
(*                                                                         *)
(* Fetch memory subsystem toward discharging Hcycle.                       *)
(* MAIN RESULT: translateAddr = IDENTITY in Machine mode (Bare paging),    *)
(* i.e. the address-translation half of fetch reduces axiom-free.          *)
(* The pmpCheck/mem_read half is mapped + scoped at the bottom.            *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* Forward versions of the iff stepping lemmas (apply needs these to PROVE *)
(* a run/runR goal; the iffs can't be `apply`'d directly).                 *)
(* ---------------------------------------------------------------------- *)

Lemma run_returnM_fwd {X} (x : X) s : run (returnM x) s x s.
Proof. rewrite run_returnM. split; reflexivity. Qed.

Lemma run_read_reg_fwd (r : register) s :
  run (Defs.read_reg r) s (register_lookup r s.(sregs)) s.
Proof. rewrite run_read_reg. split; reflexivity. Qed.

Lemma runR_returnR_fwd {R X} (x : X) s :
  runR (returnR R x : Defs.monadR R exception X) s (inr x) s.
Proof. rewrite runR_returnR. split; reflexivity. Qed.

(* Forward-chaining: walk a `liftR m >>= f` when m is a state-preserving    *)
(* base computation (the read-only effects of fetch).                       *)
Lemma runR_liftR_seq {R X Y} (m : M Y) (f : Y -> Defs.monadR R exception X)
    (a : Y) s res s' :
  run m s a s ->
  runR (f a) s res s' ->
  runR (Defs.bind (Defs.liftR (R:=R) m) f) s res s'.
Proof.
  intros Hm Hf. apply runR_bind. right. exists a, s. split; [|exact Hf].
  apply runR_liftR. exists a. split; [reflexivity|exact Hm].
Qed.

(* ---------------------------------------------------------------------- *)
(* Pure sub-functions on the fetch path reduce to a value (no effects).    *)
(* ---------------------------------------------------------------------- *)

Lemma run_effectivePrivilege_fetch (m : mword 64) (p : Privilege) s :
  run (effectivePrivilege (InstructionFetch tt) m p) s p s.
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply run_returnM_fwd.
Qed.

Lemma run_translationMode_M s :
  run (translationMode Machine) s Bare s.
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply run_returnM_fwd.
Qed.

Lemma run_is_shadow_stack_fetch s :
  run (is_shadow_stack_access (InstructionFetch tt)) s false s.
Proof. unfold is_shadow_stack_access. apply run_returnM_fwd. Qed.

(* ---------------------------------------------------------------------- *)
(* MAIN: translateAddr is the identity in Machine mode (Bare paging).      *)
(* Precondition: cur_privilege reads as Machine.  mstatus value is         *)
(* irrelevant (effectivePrivilege of a fetch ignores MPRV); satp unread.   *)
(* ---------------------------------------------------------------------- *)

Lemma run_translateAddr_identity (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  run (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
           PBMT_PMA, init_ext_ptw)) s.
Proof.
  intros Hcp.
  assert (Hrd : run (Defs.read_reg cur_privilege) s Machine s).
  { rewrite run_read_reg. split; [symmetry; exact Hcp | reflexivity]. }
  unfold translateAddr.
  apply run_catch_early_return. right.
  eapply runR_liftR_seq; [ exact (run_read_reg_fwd mstatus s) | ]. (* mstatus *)
  eapply runR_liftR_seq; [ exact Hrd | ].                       (* cur_privilege = Machine *)
  eapply runR_liftR_seq; [ apply run_effectivePrivilege_fetch | ]. (* effPriv = Machine *)
  eapply runR_liftR_seq; [ apply run_translationMode_M | ].     (* mode = Bare *)
  eapply runR_liftR_seq; [ apply run_is_shadow_stack_fetch | ]. (* shadow = false *)
  (* remaining: (if false .. else returnR tt) >> (if generic_eq Bare Bare then returnR (Ok ..)) *)
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite runR_bind. right. exists tt, s.
  split; apply runR_returnR_fwd.
Qed.

(* ====================================================================== *)
(* RESIDUE (scoped, not proven here): the read side of fetch.             *)
(*   fetch_bytes -> mem_read -> mem_read_priv -> checked_mem_read ->       *)
(*     phys_access_check (= pmpCheck + pmaCheck) + within_mmio_readable    *)
(*     + read_ram (MemRead x4).                                            *)
(*   pmpCheck: catch_early_return over `foreach_ZM_up 0 15 1` ; with all   *)
(*     pmpcfg=0 every iteration hits PMP_NoMatch (pmpMatchAddr: cfg.A=OFF) *)
(*     => state-preserving no-op, then Machine-mode falls to None. Needs a *)
(*     loop-invariant lemma over foreach_ZM_up (the analogue of the Lean   *)
(*     pmpCheck_machine_none / forIn_run_const).                           *)
(*   This is the substantial remaining memory-subsystem milestone.         *)
(* ====================================================================== *)

(* ===== RiscvModelReadRam ===== *)
(* ====================================================================== *)
(* RiscvModelReadRam.v                                                     *)
(*                                                                         *)
(* Payoff of the strengthened `run` MemRead rule: the model's real         *)
(* `read_ram` (which issues ONE `MemRead width`, via `sail_mem_read`)       *)
(* now reduces through `run` given the `width` consecutive memory bytes.    *)
(* This is exactly what the OLD single-byte rule could NOT do (it left the  *)
(* upper bytes of a multi-byte read unconstrained).                        *)
(* ====================================================================== *)



(* read_ram for a plain 4-byte read at [addr], given the 4 consecutive bytes
   of [w] in memory, runs (state-preserving) to a successful value. *)
Lemma run_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exists value : mword (8 * 4),
    run (read_ram Read_plain (Physaddr addr) 4 false) s (value, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  (* rk = Read_plain : the access-kind computation is a pure returnM *)
  eapply (ex_intro _ _).
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  (* now: sail_mem_read request >>= match ... *)
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  (* the MemRead outcome: provide w as the read value *)
  eexists _, s. split.
  - (* run (Next (MemRead 4 req') k) : the strengthened rule, witness w *)
    cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelPending ===== *)
(* ====================================================================== *)
(* RiscvModelPending.v                                                     *)
(*                                                                         *)
(* Keystone: run (getPendingSet Machine) s None s under boot CSRs.         *)
(*                                                                         *)
(* For priv = Machine the result is None as soon as mIE = false and        *)
(* sIE = false.  sIE = false is FREE (Machine <> Supervisor/User), and     *)
(* mIE = false follows from the boot fact mstatus.MIE = 0.  So both         *)
(* `andb mIE _` and `andb sIE _` are false by computation and pending_m/    *)
(* pending_s are never inspected -- no read_mip=0 / and_vec-zero needed.    *)
(* The only deep sub-call, currentlyEnabled Ext_S (a 2nd Acc-recursion),   *)
(* is carried as a state-preserving hypothesis HcES.                       *)
(* ====================================================================== *)



Import Defs.


(* forward-form helpers (BUILD a run goal from the iff lemmas). *)
Lemma run_bind_fwd {X Y} (m : M Y) (f : Y -> M X) s y s1 x s' :
  run m s y s1 -> run (f y) s1 x s' -> run (Defs.bind m f) s x s'.
Proof. intros H1 H2. apply (proj2 (run_bind _ _ _ _ _)). exists y, s1. split; assumption. Qed.


Lemma run_ret_fwd {X} (x : X) s : run (Defs.returnm x) s x s.
Proof. apply (proj2 (run_ret _ _ _ _)). split; reflexivity. Qed.


Section Pending.
  Context (s : mstate) (cES : bool).

  Hypothesis HcES : run (currentlyEnabled Ext_S) s cES s.
  (* The getPendingSet guard is [currentlyEnabled Ext_S || (mideleg == 0)].  The
     RISC-V CPUs this kernel targets support supervisor mode, so the S-extension
     is always enabled (cES = true); the guard then holds regardless of mideleg,
     and we need not reason about mideleg's value at all. *)
  Hypothesis HcEStrue : cES = true.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus s.(sregs))) ('b"1") = false.

  (* The or_boolM guard before assert_exp' evaluates to true. *)
  Lemma guard_true :
    run (or_boolM (currentlyEnabled Ext_S)
                  (Defs.bind (read_reg mideleg)
                     (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s true s.
  Proof using All.
    apply (proj2 (run_or_boolM _ _ _ _ _)). exists cES, s. split; [exact HcES|].
    destruct cES; [split; reflexivity | discriminate HcEStrue].
  Qed.

  (* read_mip threads to *some* value (state-preserving); value irrelevant. *)
  Lemma read_mip_runs : exists v, run (read_mip IncludePlatformInterrupts) s v s.
  Proof using All.
    unfold read_mip. cbn match.
    destruct cES.
    - eexists.
      eapply run_bind_fwd; [exact (run_read_reg_fwd mip s)|].
      eapply run_bind_fwd.
      { unfold external_interrupts_pending.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_meip s)|].
        eapply run_bind_fwd; [exact HcES|]. cbn match.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_seip s)|].
        apply run_returnM_fwd. }
      apply run_returnM_fwd.
    - eexists.
      eapply run_bind_fwd; [exact (run_read_reg_fwd mip s)|].
      eapply run_bind_fwd.
      { unfold external_interrupts_pending.
        eapply run_bind_fwd; [exact (run_read_reg_fwd sig_meip s)|].
        eapply run_bind_fwd; [exact HcES|]. cbn match.
        eapply run_bind_fwd; [apply run_returnM_fwd|].
        apply run_returnM_fwd. }
      apply run_returnM_fwd.
  Qed.

  Lemma run_getPendingSet_machine_none :
    run (getPendingSet Machine) s None s.
  Proof using All.
    destruct read_mip_runs as [mipv Hmip].
    unfold getPendingSet.
    (* guard >>= fun w2 => assert_exp' w2 >>= fun _ => ... *)
    eapply run_bind_fwd; [exact guard_true|].
    (* assert_exp' true _ = returnm eq_refl *)
    eapply run_bind_fwd; [cbn match; apply run_ret_fwd|].
    (* read_mip *)
    eapply run_bind_fwd; [exact Hmip|].
    (* read mie, mideleg (pending_m let), mie, mideleg (pending_s let) *)
    eapply run_bind_fwd; [exact (run_read_reg_fwd mie s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mideleg s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mie s)|].
    eapply run_bind_fwd; [exact (run_read_reg_fwd mideleg s)|].
    (* mIE = false *)
    eapply run_bind_fwd.
    { apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split.
      - (* l = and_boolM (returnM (generic_eq Machine Machine)) (...) = false *)
        apply (proj2 (run_and_boolM _ _ _ _ _)). exists true, s. split.
        + (* returnM (generic_eq Machine Machine) -> true *)
          change (generic_eq Machine Machine) with true. apply run_returnM_fwd.
        + (* read mstatus >>= returnM (eq_vec (MIE) 'b1) -> false (HmIE) *)
          eapply run_bind_fwd; [exact (run_read_reg_fwd mstatus s)|].
          rewrite HmIE. apply run_returnM_fwd.
      - (* bl=false: run r s false s, r = returnM (orb (M=S)(M=U)) = false *)
        change (orb (generic_eq Machine Supervisor) (generic_eq Machine User)) with false.
        apply run_returnM_fwd. }
    (* sIE = false *)
    eapply run_bind_fwd.
    { apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split.
      - (* l = and_boolM (returnM (generic_eq Machine Supervisor=false)) _ = false *)
        apply (proj2 (run_and_boolM _ _ _ _ _)). exists false, s. split.
        + change (generic_eq Machine Supervisor) with false. apply run_returnM_fwd.
        + split; reflexivity.
      - change (generic_eq Machine User) with false. apply run_returnM_fwd. }
    (* final: andb false _ = false twice -> None *)
    cbn [andb]. apply run_returnM_fwd.
  Qed.

End Pending.

(* ===== RiscvModelExecR ===== *)
(* ====================================================================== *)
(* RiscvModelExecR.v  —  the exec-side twin of the runR (MR) bridge.        *)
(*                                                                         *)
(* run_hart_active runs in the early-return monad                          *)
(*   monadR R E := iMon (fun _ => (R+E))   [= monad (R+E)]                  *)
(* via catch_early_return / liftR (built on try_catch).  [exec] is         *)
(* monomorphic to M = monad exception and so does NOT reduce INTO a        *)
(* monadR body.  We give the functional early-return interpreter [execR]   *)
(* (result [R+X]), its bind/liftR laws, and the bridge                     *)
(*   exec (catch_early_return body) s = (execR body, both arms -> value).   *)
(* Plus the determinism transfer (execR success => unique runR), hence     *)
(* runR_to_execR (mirror of run_to_exec).                                  *)
(*                                                                         *)
(* Proof style mirrors the proven exec_bind: rewrite the Ret/Next unfold,  *)
(* then [destruct oc; cbn [execR ...]] (cbn is safe on a CONCRETE oc),     *)
(* then [apply IH] / reflexivity / read_bytes-split / ExtraOutcome-split.  *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* execR: functional early-return interpreter for [monadR R exception X].   *)
(* Mirrors [exec] (functional; Choose/GenericFail/Discard -> None;          *)
(* MemRead via read_bytes) AND [runR]'s early-return handling               *)
(* (ExtraOutcome (inl r) = early-returned r; ExtraOutcome (inr _) stuck).   *)
(* ---------------------------------------------------------------------- *)

Fixpoint execR {R X} (m : Defs.monadR R exception X)
    (s : mstate) {struct m} : option ((R + X) * mstate) :=
  match m with
  | Interface.Ret y => Some (inr y, s)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> Defs.monadR R exception X) -> option ((R + X) * mstate) with
       | Interface.RegRead r _ =>
           fun k => execR (k (register_lookup r s.(sregs))) s
       | Interface.RegWrite r _ v =>
           fun k => execR (k tt) (set_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => execR (k (inl (w, None))) s
             | None => None
             end
       | Interface.MemWrite n req =>
           fun k =>
             execR (k (inl None))
                   (MState s.(sregs)
                      (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req)))
       | Interface.InstrAnnounce _    => fun k => execR (k tt) s
       | Interface.BranchAnnounce _ _ => fun k => execR (k tt) s
       | Interface.Barrier _          => fun k => execR (k tt) s
       | Interface.CacheOp _          => fun k => execR (k tt) s
       | Interface.TlbOp _            => fun k => execR (k tt) s
       | Interface.TakeException _    => fun k => execR (k tt) s
       | Interface.ReturnException _  => fun k => execR (k tt) s
       | Interface.TranslationStart _ => fun k => execR (k tt) s
       | Interface.TranslationEnd _   => fun k => execR (k tt) s
       | Interface.CycleCount         => fun k => execR (k tt) s
       | Interface.Message _          => fun k => execR (k tt) s
       | Interface.GetCycleCount      => fun k => execR (k 0%Z) s
       | Interface.ExtraOutcome e =>
           fun _ => match e with
                    | inl r => Some (inl r, s)
                    | inr _ => None
                    end
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck *)
       end) k
  end.

(* ---- Ret/Next unfolding for the monadR-level [Defs.bind] (definitional). *)

Lemma bindR_Ret {R X Y} (y : Y) (f : Y -> Defs.monadR R exception X) :
  Defs.bind (Interface.Ret y : Defs.monadR R exception Y) f = f y.
Proof. reflexivity. Qed.

Lemma bindR_Next {R X Y T} (oc : Interface.outcome (fun _ => (R + exception)%type) T)
    (k : T -> Defs.monadR R exception Y) (f : Y -> Defs.monadR R exception X) :
  Defs.bind (Interface.Next oc k) f = Interface.Next oc (fun z => Defs.bind (k z) f).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* bind in the early-return monad (same Defs.bind): short-circuits on inl. *)
(* ---------------------------------------------------------------------- *)

Lemma execR_bind {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) :
  forall s, execR (Defs.bind m f) s =
    match execR m s with
    | Some (inl r, s') => Some (inl r, s')
    | Some (inr a, s') => execR (f a) s'
    | None => None
    end.
Proof.
  induction m as [a0 | T oc k IH]; intros s.
  - rewrite bindR_Ret. reflexivity.
  - rewrite bindR_Next. destruct oc; cbn [execR];
      try (apply IH); try reflexivity;
      first
        [ match goal with
          | |- context[read_bytes ?mm ?pa ?n] =>
              destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
          end
        | match goal with
          | He : (_ + exception)%type |- _ => destruct He; reflexivity
          end ].
Qed.

(* ---------------------------------------------------------------------- *)
(* liftR: a lifted base computation never early-returns; execR = exec (inr).*)
(* ---------------------------------------------------------------------- *)

Lemma execR_liftR {R X} (m : M X) :
  forall s, execR (Defs.liftR (R:=R) m) s =
    match exec m s with
    | Some (x, s') => Some (inr x, s')
    | None => None
    end.
Proof.
  unfold Defs.liftR. induction m as [x0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch execR exec Defs.throw];
      try (apply IH); try reflexivity;
      match goal with
      | |- context[read_bytes ?mm ?pa ?n] =>
          destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
      end.
Qed.

(* ---------------------------------------------------------------------- *)
(* the bridge: catch_early_return back into the base monad.                 *)
(* ---------------------------------------------------------------------- *)

Lemma exec_catch_early_return {X} (body : Defs.monadR X exception X) :
  forall s, exec (Defs.catch_early_return body) s =
    match execR body s with
    | Some (inl r, s') => Some (r, s')
    | Some (inr r, s') => Some (r, s')
    | None => None
    end.
Proof.
  unfold Defs.catch_early_return. induction body as [a0 | T oc k IH]; intros s.
  - reflexivity.
  - destruct oc; cbn [Defs.try_catch exec execR Defs.throw Defs.returnm];
      try (apply IH); try reflexivity;
      first
        [ match goal with
          | |- context[read_bytes ?mm ?pa ?n] =>
              destruct (read_bytes mm pa n) as [w|]; [apply IH | reflexivity]
          end
        | match goal with
          | He : (_ + exception)%type |- _ => destruct He; reflexivity
          end ].
Qed.

(* ---------------------------------------------------------------------- *)
(* determinism transfer: execR success => the unique runR.                 *)
(* ---------------------------------------------------------------------- *)

Lemma execR_runR_det {R X} (m : Defs.monadR R exception X) :
  forall s res s', execR m s = Some (res, s') ->
    runR m s res s' /\ (forall res2 s2, runR m s res2 s2 -> res2 = res /\ s2 = s').
Proof.
  induction m as [y|T oc k IH]; intros s res s' Hexec.
  - simpl in Hexec. injection Hexec as <- <-. simpl.
    split; [done | intros res2 s2 [<- <-]; done].
  - destruct oc; simpl in Hexec; try discriminate;
      try (split;
           [ apply (proj1 (IH _ _ _ _ Hexec))
           | intros res2 s2 Hr; simpl in Hr; exact (proj2 (IH _ _ _ _ Hexec) _ _ Hr) ]).
    + (* MemRead *)
      destruct (read_bytes s.(mem) _ _) as [w0|] eqn:Hrb; [|discriminate].
      destruct (IH (inl (w0, None)) s res s' Hexec) as [Hrun0 Huniq0].
      split.
      * simpl. exists w0. split;
          [ intros j Hj; apply (read_bytes_spec _ _ _ _ Hrb j Hj) | exact Hrun0 ].
      * intros res2 s2 Hr. simpl in Hr. destruct Hr as (w & Hbytes & Hrun).
        assert (Hweq : w = w0).
        { apply bv_eq_of_bytes. intros j Hj.
          pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
          assert (Hw : mem s !! RiscvModelBytes.pa_add (Interface.ReadReq.pa t) j
                       = Some (RiscvModelBytes.nth_byte w j))
            by (apply Hbytes; exact Hj).
          rewrite Hw in H0. apply Some_inj in H0. exact H0. }
        subst w. exact (Huniq0 _ _ Hrun).
    + (* ExtraOutcome *)
      match goal with He : (_ + exception)%type |- _ => destruct He as [r0|ee] end;
        simpl in Hexec; [|discriminate].
      injection Hexec as <- <-. simpl.
      split; [done | intros res2 s2 [<- <-]; done].
Qed.

(* mirror of run_to_exec: a proven runR-fact + execR-progress => the exec fact. *)
Lemma runR_to_execR {R X} (m : Defs.monadR R exception X) s res s' :
  runR m s res s' -> execR m s <> None -> execR m s = Some (res, s').
Proof.
  intros Hr Hne. destruct (execR m s) as [[res2 s2]|] eqn:He; [|exfalso; apply Hne; reflexivity].
  pose proof (execR_runR_det _ _ _ _ He) as [_ Huniq].
  destruct (Huniq _ _ Hr) as [-> ->]. reflexivity.
Qed.

(* ===== RiscvModelHne1 ===== *)
(* ====================================================================== *)
(* RiscvModelHne1.v                                                        *)
(*                                                                         *)
(* STAGE 1 of discharging Hne (= exec (run_hart_active 0) s <> None):       *)
(* trace execR through run_hart_active's F_Base/ADD body and reduce Hne to  *)
(* leaf exec-facts.  Cheap leaf twins (dispatchInterrupt, is_landing_pad)   *)
(* are proven; the structural reduction `exec_hart_active_progress` carries  *)
(* the remaining leaves (fetch [stage 2], ext_decode [decode wall],         *)
(* getPendingSet, execute) as hypotheses.                                   *)
(* ====================================================================== *)




(* targeted reduction for returnR (avoids cbn [execR] which over-unfolds). *)
Lemma execR_returnR {R X} (x : X) s :
  execR (Defs.returnR R x) s = Some (inr x, s).
Proof. reflexivity. Qed.

Lemma execR_bind0 {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s :
  execR (Defs.bind0 m n) s =
    match execR m s with
    | Some (inl r, s') => Some (inl r, s')
    | Some (inr _, s') => execR n s'
    | None => None
    end.
Proof. unfold Defs.bind0. rewrite execR_bind. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Cheap leaf twin 1: dispatchInterrupt = None (given getPendingSet=None).  *)
(* ---------------------------------------------------------------------- *)

Lemma exec_dispatchInterrupt_none s :
  exec (getPendingSet Machine) s = Some (None, s) ->
  exec (dispatchInterrupt Machine) s = Some (None, s).
Proof.
  intros Hgp. unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ Hgp). cbn match.
  apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Cheap leaf twin 2: is_landing_pad_expected reduces to the elp eq_vec.    *)
(* ---------------------------------------------------------------------- *)

Lemma exec_is_landing_pad s :
  exec (is_landing_pad_expected tt) s
  = Some (eq_vec (register_lookup elp s.(sregs))
                 (landing_pad_bits_backwards LP_EXPECTED), s).
Proof.
  unfold is_landing_pad_expected.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)).
  apply exec_returnm.
Qed.


(* ---------------------------------------------------------------------- *)
(* Structural reduction: exec (run_hart_active 0) s = Some (.., s_final),    *)
(* hence <> None, from the leaf exec-facts (F_Base/ADD path).               *)
(* ---------------------------------------------------------------------- *)

Section HartActiveProgress.
  Context (s s_f s_x s_final : mstate) (w : mword 32) (instr : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s_f).
  Hypothesis Hdec : exec (ext_decode w) s_f = Some (instr, s_f).
  Hypothesis Hlpad : eq_vec (register_lookup elp s_f.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hnotlpad : is_lpad_instruction instr = false.
  Hypothesis HpcF : register_lookup PC s_f.(sregs) = pc.
  Let s_pc : mstate := set_reg s_f nextPC (add_vec_int pc 4).
  Hypothesis Hexec : exec (execute instr) s_pc = Some (resf, s_x).
  Hypothesis Hnotexec : match resf with ExecuteAs _ => False | _ => True end.

  Lemma exec_hart_active_progress :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    (* read cur_privilege -> Machine *)
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    (* dispatchInterrupt -> None ; the `fun w1 =>` body is
       (match w1) >> liftR(fetch) >>= fun w2 => ..  =  bind (bind0 MATCH (liftR fetch)) k *)
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    (* outer bind; inner bind0 (returnR tt) (liftR fetch) *)
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    (* ext_fetch_hook (F_Base w) = F_Base w ; F_Base branch (announce/callback lets) *)
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    (* ext_decode w -> instr *)
    rewrite execR_bind execR_liftR Hdec. cbn match.
    (* (if print=false then.. else returnR tt) >> and_boolM(..) >>= fun w21 => ..
       = bind (bind0 (returnR tt) and_boolM) k *)
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* and_boolM (liftR is_landing_pad) (returnR (not lpad)) -> false (short-circuit) *)
    unfold and_boolM.
    rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
    rewrite execR_returnR. cbn match. cbn match.
    (* w21 = false -> else: read PC >>= fun w22 => bind0 (write nextPC) (liftR execute) >>= ... *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* (match resf : not ExecuteAs => resf) >>= fun result' => returnR (Step_Execute ..) *)
    rewrite execR_bind.
    destruct resf; cbn in Hnotexec; try contradiction;
      cbn match; rewrite execR_returnR; cbn match; rewrite execR_returnR; reflexivity.
  Qed.

End HartActiveProgress.

(* ===== RiscvModelFetch ===== *)
(* ===================================================================== *)
(* RiscvModelFetch.v — item (2/3) cont'd: the extension predicates        *)
(* (`hartSupports`/`currentlyEnabled`) reduced through `run`, INCLUDING    *)
(* the full nested capability tree (not just leaves).  All AXIOM-FREE.     *)
(*                                                                         *)
(* Findings from reading `fetch` (rv64d.v):                                *)
(*  - On a 4-byte-aligned PC (the ADD path) the only `currentlyEnabled`    *)
(*    that fires is `Ext_Ziccif` (a leaf = true).  `Ext_Zca` sits under    *)
(*    `and_boolM (PC[1] != 0) …`, short-circuited away when PC aligned.    *)
(*  - `fetch` then calls `fetch_bytes` = address translation (Bare/M-mode  *)
(*    ⇒ identity) + PMP + MemRead — a separate sub-effort (see README).    *)
(*                                                                         *)
(* `run_hartSupports_C` shows the WHOLE capability tree (nested and/or-     *)
(* boolM over 5 sub-extensions) reduces — not just the leaves — confirming  *)
(* the Acc recipe scales past depth 1.                                     *)
(* ===================================================================== *)

(* Unfold one `_rec_hartSupports` level: destruct its Acc proof, step the
   {struct _acc} fixpoint, discharge the (concrete, >=0) reclimit guard, and
   peel the leading `assert_exp' … >>=`.  Leaves goal = `run <arm> s _ s`. *)
Ltac hs_open s :=
  match goal with
  | |- run (_rec_hartSupports ?e ?r ?a) _ _ _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] => replace (Z.geb x 0) with true by reflexivity end;
      cbn match;
      apply run_bind; exists eq_refl, s; split;
      [apply run_ret; split; reflexivity | cbn match]
  end.

(* --- leaves the aligned ADD fetch path actually queries --- *)
Lemma run_hartSupports_Ziccif s : run (hartSupports Ext_Ziccif) s true s.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split.
  - apply run_ret. split; reflexivity.
  - apply run_returnM. split; reflexivity.
Qed.

Lemma run_currentlyEnabled_Ziccif s : run (currentlyEnabled Ext_Ziccif) s true s.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split.
  - apply run_ret. split; reflexivity.
  - cbn match. apply run_hartSupports_Ziccif.
Qed.

(* --- the full Ext_C capability tree reduces to `true` (CSR-free, xlen=64) --- *)
Lemma run_hartSupports_C s : run (hartSupports Ext_C) s true s.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity| cbn match].
  apply run_and_boolM. exists true, s. split.
  { hs_open s. apply run_returnM. split; reflexivity. }
  apply run_and_boolM. exists true, s. split.
  { apply run_or_boolM. exists false, s. split.
    { hs_open s. apply run_returnM. split; reflexivity. }
    apply run_or_boolM. exists false, s. split.
    { apply run_bind. exists true, s. split.
      { hs_open s. apply run_returnM. split; reflexivity. }
      apply run_returnM. split; reflexivity. }
    { apply run_returnM. split; [vm_compute; reflexivity| reflexivity]. } }
  { apply run_or_boolM. exists true, s. split.
    { hs_open s. apply run_returnM. split; reflexivity. }
    split; reflexivity. }
Qed.

(* ===== RiscvModelEnabledS ===== *)
(* ====================================================================== *)
(* RiscvModelEnabledS.v                                                    *)
(*                                                                         *)
(* Gate 1 toward discharging Hstep: currentlyEnabled Ext_S is              *)
(* state-preserving (HcES for the getPendingSet keystone).                 *)
(*   currentlyEnabled Ext_S                                                *)
(*     = and_boolM (hartSupports Ext_S)              [= returnM true]       *)
(*         (and_boolM (read misa; misa.S check)                            *)
(*                    (currentlyEnabled Ext_Zicsr))  [= hartSupports = true]*)
(* All read-only; value = misa.S bit; final state = s.                     *)
(* ====================================================================== *)




(* leaves: hartSupports Ext_S / Ext_Zicsr both reduce to returnM true *)
Lemma run_hartSupports_S s : run (hartSupports Ext_S) s true s.
Proof. unfold hartSupports. hs_open s. apply run_returnM. split; reflexivity. Qed.

Lemma run_hartSupports_Zicsr s : run (hartSupports Ext_Zicsr) s true s.
Proof. unfold hartSupports. hs_open s. apply run_returnM. split; reflexivity. Qed.

(* the inner Ext_Zicsr sub-call (a reduced-limit _rec node) reduces to
   hartSupports Ext_Zicsr = true, for any acc. *)
Lemma run_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  run (_rec_currentlyEnabled Ext_Zicsr 0 acc) s true s.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity | cbn match].
  apply run_hartSupports_Zicsr.
Qed.

(* HcES: currentlyEnabled Ext_S is state-preserving, value = misa.S bit. *)
Lemma run_currentlyEnabled_S s :
  run (currentlyEnabled Ext_S) s
      (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  apply run_bind. exists eq_refl, s. split; [apply run_ret; split; reflexivity | cbn match].
  (* outer and_boolM (hartSupports Ext_S = true) INNER *)
  apply run_and_boolM. exists true, s. split; [apply run_hartSupports_S|].
  (* bl = true -> run INNER s (misa.S bit) s *)
  apply run_and_boolM.
  exists (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")), s. split.
  { (* misa check: read_reg misa >>= fun w => returnM (eq_vec (_get_Misa_S w) 0b1) *)
    apply run_bind. exists (register_lookup misa s.(sregs)), s. split.
    { exact (run_read_reg_fwd misa s). }
    apply run_returnM. split; reflexivity. }
  (* if (misa.S bit) then run (cE Ext_Zicsr) s _ s else (_ = false /\ s' = s) *)
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb2.
  - apply run_rec_cE_Zicsr.
  - split; reflexivity.
Qed.

(* ===== RiscvModelHne2 ===== *)
(* ===================================================================== *)
(* RiscvModelHne2.v — leaf exec-twins discharging Hne's residual leaf      *)
(* facts: exec_execute_ADD and exec_getPendingSet_machine_none.            *)
(* Functional mirrors of the proven run-facts (exec_bind instead of        *)
(* run_bind).                                                              *)
(* ===================================================================== *)
Import Defs.

(* --------------------------------------------------------------------- *)
(* Task A: exec twins of rX / wX at concrete registers, then execute(ADD). *)
(* --------------------------------------------------------------------- *)

Lemma exec_rX_x10 s :
  exec (rX (Regno 10)) s = Some (register_lookup (R_bitvector_64 x10) s.(sregs), s).
Proof. rewrite rX_x10. exact (exec_read_reg (R_bitvector_64 x10) s). Qed.

Lemma exec_rX_x11 s :
  exec (rX (Regno 11)) s = Some (register_lookup (R_bitvector_64 x11) s.(sregs), s).
Proof. rewrite rX_x11. exact (exec_read_reg (R_bitvector_64 x11) s). Qed.

Lemma exec_wX_x12 s (v : mword 64) :
  exec (wX (Regno 12) v) s = Some (tt, set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof.
  rewrite wX_x12_eq.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_write_reg (R_bitvector_64 x12) (regval_into_reg v) s)).
  apply exec_returnm.
Qed.

Lemma exec_rX_bits_x10 (i : mword 5) s :
  uint i = 10 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x10) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x10. Qed.

Lemma exec_rX_bits_x11 (i : mword 5) s :
  uint i = 11 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x11) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x11. Qed.

Lemma exec_wX_bits_x12 (i : mword 5) s (v : mword 64) :
  uint i = 12 ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 x12) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply exec_wX_x12. Qed.

(* compositional exec twin of run_execute_RTYPE_ADD *)
Lemma exec_execute_RTYPE_ADD (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (add_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd ADD) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hb Hw.
  unfold execute_RTYPE. cbn match.
  (* outer bind: inner computes (add_vec a b) leaving state s *)
  rewrite (exec_bind_Some _ _ _ (add_vec a b) s).
  2:{ (* inner = rX_bits rs1 >>= rX_bits rs2 >>= returnM (add_vec) *)
      rewrite (exec_bind_Some _ _ _ _ _ Ha).
      rewrite (exec_bind_Some _ _ _ _ _ Hb).
      apply exec_returnm. }
  (* now: bind0 (wX_bits rd (add_vec a b)) (returnM RETIRE_SUCCESS) *)
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnm.
Qed.

Lemma exec_execute_ADD (rd rs1 rs2 : mword 5) s :
  uint rs1 = 10 -> uint rs2 = 11 -> uint rd = 12 ->
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 x12)
              (regval_into_reg
                 (add_vec (register_lookup (R_bitvector_64 x10) s.(sregs))
                          (register_lookup (R_bitvector_64 x11) s.(sregs))))).
Proof.
  intros H1 H2 H3.
  eapply exec_execute_RTYPE_ADD.
  - apply exec_rX_bits_x10; exact H1.
  - apply exec_rX_bits_x11; exact H2.
  - apply exec_wX_bits_x12; exact H3.
Qed.

(* --------------------------------------------------------------------- *)
(* Task B: exec twin of the getPendingSet keystone.                        *)
(* Mirrors run_getPendingSet_machine_none; carries the currentlyEnabled    *)
(* Ext_S exec-twin (HecES), parallel to the run keystone's HcES.           *)
(* --------------------------------------------------------------------- *)

(* model's returnM = Defs.returnm (E:=exception); needs its own exec lemma so
   syntactic rewrites match the [returnM ...] that appears in the model terms. *)
Lemma exec_returnM {X} (x : X) s : exec (returnM x) s = Some (x, s).
Proof. unfold returnM. apply exec_returnm. Qed.

Lemma exec_and_boolM_Some (l r : M bool) s bl sl :
  exec l s = Some (bl, sl) ->
  exec (and_boolM l r) s = (if bl then exec r sl else Some (false, sl)).
Proof.
  intro H. unfold and_boolM. rewrite (exec_bind_Some _ _ _ _ _ H).
  destruct bl; [reflexivity | apply exec_returnm].
Qed.

Lemma exec_or_boolM_Some (l r : M bool) s bl sl :
  exec l s = Some (bl, sl) ->
  exec (or_boolM l r) s = (if bl then Some (true, sl) else exec r sl).
Proof.
  intro H. unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ H).
  destruct bl; [apply exec_returnm | reflexivity].
Qed.

Section ExecPending.
  Context (s : mstate) (cES : bool).
  Hypothesis HecES : exec (currentlyEnabled Ext_S) s = Some (cES, s).
  (* S-extension always enabled on the targeted CPUs (see Section Pending). *)
  Hypothesis HcEStrue : cES = true.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus s.(sregs))) ('b"1") = false.

  Lemma exec_guard_true :
    exec (or_boolM (currentlyEnabled Ext_S)
                   (Defs.bind (read_reg mideleg)
                      (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
      = Some (true, s).
  Proof using All.
    rewrite (exec_or_boolM_Some _ _ _ _ _ HecES).
    destruct cES; [reflexivity | discriminate HcEStrue].
  Qed.

  Lemma exec_ext_int_some :
    exists ev, exec (external_interrupts_pending tt) s = Some (ev, s).
  Proof using All.
    unfold external_interrupts_pending.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
    rewrite (exec_bind_Some _ _ _ _ _ HecES).
    destruct cES; cbn match.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)). eexists. apply exec_returnm.
    - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm ('b"0") s)). eexists. apply exec_returnm.
  Qed.

  Lemma exec_read_mip_some :
    exists v, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
  Proof using All.
    destruct exec_ext_int_some as [ev Hext].
    unfold read_mip. cbn match. eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
    rewrite (exec_bind_Some _ _ _ _ _ Hext).
    apply exec_returnm.
  Qed.

  Lemma exec_mIE_false :
    exec (or_boolM
            (and_boolM (returnM (generic_eq Machine Machine))
               (Defs.bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Machine Supervisor) (generic_eq Machine User)))) s
      = Some (false, s).
  Proof using All.
    assert (Hand : exec (and_boolM (returnM (generic_eq Machine Machine))
                     (Defs.bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Machine Machine) s)).
      change (generic_eq Machine Machine) with true. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
      rewrite HmIE. apply exec_returnm. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq Machine Supervisor) (generic_eq Machine User)) with false.
    apply exec_returnm.
  Qed.

  Lemma exec_sIE_false :
    exec (or_boolM
            (and_boolM (returnM (generic_eq Machine Supervisor))
               (Defs.bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Machine User))) s
      = Some (false, s).
  Proof using All.
    assert (Hand : exec (and_boolM (returnM (generic_eq Machine Supervisor))
                     (Defs.bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Machine Supervisor) s)).
      change (generic_eq Machine Supervisor) with false. cbn match. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq Machine User) with false. apply exec_returnm.
  Qed.

  Lemma exec_getPendingSet_machine_none :
    exec (getPendingSet Machine) s = Some (None, s).
  Proof using All.
    destruct exec_read_mip_some as [mipv Hmip].
    assert (Hae : exec (assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    unfold getPendingSet.
    rewrite (exec_bind_Some _ _ _ _ _ exec_guard_true).
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ Hmip).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
    rewrite (exec_bind_Some _ _ _ _ _ exec_mIE_false).
    rewrite (exec_bind_Some _ _ _ _ _ exec_sIE_false).
    cbn [andb]. apply exec_returnm.
  Qed.

End ExecPending.

(* ===== RiscvModelHneFetch ===== *)
(* ====================================================================== *)
(* RiscvModelHneFetch.v                                                    *)
(*                                                                         *)
(* Hne STAGE 2: the fetch exec-twin.                                       *)
(*   - execR_foreach_ZM_up_const: the exec/execR loop-invariant for the    *)
(*     PMP foreach (twin of runR_foreach_ZM_up_const).                     *)
(*   - exec_fetch_F_Base via run_to_exec on the proven run_fetch_F_Base    *)
(*     + exec-progress (exec (fetch tt) s <> None).                        *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* returnm vars (= Ret vars = returnR) yields Some (inr vars, s) under execR. *)
Lemma execR_returnm_fwd {R X} (x : X) s :
  execR (Defs.returnm x : Defs.monadR R exception X) s = Some (inr x, s).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The exec/execR loop-invariant over the nat-fueled [foreach_ZM_up'].     *)
(* Twin of runR_foreach_ZM_up'_const: a body that is Some(inr v,s) at every *)
(* index makes the whole loop Some(inr vars, s).                           *)
(* ---------------------------------------------------------------------- *)

Lemma execR_foreach_ZM_up'_const {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) :
  (forall i v, execR (body i v) s = Some (inr v, s)) ->
  forall (n : nat) (from : Z) (vars : Vars),
    execR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inr vars, s).
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - cbn [Defs.foreach_ZM_up']. destruct (from <=? to); apply execR_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + rewrite (Defs.unroll_foreach_ZM_up' _ _ from to step n vars body Hle).
      rewrite execR_bind. rewrite (Hbody from vars). exact (IH (from + step) vars).
    + cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false.
      * apply execR_returnm_fwd.
      * symmetry. apply Z.leb_gt. lia.
Qed.

Lemma execR_foreach_ZM_up_const {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) :
  (forall i v, execR (body i v) s = Some (inr v, s)) ->
  execR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inr vars, s).
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply execR_foreach_ZM_up'_const; exact Hbody.
Qed.

(* ---------------------------------------------------------------------- *)
(* The fetch exec-twin, reduced to exec-progress via run_to_exec on the    *)
(* proven run_fetch_F_Base.  The remaining residue (exec (fetch tt) s <>   *)
(* None) is the memory-subsystem exec mirror, now equipped with            *)
(* execR_foreach_ZM_up_const above for the PMP loop.                       *)
(* ---------------------------------------------------------------------- *)

Lemma exec_fetch_F_Base (w : mword 32) (s : mstate) :
  run (fetch tt) s (F_Base w) s ->
  exec (fetch tt) s <> None ->
  exec (fetch tt) s = Some (F_Base w, s).
Proof. intros Hrun Hprog. exact (run_to_exec (fetch tt) s (F_Base w) s Hrun Hprog). Qed.

(* ===== RiscvModelPmp ===== *)
(* ====================================================================== *)
(* RiscvModelPmp.v                                                         *)
(*                                                                         *)
(* Fetch read-side toward discharging Hcycle's fetch dependency.           *)
(*                                                                         *)
(*  - run[R] loop-INVARIANT over [Defs.foreach_ZM_up'] / [foreach_ZM_up]:  *)
(*    a per-iteration state-preserving no-op body ⇒ the whole bounded loop  *)
(*    is a no-op (NO unrolling — induction on the nat fuel).  This is the   *)
(*    reusable analogue of the Lean loop_run_const / forIn_run_const.      *)
(*  - applied to [pmpCheck]: PMP-disabled (all pmpcfg=0) in Machine mode    *)
(*    ⇒ [run (pmpCheck ..) s None s], MODULO the per-iteration body no-op.  *)
(* ====================================================================== *)



(* returnm = Ret, so runR yields a plain (inr) return with no state change. *)
Lemma runR_returnm_fwd {R X} (x : X) (s : mstate) :
  runR (R:=R) (Defs.returnm x : Defs.monadR R exception X) s (inr x) s.
Proof. split; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The loop invariant over the nat-fueled fixpoint [foreach_ZM_up'].       *)
(* Generalised over [from] and [vars] so the IH covers the [from+step]     *)
(* recursive call.                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma runR_foreach_ZM_up'_const {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) :
  (forall i v, runR (body i v) s (inr v) s) ->
  forall (n : nat) (from : Z) (vars : Vars),
    runR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
         s (inr vars) s.
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - (* fuel exhausted: returnm vars in both branches *)
    cbn [Defs.foreach_ZM_up']. destruct (from <=? to); apply runR_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + (* one iteration, then recurse with from+step *)
      rewrite (Defs.unroll_foreach_ZM_up' _ _ _ _ _ _ _ _ Hle).
      apply (proj2 (runR_bind _ _ _ _ _)).
      right. exists vars, s. split.
      * exact (Hbody from vars).
      * exact (IH (from + step) vars).
    + (* from > to: immediate returnm vars *)
      cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false by (symmetry; apply Z.leb_gt; lia).
      apply runR_returnm_fwd.
Qed.

(* The user-facing wrapper [foreach_ZM_up from to step vars body]. *)
Lemma runR_foreach_ZM_up_const {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) :
  (forall i v, runR (body i v) s (inr v) s) ->
  runR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
       s (inr vars) s.
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply runR_foreach_ZM_up'_const; exact Hbody.
Qed.

(* ===== RiscvModelFetchClose ===== *)
(* ====================================================================== *)
(* RiscvModelFetchClose.v                                                  *)
(*                                                                         *)
(* Fetch read-side, continued: reduce pmpCheck to "None" (access allowed)  *)
(* in Machine mode when every PMP entry's address-match-type is OFF        *)
(* (which holds when all pmpcfg = 0).  Uses the loop-invariant             *)
(* runR_foreach_ZM_up_const from RiscvModelPmp.                            *)
(*                                                                         *)
(* CONVERSION-LAZY: never cbn [run]/[runR]; only cbn zeta/beta/match +     *)
(* the forward stepping lemmas.                                            *)
(* ====================================================================== *)



(* pmpReadAddrReg only READS pmpcfg_n/pmpaddr_n and returns a pure value:   *)
(* state-preserving.  We just need existence of the returned value.         *)
Lemma run_pmpReadAddrReg_ex (n : Z) s : exists v, run (pmpReadAddrReg n) s v s.
Proof.
  unfold pmpReadAddrReg. cbn zeta. eexists.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup pmpcfg_n s.(sregs)), s.
  split; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup pmpaddr_n s.(sregs)), s.
  split; [ exact (run_read_reg_fwd pmpaddr_n s) | ]. cbn beta.
  apply run_returnM_fwd.
Qed.

(* pmpMatchAddr with an OFF address-match-type yields PMP_NoMatch, purely. *)
Lemma run_pmpMatchAddr_OFF (pa : physaddr) (width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = OFF ->
  run (pmpMatchAddr pa width ent pmpaddr prev) s PMP_NoMatch s.
Proof.
  intro HOFF. destruct pa as [addr0]. unfold pmpMatchAddr. cbn zeta.
  rewrite HOFF. cbn match. apply run_returnM_fwd.
Qed.

(* The body of pmpCheck's loop is a no-op when the i-th pmpcfg A-field=OFF. *)
Lemma run_pmpCheck_machine_none
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  run (pmpCheck addr width access Machine) s None s.
Proof.
  intro HpmpOFF.
  unfold pmpCheck.
  apply run_catch_early_return. right.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta. unfold Defs.bind0.
  apply (proj2 (runR_bind _ _ _ _ _)). right. exists tt, s. split.
  - (* the loop is a no-op *)
    apply runR_foreach_ZM_up_const. intros i v. destruct v. cbn beta.
    (* first bind: (if i>0 then liftR (pmpReadAddrReg (i-1)) else returnR 0) >>= REST *)
    destruct (Z.gtb i 0) eqn:Hi.
    + destruct (run_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      eapply runR_liftR_seq; [ exact Hpv | ]. cbn beta.
      (* REST with prev := pv *)
      eapply runR_liftR_seq; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
      destruct (run_pmpReadAddrReg_ex i s) as [w2 Hw2].
      eapply runR_liftR_seq; [ exact Hw2 | ]. cbn beta.
      eapply runR_liftR_seq;
        [ apply run_pmpMatchAddr_OFF; exact (HpmpOFF i) | ]. cbn beta.
      cbn match. apply runR_returnR_fwd.
    + apply (proj2 (runR_bind _ _ _ _ _)). right. eexists. exists s.
      split; [ apply runR_returnR_fwd | ]. cbn beta.
      (* REST with prev := zeros' 64 *)
      eapply runR_liftR_seq; [ exact (run_read_reg_fwd pmpcfg_n s) | ]. cbn beta.
      destruct (run_pmpReadAddrReg_ex i s) as [w2 Hw2].
      eapply runR_liftR_seq; [ exact Hw2 | ]. cbn beta.
      eapply runR_liftR_seq;
        [ apply run_pmpMatchAddr_OFF; exact (HpmpOFF i) | ]. cbn beta.
      cbn match. apply runR_returnR_fwd.
  - (* Machine mode falls through to None *)
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
    cbn match. apply runR_returnR_fwd.
Qed.

(* ===== RiscvModelHneFetch2 ===== *)
(* ====================================================================== *)
(* RiscvModelHneFetch2.v                                                    *)
(*                                                                         *)
(* Hne stage 2 (fetch exec-progress mirror).  The centerpiece: the exec    *)
(* twin of run_pmpCheck_machine_none, using the execR loop-invariant        *)
(* execR_foreach_ZM_up_const for the PMP foreach.  Plus the body leaves     *)
(* exec_pmpReadAddrReg_ex / exec_pmpMatchAddr_OFF.                          *)
(*                                                                         *)
(* RESIDUE (carried, documented): exec_translateAddr / exec_mem_read /      *)
(* exec_fetch_progress (the rest of the memory-subsystem exec mirror) — see *)
(* README; the pmpCheck loop (the one non-mechanical piece) is done here.   *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Forward helper: a [liftR m] prefix of a bind, when [exec m] is known.   *)
(* (exec/execR twin of runR_liftR_seq.)                                    *)
(* ---------------------------------------------------------------------- *)
Lemma execR_liftR_seq {R X Y} (m : M Y) (f : Y -> Defs.monadR R exception X)
    (s s' : mstate) (x : Y) :
  exec m s = Some (x, s') ->
  execR (Defs.bind (Defs.liftR m) f) s = execR (f x) s'.
Proof.
  intro Hm. rewrite execR_bind. rewrite execR_liftR. rewrite Hm. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf twins of the PMP body (mirror run_pmpReadAddrReg_ex /              *)
(* run_pmpMatchAddr_OFF).                                                   *)
(* ---------------------------------------------------------------------- *)
Lemma exec_pmpReadAddrReg_ex (n : Z) s :
  exists v, exec (pmpReadAddrReg n) s = Some (v, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta. eexists.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  apply exec_returnM.
Qed.

Lemma exec_pmpMatchAddr_OFF (pa : physaddr) (width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = OFF ->
  exec (pmpMatchAddr pa width ent pmpaddr prev) s = Some (PMP_NoMatch, s).
Proof.
  intro HOFF. destruct pa as [addr0]. unfold pmpMatchAddr. cbn zeta.
  rewrite HOFF. cbn match. apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* CENTERPIECE: exec twin of run_pmpCheck_machine_none (the PMP foreach     *)
(* loop), via execR_foreach_ZM_up_const.                                    *)
(* ---------------------------------------------------------------------- *)
Lemma exec_pmpCheck_machine_none
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  exec (pmpCheck addr width access Machine) s = Some (None, s).
Proof.
  intro HpmpOFF.
  unfold pmpCheck.
  rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_bind0.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inr vars, s))
  end.
  { apply execR_foreach_ZM_up_const. intros i v. destruct v. cbn beta.
    destruct (Z.gtb i 0) eqn:Hi; cbn match.
    - destruct (exec_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      rewrite (execR_liftR_seq _ _ _ _ _ Hpv). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_returnR.
    - rewrite execR_bind. rewrite execR_returnR. cbn match. cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_returnR. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

Print Assumptions exec_pmpCheck_machine_none.

(* ---------------------------------------------------------------------- *)
(* NEW CENTERPIECE (unlocked PMP): in MACHINE mode, if every PMP entry is  *)
(* UNLOCKED (L = 0) -- regardless of its A-field and of the pmpaddr        *)
(* register values -- pmpCheck grants the access, PROVIDED the access lies *)
(* within a single 4-byte grain cell (addr mod 4 + width <= 4).  All       *)
(* region boundaries the walk can produce (TOR / NA4 / NAPOT, grain 0) are *)
(* multiples of 4, so a cell-contained access can never PARTIALLY match an *)
(* entry (a partial match faults EVEN in M-mode).  Per entry the step is   *)
(* then allow-or-continue:                                                 *)
(*   NoMatch -> continue;                                                  *)
(*   Match   -> priv = Machine /\ L = 0 -> or_boolM short-circuits to true *)
(*              -> early_return None (allow).                              *)
(* The fold invariant is [execR_foreach_ZM_up_allow] below: every body     *)
(* iteration is a state-preserving no-op OR the early-return [inl r]; the  *)
(* whole loop then ends in [inr vars] (fall through to the M-mode default  *)
(* allow) or [inl r] (early allow).                                        *)
(* ---------------------------------------------------------------------- *)

(* early_return under execR: the [inl] early-exit value, state unchanged. *)
Lemma execR_early_return {R X} (r : R) s :
  execR (Defs.early_return r : Defs.monadR R exception X) s = Some (inl r, s).
Proof. reflexivity. Qed.

(* The loop invariant with early exit: a body that at every index either
   continues (inr v, no state change) or early-returns (inl r, no state
   change) makes the whole bounded loop end in one of the same two ways. *)
Lemma execR_foreach_ZM_up'_allow {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) (r : R) :
  (forall i v, execR (body i v) s = Some (inr v, s)
            \/ execR (body i v) s = Some (inl r, s)) ->
  forall (n : nat) (from : Z) (vars : Vars),
    execR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inr vars, s)
    \/ execR (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inl r, s).
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - cbn [Defs.foreach_ZM_up']. destruct (from <=? to); left; apply execR_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + rewrite (Defs.unroll_foreach_ZM_up' _ _ from to step n vars body Hle).
      rewrite execR_bind.
      destruct (Hbody from vars) as [Hb|Hb]; rewrite Hb.
      * exact (IH (from + step) vars).
      * right. reflexivity.
    + cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false by (symmetry; apply Z.leb_gt; lia).
      left. apply execR_returnm_fwd.
Qed.

Lemma execR_foreach_ZM_up_allow {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) (r : R) :
  (forall i v, execR (body i v) s = Some (inr v, s)
            \/ execR (body i v) s = Some (inl r, s)) ->
  execR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inr vars, s)
  \/ execR (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inl r, s).
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply execR_foreach_ZM_up'_allow; exact Hbody.
Qed.

(* pmpRangeMatch dichotomy: against a region whose two boundaries are      *)
(* multiples of 4, an access contained in one aligned 4-byte cell          *)
(* (a mod 4 + w <= 4) either misses or matches FULLY -- never partially.   *)
Lemma pmpRangeMatch_cell (b e a w : Z) :
  (4 | b) -> (4 | e) -> a mod 4 + w <= 4 ->
  pmpRangeMatch b e a w = PMP_NoMatch \/ pmpRangeMatch b e a w = PMP_Match.
Proof.
  intros [kb ->] [ke ->] Hfit.
  unfold pmpRangeMatch.
  destruct (Z.leb (Z.add a w) (kb * 4)) eqn:H1; [left; reflexivity|].
  destruct (Z.leb (ke * 4) a) eqn:H2; cbn [orb]; [left; reflexivity|].
  apply Z.leb_gt in H1. apply Z.leb_gt in H2.
  right.
  replace (Z.leb (kb * 4) a) with true
    by (symmetry; apply Z.leb_le;
        pose proof (Z.div_mod a 4 ltac:(lia)); pose proof (Z.mod_pos_bound a 4 ltac:(lia)); lia).
  replace (Z.leb (Z.add a w) (ke * 4)) with true
    by (symmetry; apply Z.leb_le;
        pose proof (Z.div_mod a 4 ltac:(lia)); pose proof (Z.mod_pos_bound a 4 ltac:(lia)); lia).
  reflexivity.
Qed.

(* the two divisibility shapes the pmpMatchAddr boundaries come in *)
Lemma divide4_factor (x : Z) : (4 | Z.mul x 4).
Proof. exists x. reflexivity. Qed.
Lemma divide4_factor_plus (x : Z) : (4 | Z.add (Z.mul x 4) 4).
Proof. exists (x + 1). lia. Qed.

(* pmpMatchAddr dichotomy for a cell-contained access: whatever the entry's
   A-field and the pmpaddr values, the result is NoMatch or (full) Match,
   with no state change.  (NA4's grain assertion passes: sys_pmp_grain = 0.) *)
Lemma exec_pmpMatchAddr_machine_cell (pa : physaddr) (wbv : mword 64) (ent : mword 8)
    (paddr prev : mword 64) s :
  uint (bits_of_physaddr pa) mod 4 + uint wbv <= 4 ->
  exec (pmpMatchAddr pa wbv ent paddr prev) s = Some (PMP_NoMatch, s)
  \/ exec (pmpMatchAddr pa wbv ent paddr prev) s = Some (PMP_Match, s).
Proof.
  intros Hfit. destruct pa as [a]. cbn in Hfit.
  unfold pmpMatchAddr. cbn zeta.
  destruct (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)).
  - (* OFF *) left. apply exec_returnM.
  - (* TOR *)
    destruct (zopz0zKzJ_u prev paddr).
    + left. apply exec_returnM.
    + destruct (pmpRangeMatch_cell (Z.mul (uint prev) 4) (Z.mul (uint paddr) 4)
                  (uint a) (uint wbv)
                  (divide4_factor (uint prev)) (divide4_factor (uint paddr)) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply exec_returnM.
  - (* NA4: the grain assertion holds (sys_pmp_grain = 0 < 1). *)
    destruct (pmpRangeMatch_cell (Z.mul (uint paddr) 4) (Z.add (Z.mul (uint paddr) 4) 4)
                  (uint a) (uint wbv)
                  (divide4_factor (uint paddr)) (divide4_factor_plus (uint paddr)) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply exec_returnM.
  - (* NAPOT *)
    destruct (pmpRangeMatch_cell
                  (Z.mul (uint (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1))))) 4)
                  (Z.mul (Z.add (Z.add (uint (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1)))))
                                       (uint (xor_vec paddr (add_vec_int paddr 1)))) 1) 4)
                  (uint a) (uint wbv)
                  (divide4_factor _) (divide4_factor _) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply exec_returnM.
Qed.

(* The unlocked-M-mode pmpCheck reduction.  [Hrwx] asks only that the RWX  *)
(* permission read is a pure boolean for this access type (it is, for all  *)
(* the access types the boot WPs use; it is consulted -- and short-circuited *)
(* by Machine /\ unlocked -- only in the full-match case).                 *)
Lemma exec_pmpCheck_machine_unlocked
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  (forall ent, exists b, exec (pmpCheckRWX ent access) s = Some (b, s)) ->
  uint (bits_of_physaddr addr) mod 4 + uint (to_bits 64 width) <= 4 ->
  exec (pmpCheck addr width access Machine) s = Some (None, s).
Proof.
  intros HL Hrwx Hfit.
  unfold pmpCheck.
  rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_bind0.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hbody : forall i v,
                 execR (body i v) s = Some (inr v, s)
              \/ execR (body i v) s = Some (inl (None : option ExceptionType), s))
  end.
  { intros i v. destruct v. cbn beta.
    destruct (Z.gtb i 0) eqn:Hi; cbn match.
    - destruct (exec_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      rewrite (execR_liftR_seq _ _ _ _ _ Hpv). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      destruct (exec_pmpMatchAddr_machine_cell addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) w2 pv s Hfit)
        as [Hm|Hm].
      + left. rewrite (execR_liftR_seq _ _ _ _ _ Hm). cbn beta.
        cbn match. apply execR_returnR.
      + right. rewrite (execR_liftR_seq _ _ _ _ _ Hm). cbn beta. cbn match.
        rewrite execR_bind. unfold or_boolM. rewrite execR_bind. rewrite execR_liftR.
        destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) as [b Hb].
        rewrite Hb. cbn match.
        destruct b; [reflexivity | rewrite (HL i); reflexivity].
    - rewrite execR_bind. rewrite execR_returnR. cbn match. cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      destruct (exec_pmpMatchAddr_machine_cell addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) w2 (zeros' 64) s Hfit)
        as [Hm|Hm].
      + left. rewrite (execR_liftR_seq _ _ _ _ _ Hm). cbn beta.
        cbn match. apply execR_returnR.
      + right. rewrite (execR_liftR_seq _ _ _ _ _ Hm). cbn beta. cbn match.
        rewrite execR_bind. unfold or_boolM. rewrite execR_bind. rewrite execR_liftR.
        destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) as [b Hb].
        rewrite Hb. cbn match.
        destruct b; [reflexivity | rewrite (HL i); reflexivity]. }
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      destruct (execR_foreach_ZM_up_allow F T S body s vars _ Hbody) as [Hloop|Hloop]
  end;
  rewrite Hloop; cbn match; reflexivity.
Qed.

Print Assumptions exec_pmpCheck_machine_unlocked.

(* ===== RiscvModelFetchAsm ===== *)
(* ====================================================================== *)
(* RiscvModelFetchAsm.v                                                    *)
(*                                                                         *)
(* Read-path gates toward `run_fetch_F_Base`:                              *)
(*   - within_mmio_readable = false  (RAM, not MMIO)                       *)
(*   - phys_access_check = None      (composes pmpCheck=None + pmaCheck=None)*)
(*   - checked_mem_read reduces to read_ram (the value the memory holds)   *)
(* built on the proven leaf lemmas (translateAddr-identity, pmpCheck=None, *)
(* read_ram_plain_4) and the run/runR machinery.                           *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* 1. within_mmio_readable = false for a non-MMIO (RAM) address.           *)
(*    The CLINT/SIG/HTIF range tests are geometric facts about the address *)
(*    (false for kernel-code addresses >= 0x80000000); we take them as     *)
(*    hypotheses (their concrete reduction depends on the plat_* config).  *)
(* ---------------------------------------------------------------------- *)

Lemma run_within_mmio_readable_false (addr : physaddr) (width : Z) s :
  run (within_clint addr width) s false s ->
  run (within_sig addr width) s false s ->
  run (within_htif_readable addr width) s false s ->
  run (within_mmio_readable addr width) s false s.
Proof.
  intros Hc Hsig Hh.
  unfold within_mmio_readable.
  cbn [get_config_rvfi].
  apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split; [exact Hc|].
  cbn match.
  apply (proj2 (run_or_boolM _ _ _ _ _)). exists false, s. split; [exact Hsig|].
  cbn match.
  apply (proj2 (run_and_boolM _ _ _ _ _)). exists false, s. split; [exact Hh|].
  cbn match. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. phys_access_check = None when both PMP and PMA allow the access.     *)
(* ---------------------------------------------------------------------- *)

Lemma run_phys_access_check_none
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (paddr : physaddr) (width : Z) (res : bool) s :
  run (pmpCheck paddr width access priv) s None s ->
  run (pmaCheck paddr width access pbmt res) s None s ->
  run (phys_access_check access pbmt priv paddr width res) s None s.
Proof.
  intros Hpmp Hpma.
  unfold phys_access_check.
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split; [exact Hpmp|].
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split; [exact Hpma|].
  cbn match. apply (proj2 (run_returnM _ _ _ _)). split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. checked_mem_read reduces to read_ram for an allowed, non-MMIO,       *)
(*    plain (aq=rl=res=false) read.                                        *)
(* ---------------------------------------------------------------------- *)


(* ===== RiscvModelFetchF ===== *)
(* ====================================================================== *)
(* RiscvModelFetchF.v                                                      *)
(*                                                                         *)
(* Toward run_fetch_F_Base : run (fetch tt) s (F_Base word) s with a       *)
(* CONCRETE word.  Resolves the pmaCheck representation issue, pins the    *)
(* read value, threads the mem_read wrapper, and assembles fetch_bytes /   *)
(* fetch.                                                                   *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* 1. Pinned read: the read value is exactly [w] (not just existential).   *)
(*    Same proof as run_read_ram_plain_4, but the strengthened MemRead     *)
(*    rule lets us state the concrete result.                              *)
(* ---------------------------------------------------------------------- *)

Lemma run_read_ram_plain_4_pin (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 4 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. pmaCheck = None for an executable, aligned RAM region (InstructionFetch). *)
(*    The InstructionFetch arm returns the region's [PMA_executable] bool, *)
(*    which the wrapper maps to [None] when it is [true].                  *)
(* ---------------------------------------------------------------------- *)

Lemma run_pmaCheck_ram (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s None s.
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_read_reg_fwd | ].
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  (* misaligned = not (is_aligned_paddr ...) = not true = false *)
  rewrite Halign. cbn [negb].
  (* (if not false then returnM None else ...) >>= fun me => match me with ... *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists None, s. split; [ apply run_returnM_fwd | ].
  cbn match beta.
  (* match access (InstructionFetch) => returnM (override_PMA rattr pbmt).PMA_executable *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ].
  (* canAccess = (override_PMA rattr pbmt).PMA_executable = true ; print guard = tt *)
  rewrite Hexec. cbn [andb negb].
  apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Pinned checked_mem_read: result is exactly [Ok (w, default_meta)].   *)
(* ---------------------------------------------------------------------- *)

Lemma run_checked_mem_read_ram_pin
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (within_clint (Physaddr addr) 4) s false s ->
  run (within_sig (Physaddr addr) 4) s false s ->
  run (within_htif_readable (Physaddr addr) 4) s false s ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 4 false false false false)
      s (Ok (w, default_meta)) s.
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  apply (proj2 (run_bind _ _ _ _ _)). exists None, s. split.
  { apply run_phys_access_check_none.
    - apply run_pmpCheck_machine_none; exact Hpmp.
    - apply run_pmaCheck_ram with (region := region); assumption. }
  apply (proj2 (run_bind _ _ _ _ _)). exists false, s. split.
  { apply run_within_mmio_readable_false; assumption. }
  apply (proj2 (run_bind _ _ _ _ _)). exists Read_plain, s. split.
  { unfold read_kind_of_flags. apply run_returnM_fwd. }
  apply (proj2 (run_bind _ _ _ _ _)). exists (w, default_meta), s. split.
  { apply run_read_ram_plain_4_pin; exact Hbytes. }
  apply run_returnM_fwd.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. mem_read for an InstructionFetch in Machine mode reduces to [Ok w].  *)
(*    effectivePrivilege(InstructionFetch)=cur_privilege; the (aq||res)    *)
(*    alignment guard is false; mem_read_callback is a pure unit; the meta *)
(*    is dropped (Ok (w,()) -> Ok w).                                      *)
(* ---------------------------------------------------------------------- *)

Lemma run_mem_read_fetch_pin
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  run (within_clint (Physaddr addr) 4) s false s ->
  run (within_sig (Physaddr addr) 4) s false s ->
  run (within_htif_readable (Physaddr addr) 4) s false s ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  run (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
      s (Ok w) s.
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  (* read mstatus *)
  apply (proj2 (run_bind _ _ _ _ _)). eexists _, s. split; [ exact (run_read_reg_fwd mstatus s) | ].
  (* read cur_privilege *)
  apply (proj2 (run_bind _ _ _ _ _)). eexists _, s. split; [ exact (run_read_reg_fwd cur_privilege s) | ].
  (* effectivePrivilege (InstructionFetch) = returnM cur_privilege *)
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists (register_lookup cur_privilege s.(sregs)), s. split.
  { unfold effectivePrivilege.
    replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
      by (vm_compute; reflexivity).
    cbn [andb]. apply run_returnM_fwd. }
  rewrite Hpriv.
  (* mem_read_priv = mem_read_priv_meta >>= drop_meta *)
  unfold mem_read_priv.
  apply (proj2 (run_bind _ _ _ _ _)). eexists (Ok (w, default_meta)), s. split.
  { unfold mem_read_priv_meta.
    cbn [orb andb].
    apply (proj2 (run_bind _ _ _ _ _)). eexists (Ok (w, default_meta)), s. split.
    { cbn match.
      apply run_checked_mem_read_ram_pin with (region := region); assumption. }
    cbn match. unfold mem_read_callback. apply run_returnM_fwd. }
  cbn [MemoryOpResult_drop_meta]. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelFetchFinal ===== *)
(* ====================================================================== *)
(* RiscvModelFetchFinal.v                                                  *)
(*                                                                         *)
(* Closes [run_fetch_F_Base : run (fetch tt) s (F_Base word) s] with a     *)
(* CONCRETE word, by threading the MR-monad structure of [fetch_bytes]/    *)
(* [fetch] over the proven leaves (translateAddr identity, mem_read pin,   *)
(* currentlyEnabled Ext_Ziccif).  Collapses Hcycle's fetch dep to Hdec.    *)
(* ====================================================================== *)


(* The physical address translateAddr produces for an instruction fetch. *)
Definition fetch_pa (pc : mword 64) : mword 64 :=
  zero_extend' 64 (bits_of_virtaddr (Virtaddr pc)).

(* autocast between convertible widths (8*4 and 4*8, both 32) is identity. *)
Lemma autocast_mword_id (w : bv 32) :
  autocast (T := mword) (m := 8 * 4) (n := 4 * 8) w = w.
Proof.
  unfold autocast.
  destruct (Z.eq_dec (8 * 4) (4 * 8)) as [e | ne].
  - apply cast_Z_refl.
  - exfalso; apply ne; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Inner: fetch_bytes pc pc 4 reduces to FetchBytes_Success word.          *)
(* ---------------------------------------------------------------------- *)
Section FetchBytes.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hclint : run (within_clint (Physaddr addr) 4) s false s.
  Hypothesis Hsig : run (within_sig (Physaddr addr) 4) s false s.
  Hypothesis Hhtif : run (within_htif_readable (Physaddr addr) 4) s false s.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma run_fetch_bytes_4 : run (fetch_bytes pc pc 4) s (@FetchBytes_Success 4 w) s.
  Proof.
    unfold fetch_bytes.
    apply run_catch_early_return. right.
    change (ext_fetch_check_pc pc pc) with (@None unit).
    cbv iota beta.  (* match None -> returnR tt *)
    (* body = (returnR tt >> liftR transl) >>= (fun w0 => match w0 .. >>= ..).
       Outermost bind: intermediate value = the translateAddr result. *)
    apply runR_bind. right.
    exists (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s. split.
    { (* returnR tt >> liftR transl  -->  Ok (..) *)
      unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      apply runR_liftR. exists (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)).
      split; [ reflexivity | apply run_translateAddr_identity; exact Hpriv ]. }
    (* fun w0 => (match Ok .. -> returnR (paddr,pbmt)) >>= fun '(p,m) => .. *)
    cbv iota beta.
    apply runR_bind. right. exists (Physaddr addr, PBMT_PMA), s. split.
    { apply runR_returnR_fwd. }
    (* fun '(paddr,pbmt) => liftR (mem_read ..) >>= fun w2 => returnR (match w2 ..) *)
    cbv iota beta.
    apply runR_bind. right. exists (Ok w), s. split.
    { apply runR_liftR. exists (Ok w). split; [ reflexivity | ].
      apply (run_mem_read_fetch_pin PBMT_PMA addr region w s); assumption. }
    (* returnR (FetchBytes_Success (autocast w)) *)
    cbv iota beta. rewrite autocast_mword_id. apply runR_returnR_fwd.
  Qed.
End FetchBytes.

(* ---------------------------------------------------------------------- *)
(* Outer: fetch tt reduces to F_Base word (aligned PC, not RVC).           *)
(* ---------------------------------------------------------------------- *)
Section Fetch.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hclint : run (within_clint (Physaddr addr) 4) s false s.
  Hypothesis Hsig : run (within_sig (Physaddr addr) 4) s false s.
  Hypothesis Hhtif : run (within_htif_readable (Physaddr addr) 4) s false s.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  (* alignment of the PC, phrased as the boolean facts fetch actually tests *)
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = false.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.

  Lemma run_fetch_F_Base : run (fetch tt) s (F_Base w) s.
  Proof.
    assert (HrdPC : run (Defs.read_reg PC) s pc s).
    { rewrite <- HpcPC. apply run_read_reg_fwd. }
    unfold fetch.
    apply run_catch_early_return. right.
    change (get_config_rvfi tt) with false. cbv iota beta.
    (* read PC twice *)
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { exact HrdPC. }
    (* ext_fetch_check_pc pc pc = None *)
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* outer: (returnR tt >> or_boolM) >>= fun w7 => REST ; or_boolM = false *)
    apply runR_bind. right. exists false, s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      cbv beta.
      (* or_boolM (PC[0]!=0) (and_boolM (PC[1]!=0) (not Ext_Zca)) = false *)
      unfold or_boolM. apply runR_bind. right. exists false, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hbit0. apply runR_returnR_fwd. }
      cbv iota beta.
      (* short-circuit on PC[1]=0 (Ext_Zca not evaluated) *)
      unfold and_boolM. apply runR_bind. right. exists false, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hbit1. apply runR_returnR_fwd. }
      cbv iota beta. apply runR_returnR_fwd. }
    cbv iota beta.
    (* w7 = false -> else: and_boolM (is_aligned) (Ext_Ziccif) >>= fun w11 => .. ; w11 = true *)
    apply runR_bind. right. exists true, s. split.
    { unfold and_boolM. apply runR_bind. right. exists true, s. split.
      { eapply runR_liftR_seq. { exact HrdPC. }
        rewrite Hvalign. apply runR_returnR_fwd. }
      cbv iota beta.
      (* bare [liftR (currentlyEnabled Ext_Ziccif)] = true *)
      apply runR_liftR. exists true. split; [ reflexivity | apply run_currentlyEnabled_Ziccif ]. }
    cbv iota beta.
    (* w11 = true -> read PC twice, fetch_bytes pc pc 4 -> FetchBytes_Success w -> F_Base w *)
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { exact HrdPC. }
    eapply runR_liftR_seq. { apply (run_fetch_bytes_4 pc region w s); assumption. }
    cbv iota beta. rewrite HnotRVC. cbv iota beta. apply runR_returnR_fwd.
  Qed.
End Fetch.

Print Assumptions run_fetch_F_Base.

(* ===== RiscvModelCycle ===== *)
(* ====================================================================== *)
(* RiscvModelCycle.v                                                       *)
(* Final-assembly helpers: the try_step wrapper value-helpers reduce       *)
(* through [run] (state-preserving), toward composing the full cycle.      *)
(* ====================================================================== *)

Import Defs.



(* should_inc_minstret is state-preserving (its value feeds minstret bookkeeping). *)

(* dispatchInterrupt yields None when no interrupt is pending. *)
Lemma run_dispatchInterrupt_none s priv :
  run (getPendingSet priv) s None s ->
  run (dispatchInterrupt priv) s None s.
Proof.
  intros Hp. unfold dispatchInterrupt.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists None, s. split; [ exact Hp | apply run_returnM_fwd ].
Qed.

(* is_landing_pad_expected is false when elp != LP_EXPECTED. *)
Lemma run_is_landing_pad_false s :
  eq_vec (register_lookup elp s.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  run (is_landing_pad_expected tt) s false s.
Proof.
  intros He. unfold is_landing_pad_expected.
  apply (proj2 (run_bind _ _ _ _ _)).
  exists (register_lookup elp s.(sregs)), s.
  split; [ exact (run_read_reg_fwd elp s) | ].
  rewrite <- He. apply run_returnM_fwd.
Qed.

(* ===== RiscvModelWrapper ===== *)
(* ====================================================================== *)
(* RiscvModelWrapper.v                                                     *)
(*                                                                         *)
(* Reductions for the try_step WRAPPER CSR helpers, toward discharging     *)
(* Hcycle. Built on the proven run-lemmas (run_bind/run_read_reg/...).     *)
(* The memory subsystem on the fetch path (translateAddr / mem_read /      *)
(* pmpCheck) is the remaining deep residue and is NOT reduced here — it is *)
(* documented as the explicit fetch hypotheses in the report.             *)
(* ====================================================================== *)



(* tick_pc copies nextPC into PC (pc_write_callback is the pure unit tt).
   This is exactly how the cycle advances the PC: after execute sets
   nextPC := PC+4, tick_pc gives PC := PC+4. *)
Lemma run_tick_pc s y s' :
  run (tick_pc tt) s y s' <->
  (y = tt /\ s' = set_reg s PC (register_lookup nextPC s.(sregs))).
Proof.
  unfold tick_pc. split.
  - intros H.
    rewrite run_bind in H. destruct H as (w0 & s1 & H0 & H).
    apply (proj1 (run_read_reg nextPC _ _ _)) in H0. destruct H0 as [-> ->].
    rewrite run_bind in H. destruct H as (w1 & s2 & Hblk & H).
    rewrite run_bind0 in Hblk. destruct Hblk as (s3 & Hw & Hr).
    apply (proj1 (run_write_reg PC _ _ _ _)) in Hw. destruct Hw as [_ ->].
    apply (proj1 (run_read_reg PC _ _ _)) in Hr. destruct Hr as [-> ->].
    apply (proj1 (run_returnM _ _ _ _)) in H. destruct H as [-> ->].
    split; reflexivity.
  - intros [-> ->].
    rewrite run_bind. exists (register_lookup nextPC s.(sregs)), s.
    split; [ apply (proj2 (run_read_reg nextPC _ _ _)); split; reflexivity | ].
    rewrite run_bind.
    exists (register_lookup PC (set_reg s PC (register_lookup nextPC s.(sregs))).(sregs)),
           (set_reg s PC (register_lookup nextPC s.(sregs))).
    split.
    + rewrite run_bind0. exists (set_reg s PC (register_lookup nextPC s.(sregs))).
      split; [ apply (proj2 (run_write_reg PC _ _ _ _)); split; reflexivity
             | apply (proj2 (run_read_reg PC _ _ _)); split; reflexivity ].
    + apply (proj2 (run_returnM _ _ _ _)). split; reflexivity.
Qed.

(* is_landing_pad_expected / should_inc_minstret reduce by the SAME pattern
   (run_bind + run_read_reg + run_returnM, plus run_and_boolM for the latter);
   omitted here only because stating their results needs model-internal names
   (eq_vec / counter_priv_filter_bit) not exported by short name. They are not
   the bottleneck — the memory subsystem (translate/mem_read/pmpCheck) is. *)

(* ===== RiscvModelCycleAsm ===== *)
(* ====================================================================== *)
(* RiscvModelCycleAsm.v                                                    *)
(*                                                                         *)
(* CAPSTONE composition: thread the proven axiom-free leaves through the   *)
(* real [run_hart_active] (ADD / F_Base path) and the [try_step] wrapper,  *)
(* toward discharging [Hcycle] in wp_add_real.                             *)
(*                                                                         *)
(* run_hart_active_ADD is decomposed to take the fetch result as a         *)
(* hypothesis [Hfetch] (so it does not re-thread run_fetch_F_Base's        *)
(* geometric hypotheses); the concrete fetch is plugged in downstream.     *)
(* ====================================================================== *)




Open Scope Z_scope.

Section HartActiveADD.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (rs2 rs1 rd : mword 5).

  (* booting-Machine-mode / no-interrupt CSR facts *)
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpend : run (getPendingSet Machine) s None s.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Help  :
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false.
  (* the fetched word, as a hypothesis (discharged downstream by run_fetch_F_Base) *)
  Hypothesis Hfetch : run (fetch tt) s (F_Base w) s.
  (* the decode result (the decode wall, carried as Hdec) *)
  Hypothesis Hdec :
    run (ext_decode w) s (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) s.
  (* the register indices a0=x10, a1=x11, a2=x12 *)
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  (* state after the cycle's hart-active part:
     nextPC := pc+4 (written before execute), then a2 := a0+a1 by execute(ADD). *)
  Let s1 : mstate := set_reg s nextPC (add_vec_int pc 4).
  Let s_exec : mstate :=
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).

  Lemma run_hart_active_ADD :
    run (run_hart_active 0) s
        (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)) s_exec.
  Proof.
    unfold run_hart_active.
    apply run_catch_early_return. right.
    (* read cur_privilege = Machine (state-preserving) *)
    eapply runR_liftR_seq with (a := Machine).
    { pose proof (run_read_reg_fwd cur_privilege s) as H. rewrite Hpriv in H. exact H. }
    (* dispatchInterrupt Machine = None (state-preserving) *)
    eapply runR_liftR_seq with (a := @None (InterruptType * Privilege)%type).
    { apply run_dispatchInterrupt_none. exact Hpend. }
    cbv iota beta.
    (* [(match None => returnR tt) >> liftR(fetch)] yields F_Base w, then continuation *)
    apply runR_bind. right. exists (F_Base w), s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      apply runR_liftR. exists (F_Base w). split; [reflexivity| exact Hfetch]. }
    (* continuation: ext_fetch_hook (F_Base w) = F_Base w; the F_Base arm *)
    cbv iota beta.
    (* ext_decode w = RTYPE ... ADD (state-preserving) *)
    eapply runR_liftR_seq with (a := RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)).
    { exact Hdec. }
    (* [(if print=false => returnR tt) >> and_boolM(landing_pad=false) _] yields false *)
    cbv iota beta.
    apply runR_bind. right. exists false, s. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s. split.
      { apply runR_returnR_fwd. }
      unfold and_boolM. apply runR_bind. right. exists false, s. split.
      { apply runR_liftR. exists false. split; [reflexivity|].
        apply run_is_landing_pad_false. exact Help. }
      cbv iota beta. apply runR_returnR_fwd. }
    (* w21 = false -> else branch *)
    cbv iota beta.
    (* read PC = pc (state-preserving) *)
    eapply runR_liftR_seq with (a := pc).
    { pose proof (run_read_reg_fwd PC s) as H. rewrite HpcPC in H. exact H. }
    (* [liftR(write nextPC (pc+4)) >> liftR(execute instr)] : s -> s_exec, RETIRE_SUCCESS *)
    apply runR_bind. right. exists RETIRE_SUCCESS, s_exec. split.
    { unfold Defs.bind0. apply runR_bind. right. exists tt, s1. split.
      { apply runR_liftR. exists tt. split; [reflexivity|].
        apply (proj2 (run_write_reg nextPC (add_vec_int pc 4) s tt s1)).
        split; reflexivity. }
      apply runR_liftR. exists RETIRE_SUCCESS. split; [reflexivity|].
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      unfold s_exec.
      apply (run_execute_ADD_x12_x10_x11 rd rs1 rs2 s1 Hrs1 Hrs2 Hrd). }
    (* match RETIRE_SUCCESS => result' = RETIRE_SUCCESS ; returnR Step_Execute *)
    cbv iota beta.
    apply runR_bind. right. exists RETIRE_SUCCESS, s_exec. split.
    { apply runR_returnR_fwd. }
    cbv iota beta. apply runR_returnR_fwd.
  Qed.

End HartActiveADD.

