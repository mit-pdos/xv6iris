(* CalleeSaved.v -- a predicate for callee-saved register preservation across a
   function call, for use in whole-function WP postconditions.

   A well-behaved RISC-V function preserves the callee-saved registers: it may
   clobber the caller-saved ones (ra, t0-t6, a0-a7) freely, but every
   callee-saved register holds, on return, exactly the value it held on entry.
   [callee_saved m m'] captures precisely that relationship between the entry
   register map [m] and the return register map [m']: it says nothing about the
   caller-saved registers (their values are arbitrary and irrelevant), and
   asserts that each preserved register agrees in [m] and [m'].

   The preserved set is: sp (x2), s0 (x8), s1 (x9), s2..s11 (x18..x27) -- the
   classic RISC-V callee-saved registers -- plus tp (x4), which this kernel pins
   to the cpuid and every function preserves.  Function-call WPs universally
   quantify the return register map over the whole continuation --
   [∀ m', ... -∗ gpr_file m' -∗ ⌜callee_saved m m'⌝ -∗ ... -∗ WP ...] -- in place
   of an ad-hoc, per-function list of individual register-preservation facts.
   (Callers thus receive [m'] and the preservation fact directly, rather than
   destructing an [∃ m', gpr_file m' ∗ ⌜callee_saved m m'⌝] package.) *)
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Import ListNotations.

Definition callee_saved (m m' : regfile) : Prop :=
  m' !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\                            (* x2  sp  *)
  m' !!! Regidx (mword_of_int 4 : mword 5)  = m !!! Regidx (mword_of_int 4 : mword 5)  /\  (* x4  tp *)
  m' !!! Regidx (mword_of_int 8 : mword 5)  = m !!! Regidx (mword_of_int 8 : mword 5)  /\  (* x8  s0 *)
  m' !!! Regidx (mword_of_int 9 : mword 5)  = m !!! Regidx (mword_of_int 9 : mword 5)  /\  (* x9  s1 *)
  m' !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\  (* x18 s2 *)
  m' !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\  (* x19 s3 *)
  m' !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\  (* x20 s4 *)
  m' !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\  (* x21 s5 *)
  m' !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\  (* x22 s6 *)
  m' !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\  (* x23 s7 *)
  m' !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\  (* x24 s8 *)
  m' !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\  (* x25 s9 *)
  m' !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\  (* x26 s10 *)
  m' !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).     (* x27 s11 *)

Lemma callee_saved_refl (m : regfile) : callee_saved m m.
Proof. unfold callee_saved. repeat split; reflexivity. Qed.

Lemma callee_saved_trans (m1 m2 m3 : regfile) :
  callee_saved m1 m2 -> callee_saved m2 m3 -> callee_saved m1 m3.
Proof.
  unfold callee_saved.
  intros (?&?&?&?&?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  repeat split; etransitivity; eassumption.
Qed.

(* [is_cs_idx k] : is register index [k] one of the fourteen callee-saved
   registers?  A [bool] so the side condition below discharges by [vm_compute]. *)
Definition is_cs_idx (k : mword 5) : bool :=
  existsb (fun c => bool_decide (k = (mword_of_int c : mword 5)))
    [2;4;8;9;18;19;20;21;22;23;24;25;26;27]%Z.

Lemma is_cs_idx_true_neq (k c : mword 5) :
  is_cs_idx k = false -> is_cs_idx c = true -> Regidx k <> Regidx c.
Proof. intros Hk Hc Heq. injection Heq as Heq'. subst c. rewrite Hc in Hk. discriminate. Qed.

(* [Regidx] is injective.  The other half of the callee-saved peel's
   disequality discharge: where the WRITTEN register is itself callee-saved,
   [is_cs_idx_true_neq] does not apply and the branch has to turn the
   index disequality it has in context into the [Regidx] one [upd_ne]
   asks for.  Named (rather than inlined as [injection]) so that branch
   can stay NAME-FREE -- an [Ltac] body cannot reference a hypothesis by
   literal name (claude-notes/durable-notes.md); see the peel recipe at
   the end of claude-notes/optimization.md. *)
Lemma regidx_inj (x y : mword 5) : Regidx x = Regidx y -> x = y.
Proof. intro H. injection H as H. exact H. Qed.


(* Project one register out of a [callee_saved] fact, uniformly for ANY
   callee-saved index [c] (decided by [is_cs_idx c = true]).  A caller that
   threads a register through a sub-call hop can [rewrite (callee_saved_lookup
   H (mword_of_int c) …)] instead of picking the right conjunct out of a
   [first [rewrite H_tp | rewrite H_s3 | …]] alternation (O(#conjuncts) failed
   rewrites per hop). *)
Lemma callee_saved_lookup {m m' : regfile}
      (Hcs : callee_saved m m') (c : mword 5) :
  is_cs_idx c = true -> m' !!! Regidx c = m !!! Regidx c.
Proof.
  intros Hc. unfold callee_saved in Hcs.
  destruct Hcs as (H&H0&H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12).
  (* [c] is one of the 14 concrete indices; [is_cs_idx c] picks which. *)
  unfold is_cs_idx in Hc. cbn [existsb] in Hc. rewrite !orb_true_iff in Hc.
  repeat (destruct Hc as [Hc|Hc]); try discriminate;
    apply bool_decide_eq_true in Hc; subst c;
    first [ change (mword_of_int 2) with (csp_rs1 : mword 5); assumption | assumption ].
Qed.

(* Writing a CALLER-saved register (rd, ra, or any t/a register) leaves
   [callee_saved] intact.  This is THE efficient discharge primitive for own
   register writes: each own-write becomes one [apply callee_saved_insert_r]
   with a [vm_compute]-decided side condition, instead of re-peeling the whole
   insert tower once per callee-saved register (the O(depth * 14) blowup).  For
   a function's saved-then-restored frame registers (which ARE callee-saved)
   the final value equals the entry value, so those few conjuncts stay explicit;
   compose across sub-calls with [callee_saved_trans] on the callees' whole
   [callee_saved] facts rather than destructuring them. *)
Lemma callee_saved_insert_r (k : mword 5) (v : mword 64)
      (m m' : regfile) :
  is_cs_idx k = false ->
  callee_saved m m' ->
  callee_saved m (<[Regidx k := v]> m').
Proof.
  intros Hk Hcs. unfold callee_saved in *.
  destruct Hcs as (H&H0&H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12).
  repeat split;
    (rewrite upd_ne
       by (apply not_eq_sym, (is_cs_idx_true_neq _ _ Hk); vm_compute; reflexivity);
     assumption).
Qed.

(* -------------------------------------------------------------------------- *)
(* Discharging [callee_saved m mF] when [mF] is a deep insert TOWER over [m]    *)
(* (a whole-function's output register file).  A function that saves-then-      *)
(* restores its callee-saved frame registers produces intermediate maps that   *)
(* are NOT [callee_saved] wrt [m] (a register mid-save holds the wrong value),  *)
(* so a per-insert outside-in peel cannot work.  The correct view is the        *)
(* WRITE-LIST: only the OUTERMOST write to each register survives, so           *)
(* [callee_saved] holds iff every callee-saved register's outermost write (if   *)
(* any) restores its entry value.  Express the tower as [apply_writes ws m]     *)
(* (outermost first) and discharge one [Forall] whose 12 untouched registers    *)
(* are [None] (decided by [vm_compute] on the key list, values irrelevant) and  *)
(* whose few restored frame registers carry an explicit value obligation.       *)
Definition apply_writes (ws : list (mword 5 * mword 64)) (m : regfile)
  : regfile :=
  foldr (fun kv M => <[Regidx (fst kv) := snd kv]> M) m ws.

Fixpoint outer_write (c : mword 5) (ws : list (mword 5 * mword 64)) : option (mword 64) :=
  match ws with
  | [] => None
  | (k,v) :: ws' => if bool_decide (k = c) then Some v else outer_write c ws'
  end.

(* Reduce [outer_write] one step, keys only -- never forces the (heavy) values,
   so it is safe over a write-list built from a whole-function's register map. *)

Lemma outer_write_cons_eq (c k : mword 5) (v : mword 64) ws :
  k = c -> outer_write c ((k,v)::ws) = Some v.
Proof. intros ->. cbn [outer_write]. rewrite bool_decide_eq_true_2 by reflexivity. reflexivity. Qed.

(* A register whose index is not written at all has no outer write.  The premise
   [c ∉ map fst ws] is over the KEY list (values dropped by [map fst]), so it is
   discharged by [cbn [map fst]] + concrete membership -- again values-blind. *)

Lemma apply_writes_lookup (ws : list (mword 5 * mword 64)) m (c : mword 5) :
  (apply_writes ws m) !!! Regidx c
  = match outer_write c ws with Some v => v | None => m !!! Regidx c end.
Proof.
  induction ws as [|[k v] ws IH]; [reflexivity|].
  simpl. destruct (bool_decide (k = c)) eqn:Hkc.
  - apply bool_decide_eq_true in Hkc. subst k. by rewrite upd_eq.
  - apply bool_decide_eq_false in Hkc.
    rewrite upd_ne; [exact IH | congruence].
Qed.

Lemma callee_saved_apply_writes (m : regfile) ws :
  Forall (fun c => match outer_write (mword_of_int c : mword 5) ws with
                   | None => True
                   | Some v => v = m !!! Regidx (mword_of_int c : mword 5)
                   end)
         [2;4;8;9;18;19;20;21;22;23;24;25;26;27]%Z ->
  callee_saved m (apply_writes ws m).
Proof.
  intros HF. unfold callee_saved.
  assert (Hsp2 : (csp_rs1 : mword 5) = mword_of_int 2) by (vm_compute; reflexivity).
  repeat match goal with
         | H : Forall _ (_ :: _) |- _ => inversion H as [|? ? ? ?]; subst; clear H
         end.
  repeat split;
    rewrite ?Hsp2; rewrite apply_writes_lookup;
    match goal with
    | H : match outer_write ?c ws with _ => _ end |- _ =>
        destruct (outer_write c ws); [ exact H | reflexivity ]
    end.
Qed.

(* Discharging ONE [callee_saved m mF] conjunct for a register the function
   itself never writes, when [mF] is an insert tower over the map a CALLEE
   returned: strip the local tower down to that map, hop the callee's own
   [callee_saved], then strip the tower the prologue built.  Both strips are
   [reg_lookup] -- a cheap vm-cast, never bare conversion (see RegFile.v on the
   async-Qed hazard) -- and the register is a MISS in both towers, so no
   symbolic register value is ever reduced.

   This is the shape every whole-function proof needs whose save/restore of a
   frame register SPANS a call: mid-call that register holds the wrong value,
   so the fact does not factor through [callee_saved m mo] / [callee_saved mo
   mF] and each conjunct has to be discharged on its own. *)
Ltac cs_through Hcs base :=
  match goal with
  | |- _ !!! Regidx ?c = _ =>
      transitivity (base !!! Regidx c);
      [ reg_lookup
      | rewrite (callee_saved_lookup Hcs c ltac:(vm_compute; reflexivity)); reg_lookup ]
  end.
