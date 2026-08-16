(* HartGoodb.v -- the bridge from the DECODE CATALOGUE's certificate to the
   [swp] layer's footprinted characterization.

   THE PROBLEM THIS SOLVES.  [HartMRun.swp_run_hart_active_base]/[_rvc] want
   the decode as a footprinted fact ([hval], or [hfrun] at some fuel); the
   [instr] bundle -- and the 3752 generated [kd_] lemmas under it -- supply
   it as [exec (decode_fetch r) σ = Some (i, σ)].  A general [exec] ->
   footprint bridge looks circular: to know a footprinted walker will not
   REFUSE, you need "reads only [D], touches no memory", which is exactly
   what the footprinted walker exists to decide.

   THE HYPOTHESIS IS ALREADY IN THE TREE.  [WpDecodeBridge.goodb Db m s] is
   a COMPUTABLE certificate of precisely that: [Ret] passes, a [RegRead r]
   passes iff [Db r], the silent classes pass, and EVERYTHING ELSE -- memory,
   [Choose], failures, and REGISTER WRITES -- is [false].  Every generated
   decode proof already establishes it by [vm_compute], because
   [decode_state_bridge] consumes it.

   So [goodb] and [hfrun] are the same structural walk, and this file is the
   induction that says so.  Two consequences fall out of [goodb] rejecting
   writes: the walk cannot change the register file, so the post-file is the
   pre-file; and [exec] is guaranteed to succeed, so no [exec] hypothesis is
   needed -- the value is produced, not assumed. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import HartSpan HartSpanChar WpDecodeBridge.
Local Open Scope Z_scope.

(* ONE induction, producing the walker's answer AND [exec]'s together. *)
Lemma hfrun_of_goodb {X : Type} (Db : register -> bool) (D Drw : gset register)
    (m : M X) (s : mstate) :
  (forall r : register, Db r = true -> r ∈ D) ->
  goodb Db m s = true ->
  exists (n : nat) (x : X),
    hfrun n D Drw s.(sregs) m = Some (x, s.(sregs)) /\ exec m s = Some (x, s).
Proof.
  intros HD. revert m.
  fix IH 1. intros m Hg.
  destruct m as [y | T oc k].
  - exists 1%nat, y. split; reflexivity.
  - destruct oc; simpl in Hg; try discriminate Hg.
    + (* RegRead: goodb pins the register inside Db, hence inside D *)
      apply andb_prop in Hg as [Hr Hk].
      destruct (IH _ Hk) as (n & x & Hf & He).
      exists (S n), x. split.
      * simpl. rewrite (bool_decide_eq_true_2 _ (HD _ Hr)). exact Hf.
      * simpl. exact He.
    + (* InstrAnnounce *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* BranchAnnounce *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* Barrier *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* CacheOp *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* TlbOp *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* TakeException *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* ReturnException *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* TranslationStart *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* TranslationEnd *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* GetCycleCount *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* CycleCount *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
    + (* Message *)
      destruct (IH _ Hg) as (n & x & Hf & He).
      exists (S n), x. split; [exact Hf | exact He].
Qed.


(* [goodb] transports across a file that agrees on [Db] -- the same induction
   again, and the reason the reference-state trick works at all. *)
Lemma goodb_congr {X : Type} (Db : register -> bool) (m : M X) (s1 s2 : mstate) :
  (forall r : register, Db r = true ->
     register_lookup r s1.(sregs) = register_lookup r s2.(sregs)) ->
  goodb Db m s1 = true -> goodb Db m s2 = true.
Proof.
  intros Hag. revert m.
  fix IH 1. intros m Hg.
  destruct m as [y | T oc k]; [reflexivity|].
  destruct oc; simpl in Hg |- *; try discriminate Hg.
  - apply andb_prop in Hg as [Hr Hk].
    rewrite Hr. simpl. rewrite <- (Hag _ Hr). exact (IH _ Hk).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
  - exact (IH _ Hg).
Qed.

(* ====================================================================== *)
(* THE BRIDGE the [instr] bundle uses.                                     *)
(*                                                                        *)
(* [hval] rather than [hfrun]: it is FUEL-FREE, so no fuel reaches the     *)
(* proof interface, and [swp_span] consumes it directly.  The post-file is *)
(* the pre-file because [goodb] rejects register writes.                   *)
(* ====================================================================== *)
Lemma hval_of_goodb {X : Type} (Db : register -> bool) (D Drw : gset register)
    (m : M X) (dst : mstate) (rs : regstate) (x : X) :
  (forall r : register, Db r = true -> r ∈ D) ->
  (forall r : register, Db r = true ->
     register_lookup r rs = register_lookup r dst.(sregs)) ->
  goodb Db m dst = true ->
  exec m dst = Some (x, dst) ->
  hval D Drw rs m x rs.
Proof.
  intros HD Hag Hg He.
  assert (Hag2 : forall r, Db r = true ->
            register_lookup r dst.(sregs)
            = register_lookup r (MState rs dst.(mem) dst.(mdev)).(sregs))
    by (intros r Hr; symmetry; exact (Hag r Hr)).
  assert (Hg2 : goodb Db m (MState rs dst.(mem) dst.(mdev)) = true)
    by exact (goodb_congr Db m dst _ Hag2 Hg).
  destruct (hfrun_of_goodb Db D Drw m (MState rs dst.(mem) dst.(mdev)) HD Hg2)
    as (n & x' & Hf & He2).
  destruct (exec_goodb_congr Db m dst (MState rs dst.(mem) dst.(mdev)) Hag2 Hg)
    as (x'' & Hd & Hs).
  rewrite He in Hd. injection Hd as <-.
  rewrite He2 in Hs. injection Hs as Hxx.
  rewrite Hxx in Hf.
  exact (hfrun_hval n D Drw rs m x rs Hf).
Qed.
