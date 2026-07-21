(* RegFile.v -- the register file as a total function [regidx -> mword 64].

   This replaces the old [gmap regidx (mword 64)] register-map representation.
   The point is proof-level lookup speed: [M !!! Regidx j] over a deep chain of
   updates is decided by [reg_lookup] (ONE [vm_compute] over the concrete-key
   if-chain) instead of O(depth) ssreflect [rewrite lookup_total_*] peels.
   Measured: one funnel's 9 register lookups over a 20-deep chain drop from
   ~1.2 s (gmap peel) to ~0.04 s (~30x).  [reg_lookup] is SAFE on symbolic
   register values (iota discards the unselected [then]-branches, so a miss
   bottoms out at [base j] without ever reducing e.g. [add_vec p …]).

   [Insert]/[LookupTotal] instances keep the stdpp map syntax [<[k:=v]> f] and
   [f !!! k] UNCHANGED, so porting a proof is mostly a type-annotation swap
   ([gmap regidx (mword 64)] -> [regfile]) plus [peel_reg] -> [reg_lookup].

   [rf_upd] is kept TRANSPARENT (see the note there): that is what makes
   [reg_lookup] a single fast [vm_compute].  The ONE cost — a whole-function
   proof's async [Qed] re-reducing a deep tower when a [callee_saved] conjunct
   was closed by bare [reflexivity]/conversion (pathological, ~9 min) — is
   avoided by discharging every such conjunct with [reg_lookup] (a vm-cast proof
   term is cheap for the kernel to re-check), NEVER [repeat split]/[reflexivity].

   [gpr_file]/[sie_cap]/[callee_saved] fold over [rf_to_gmap f] (a bridge to a
   [gmap] via [Finite regidx]) so the existing [big_sepM_*] interface is reused.

   Uses functional extensionality (for [upd_upd]); accepted. *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import gmap finite bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Local Open Scope Z_scope.

(* ================================================================== *)
(*  The representation and its drop-in map syntax.                     *)
(* ================================================================== *)
Definition regfile := regidx -> mword 64.

(* [rf_upd] is TRANSPARENT: [reg_lookup] then resolves a lookup with ONE
   [vm_compute] over the concrete-key if-chain, and — crucially — it stays SAFE
   on symbolic register values (e.g. [add_vec p …]): iota-reduction of the
   if-chain discards the unselected [then]-branches without reducing them, so a
   miss bottoms out at [base j] and a symbolic value is never fed to modular
   [add_vec] (which would not terminate).  The one hazard a transparent [rf_upd]
   introduces — the async [Qed] re-reducing a deep tower when a [callee_saved]
   conjunct was closed by bare [reflexivity]/conversion — is avoided by
   discharging every such conjunct with [reg_lookup] (a vm-cast proof term is
   cheap to re-check), NOT [repeat split]/[reflexivity]. *)
Definition rf_upd (f : regfile) (k : regidx) (v : mword 64) : regfile :=
  fun j => if bool_decide (j = k) then v else f j.

Global Instance regfile_insert : Insert regidx (mword 64) regfile :=
  fun k v f => rf_upd f k v.
Global Instance regfile_lookup_total : LookupTotal regidx (mword 64) regfile :=
  fun k f => f k.

Lemma rf_lookup (f : regfile) (k : regidx) : f !!! k = f k.
Proof. reflexivity. Qed.

Lemma upd_eq (f : regfile) (k : regidx) (v : mword 64) : (<[k := v]> f) !!! k = v.
Proof.
  unfold lookup_total, regfile_lookup_total, insert, regfile_insert, rf_upd.
  rewrite bool_decide_eq_true_2 //. Qed.

Lemma upd_ne (f : regfile) (k j : regidx) (v : mword 64) :
  j <> k -> (<[k := v]> f) !!! j = f !!! j.
Proof.
  intros. unfold lookup_total, regfile_lookup_total, insert, regfile_insert, rf_upd.
  rewrite bool_decide_eq_false_2 //. Qed.

(* [insert_insert] analogue (funext) *)
Lemma upd_upd (f : regfile) (k : regidx) (a b : mword 64) :
  <[k := a]> (<[k := b]> f) = <[k := a]> f.
Proof.
  apply functional_extensionality; intro j.
  unfold insert, regfile_insert, rf_upd. by destruct (bool_decide (j = k)). Qed.

(* ================================================================== *)
(*  Finite regidx  (from Finite (bv 5) via the Regidx bijection).      *)
(* ================================================================== *)
Global Program Instance regidx_finite : Finite regidx :=
  {| enum := Regidx <$> enum (bv 5) |}.
Next Obligation.
  apply NoDup_fmap_2; [intros ?? [=]; congruence | apply NoDup_enum].
Qed.
Next Obligation.
  intros [b]. apply elem_of_list_fmap. exists b. split; [done | apply elem_of_enum].
Qed.

(* ================================================================== *)
(*  Bridge to a gmap so the existing big_sepM interface still works.   *)
(* ================================================================== *)
Definition rf_to_gmap (f : regfile) : gmap regidx (mword 64) :=
  list_to_map ((fun r => (r, f r)) <$> enum regidx).

Lemma rf_to_gmap_lookup (f : regfile) (r : regidx) : rf_to_gmap f !! r = Some (f r).
Proof.
  unfold rf_to_gmap. apply elem_of_list_to_map_1.
  - rewrite -list_fmap_compose. apply NoDup_fmap_2_strong; [| apply NoDup_enum].
    intros x y ?? [=]; done.
  - apply elem_of_list_fmap. exists r. split; [done | apply elem_of_enum].
Qed.

Lemma rf_to_gmap_dom (f : regfile) (r : regidx) : r ∈ dom (rf_to_gmap f).
Proof. apply elem_of_dom. rewrite rf_to_gmap_lookup. eauto. Qed.

Lemma rf_to_gmap_upd (f : regfile) (k : regidx) (v : mword 64) :
  rf_to_gmap (<[k := v]> f) = <[k := v]> (rf_to_gmap f).
Proof.
  apply map_eq; intro j. rewrite rf_to_gmap_lookup.
  destruct (decide (j = k)) as [->|Hne].
  - rewrite lookup_insert. f_equal. apply upd_eq.
  - rewrite lookup_insert_ne // rf_to_gmap_lookup. f_equal. by apply upd_ne.
Qed.

(* ================================================================== *)
(*  reg_lookup : the peel_reg replacement.  ONE [vm_compute] over the  *)
(*  concrete-key if-chain: it unfolds the [set]-chain of local map     *)
(*  defs (zeta), reduces [rf_upd]'s [bool_decide]s, and iota-selects — *)
(*  discarding unselected [then]-branches, so symbolic values (a miss  *)
(*  bottoms out at [base j]) are never reduced.  Use it to discharge   *)
(*  [callee_saved]/lookup side goals instead of [reflexivity], both to *)
(*  peel fast AND to keep the proof term a cheap-to-recheck vm-cast    *)
(*  (bare conversion over the tower blows up the async [Qed]).         *)
(* ================================================================== *)
Ltac reg_lookup :=
  rewrite ?rf_lookup; vm_compute; reflexivity.
