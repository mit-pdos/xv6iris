(* ====================================================================== *)
(* CtxIdDefs.v -- THE CONTEXT IDENTITY, AND THE AMBIENT CLASS THAT        *)
(* NAMES ONE.                                                             *)
(*                                                                        *)
(* [CtxId] and [CurCtx] alone, over nothing but [gname] and stdpp's        *)
(* decidability classes.  They are the VOCABULARY every file that merely   *)
(* binds a context writes its statements in -- [Context `{XI : CurCtx}] -- *)
(* and that is nearly every S-mode leaf and WP file in the tree.           *)
(*                                                                        *)
(* THEY LIVED IN [TsoCtx.v], WHICH IS THE REASON THIS FILE EXISTS.  That   *)
(* file is the context KIT: the tokens, the domination relation, the       *)
(* morphism class and the transports -- 313 declarations, and one of the   *)
(* heaviest nodes on the build's critical path.  A file that only needs to *)
(* say "there is an ambient context" had to import the whole kit to say    *)
(* it.  See claude-notes/design/code-organization.md, “a lemma belongs at  *)
(* the altitude of what it says”.                                         *)
(*                                                                        *)
(* [TsoCtx.v] RE-EXPORTS this file, so every existing importer sees these  *)
(* names exactly where it saw them before; a file that needs nothing but   *)
(* the identity should require THIS one instead.                          *)
(* ====================================================================== *)
From stdpp Require Import base countable.
From transfinite.base_logic.lib Require Import own.   (* [gname] *)

(* TWO GNAMES, BOTH THE CONTEXT'S OWN ([TsoCtxTwin2.CtxId] is the same
   record): the BOUND authority (one monotone nat -- clean facts'
   justification) and the DIRTY-SET authority (a ghost map keyed by
   (timestamp, byte)).  The identity carrying its own ghost names is
   what lets a token -- and hence every authority -- be minted wherever
   the identity can, with no global roster: the corrected construction's
   cornerstone. *)
Record CtxId := MkCtxId { ctx_bound_name : gname; ctx_dirty_name : gname }.
From xv6iris Require Import StepIndex.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
(* INHABITED IS LOAD-BEARING, not decoration: a [CtxId] existentially bound
   inside a ▷-guarded record (the parked context, SwtchCtx.valid_context_pre)
   can only have its later pushed inward by [bi.later_exist], which HOLDS
   ONLY OVER AN INHABITED DOMAIN.  Without this instance the resumer cannot
   open the record it is about to run. *)
Global Instance ctx_id_inhabited : Inhabited CtxId :=
  populate (MkCtxId inhabitant inhabitant).

Global Instance ctx_id_countable : Countable CtxId.
Proof.
  apply (inj_countable' (λ ξ, (ctx_bound_name ξ, ctx_dirty_name ξ))
           (λ p, MkCtxId p.1 p.2)).
  by intros [].
Qed.

(* Ambient, and -- unlike [CurKtier] -- WITHOUT a default instance; see
   [TsoCtx.v]'s header, ruling 1. *)
Class CurCtx := cur_ctx : CtxId.

(* The class TYPE is transparent to typeclass unification: [CurCtx] is
   definitionally [CtxId], and instance search must see through the
   wrapper's binder type or every [Persistent (is_lock … <{P}>)] /
   [CtxMorph <{P}>] resolution dies at the (CurCtx → iProp) vs
   (CtxId → iProp) seam.  This transparency is about the TYPE only; which
   ambient [CurCtx] INSTANCE a term picks up is unaffected (the
   silent-drop hazard in tso-port.md §2d concerns instance selection, not
   type unfolding). *)
Global Typeclasses Transparent CurCtx.
