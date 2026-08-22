(* ====================================================================== *)
(* FsWf.v -- [fs_durable_wf]: THE well-formedness invariant of the durable *)
(* committed view (claude-notes/design/crash.md, "The split crash           *)
(* predicate"; worklist stage F1).                                          *)
(*                                                                          *)
(* The property every reachable committed state has and every commit        *)
(* preserves; [fs.img] is merely the base case of the poweroff/poweron      *)
(* loop invariant.  It rides [FsCrash.fs_rec_wf] as the [P_wf] conjunct     *)
(* and is what the era's boot mint will read its image facts from           *)
(* (stage H).                                                               *)
(*                                                                          *)
(* THE BODY IS A PLACEHOLDER ([True]) until stage F1 lands the general      *)
(* content sweeps (fsimg_wf minus log-cleanliness, W9 at reachable-dir      *)
(* tickets -- see the worklist for the pinned form).  The INTERFACE is      *)
(* final now so the crash layer's permits are stated against it.            *)
(* ====================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.

Local Open Scope Z_scope.

Definition fs_durable_wf (D : gmap Z (list (bv 8))) : Prop := True.

(* THE GATE (delete together with the placeholder body).  Every use of this
   lemma marks a site that may NOT survive stage F1's real body:
     - the recovery-side permits' RE-BASE of [fr_D] (stage H makes them
       ghost no-ops first);
     - the commit permit's compat wrapper (stage G supplies the real
       preservation fupd);
     - [P_fs_alloc]'s establishment (stage E4 discharges it at the image
       via [fsimg_wf -> fs_durable_wf]).
   When F1 replaces the body, this lemma becomes unprovable and each use
   site surfaces as an error -- that is the mechanism, not an accident. *)
Lemma fs_durable_wf_placeholder (D : gmap Z (list (bv 8))) : fs_durable_wf D.
Proof. exact I. Qed.
