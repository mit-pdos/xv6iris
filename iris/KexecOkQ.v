(* ===================================================================== *)
(*  KexecOkQ.v -- kexec's RESULT RELATION, GENERIC IN THE ENTRY POINT     *)
(*  (claude-notes/projects/namei-pinned-lookup.md §13.3)                  *)
(* ===================================================================== *)

(*  WHY THIS EXISTS.  [SpecKexec.kexec_ok] is spelled in thirty-one places
    across the kexec cone, and every one of them is a phase lemma RELAYING
    kexec's own exit continuation:

      wp_next true pj (fun CID => ∀ mf V' entry spv szv',
         ⌜callee_saved m mf⌝ -∗ ⌜kexec_ok V V' (mf!!!a0) entry spv szv' ..⌝
         -∗ .. -∗ WP Loop)

    A client that wants to SAY something about [entry] cannot weaken its own
    strengthened continuation into that shape: the missing side is a pure
    fact about a universally quantified [entry], and no resource the exit
    hands over determines it.  So the strengthening cannot be threaded
    through one landed relay -- it has to be threaded through all of them,
    and the cheap way to do that is to punch a hole in the relation once
    and pass the plug down.  This is the eb-generic sweep's shape exactly
    (claude-notes/completed/eb-generic-sweep.md), on the exit relation
    rather than on the interrupt index.

    THE HOLE IS IN THE SUCCESS ARM ONLY, and that is what makes the sweep
    free: [kexec_ok]'s FAILURE arm does not mention [entry] at all, so all
    eight of kexec's [bad:] tails prove [kexec_ok_q Q] with the SAME proof
    term they proved [kexec_ok] with, at every [Q].  The one site that has
    to pay is the commit block's [ld a4,-408(s0)] -- and it pays with the
    premise [Q (kxq_entry ef)], which is a fact about the ELF header the
    walk read, i.e. exactly the fact the pinned walk brings.

    [SpecKexec.v] IS UNTOUCHED: [kexec_ok] stays what it is and
    [kexec_ok_q_True] below is the row that keeps [wp_kexec_sconf] the
    theorem it has always been -- the cone is instantiated at
    [Q := fun _ => True] and the two relations are then equivalent.       *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import ProcGeom.
Require Import UserPtTree.      (* [ud_tfp] / [ud_root] *)
Require Import ProcInv.
Require Import ElfEnc.          (* [le_at] -- the entry field's reader *)
Require Import SpecKexec.       (* [kexec_ok] and its vocabulary       *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE RELATION WITH THE HOLE                                        *)
(* ===================================================================== *)

(*  [SpecKexec.kexec_ok] verbatim, with one conjunct [Q entry] added at the
    FRONT of the success arm.  The failure arm is character-for-character
    the landed one.                                                       *)
Definition kexec_ok_q (Q : mword 64 -> Prop) (V V' : pprivate) (r : mword 64)
    (entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) : Prop :=
  (* FAILED: nothing moved -- and, in particular, nothing is claimed about
     [entry], which is why every [bad:] tail is generic for free. *)
  (r = (mword_of_int (-1) : mword 64) /\ V' = V)
  \/
  (* SUCCEEDED: the landed arm, plus the caller's claim on the entry PC. *)
  (Q entry /\
   r = (mword_of_int (Z.of_nat na) : mword 64) /\
   (na <= MAXARG)%nat /\
   kxc_stack_ok (uint szv') (uint szv' - 4096) alen na /\
   pv_sz V' = szv' /\
   spv = (mword_of_int (kxc_sp_final (uint szv') alen na) : mword 64) /\
   ud_tfp (pv_upt V') = ud_tfp (pv_upt V) /\
   kxc_tf (pv_tf V) (pv_tf V') entry spv /\
   pv_ofile V' = pv_ofile V /\
   pv_cwd V' = pv_cwd V /\
   length (pv_name V') = PNAMELEN /\
   (uint szv' - 4096 <= uint spv)%Z /\
   (uint spv <= uint szv')%Z).

(* THE ROW THAT KEEPS [SpecKexec.wp_kexec_sconf] WHAT IT IS: the landed
   relation IS the vacuous instance. *)
Lemma kexec_ok_q_True (V V' : pprivate) (r entry spv szv' : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok_q (fun _ => True) V V' r entry spv szv' na alen
  <-> kexec_ok V V' r entry spv szv' na alen.
Proof.
  unfold kexec_ok_q, kexec_ok. split.
  - intros [Hl | (_ & H)]; [by left | by right].
  - intros [Hl | H]; [by left | right; split; [exact I | exact H]].
Qed.

(* ...and its two one-way readings, which is what the [iApply]s use. *)
Lemma kexec_ok_q_weaken (Q : mword 64 -> Prop)
    (V V' : pprivate) (r entry spv szv' : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok_q Q V V' r entry spv szv' na alen ->
  kexec_ok V V' r entry spv szv' na alen.
Proof. intros [Hl | (_ & H)]; unfold kexec_ok; [by left | by right]. Qed.

Lemma kexec_ok_q_of_True (V V' : pprivate) (r entry spv szv' : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok V V' r entry spv szv' na alen ->
  kexec_ok_q (fun _ => True) V V' r entry spv szv' na alen.
Proof. intro H. by apply kexec_ok_q_True. Qed.

(* ===================================================================== *)
(*  2.  THE ONE VALUE THE HOLE IS EVER PLUGGED WITH                       *)
(* ===================================================================== *)

(*  The word the commit block loads at +0x2f0 ([ld a4,-408(s0)], byte 24 of
    the frame's [struct elfhdr]) and stores into [trapframe->epc] --
    spelled here EXACTLY as [ProofKexecD.kxd_commit] produces it, so its
    [Q entry] obligation is discharged by [assumption] from the premise
    [Q (kxq_entry ef)].  It is [ElfEnc.eh_entry] at the 64-bit width.     *)
Definition kxq_entry (ef : nat -> bv 8) : mword 64 :=
  (Z_to_bv 64 (le_at ef 24 8) : mword 64).

(*  [le_at] reads eight bytes from offset 24, so two headers that agree
    below 64 give the same entry point.  This is the whole of what the
    pinned walk has to prove at the commit. *)
Lemma kxq_entry_ext (ef ef' : nat -> bv 8) :
  (forall j : nat, (j < 64)%nat -> ef j = ef' j) ->
  kxq_entry ef = kxq_entry ef'.
Proof.
  intro Hj. unfold kxq_entry, le_at. do 2 f_equal.
  apply map_ext_in. intros x Hx. apply in_seq in Hx. apply Hj. lia.
Qed.

(* ===================================================================== *)
(*  3.  THE HEADER CLAIM THE WALK CARRIES ACROSS THE +0x090 SEAM          *)
(* ===================================================================== *)

(*  Phase A reads [struct elfhdr elf] and phase B reads two fields out of
    it; between them sits the +0x090 seam, which the landed walk crosses
    with the buffer as existential [stack_own].  [ProofKexecTail.kxc_frameA6x]
    carries it NAMED instead, and this is the claim that rides beside the
    name: NOTHING at all for the landed instantiation, and "these are
    /init's first 64 bytes" for the pinned one.  An option rather than a
    predicate because the landed side must not have to prove anything.    *)
Definition kxq_hdr_ok (HD : option (nat -> bv 8)) (ef : nat -> bv 8) : Prop :=
  match HD with
  | None => True
  | Some h => forall j : nat, (j < 64)%nat -> ef j = h j
  end.

Lemma kxq_hdr_ok_none (ef : nat -> bv 8) : kxq_hdr_ok None ef.
Proof. exact I. Qed.

(* transport along agreement below 64 -- what phase A's readi gives it *)
Lemma kxq_hdr_ok_ext (HD : option (nat -> bv 8)) (ef ef' : nat -> bv 8) :
  (forall j : nat, (j < 64)%nat -> ef j = ef' j) ->
  kxq_hdr_ok HD ef' -> kxq_hdr_ok HD ef.
Proof.
  intros Hj. destruct HD as [h |]; [| by intros _]. cbn.
  intros Hh j Hlt. rewrite (Hj j Hlt). exact (Hh j Hlt).
Qed.

(* ...and what the commit block's obligation reduces to under it *)
Lemma kxq_entry_of_hdr (h ef : nat -> bv 8) :
  kxq_hdr_ok (Some h) ef -> kxq_entry ef = kxq_entry h.
Proof. intro H. by apply kxq_entry_ext. Qed.
