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
(* the bi notations [⌜ ⌝] / [-∗] / [[∗ list]] that [kexec_closer] below is
   written in; this file used to be pure Prop and needed none of them *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import ProcGeom.
Require Import UserPtTree.      (* [ud_tfp] / [ud_root] *)
Require Import ProcInv.
Require Import ElfEnc.          (* [le_at] -- the entry field's reader *)
Require Import SpecKexec.       (* [kexec_ok] and its vocabulary       *)

(* ...and the vocabulary [kexec_closer] below needs.  Every one of these is
   already in this file's transitive cone through [SpecKexec]; naming them
   here only brings them into SCOPE. *)
Require Import Riscv.rv64d_types.  (* [Regidx]                          *)
Require Import RegFile.         (* [regfile]                            *)
Require Import RiscvPtsto.      (* the [↦₄]/[↦₈]/[↦ₘ] notations         *)
Require Import InstrBytes.      (* [pc_is]                              *)
Require Import IntrDefs.        (* [sie_cap_gpr], [trap_csrs_ext], ...  *)
Require Import CpuOwn.          (* [cpu_own]                            *)
Require Import WpNext.          (* [wp_next], [ret_pc]                  *)
Require Import CalleeSaved.     (* [callee_saved]                       *)
Require Import BioDefs.         (* [bslots]                             *)
Require Import IrefSlots.       (* [iref_slots]                         *)
Require Import BitmapInv.       (* [sb_bmapstart]                       *)
Require Import InodeInv.        (* [sb_inodestart]                      *)
Require Import KvmSpec.         (* [kalloc_env]                         *)
Require Import Xv6G.            (* [xv6G]                               *)
Require Import FdSlots.         (* [fdslotG]                            *)
Require Import FileInvDefs.     (* [fileG]                              *)
Require Import ProcAvail.       (* [pavG]                               *)

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
   (* ...and its fd-state ghost name -- see [SpecKexec.kexec_ok]'s note *)
   pv_fdg V' = pv_fdg V /\
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
(*  1a.  THE EXIT CONTINUATION THAT RELAYS IT, NAMED ONCE                  *)
(* ===================================================================== *)

(*  THE OTHER HALF OF THIS FILE'S OWN OPENING PARAGRAPH.  That paragraph
    says [kexec_ok] is spelled in thirty-one places "and every one of them
    is a phase lemma RELAYING kexec's own exit continuation" -- and then
    names the RELATION, leaving the CONTINUATION spelled out at all of
    them.  It is thirteen rows, ~800 printed characters, and a count over
    the cone finds THIRTY-NINE copies in twelve files (ProofKexecC x13,
    B3 x6, B x5, Pinned x4, Tail x4, A x3, SpecKexecB2 x3, SpecKexecB3 x3,
    Kexec x2, D x2, PinnedA x2, SpecKexecPinned x1), differing only in
    bound-variable names and in which of [b]/[eb] and [lks]/[emptyset] the
    caller passes.

    claude-notes/optimization.md, "Seal a whole-function proof's
    continuation" and the ProofSysUnlink case study beside it: an inline
    continuation is re-embedded in the term of EVERY proofmode step that
    carries it, so it is priced by |Delta| x steps, and in the kexec block
    lemmas it measures 35-44 % of the statement.  Naming it changes no
    proof script -- the constant is TRANSPARENT, so the [iApply ("Hcont"
    $! ...)] sites unify straight through.

    Kept TRANSPARENT for that reason, and NOT sealed: opacity would break
    the specialisations rather than help them.                            *)
Definition kexec_closer
    (* EXACTLY the classes the rows below need, which is the kexec
       contract's list MINUS [pavG]: [proc_priv] is [ProcInv]'s, and that
       section takes `{!riscvGS, !fileG, !xv6G, !bioslotG, !fdslotG,
       !irefslotG}; nothing here comes from [ProcAvail].

       BOTH EDGES OF THIS LIST BITE, and they fail in opposite ways.
       Carrying [pavG] when no row needs it makes it an unresolvable evar
       at every call site whose context does not already fix it --
       "Could not find an instance for ProcAvail.pavG" in ProofKexecD, and
       an UNDEFINED EVARS on a whole statement in ProofKexecC.  Dropping a
       class a row DOES need ([fileG]/[fdslotG], via [proc_priv]) is far
       worse: it does not error, it DIVERGES -- resolution goes hunting
       through the gFunctors instances and this file alone reached 300 GB
       before it was killed.  A missing class is not a clean failure here;
       cap the memory when experimenting with this binder list. *)
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Q : mword 64 -> Prop)
    (gf ga : gname) (pj : mword 64) (pidv : mword 32) (V : pprivate)
    (m : regfile) (ret_tgt : mword 64) (K : nat) (b eb : bool)
    (lks : gset string) (dqb dqs : dfrac) (bmapstart inodestart : Z)
    (na : nat) (alen : nat -> nat)
    (plen : nat) (pv : mword 64) (dqpv : dfrac) (pfun : nat -> bv 8)
    (av : mword 64) (dqa : dfrac) (avf : nat -> mword 64)
    (aslen : nat -> nat) (dqas : dfrac) (afun : nat -> nat -> bv 8)
    : iProp Σ :=
  (∀ (mf : regfile) (V' : pprivate) (entry spv szv' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      ⌜kexec_ok_q Q V V' (mf !!! Regidx (mword_of_int 10 : mword 5))
                  entry spv szv' na alen⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      kalloc_env ga None -∗
      proc_priv gf pj pidv V' -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
      ([∗ list] i ∈ seq 0 na,
         [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
      bslots 3 -∗
      iref_slots 2 -∗
      WP (Loop : expr riscv_lang))%I.

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
