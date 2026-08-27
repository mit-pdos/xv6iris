(*  ProbeR1a.v -- STAGE 0 of lane R1a ("de-thread the ambient names").

    NOT in [_CoqProject]; nothing builds it.  Compile it by hand against a
    built tree:

      rocq compile -q -R . xv6iris -R ../model-xv6iris Riscv \
        -R ../kernel-rocq Kernel -R ../user-rocq User ProbeR1a.v

    It answers the one question the whole rank rests on, at the EXACT
    instance environment of a group-B file ([SpecNamex.v]:440-441, which
    binds [!fileG Σ] AND a standalone [ICFG : icfg], holds
    [inode_held (pv_cwd Vpr)] at :345 and states [dev = icfg_dev] at :473):

      (i)  does a proposition that mixes an [fscfg]-resource (reached only
           through [file_fscfg]) with an [icfg]-resource (reachable through
           BOTH [file_icfg] and the standalone [ICFG]) fail to meet the
           SAME proposition written by an ambient-only (group-A) file?
      (ii) does dropping the standalone [ICFG] cure it, framing and all,
           and does a [Module Type] / [Module ... : T] pair then seal?

    The predicted answers are yes and yes; everything below that is marked
    [Fail] is an ASSERTION that the failure happens, so this file compiling
    is the probe passing.  Each [Fail] has a CONTROL beside it in the cured
    section -- the same tactic on the same text, succeeding -- so a [Fail]
    that passed for an unrelated reason would show up as its control also
    failing.

    ---- THE MEASURED WITNESS (Set Printing All on the two definitions) ---

    The one difference, and it is the whole rank:

      amb_pre := ... (@inode_held Σ _ _ _ (@file_icfg Σ fileG0) v)
                 ... (@icfg_dev (@file_icfg Σ fileG0)) ...
      loc_pre := ... (@inode_held Σ _ _ _ ICFG v)
                 ... (@icfg_dev ICFG) ...

    -- the [fsc_ic] conjunct is [@fsc_ic (@file_fscfg Σ fileG0)] in BOTH,
    because [fscfg] has only one path.  So the standalone [ICFG] wins
    resolution for the [icfg] half while [fileG] necessarily wins for the
    [fscfg] half, and the two halves of one proposition end up at
    unrelated records.  The proofmode's report is
    [Tactic failure: iFrame: cannot frame (inode_held v)].               *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var mono_nat ghost_map.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.
Require Import BioInv.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import InodeInv.        (* [ROOTDEV] *)
Require Import IcacheEscrow.    (* [ic_tok], [ic_names] *)
Require Import IcacheRef.       (* [icfg], [inode_held] *)
Require Import FsCfg.           (* [fscfg], [fsc_ic] *)
Require Import FileInvDefs.     (* [fileG] = capacity + [icfg] + [fscfg] *)
Require Import Xv6G.
Local Open Scope Z_scope.

Notation ROOTDEV := InodeInv.ROOTDEV.

(* ===================================================================== *)
(*  0.  THE DE-THREADED (GROUP-A) SIDE                                    *)
(*                                                                        *)
(*  What a contract looks like AFTER stage 1: no [cn] parameter, no       *)
(*  [dev] parameter, no tie premise -- [fsc_ic] and [icfg_dev] are read   *)
(*  off the ambient records.  There is exactly ONE instance path to each  *)
(*  here, because the only config in the binder group is [fileG]'s.       *)
(* ===================================================================== *)
Section Ambient.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Definition amb_pre (v : mword 64) : iProp Σ :=
    (ic_tok fsc_ic 0 ∗ inode_held v ∗ ⌜icfg_dev = ROOTDEV⌝)%I.
End Ambient.

(* ===================================================================== *)
(*  (i)  THE FAILURE, at SpecNamex.v's binder group                       *)
(* ===================================================================== *)
Section ProbeFail.
  (* VERBATIM SpecNamex.v:440-441. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* The SAME text as [amb_pre], written inside the group-B file.  It is
     NOT the same proposition: [fsc_ic] can only come from [file_fscfg],
     while [inode_held] and [icfg_dev] resolve to the standalone [ICFG]. *)
  Definition loc_pre (v : mword 64) : iProp Σ :=
    (ic_tok fsc_ic 0 ∗ inode_held v ∗ ⌜icfg_dev = ROOTDEV⌝)%I.

  (* --- (i.a) they are not even convertible --- *)
  Lemma probe_i_not_convertible v : loc_pre v ⊢ amb_pre v.
  Proof. rewrite /loc_pre /amb_pre. Fail reflexivity. Abort.

  (* --- (i.b) the proofmode symptom: [iFrame] leaves the goal --- *)
  Lemma probe_i_no_frame v : loc_pre v -∗ amb_pre v.
  Proof.
    rewrite /loc_pre /amb_pre. iIntros "H".
    (* the [inode_held] conjunct is at a different [icfg]; framing the
       hypothesis wholesale cannot close the goal *)
    Fail iFrame "H".
    (* and neither does the surgical form *)
    iDestruct "H" as "(Htok & Hheld & %Hdev)".
    iFrame "Htok". Fail iFrame "Hheld".
  Abort.

  (* --- (i.c) the [iSpecialize] symptom the SpecCreate.v:443-454 note
         predicts: a wand asking for the AMBIENT precondition cannot be
         fed the file's own. --- *)
  Lemma probe_i_no_specialize v (Q : iProp Σ) :
    (amb_pre v -∗ Q) -∗ loc_pre v -∗ Q.
  Proof.
    iIntros "HQ H". rewrite /loc_pre /amb_pre.
    Fail iApply ("HQ" with "H").
    Fail iSpecialize ("HQ" with "H").
  Abort.
End ProbeFail.

(* --- (i.d) THE SEALED FORM: statable, and unprovable.  This is the
       shape a [Module Type] gives the lemma -- the two configs quantified
       INDEPENDENTLY -- and it is why the hazard is fatal rather than
       merely annoying: the sealer must supply the statement with [ICFG]
       and [file_icfg fileG0] unrelated. --- *)
Lemma probe_i_sealed_shape :
  forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
           ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} (v : mword 64),
    (ic_tok fsc_ic 0 ∗ inode_held v ∗ ⌜icfg_dev = ROOTDEV⌝)%I ⊢ amb_pre v.
Proof.
  intros. rewrite /amb_pre.
  Fail reflexivity.
  iIntros "(Htok & Hheld & %Hdev)". iFrame "Htok". Fail iFrame "Hheld".
Abort.

(* ===================================================================== *)
(*  (ii)  THE CURE: drop the standalone [ICFG]                            *)
(* ===================================================================== *)
Section ProbeCure.
  (* SpecNamex.v:440-441 MINUS [ICFG : icfg]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Definition cured_pre (v : mword 64) : iProp Σ :=
    (ic_tok fsc_ic 0 ∗ inode_held v ∗ ⌜icfg_dev = ROOTDEV⌝)%I.

  (* --- (ii.a) now it is literally the same proposition --- *)
  Lemma probe_ii_convertible v : cured_pre v ⊢ amb_pre v.
  Proof. rewrite /cured_pre /amb_pre. reflexivity. Qed.

  (* --- (ii.b) framing goes through, wholesale --- *)
  Lemma probe_ii_frame v : cured_pre v -∗ amb_pre v.
  Proof. rewrite /cured_pre /amb_pre. iIntros "H". iFrame "H". Qed.

  (* --- (ii.c) and so does [iSpecialize] against a wand stated at the
         ambient precondition --- *)
  Lemma probe_ii_specialize v (Q : iProp Σ) :
    (amb_pre v -∗ Q) -∗ cured_pre v -∗ Q.
  Proof.
    iIntros "HQ H". rewrite /cured_pre /amb_pre.
    iSpecialize ("HQ" with "H"). iApply "HQ".
  Qed.
End ProbeCure.

(* ===================================================================== *)
(*  (ii.d)  AND THE SEAL.  A toy [Module Type] / [Module ... : T] pair    *)
(*  in exactly the tree's [SpecF]/[LinkF] shape: the Parameter's binder   *)
(*  group is the cured one, so the functor's statement and the proof's    *)
(*  statement are the same proposition and the ascription checks.         *)
(* ===================================================================== *)
Module Type TOY_CURED.
  Parameter toy_walk :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (v : mword 64) (Q : iProp Σ),
      (amb_pre v -∗ Q) -∗ cured_pre v -∗ Q.
End TOY_CURED.

Module ToyCuredProof : TOY_CURED.
  Lemma toy_walk :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (v : mword 64) (Q : iProp Σ),
      (amb_pre v -∗ Q) -∗ cured_pre v -∗ Q.
  Proof. intros. apply probe_ii_specialize. Qed.
End ToyCuredProof.

(* A consumer of the SEALED interface, at the cured binder group: the
   functor's conclusion is usable, which is the property the real
   [Link*.v] files need. *)
Module ToyClient (T : TOY_CURED).
  Section Client.
    Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
              !irefslotG Σ, !pavG Σ}.
    Context `{GEN : GenId}.
    Lemma toy_client v : cured_pre v -∗ amb_pre v.
    Proof. iIntros "H". iApply (T.toy_walk v with "[] H"). auto. Qed.
  End Client.
End ToyClient.

Module ToyClientInst := ToyClient ToyCuredProof.

(*  ---- WHAT THIS FILE ESTABLISHES ------------------------------------
    (i)  A group-B binder group (fileG + standalone ICFG) makes a
         de-threaded contract's precondition UNREACHABLE: not convertible,
         not framable, not specializable -- and the [Module Type] shape of
         the same statement is unprovable while perfectly statable.
    (ii) Deleting the standalone [ICFG] is the whole cure: the two
         propositions become the same term, [iFrame]/[iSpecialize] go
         through, and a sealed functor pair type-checks and is usable by a
         client at the same binder group.
    The rank-1 RULE follows: a sealed file has exactly ONE instance path
    to each config -- [fileG] alone, or an explicit [ICFG] + [FSC] pair
    with no [fileG].

    ---- (iii) THE Link*.v SWEEP ----------------------------------------

    All 206 [Link*.v] were scanned OUTSIDE COMMENTS for a code-level
    mention of any of the 198 names that lose a threaded parameter in this
    rank's first slice.  There is exactly ONE, and it is a positional
    application:

      LinkNameiRootBoot.v:  iApply (NameiRoot.wp_namei_root fsc_itlock
        fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_ist icfg_nib
        icfg_dev dqp m n K eb p b lks (MkPPriv ...) HK Hn eq_refl eq_refl
        Hdev Hnib Hlks with "...")

    -- so it already instantiates the corner AT the ambient fields, and
    de-threading a parameter there is deleting the corresponding argument
    (and, if the parameter's tie premise goes with it, one [eq_refl]).
    Every other [Link*.v] is a pure functor application over MODULE
    arguments ([Module Iget := IgetProof Acquire Release Panic.]), which no
    parameter change can reach.  The four other files that name an
    affected contract ([LinkFsinit], [LinkIalloc], [LinkIput],
    [LinkIreclaim]) do so only in comments.                              *)
