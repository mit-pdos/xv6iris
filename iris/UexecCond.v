(* ===================================================================== *)
(* UexecCond.v -- PROBE (uncommitted; the force-link probe patch).         *)
(*                                                                         *)
(* STEP 1 -- the DECIDABLE TEST that a process's memory image carries       *)
(* `sync`'s text verbatim, so a mint site can do                            *)
(*                                                                         *)
(*   destruct (decide (text_region_eq M)) as [Heq | _]                      *)
(*                                                                         *)
(* BEFORE deciding which WP to construct.  The case analysis is             *)
(* PROOF-LEVEL: [decide] on a SYMBOLIC [M] is an ordinary [Decision]        *)
(* elimination and never reduces the 2242-byte [SyncInstrs.sync_bytes]      *)
(* literal.  MEASURED, and with one caveat that is a real trap:             *)
(*                                                                         *)
(*   * [destruct (decide (text_region_eq M))] at symbolic [M]: FREE         *)
(*     (whole probe file 0.77 s).                                           *)
(*   * a bare [simpl] or [cbn] on ANY goal that merely MENTIONS             *)
(*     [dom SyncInstrs.sync_bytes] does NOT terminate (>30 s, killed;       *)
(*     three earlier full-file attempts sat at 1.2 GB RSS for 12-22 min).   *)
(*     Use [cbn [fst]] -- a delta list -- to reduce the pair projection     *)
(*     without touching the literal.                                        *)
(*                                                                         *)
(* STEP 2 -- [cond_entry_slot], the conditional constructor, standalone.    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ProcGeom ProcDefs ProcPtOwn.
Require Import UserPtTree UserExec.
Require Import UmodeCap UmodeAbi UmodeSyscall.
Require Import UCodeSync.
Require Import UexecWp UexecSlot USyncKernel.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 The predicate, and why it is spelled with [filter].                 *)
(*                                                                         *)
(* "the TEXT PORTION of M equals sync's image": restrict [M] to the         *)
(* addresses [sync_bytes] names and ask for map equality.  The stdpp        *)
(* spelling that gets a [Decision] cleanly is [map_filter] on the KEY       *)
(* (decidable: [elem_of] on a [gset Z]) plus [EqDecision (gmap Z (bv 8))].  *)
(* ===================================================================== *)
Definition in_sync_text (kv : Z * bv 8) : Prop :=
  kv.1 ∈ dom SyncInstrs.sync_bytes.

Global Instance in_sync_text_dec (kv : Z * bv 8) : Decision (in_sync_text kv).
Proof. unfold in_sync_text. apply _. Defined.

Definition text_region_eq (M : gmap Z (bv 8)) : Prop :=
  base.filter in_sync_text M = SyncInstrs.sync_bytes.

Global Instance text_region_eq_dec (M : gmap Z (bv 8)) :
  Decision (text_region_eq M).
Proof. unfold text_region_eq. apply _. Defined.

(* ===================================================================== *)
(* SS2 ...and what it buys: sync's own image premise.                      *)
(* ===================================================================== *)
Lemma text_region_eq_uimg_sub (M : gmap Z (bv 8)) :
  text_region_eq M -> uimg_sub SyncInstrs.sync_bytes M.
Proof.
  unfold text_region_eq, uimg_sub. intros Heq a b Hb.
  assert (Hf : base.filter in_sync_text M !! a = Some b) by (rewrite Heq; exact Hb).
  apply map_lookup_filter_Some in Hf as [HM _]. exact HM.
Qed.

(* The converse: an image CONTAINING the text has that text as its
   restriction -- so the test is exactly as strong as [uimg_sub] and no
   stronger.  NOTE [cbn [fst]], never [simpl]: see the header. *)
Lemma uimg_sub_text_region_eq (M : gmap Z (bv 8)) :
  uimg_sub SyncInstrs.sync_bytes M -> text_region_eq M.
Proof.
  unfold text_region_eq, uimg_sub. intros Hsub.
  apply map_eq. intros a.
  destruct (SyncInstrs.sync_bytes !! a) as [b|] eqn:Hsb.
  - apply map_lookup_filter_Some. split; [exact (Hsub a b Hsb)|].
    unfold in_sync_text. cbn [fst]. apply elem_of_dom.
    exact (mk_is_Some _ _ Hsb).
  - apply map_lookup_filter_None. right. intros x _.
    unfold in_sync_text. cbn [fst]. rewrite not_elem_of_dom. exact Hsb.
Qed.

(* ===================================================================== *)
(* SS3 THE CONDITIONAL CONSTRUCTOR.                                        *)
(*                                                                         *)
(* The two conditions that HAVE a [Decision] are decided here; the two      *)
(* that do not ([sync_layout], [uv_stack] -- both bottom out in            *)
(* [UserPtTree.uleaf_ok], a forall over (mword 1)^2 x bool^2 of the Sail    *)
(* [pte_check_ok], for which no decider exists) are taken as a PURE         *)
(* premise, CONDITIONED on the two decided ones so the generic branch owes  *)
(* nothing.  And [uv_cap] is not a [Prop] at all -- it is an iProp premise, *)
(* which is the headline wart: supplying it at a mint site is an ASSUMPTION *)
(* entering the composition.                                                *)
(* ===================================================================== *)
Definition sync_entry_pure (U : ustate) : Prop :=
  sync_layout (pv_upt (us_V U))
  /\ uv_stack (pv_upt (us_V U)) (us_M U) (tf_w (us_V U) tf_sp_idx) 32.

Section UexecCond.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma cond_entry_slot (U : ustate) :
    (text_region_eq (us_M U) ->
     tf_resume_pc (us_V U) = (mword_of_int SyncSyms.start : mword 64) ->
     sync_entry_pure U) ->
    □ (∀ C : ucfg, ⌜loop_ok C (pv_upt (us_V U))⌝ -∗
         uv_cap C (pv_upt (us_V U)) (xv6_sys_protocol C (pv_upt (us_V U)))) -∗
    uexec_wp -∗
    uexec_slot U.
  Proof.
    intros Hpure. iIntros "#Hcap Hgen".
    destruct (decide (text_region_eq (us_M U))) as [Hteq | _]; last first.
    { iApply (uexec_wp_slot U with "Hgen"). }
    destruct (decide (tf_resume_pc (us_V U) = (mword_of_int SyncSyms.start : mword 64)))
      as [Hpc | _]; last first.
    { iApply (uexec_wp_slot U with "Hgen"). }
    destruct (Hpure Hteq Hpc) as [Hlay Hst].
    iApply (sync_uexec_slot U Hpc Hlay (text_region_eq_uimg_sub (us_M U) Hteq) Hst).
    iExact "Hcap".
  Qed.

End UexecCond.

(* ===================================================================== *)
(* SS4 THE RE-KEY LEMMA the park channel needs.                            *)
(*                                                                         *)
(* [uexec_slot V M] reads [V] ONLY through [pv_upt V] (the table) and       *)
(* [pv_tf V] (via [tf_resume_pc] / [tf_resume_gpr]).  So a slot minted at   *)
(* the descriptor a PARKER holds can be spent at the descriptor a RESUMER   *)
(* produces, given those two equations -- which is exactly the gap in       *)
(* [ParkCap.park_token_park]: the captured [fd_frags_any (pv_fdg V)] row is *)
(* re-keyed onto the closer's own [∀ V'] by [rewrite -Hfg] off the closer's *)
(* [⌜pv_fdg V' = pv_fdg V⌝], and there is NO analogous premise for the      *)
(* table or the trapframe.  With this lemma, adding                        *)
(* [⌜pv_upt V' = pv_upt V⌝ ∗ ⌜pv_tf V' = pv_tf V⌝] to the package's resume  *)
(* closer is all a keyed row costs.                                        *)
(* ===================================================================== *)
Section UexecCondCongr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma uexec_slot_congr (U1 U2 : ustate) :
    pv_upt (us_V U1) = pv_upt (us_V U2) ->
    pv_tf (us_V U1) = pv_tf (us_V U2) ->
    us_M U1 = us_M U2 ->
    uexec_slot U1 -∗ uexec_slot U2.
  Proof.
    intros Hupt Htf Hm.
    rewrite /uexec_slot /tf_resume_pc /tf_resume_gpr /tf_w Hupt Htf Hm.
    iIntros "H". iExact "H".
  Qed.

End UexecCondCongr.

(* ===================================================================== *)
(* SS5 THE GATED FORM -- what would make the hook LANDABLE at a mint site. *)
(*                                                                         *)
(* [cond_entry_slot] takes [uv_cap] UNCONDITIONALLY, and that is the       *)
(* headline wart: supplying it at userinit's park would put an ASSUMPTION  *)
(* into the composition.  The cap is only ever USED on the true branch, so *)
(* it can be GATED on the two DECIDED facts -- and so can the pure         *)
(* premise.  A mint site then owes the sync side NOTHING as soon as it can *)
(* refute the gate.                                                        *)
(* ===================================================================== *)
Section UexecCondGated.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma cond_entry_slot_gated (U : ustate) :
    (⌜text_region_eq (us_M U)⌝ -∗
     ⌜tf_resume_pc (us_V U) = (mword_of_int SyncSyms.start : mword 64)⌝ -∗
     ⌜sync_entry_pure U⌝ ∗
     □ (∀ C : ucfg, ⌜loop_ok C (pv_upt (us_V U))⌝ -∗
          uv_cap C (pv_upt (us_V U)) (xv6_sys_protocol C (pv_upt (us_V U))))) -∗
    uexec_wp -∗
    uexec_slot U.
  Proof.
    iIntros "Hsync Hgen".
    destruct (decide (text_region_eq (us_M U))) as [Hteq | _]; last first.
    { iApply (uexec_wp_slot U with "Hgen"). }
    destruct (decide (tf_resume_pc (us_V U) = (mword_of_int SyncSyms.start : mword 64)))
      as [Hpc | _]; last first.
    { iApply (uexec_wp_slot U with "Hgen"). }
    iDestruct ("Hsync" with "[%] [%]") as "[%Hpure #Hcap]";
      [exact Hteq | exact Hpc |].
    destruct Hpure as [Hlay Hst].
    iApply (sync_uexec_slot U Hpc Hlay (text_region_eq_uimg_sub (us_M U) Hteq) Hst).
    iExact "Hcap".
  Qed.

End UexecCondGated.

(* THE DISCHARGE AT userinit, and the ONE fact about the literal it needs.
   userinit's process has the EMPTY user map -- allocproc's arm delivers
   [pv_upt V = ProcPtOwn.upt_desc root tfp] and
   [upt_desc root tfp = UPTD root tfp emptyset (um_pas emptyset)] -- so the
   SYNC BRANCH IS REFUTABLE THERE, with no computation over the byte
   literal at all: *)
Lemma sync_layout_upt_desc (root tfp : mword 44) :
  ~ sync_layout (upt_desc root tfp).
Proof.
  intros [ (w & Hl & _) ]. unfold upt_desc in Hl. cbn [ud_um] in Hl.
  rewrite lookup_empty in Hl. discriminate Hl.
Qed.

(* ...but [sync_layout] is the gate's CONSEQUENT, not its antecedent, so the
   discharge above cannot be used directly: a mint site must refute
   [text_region_eq M], and that needs the image's domain plus ONE fact about
   the literal -- that [sync_bytes] names an address at all.  Stated here as
   a hypothesis so the report can say exactly what is owed; discharging it is
   a single [sync_bytes !! a] lookup, the only place in the whole hook where
   the 2242-entry literal would be reduced. *)
Lemma text_region_eq_hits (M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  SyncInstrs.sync_bytes !! a = Some b -> text_region_eq M -> M !! a = Some b.
Proof. intros Hb Heq. exact (text_region_eq_uimg_sub M Heq a b Hb). Qed.
