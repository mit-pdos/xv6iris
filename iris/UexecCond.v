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
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import ProcGeom ProcDefs ProcPt ProcPtOwn.
Require Import UserPtTree UserFrame UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeSyscall.
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
(* The two conditions that HAVE a [Decision] -- both about the KEY [W]     *)
(* alone -- are decided here; the two that do not ([sync_layout],          *)
(* [uv_stack] -- both bottom out in [UserPtTree.uleaf_ok], a forall over   *)
(* (mword 1)^2 x bool^2 of the Sail [pte_check_ok], for which no decider   *)
(* exists) are ALSO the two about the TABLE, which the slot binds inside;  *)
(* they are taken as [USyncKernel.sync_entry_tbl], a PURE premise guarded  *)
(* under the slot's own [∀ (C, P), loop_ok C P], and CONDITIONED on the two *)
(* decided ones so the generic branch owes nothing.  And [uv_cap] is not a  *)
(* [Prop] at all -- it is an iProp premise, which is the headline wart:     *)
(* supplying it at a mint site is an ASSUMPTION entering the composition.   *)
(* ===================================================================== *)
Section UexecCond.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma cond_entry_slot (W : uvis) :
    (text_region_eq (uvis_M W) ->
     tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64) ->
     sync_entry_tbl (uvis_M W) (tf_w (uvis_tf W) tf_sp_idx)) ->
    □ (∀ (C : ucfg) (P : uptd), ⌜loop_ok C P⌝ -∗
         uv_cap C P (xv6_sys_protocol C P)) -∗
    uexec_wp -∗
    uexec_slot W.
  Proof.
    intros Htbl. iIntros "#Hcap Hgen".
    destruct (decide (text_region_eq (uvis_M W))) as [Hteq | _]; last first.
    { iApply (uexec_wp_slot W with "Hgen"). }
    destruct (decide (tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64)))
      as [Hpc | _]; last first.
    { iApply (uexec_wp_slot W with "Hgen"). }
    iApply (sync_uexec_slot W Hpc (text_region_eq_uimg_sub (uvis_M W) Hteq)
              (Htbl Hteq Hpc)).
    iExact "Hcap".
  Qed.

End UexecCond.

(* ===================================================================== *)
(* SS4 THE RE-KEY LEMMA the park channel needs.                            *)
(*                                                                         *)
(* [uexec_slot (uvis_of U)] reads [U] ONLY through [pv_tf (us_V U)] and     *)
(* [us_M U] -- the table is forall-bound inside the slot and never read     *)
(* from [U].  So a slot minted at the state a PARKER holds can be spent at  *)
(* the state a RESUMER produces, given those two equations -- which is      *)
(* exactly the gap in [ParkCap.park_token_park]: the captured               *)
(* [fd_frags_any (pv_fdg V)] row is re-keyed onto the closer's own [∀ V']  *)
(* by [rewrite -Hfg] off the closer's [⌜pv_fdg V' = pv_fdg V⌝], and there  *)
(* is NO analogous premise for the trapframe.  With this lemma, adding      *)
(* [⌜pv_tf V' = pv_tf V⌝] to the package's resume closer is all a keyed row *)
(* costs: a fresh TABLE (fork's child) costs nothing.                       *)
(* ===================================================================== *)
Section UexecCondCongr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma uexec_slot_congr (U1 U2 : ustate) :
    pv_tf (us_V U1) = pv_tf (us_V U2) ->
    us_M U1 = us_M U2 ->
    uexec_slot (uvis_of U1) -∗ uexec_slot (uvis_of U2).
  Proof.
    intros Htf Hm. rewrite /uvis_of Htf Hm. iIntros "H". iExact "H".
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

  Lemma cond_entry_slot_gated (W : uvis) :
    (⌜text_region_eq (uvis_M W)⌝ -∗
     ⌜tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64)⌝ -∗
     ⌜sync_entry_tbl (uvis_M W) (tf_w (uvis_tf W) tf_sp_idx)⌝ ∗
     □ (∀ (C : ucfg) (P : uptd), ⌜loop_ok C P⌝ -∗
          uv_cap C P (xv6_sys_protocol C P))) -∗
    uexec_wp -∗
    uexec_slot W.
  Proof.
    iIntros "Hsync Hgen".
    destruct (decide (text_region_eq (uvis_M W))) as [Hteq | _]; last first.
    { iApply (uexec_wp_slot W with "Hgen"). }
    destruct (decide (tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64)))
      as [Hpc | _]; last first.
    { iApply (uexec_wp_slot W with "Hgen"). }
    iDestruct ("Hsync" with "[%] [%]") as "[%Htbl #Hcap]";
      [exact Hteq | exact Hpc |].
    iApply (sync_uexec_slot W Hpc (text_region_eq_uimg_sub (uvis_M W) Hteq) Htbl).
    iExact "Hcap".
  Qed.

End UexecCondGated.

(* THE DISCHARGE AT userinit, and the ONE fact about the literal it needs.
   userinit's process has the EMPTY user map -- allocproc's arm delivers
   [pv_upt V = ProcPtOwn.upt_desc root tfp] and
   [upt_desc root tfp = UPTD root tfp emptyset (um_pas emptyset)] -- so the
   SYNC BRANCH IS REFUTABLE THERE, with no computation over the byte
   literal at all -- though note that with the table forall-bound inside
   the slot, [sync_entry_tbl]'s obligation is at EVERY [loop_ok] table,
   not at the one the process holds; refuting the gate on the DECIDED
   facts is the route that owes nothing: *)
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

(* ===================================================================== *)
(* SS6 THE ∀-TABLE GUARD IS UNSATISFIABLE -- the satisfiability witness   *)
(* durable-notes' "GAP PREMISE" rule asks for.                            *)
(*                                                                        *)
(* [sync_entry_tbl M sp] owes [sync_layout P] at EVERY [loop_ok] table    *)
(* [P], and the empty table (userinit's, [upt_desc root tfp]) is one: its *)
(* text page is unmapped, so [sync_layout] fails there                    *)
(* ([sync_layout_upt_desc]).  Hence no [M], [sp] satisfies                *)
(* [sync_entry_tbl] once ANY [loop_ok] config exists -- and one does,     *)
(* since the loop runs.  [sync_uexec_slot] and both [cond_entry_slot]     *)
(* forms are therefore vacuous as stated: the table facts a program needs *)
(* (its text page fetch-permitted, its stack page writable) are not a     *)
(* function of the image's DOMAIN, which is all the slot's ∀ pins, and    *)
(* [upt_acc_wf] only says each leaf is ok-or-denied per access, never     *)
(* which.  The fix is an owner ruling on the KEY (the per-page permission *)
(* view is user-visible state); see claude-notes/projects/user-wp-slot.md *)
(* SS3 item 2.                                                            *)
(* ===================================================================== *)
Lemma loop_ok_upt_desc (C : ucfg) (P : uptd) (root tfp : mword 44) :
  loop_ok C P -> page_valid (page_base tfp) -> loop_ok C (upt_desc root tfp).
Proof.
  intros (Hstvec & Hdqc & Hmie & Hmedl & _ & _) Hv.
  split_and!; [ exact Hstvec | exact Hdqc | exact Hmie | exact Hmedl | reflexivity | ].
  unfold upt_desc. cbn [ud_um ud_tfp].
  split; [ exact ProcPt.upt_map_wf_empty | ].
  split; [ exact upt_acc_wf_empty | ].
  split; [ exact um_pages_valid_empty | ].
  split; [ exact um_inj_empty | exact Hv ].
Qed.

Lemma sync_entry_tbl_refuted (C : ucfg) (P : uptd) (root tfp : mword 44)
    (M : gmap Z (bv 8)) (sp : mword 64) :
  loop_ok C P -> page_valid (page_base tfp) -> ~ sync_entry_tbl M sp.
Proof.
  intros Hlo Hv Htbl.
  destruct (Htbl C (upt_desc root tfp) (loop_ok_upt_desc C P root tfp Hlo Hv)) as [Hlay _].
  exact (sync_layout_upt_desc root tfp Hlay).
Qed.
