(* ===================================================================== *)
(* UexecCond.v -- THE CONDITIONAL ENTRY DEPOSIT: at a mint site, decide    *)
(* on the KEY alone whether the process is a VERIFIED PROGRAM at its        *)
(* entry, and deposit that program's slot if so, the generic one            *)
(* otherwise.  NO assumption enters the composition on any branch.          *)
(*                                                                         *)
(* TWO PROGRAMS NOW: `sync` and `echo`.  [cond_entry_slot] is a CHAIN of    *)
(* decidable gates ending in the generic WP; adding the next verified       *)
(* program is one more [destruct].  Everything below that reads "sync" is   *)
(* parametric in the program's dumped image ([text_region_eq_of]), with the *)
(* sync-named forms kept as the instance the mint sites already spell.      *)
(*                                                                         *)
(* STEP 1 -- the DECIDABLE TEST that a process's memory image carries a     *)
(* program's text verbatim ([text_region_eq_of]), so a mint site can do      *)
(*                                                                         *)
(*   destruct (decide (sync_gate W)) as [Hgate | _]                          *)
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
(* STEP 2 -- [cond_entry_slot], the conditional constructor.  ALL FOUR of   *)
(* sync's entry conditions -- and all FIVE of echo's, whose extra one is    *)
(* the argc/argv area ([UkAbi.uk_args_c], at the trapframe's own a0/a1/sp)  *)
(* -- are facts about the key with a [Decision]:                            *)
(* the text ([text_region_eq]), the resume pc, page 0 an X page of the      *)
(* permission map ([uk_xpage]) and the stack budget ([uk_stack]) -- the     *)
(* last two used to be facts about the TABLE ([sync_layout], [uv_stack]),  *)
(* guarded under the slot's own ∀ as [sync_entry_tbl], and THAT guard was   *)
(* UNSATISFIABLE (the empty table is [loop_ok]; the refutation              *)
(* [sync_entry_tbl_refuted] lived here until the permission map entered the *)
(* key).  See claude-notes/design/user-wp-slot.md, "The permission map".    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
From iris.base_logic.lib Require Import ghost_var.
Require Import RiscvLang RiscvPtsto.
Require Import ProcGeom ProcDefs ProcPt ProcPtOwn.   (* [tf_sp_idx] / [tf_arg_idx] *)
Require Import UserPtTree UserExec.
Require Import UmodeAbi.
Require Import UserPerm UexecWp UexecSlot UexecRet.
Require Import UkAbi.   (* [uk_xpage] / [uk_stack] / [uk_args_c]: the key-level facts *)
Require Import WpMmodeLeafBase.
Require Import USyncKernel.
Require Import UEchoKernel.
Require User.SyncInstrs.
Require User.EchoSyms User.EchoInstrs.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode*/Uk* precedent *)
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
(* PARAMETRIC IN THE PROGRAM'S IMAGE.  The test was cut for `sync` and is
   now used by `echo` too, so it takes the dumped bytes as an argument; the
   sync-named forms below are the instance at [SyncInstrs.sync_bytes] and
   keep the names the mint sites already spell. *)
Definition in_img_text (img : gmap Z (bv 8)) (kv : Z * bv 8) : Prop :=
  kv.1 ∈ dom img.

Global Instance in_img_text_dec (img : gmap Z (bv 8)) (kv : Z * bv 8) :
  Decision (in_img_text img kv).
Proof. unfold in_img_text. apply _. Defined.

Definition text_region_eq_of (img M : gmap Z (bv 8)) : Prop :=
  base.filter (in_img_text img) M = img.

Global Instance text_region_eq_of_dec (img M : gmap Z (bv 8)) :
  Decision (text_region_eq_of img M).
Proof. unfold text_region_eq_of. apply _. Defined.

Definition in_sync_text (kv : Z * bv 8) : Prop :=
  in_img_text SyncInstrs.sync_bytes kv.

Global Instance in_sync_text_dec (kv : Z * bv 8) : Decision (in_sync_text kv).
Proof. unfold in_sync_text. apply _. Defined.

Definition text_region_eq (M : gmap Z (bv 8)) : Prop :=
  text_region_eq_of SyncInstrs.sync_bytes M.

Global Instance text_region_eq_dec (M : gmap Z (bv 8)) :
  Decision (text_region_eq M).
Proof. unfold text_region_eq. apply _. Defined.

(* ===================================================================== *)
(* SS2 ...and what it buys: sync's own image premise.                      *)
(* ===================================================================== *)
Lemma text_region_eq_of_uimg_sub (img M : gmap Z (bv 8)) :
  text_region_eq_of img M -> uimg_sub img M.
Proof.
  unfold text_region_eq_of, uimg_sub. intros Heq a b Hb.
  assert (Hf : base.filter (in_img_text img) M !! a = Some b)
    by (rewrite Heq; exact Hb).
  apply map_lookup_filter_Some in Hf as [HM _]. exact HM.
Qed.

(* The converse: an image CONTAINING the text has that text as its
   restriction -- so the test is exactly as strong as [uimg_sub] and no
   stronger.  NOTE [cbn [fst]], never [simpl]: see the header. *)
Lemma uimg_sub_text_region_eq_of (img M : gmap Z (bv 8)) :
  uimg_sub img M -> text_region_eq_of img M.
Proof.
  unfold text_region_eq_of, uimg_sub. intros Hsub.
  apply map_eq. intros a.
  destruct (img !! a) as [b|] eqn:Hsb.
  - apply map_lookup_filter_Some. split; [exact (Hsub a b Hsb)|].
    unfold in_img_text. cbn [fst]. apply elem_of_dom.
    exact (mk_is_Some _ _ Hsb).
  - apply map_lookup_filter_None. right. intros x _.
    unfold in_img_text. cbn [fst]. rewrite not_elem_of_dom. exact Hsb.
Qed.

Lemma text_region_eq_uimg_sub (M : gmap Z (bv 8)) :
  text_region_eq M -> uimg_sub SyncInstrs.sync_bytes M.
Proof. exact (text_region_eq_of_uimg_sub SyncInstrs.sync_bytes M). Qed.

Lemma uimg_sub_text_region_eq (M : gmap Z (bv 8)) :
  uimg_sub SyncInstrs.sync_bytes M -> text_region_eq M.
Proof. exact (uimg_sub_text_region_eq_of SyncInstrs.sync_bytes M). Qed.

(* ===================================================================== *)
(* SS3 THE GATE, and THE CONDITIONAL CONSTRUCTOR.                          *)
(* ===================================================================== *)

(* sync's SIX entry conditions, all about the key, all decidable.  The last
   is the one that could not even be STATED before the break joined the key:
   [udata_lo] is filtered at [sz], and with [sz] bound by the slot's own ∀
   the condition had to hold at every size the slot admitted -- including
   zero, where it is false.  [uvis_sz W] pins it. *)
Definition sync_gate (W : uvis) : Prop :=
  text_region_eq (uvis_M W) /\
  tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64) /\
  sync_xopage (uvis_perm W) /\
  32 <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) /\
  uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 /\
  sync_stkdata W.

Global Instance sync_gate_dec (W : uvis) : Decision (sync_gate W).
Proof. unfold sync_gate. apply _. Defined.

(* echo's NINE.  Four are sync's, said at echo's text and entry pc.  The
   other five are the argument vector: it is well formed AT OR ABOVE the
   entry sp ([uk_args_c], which pins the array's alignment, the count, the
   readability of the array and of every string, and each string's NUL),
   and every byte of it is present in the key's writable data
   ([echo_avd_arr] for the array, [echo_avd_str] for the strings).
   [uk_args_c]'s own [uka_lo] at [lo = uint sp] is what puts the argument
   area on the far side of the cut from the frames echo carves below sp,
   and hence what lets one deposit hand out both.

   NOTHING here says the argv strings are pairwise DISJOINT, and nothing
   needs to: the area is deposited read-only ([DfracDiscarded]), so two
   slots pointing at the same string is simply not a question the gate has
   to answer.  With an exclusive [ubyte] it would have been a quadratic
   condition on the key. *)
Definition echo_gate (W : uvis) : Prop :=
  text_region_eq_of EchoInstrs.echo_bytes (uvis_M W) /\
  tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) /\
  sync_xopage (uvis_perm W) /\
  96 <= uint (uvis_sp W) /\
  uint (uvis_sp W) mod 8 = 0 /\
  echo_stkdata W /\
  uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
    (uint (uvis_sp W)) /\
  echo_avd_arr W /\
  echo_avd_str W.

Global Instance echo_gate_dec (W : uvis) : Decision (echo_gate W).
Proof. unfold echo_gate. apply _. Defined.

Section UexecCond.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* the break's ghost class, for [UkRun.usz].  It already exists in the
     tree -- [Xv6Cameras.uioG]'s [uio_brkG] is the same [ghost_varG Σ Z] --
     so nothing new enters Σ. *)
  Context `{!ghost_varG Σ Z}.

  (* THE CONDITIONAL CONSTRUCTOR: a verified program's slot when its gate
     holds, the generic one otherwise -- and nothing is assumed on any
     branch.  It is a CHAIN now rather than one test, and the order does
     not matter to the conclusion: every branch produces the same [uslot W],
     so a key that somehow satisfied two gates would simply take the first.
     Adding the next verified program is one more [destruct]. *)
  (* the gate's yes branch: sync's own slot *)
  Lemma sync_gate_slot (W : uvis) : sync_gate W -> ⊢ uslot W.
  Proof.
    intros (Hteq & Hpc & Hxo & Hroom & Hal8 & Hstk).
    exact (sync_uexec_slot W Hpc
             (text_region_eq_uimg_sub (uvis_M W) Hteq)
             (sync_xopage_addrs (uvis_perm W) Hxo)
             Hroom Hal8 (sync_stkdata_all W Hstk)).
  Qed.

  (* ...and echo's *)
  Lemma echo_gate_slot (W : uvis) : echo_gate W -> ⊢ uslot W.
  Proof.
    intros (Hteq & Hpc & Hxo & Hroom & Hal8 & Hstk & Hargs & Havd & Havs).
    exact (echo_uexec_slot W Hpc
             (text_region_eq_of_uimg_sub EchoInstrs.echo_bytes (uvis_M W) Hteq)
             (sync_xopage_addrs (uvis_perm W) Hxo)
             Hroom Hal8 (echo_stkdata_all W Hstk) Hargs
             (echo_avd_arr_all W Havd) (echo_avd_str_all W Havs)).
  Qed.

  Lemma cond_entry_slot (W : uvis) : □ uexec_wp -∗ uslot W.
  Proof.
    iIntros "#Hgen".
    destruct (decide (sync_gate W)) as [Hgate | _].
    { iApply (sync_gate_slot W Hgate). }
    destruct (decide (echo_gate W)) as [Hgate | _].
    { iApply (echo_gate_slot W Hgate). }
    iApply (uexec_wp_uslot W with "Hgen").
  Qed.

End UexecCond.

(* ===================================================================== *)
(* SS4 THE RE-KEY LEMMA the park channel needs.                            *)
(*                                                                         *)
(* [uslot (uvis_of U)] reads [U] through [pv_tf (us_V U)], [us_M U] and the *)
(* PROJECTION of the table and size -- never the table itself.  So a slot   *)
(* minted at the state a PARKER holds can be spent at the state a RESUMER   *)
(* produces, given those equations -- the gap in [ParkCap.park_token_park]: *)
(* the captured [fd_frags_any (pv_fdg V)] row is re-keyed onto the closer's *)
(* own [∀ V'] by [rewrite -Hfg] off the closer's [⌜pv_fdg V' = pv_fdg V⌝],   *)
(* and there is NO analogous premise for the trapframe.  A fresh TABLE      *)
(* (fork's child) costs only its projection agreeing -- which uvmcopy's     *)
(* leaf-for-leaf copy gives.                                                *)
(* ===================================================================== *)
Section UexecCondCongr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  Lemma uslot_congr (U1 U2 : ustate) :
    pv_tf (us_V U1) = pv_tf (us_V U2) ->
    us_M U1 = us_M U2 ->
    perm_of (ud_um (pv_upt (us_V U1))) (uint (pv_sz (us_V U1)))
    = perm_of (ud_um (pv_upt (us_V U2))) (uint (pv_sz (us_V U2))) ->
    (* the break is key material now *)
    pv_sz (us_V U1) = pv_sz (us_V U2) ->
    uslot (uvis_of U1) -∗ uslot (uvis_of U2).
  Proof.
    intros Htf Hm Hp Hs. rewrite /uvis_of Htf Hm Hp Hs. iIntros "H". iExact "H".
  Qed.

End UexecCondCongr.

(* ===================================================================== *)
(* SS5 THE DISCHARGE AT userinit, and the ONE fact about the literal it    *)
(* needs.  userinit's process has the EMPTY user map -- allocproc's arm    *)
(* delivers [pv_upt V = ProcPtOwn.upt_desc root tfp] and [upt_desc root    *)
(* tfp = UPTD root tfp emptyset (um_pas emptyset)] -- so the sync branch  *)
(* is refutable there without computing over the byte literal: page 0 is  *)
(* not an X page of the projection of an empty map at size 0 (the fill    *)
(* carries no X either).                                                   *)
(* ===================================================================== *)
Lemma uk_xpage_upt_desc (root tfp : mword 44) (sz : Z) :
  ~ uk_xpage (perm_of (ud_um (upt_desc root tfp)) sz) (mword_of_int 0).
Proof.
  intros (q & Hq & Hx). unfold uperm_at in Hq.
  destruct (perm_of_X_mapped _ _ _ _ Hq Hx) as (w & Hw & _).
  unfold upt_desc in Hw. cbn [ud_um] in Hw. rewrite lookup_empty in Hw. discriminate Hw.
Qed.

(* the empty table is [loop_ok] whenever any table is -- the fact that
   refuted the former ∀-table guard, kept for the mint site that needs it *)
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

(* ...and a mint site that has to refute [text_region_eq] instead needs one
   fact about the literal: that [sync_bytes] names an address at all.  A
   single [sync_bytes !! a] lookup, the only place in the whole hook where
   the 2242-entry literal would be reduced. *)
Lemma text_region_eq_hits (M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  SyncInstrs.sync_bytes !! a = Some b -> text_region_eq M -> M !! a = Some b.
Proof. intros Hb Heq. exact (text_region_eq_uimg_sub M Heq a b Hb). Qed.
