(* ====================================================================== *)
(* UserClassifyAsm.v -- THE PAIR CONVENTION FOR THE TIER'S TOTALITY FACTS. *)
(*                                                                        *)
(* [base_exec_total_u] / [rvc_exec_total_u] are the two obligations the    *)
(* whole U-mode execute campaign discharges: whatever this word decodes    *)
(* to, executing it at a User machine lands in one of the four U-mode      *)
(* outcomes and leaves the hart frame and pages in a state the loop        *)
(* invariant can be rebuilt from.  Under whole-cycle stepping they were    *)
(* [iProp] obligations that MOVED [mstate_interp] and [gpr_file] through a *)
(* fancy update.  Under per-node stepping there is nothing left to move:   *)
(* the frames and the bytes stay with the CALLER, which hands them to      *)
(* [HartMemRun.swp_hmrun_of_exec] together with the facts below.  So both  *)
(* become PURE [Prop]s, and roughly four thousand lines of Iris plumbing   *)
(* in [UserMemClassify] / [UserTotalU] become checkable without the        *)
(* proofmode.                                                              *)
(*                                                                        *)
(* THE CONVENTION, in one line:                                            *)
(*                                                                        *)
(*   for every [exec X ... = Some (r, s')] the tier already proves, a TWIN *)
(*   [goodmb Du_r Du_w X s mm = true] with the SAME binders and the SAME   *)
(*   hypotheses, at the SAME reference state, plus a characterisation of   *)
(*   what the call left behind.                                            *)
(*                                                                        *)
(* THE REFERENCE STATE IS ALWAYS                                           *)
(*                                                                        *)
(*   MState rs mm dev0_state                                               *)
(*                                                                        *)
(* with [rs] the frame's register file and [mm] the hart's owned byte map  *)
(* ([UserBytes.u_mem_wf P t mm]).  That choice is the whole reason the     *)
(* port is cheap: [swp_hmrun_of_exec]'s two hard-looking premises          *)
(* [reg_agree_on (Drw u Dro) rs s.(sregs)] and [mm subseteq s.(mem)]       *)
(* become [reflexivity] and subseteq-reflexivity, and the landing map is   *)
(* LITERALLY [s'.(mem)] ([u_landing_map] below turns                       *)
(* [swp_hmrun_of_exec]'s existential map into it).                         *)
(*                                                                        *)
(* WHAT THE POST-STATE CHARACTERISATION HAS TO SAY, and why it is not just *)
(* the [exec] fact.  Under the old shape the caller learned what the       *)
(* execute had done by RECEIVING [mstate_interp s_x] -- the resources      *)
(* carried the information.  A pure fact carries none, so the two things   *)
(* the loop invariant needs must be said explicitly:                       *)
(*                                                                        *)
(*   [reg_agree_on u_Dfix s'.(sregs) <the ticked file>]  -- a U-mode       *)
(*      EXECUTE writes nextPC, the GPRs and (on a TLB fill) [tlb], and     *)
(*      NOTHING else.  Every other cell of the footprint -- hart_state,    *)
(*      cur_privilege, mstatus, the trap CSRs, the counters, and the whole *)
(*      read-only half -- comes back untouched, which is what lets         *)
(*      [UserFrame.u_frames_elim] rebuild [user_cfg] / [hw_config] /       *)
(*      [upt_regs] and what discharges [swp_exec_step_full]'s [HQhart] and *)
(*      [HQmi] premises.                                                   *)
(*   [u_mem_step P t t' mm s'.(mem)]  -- the bytes moved only the way      *)
(*      [UserBytes.user_pt_inv_bytes]'s closing wand allows: arbitrary     *)
(*      data at the same domain, and a SAME-SHAPED tree (the A/D           *)
(*      write-back).                                                       *)
(*                                                                        *)
(* WHAT DID NOT CHANGE, on purpose: the NAMES, and the [exec] conjuncts.   *)
(* [UserTotalU]'s two 250-line [lazymatch] dispatch tables are keyed on    *)
(* nothing else, so they survive the reshaping verbatim.                   *)
(*                                                                        *)
(* GENERICITY, and where it lives: the memory twins (P3/P4) are stated in  *)
(* ARBITRARY [(Dr Dw : register -> bool)] with [Dr r = true] / [Dw r =     *)
(* true] hypotheses and at an ARBITRARY [mm] with [u_mem_wf]-derived       *)
(* premises ([bytes_owned mm pa n = true], [dev_addr pa = false]), exactly *)
(* as the register-only twins of [UserCsr] / [UserExecFacts] / [UserTrap]  *)
(* already are.  Only HERE, at the top, are they specialised to            *)
(* [Du_r]/[Du_w] -- by [HartMemRun.goodmb_mono] for the footprint and by   *)
(* [goodmb_map_mono] for the map.                                          *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import DevModel.
Require Import WpGpr.
Require Import HartLift HartSpan HartMemRun PtBytes.
Require Import PtreeType PtTree SmodePte UptTree UserPtTree UserFrame UserBytes.
Require Import UserExec UserClassify.
Local Open Scope Z_scope.
Import Defs.

(* 4-byte alignment implies 2-byte alignment (4 | va -> 2 | va).  Feeds the
   4-aligned producer's post_fetch_cfg [is_aligned_vaddr va 2] conjunct. *)
Lemma is_aligned_vaddr_4_2 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  is_aligned_vaddr (Virtaddr va) 2 = true.
Proof.
  intro Hal.
  unfold is_aligned_vaddr in Hal |- *.
  apply Z.eqb_eq in Hal. apply Z.eqb_eq.
  rewrite uint_unsigned in Hal |- *.
  pose proof (bv_unsigned_in_range _ va) as Hr.
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg; [ | lia | lia ].
  apply Z.mod_divide in Hal; [ | lia ]. apply Z.mod_divide; [ lia | ].
  destruct Hal as [q Hq]. exists (2 * q). lia.
Qed.

(* ===================================================================== *)
(* 1. [u_Dfix] -- THE CELLS A U-MODE EXECUTE LEAVES ALONE.                *)
(*                                                                       *)
(* It is [u_Drw u u_Dro] minus [nextPC] (a jump), minus [tlb] (a fill)    *)
(* and minus the 31 GPRs (the result).  Spelled as a LIST for             *)
(* [UserFrame]'s reason: memberships come out by [vm_compute] on a        *)
(* [bool_decide], and the GPR exclusion -- the one fact that is NOT a     *)
(* computation, because an operand index is symbolic -- is [u_gpr_notin]  *)
(* below, off the SAME [NoDup] that makes the frame splittable.           *)
(* ===================================================================== *)

(* [UserFrame.u_rw_named] minus [nextPC] and [tlb] *)
Definition u_fix_named : list register :=
  [ (R_bitvector_64 PC : register); (hart_state : register);
    (cur_privilege : register); (R_bitvector_64 mstatus : register);
    (R_bitvector_64 scause : register); (R_bitvector_64 stval : register);
    (R_bitvector_64 sepc : register); (R_bitvector_64 minstret : register);
    (R_bool minstret_increment : register); (R_bitvector_64 mcycle : register);
    (R_bitvector_64 mtime : register); (R_bitvector_64 mip : register) ].

Definition u_fix_list : list register := u_fix_named ++ u_ro_list.

Definition u_Dfix : gset register := list_to_set u_fix_list.

Local Ltac u_fix := apply (bool_decide_unpack _); vm_compute; reflexivity.

Lemma u_fix_nodup : base.NoDup u_fix_list.
Proof. u_fix. Qed.

Lemma u_Dfix_sub : u_Dfix ⊆ u_Drw ∪ u_Dro.
Proof. u_fix. Qed.

Lemma u_fix_PC : (R_bitvector_64 PC : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_hart : (hart_state : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_priv : (cur_privilege : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mst : (R_bitvector_64 mstatus : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_scause : (R_bitvector_64 scause : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_stval : (R_bitvector_64 stval : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_sepc : (R_bitvector_64 sepc : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_ms : (R_bitvector_64 minstret : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mi : (R_bool minstret_increment : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_cy : (R_bitvector_64 mcycle : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_ti : (R_bitvector_64 mtime : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_ip : (R_bitvector_64 mip : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_misa : (R_bitvector_64 misa : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_sec : (R_bitvector_64 mseccfg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_pma : (pma_regions : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_htif : (htif_tohost_base : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_elp : (R_bitvector_1 elp : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_senv : (R_bitvector_64 senvcfg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mc : (R_bitvector_32 mcountinhibit : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_micfg : (R_bitvector_64 minstretcfg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_stvec : (R_bitvector_64 stvec : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mie : (R_bitvector_64 mie : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mdl : (R_bitvector_64 mideleg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_medl : (R_bitvector_64 medeleg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_menv : (R_bitvector_64 menvcfg : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_mste : (R_bitvector_64 mstateen0 : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_sste : (R_bitvector_32 sstateen0 : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_satp : (R_bitvector_64 satp : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_pcfg : (pmpcfg_n : register) ∈ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_paddr : (pmpaddr_n : register) ∈ u_Dfix.
Proof. u_fix. Qed.

(* THE THREE THAT ARE DELIBERATELY OUT. *)
Lemma u_fix_nPC : (R_bitvector_64 nextPC : register) ∉ u_Dfix.
Proof. u_fix. Qed.
Lemma u_fix_tlb : (tlb : register) ∉ u_Dfix.
Proof. u_fix. Qed.

(* [u_fix_named] sits inside [u_rw_named], which is what lets the GPR
   exclusion below borrow [u_rw_nodup]. *)
Lemma u_fix_named_sub (r : register) : r ∈ u_fix_named -> r ∈ u_rw_named.
Proof. rewrite /u_fix_named /u_rw_named !elem_of_list_In. cbn [In]. tauto. Qed.

(* ...and the GPRs.  This is the ONE exclusion a computation cannot do: an
   operand index arrives as [gpr_of_Z (uint i)] at a SYMBOLIC [i], so
   [register_beq] does not reduce.  It comes instead off [u_rw_nodup] --
   the same decidable [NoDup] that makes the writable frame splittable --
   plus the disjointness of the two halves ([u_disj]). *)
Lemma u_gpr_notin (i : Z) :
  1 <= i < 32 -> (R_bitvector_64 (gpr_of_Z i) : register) ∉ u_Dfix.
Proof.
  intros Hi Hin.
  pose proof (u_gpr_mem i Hi) as Hg.
  rewrite /u_Dfix elem_of_list_to_set /u_fix_list elem_of_app in Hin.
  destruct Hin as [Hnamed | Hro].
  - (* it would be one of the twelve named writable cells -- refuted by
       [u_rw_nodup], since [u_rw_list] is [u_rw_named ++ u_gpr_list] and the
       twelve are all in [u_rw_named] *)
    pose proof u_rw_nodup as Hnd.
    rewrite /u_rw_list in Hnd.
    (* stdpp's [NoDup_app], NOT [List.NoDup_app] -- the two share a short
       name and the wrong one is an introduction rule, so the [apply] fails
       with a type that prints almost identically. *)
    apply (proj1 (stdpp.list_relations.NoDup_app u_rw_named u_gpr_list)) in Hnd.
    destruct Hnd as (_ & Hdisj & _).
    apply (Hdisj _ (u_fix_named_sub _ Hnamed) Hg).
  - (* or a read-only cell -- refuted by [u_disj] *)
    apply (u_disj (R_bitvector_64 (gpr_of_Z i) : register)).
    + rewrite /u_Drw elem_of_list_to_set /u_rw_list elem_of_app. by right.
    + by rewrite /u_Dro elem_of_list_to_set.
Qed.

(* ===================================================================== *)
(* 2. THE REFERENCE STATE, AND THE LANDING MAP.                           *)
(* ===================================================================== *)

(* the state every U-mode model call is stated at *)
Definition u_state (rs : regstate) (mm : pamap) : mstate :=
  MState rs mm dev0_state.

Lemma u_state_sregs (rs : regstate) (mm : pamap) : (u_state rs mm).(sregs) = rs.
Proof. reflexivity. Qed.
Lemma u_state_mem (rs : regstate) (mm : pamap) : (u_state rs mm).(mem) = mm.
Proof. reflexivity. Qed.

(* [swp_hmrun_of_exec] hands back an EXISTENTIAL post map [mm'] pinned only
   by [mm' subseteq s'.(mem)] and [dom mm' = dom mm].  At the reference
   state that pins it COMPLETELY: [u_mem_step] says [dom s'.(mem)] is
   already [dom mm], and a submap with the full domain is the map. *)
Lemma u_map_eq (m1 m2 : pamap) :
  m1 ⊆ m2 -> (dom m1 : gset Arch.pa) = dom m2 -> m1 = m2.
Proof.
  intros Hsub Hdom. apply map_eq. intro a.
  destruct (m1 !! a) as [b|] eqn:H1.
  - rewrite H1. symmetry. exact (lookup_weaken m1 m2 a b H1 Hsub).
  - destruct (m2 !! a) as [b|] eqn:H2; [| by rewrite H1 H2].
    exfalso.
    assert (Ha : a ∈ (dom m2 : gset Arch.pa)) by (apply elem_of_dom; by exists b).
    rewrite <- Hdom in Ha. apply elem_of_dom in Ha. rewrite H1 in Ha.
    by destruct Ha.
Qed.

Lemma u_landing_map (P : uptd) (t t' : ptree) (mm mm' : pamap) (s' : mstate) :
  u_mem_wf P t mm ->
  u_mem_step P t t' mm s'.(mem) ->
  mm' ⊆ s'.(mem) ->
  (dom mm' : gset Arch.pa) = dom mm ->
  mm' = s'.(mem).
Proof.
  intros Hwf Hstep Hsub Hdom. apply (u_map_eq mm' s'.(mem) Hsub).
  rewrite Hdom. symmetry. exact (u_mem_step_dom P t t' mm s'.(mem) Hwf Hstep).
Qed.

(* ===================================================================== *)
(* 2b. THE PIN BUNDLE: what the arms used to READ OFF an Iris bundle.      *)
(*                                                                       *)
(* Under the old shape each arm took [hw_config] / [user_cfg] /           *)
(* [user_pt_inv] as separating-conjunction arguments and pulled the       *)
(* values it needed out of the interpretation with [reg_valid_dq].  A     *)
(* pure fact cannot do that, so the SAME values arrive as pins on the     *)
(* frame's file.  Nothing is added and nothing is lost -- these are       *)
(* literally the pure conjuncts of the three bundles, restated at [rs].   *)
(*                                                                       *)
(* THIS BUNDLE IS THE EXTENSION POINT.  If an arm turns out to need one   *)
(* more ambient pin, it goes HERE (and the tier's one producer supplies   *)
(* it from the bundle it already holds) rather than into the arm's own    *)
(* premise list -- which is what kept the old [arm_*] statements uniform  *)
(* enough for [UserTotalU]'s dispatch tables to be [lazymatch]-driven.    *)
(* ===================================================================== *)

(* the pure content of [RiscvFetchExec.hw_config] *)
Definition u_hw_pins (rs : regstate) : Prop :=
  register_lookup misa rs = MISA_C /\
  register_lookup mseccfg rs = (mword_of_int 0 : mword 64) /\
  register_lookup senvcfg rs = (mword_of_int 0 : mword 64) /\
  register_lookup htif_tohost_base rs = None /\
  pma_allows_all (register_lookup pma_regions rs) /\
  eq_vec (register_lookup elp rs) (landing_pad_bits_backwards LP_EXPECTED)
    = false.

(* the pure content of [UserExec.user_cfg]'s two state-enable pins.  Its
   other four cells ([stvec]/[mie]/[mideleg]/[medeleg]) are deliberately
   absent: no U-mode EXECUTE reads them.  Only the trap tower does, and the
   tower is the caller's [swp_hmrun_of_exec] at [mm := empty]. *)
Definition u_cfg_pins (rs : regstate) : Prop :=
  register_lookup mstateen0 rs = (mword_of_int 0 : mword 64) /\
  register_lookup sstateen0 rs = (mword_of_int 0 : mword 32).

(* the pure content of [SmodePte.pmp_config] plus the satp pin *)
Definition u_pt_pins (P : uptd) (rs : regstate) : Prop :=
  (exists usatp : mword 64,
     upt_satp_ok P usatp /\ register_lookup satp rs = usatp) /\
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rs) 0)) = TOR /\
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n rs) 0)
    = false /\
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n rs) 0))
    ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n rs) 0))
    ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n rs) 0))
    ('b"1") = true /\
  (ram_base + ram_size
     <= uint (vec_access_dec (register_lookup pmpaddr_n rs) 0) * 4)%Z.

Definition u_exec_pins (P : uptd) (t : ptree) (rs : regstate) : Prop :=
  u_hw_pins rs /\ u_cfg_pins rs /\ u_pt_pins P rs /\
  tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rs).

(* ------------------------------------------------------------------- *)
(* THE COMPOSABLE LANDING FACT.                                         *)
(*                                                                     *)
(* A ONE-walk composer says its landing file is [rs] or ONE             *)
(* [register_set tlb], and that shape does NOT compose: collapsing      *)
(* [register_set tlb v2 (register_set tlb v1 rs)] to                    *)
(* [register_set tlb v2 rs] is a pointwise equality of the record's     *)
(* field FUNCTION, i.e. functional extensionality, which this           *)
(* development does not assume.  [u_tlb_only] is what every consumer    *)
(* actually uses the disjunction FOR -- transporting the ambient pins   *)
(* by [irrelevant_register_set] -- it is implied by it, and it IS       *)
(* transitive.  Every composer that translates TWICE (the page-         *)
(* straddling data accesses, the 2-aligned straddling fetch) concludes  *)
(* this rather than the disjunction.                                    *)
(* ------------------------------------------------------------------- *)
Definition u_tlb_only (rs rs' : regstate) : Prop :=
  forall r : register, register_beq r (tlb : register) = false ->
    register_lookup r rs' = register_lookup r rs.

Lemma u_tlb_only_land (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) -> u_tlb_only rs rs'.
Proof.
  intros [-> | (tv & ->)] r Hne;
    [ reflexivity | apply irrelevant_register_set; exact Hne ].
Qed.

Lemma u_tlb_only_refl (rs : regstate) : u_tlb_only rs rs.
Proof. intros r _. reflexivity. Qed.

Lemma u_tlb_only_trans (rs rs1 rs2 : regstate) :
  u_tlb_only rs rs1 -> u_tlb_only rs1 rs2 -> u_tlb_only rs rs2.
Proof. intros H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* every ambient pin transports across such a landing, given the new tree's
   own TLB fact -- which is the one conjunct the landing cannot supply *)
Lemma u_exec_pins_only (P : uptd) (t t' : ptree) (rs rs' : regstate) :
  u_tlb_only rs rs' ->
  tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
  u_exec_pins P t rs -> u_exec_pins P t' rs'.
Proof.
  intros Tr Htlbok' (Hhw & Hcfgp & Hpt & _).
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hcfgp as (Hmst0 & Hsst0).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HX & HW & HR & Hcovp).
  split_and!; [ | | | exact Htlbok' ].
  - split_and!;
      [ rewrite (Tr misa ltac:(vm_compute; reflexivity)); exact Hmisa
      | rewrite (Tr mseccfg ltac:(vm_compute; reflexivity)); exact Hmseccfg
      | rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)); exact Hsenv
      | rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif
      | rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall
      | rewrite (Tr elp ltac:(vm_compute; reflexivity)); exact Help ].
  - split_and!;
      [ rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)); exact Hmst0
      | rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)); exact Hsst0 ].
  - split_and!;
      [ exists usatp; split;
          [ exact Hsatpok
          | rewrite (Tr satp ltac:(vm_compute; reflexivity)); exact Hsatp ]
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp ].
Qed.

(* ===================================================================== *)
(* 3. THE TWO TOTALITIES, PURE.                                           *)
(*                                                                       *)
(* [rsf] is the file the FETCH landed on (a filling walk does not land    *)
(* where it started), [mm] the map it landed on, [t] its tree.  The       *)
(* execute runs one tick later, at                                        *)
(*   [register_set nextPC (add_vec_int va n) rsf],                        *)
(* spelled LITERALLY here because that is what                            *)
(* [HartRunFull.run_fetch_base] / [run_fetch_rvc] spell -- a [Definition] *)
(* in between would be a conversion bomb (durable notes).                 *)
(* ===================================================================== *)

(* THE POSTCONDITION BODY, named.  Both totalities are "premises -> this",
   and every [finish_*] / [arm_*] of [UserTotalU] closes exactly this for ONE
   result shape -- so it is the memory arms' contract too, and it is named
   here rather than in [UserTotalU] so P4 can code against it without paying
   that file. *)
Definition base_post (P : uptd) (t : ptree) (mm : pamap) (rsf : regstate)
    (va : mword 64) (w : mword 32) : Prop :=
  exists (instr : instruction) (r : ExecutionResult) (s_x : mstate)
         (t' : ptree),
    (* DECODE.  Read-only, so it keeps its [goodb] route: the [exec] fact is
       the one the tier already proves, and [hval] is what
       [HartRunFull.run_fetch_base] asks for -- one [hval_of_goodb]. *)
    exec (ext_decode w) (u_state rsf mm) = Some (instr, u_state rsf mm) /\
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) instr rsf /\
    is_lpad_instruction instr = false /\
    (* EXECUTE, with its certificate, at the ticked file *)
    (exec (execute instr)
       (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
       = Some (r, s_x)
     /\ goodmb Du_r Du_w (execute instr)
          (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm = true
     \/ (exists other : instruction,
           exec (execute instr)
             (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
             = Some (ExecuteAs other,
                     u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
           /\ goodmb Du_r Du_w (execute instr)
                (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm
              = true
           /\ exec (execute other)
                (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
              = Some (r, s_x)
           /\ goodmb Du_r Du_w (execute other)
                (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm
              = true)) /\
    u_result_ok r /\
    match r with ExecuteAs _ => False | _ => True end /\
    (* THE POST-STATE *)
    reg_agree_on u_Dfix s_x.(sregs)
      (register_set nextPC (add_vec_int va 4) rsf) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb s_x.(sregs)) /\
    u_mem_step P t t' mm s_x.(mem).

(* ...and the compressed twin, at [va+2] over [ext_decode_compressed], with
   the [Ext_Zca] gate riding as the extra [exec] conjunct it always was. *)
Definition rvc_post (P : uptd) (t : ptree) (mm : pamap) (rsf : regstate)
    (va : mword 64) (h : mword 16) : Prop :=
  exists (instr : instruction) (r : ExecutionResult) (s_x : mstate)
         (t' : ptree),
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (instr, u_state rsf mm) /\
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf /\
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) /\
    (exec (execute instr)
       (u_state (register_set nextPC (add_vec_int va 2) rsf) mm)
       = Some (r, s_x)
     /\ goodmb Du_r Du_w (execute instr)
          (u_state (register_set nextPC (add_vec_int va 2) rsf) mm) mm = true
     \/ (exists other : instruction,
           exec (execute instr)
             (u_state (register_set nextPC (add_vec_int va 2) rsf) mm)
             = Some (ExecuteAs other,
                     u_state (register_set nextPC (add_vec_int va 2) rsf) mm)
           /\ goodmb Du_r Du_w (execute instr)
                (u_state (register_set nextPC (add_vec_int va 2) rsf) mm) mm
              = true
           /\ exec (execute other)
                (u_state (register_set nextPC (add_vec_int va 2) rsf) mm)
              = Some (r, s_x)
           /\ goodmb Du_r Du_w (execute other)
                (u_state (register_set nextPC (add_vec_int va 2) rsf) mm) mm
              = true)) /\
    u_result_ok r /\
    match r with ExecuteAs _ => False | _ => True end /\
    reg_agree_on u_Dfix s_x.(sregs)
      (register_set nextPC (add_vec_int va 2) rsf) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb s_x.(sregs)) /\
    u_mem_step P t t' mm s_x.(mem).

(* 5-way BASE totality: decode w -> instr; execute (possibly one base
   ExecuteAs redirect, e.g. SINVAL_VMA) -> r with u_result_ok r. *)
Definition base_exec_total_u (P : uptd) (va : mword 64) (mi : bool) : Prop :=
  forall (w : mword 32) (rsf : regstate) (t : ptree) (mm : pamap),
    post_fetch_cfg (u_state rsf mm) va mi ->
    u_exec_pins P t rsf ->
    u_mem_wf P t mm ->
    base_post P t mm rsf va w.

(* 5-way RVC totality: decode_compressed h -> instr; execute either DIRECTLY
   (C_NOP/C_NTL/ZCMOP/C_NOT/C_ZEXT_B/C_ILLEGAL) or via one ExecuteAs
   redirect -> r with u_result_ok r. *)
Definition rvc_exec_total_u (P : uptd) (va : mword 64) (mi : bool) : Prop :=
  forall (h : mword 16) (rsf : regstate) (t : ptree) (mm : pamap),
    post_fetch_cfg (u_state rsf mm) va mi ->
    u_exec_pins P t rsf ->
    u_mem_wf P t mm ->
    rvc_post P t mm rsf va h.

(* ===================================================================== *)
(* 4. THE THREE POST-STATE SHAPES, once.                                  *)
(*                                                                       *)
(* Every arm's [reg_agree_on u_Dfix] obligation is one of these: the      *)
(* execute changed nothing, wrote ONE gpr, or wrote nextPC.  Stating them *)
(* here keeps the ~200 [finish_*] / [arm_*] proofs one [apply] long.      *)
(* ===================================================================== *)

Lemma u_fix_refl (rs : regstate) : reg_agree_on u_Dfix rs rs.
Proof. intros r _; reflexivity. Qed.

Lemma u_fix_gpr (rs : regstate) (ird : mword 5) (v : mword 64) :
  uint ird <> 0 ->
  reg_agree_on u_Dfix
    (register_set (R_bitvector_64 (gpr_of_Z (uint ird))) v rs) rs.
Proof.
  intros Hne r Hr.
  apply irrelevant_register_set.
  destruct (register_beq r (R_bitvector_64 (gpr_of_Z (uint ird)))) eqn:Hb;
    [| reflexivity].
  exfalso. apply register_beq_true in Hb. subst r.
  apply (u_gpr_notin (uint ird)); [| exact Hr].
  pose proof (uint5_lt ird). lia.
Qed.

Lemma u_fix_npc (rs : regstate) (v : mword 64) :
  reg_agree_on u_Dfix (register_set (R_bitvector_64 nextPC) v rs) rs.
Proof.
  intros r Hr. apply irrelevant_register_set.
  destruct (register_beq r (R_bitvector_64 nextPC)) eqn:Hb; [| reflexivity].
  exfalso. apply register_beq_true in Hb. subst r. exact (u_fix_nPC Hr).
Qed.

Lemma u_fix_trans (rs1 rs2 rs3 : regstate) :
  reg_agree_on u_Dfix rs1 rs2 -> reg_agree_on u_Dfix rs2 rs3 ->
  reg_agree_on u_Dfix rs1 rs3.
Proof. intros H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.
