(* UserTranslate.v (SLIMMED by the ptree port) -- the translateAddr layer over [upt_inv] (UserPt.v):
   worklist item 1 of the user-execution development (see CLAUDE.md).

   GOAL (the one caller-facing interface, absorbing TLB hit-vs-miss): for an
   access [acc] at virtual address [va] from a user-phase machine state, the
   model's [translateAddr (Virtaddr va) acc] takes exactly one of

     - Ok  : [va]'s vpn is mapped and the leaf check passes.  Output pa =
             [u_walk_pa (um_pte0 e) va] (covered by [u_data] via
             [upt_data_cov]); output state = the input with the tlb slot
             holding [um_tlb_ent vpn e] -- UNIFORMLY presented as the filled
             vector (on a hit the fill is the identity), so callers never
             split on hit/miss ([upt_tlb_ok_fill] re-seals).  No A/D update
             ever fires: the page tables carry A/D preset, so every walk
             takes [update_PTE_Bits = None] (this build is Svadu, ADUE=1,
             but with A/D preset the write-back path is never entered);
     - Err : non-canonical va, unmapped vpn ([upt_unmapped_walk_fault]), or
             leaf check denied ([upt_denied_walk_fault]) -- the access
             page-faults with NO state change, feeding the trap arm of the
             step obligation.

   This file currently holds the first pure bricks (the mode dispatch that
   every translateAddr reduction begins with); the per-access wrappers land
   on top of CommonWalk's [exec_translate_walk_user{,_nomatch,_err}].       *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec.
Require Import WpGprCsrwB.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The mode dispatch: at User with SXL = 64 and satp.Mode = Sv39, the   *)
(* MMU is in Sv39 -- the head of every translateAddr reduction.            *)
(* ===================================================================== *)

Lemma exec_get_satp_39 (satp0 : mword 64) s :
  register_lookup satp s.(sregs) = satp0 ->
  exec (get_satp 39) s = Some (autocast (T := mword) satp0, s).
Proof.
  intro Hsatp.
  unfold get_satp.
  assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                        "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
  { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
      by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  change (Z.eqb 39 32) with false. cbn match.
  unfold autocast_m.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
  rewrite Hsatp. apply exec_returnm.
Qed.

Lemma exec_satp_mode_width_39 s :
  exec (satp_mode_width_forwards Sv39) s = Some (39, s).
Proof. cbn. apply exec_returnm. Qed.

Lemma exec_assert_vmem431 s :
  exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s).
Proof.
  replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  unfold assert_exp'. cbn match. apply exec_returnm.
Qed.

Lemma exec_translationMode_U_sv39 (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  exec (translationMode User) s = Some (Sv39, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  change (generic_eq User Machine) with false. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  assert (Hae : exec (Defs.assert_exp' (Z.geb xlen 64) "sys/vmem.sail:254.25-254.26") s
                = Some (eq_refl, s)).
  { replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hmb : exec L s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmb).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

(* The upt-record translateAddr wrappers, the um_tlb_ent hit lemmas and
   the pre-ADUE fetch heads that used to follow were superseded by the
   ptree layer: the privilege-generic fronts live in PtTreeAdue.v §5, the
   U-mode Ok/fault instances in UserPtTree.v.  Only the pure §1 mode-
   dispatch bricks above (notably [exec_translationMode_U_sv39]) remain
   live -- consumed by UserPtTree.v.                                     *)
