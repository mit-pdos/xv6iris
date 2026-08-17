(* WpIntrCore.v -- infrastructure for the INTERRUPT-SAFETY capstone: executing
   one S-mode instruction with sstatus.SIE = 1 and stvec -> kernelvec.

   Contents:
   §1  symbolic-mstatus bit toolkit: Z.testbit-level reasoning about
       subrange/update_subrange towers over an ABSTRACT mstatus (every prior
       chain had a concrete mstatus and used vm_compute; the interrupt
       round-trip changes mstatus, so the Löb invariant must carry a symbolic
       one).  [trap_ms] is the S-mode trap's mstatus tower; the lemmas here
       bridge its bits to wp_kernelvec_hit's premises and prove the headline
       fact that the trap+SRET round trip RESTORES SIE = 1.
   §2  dispatchInterrupt determinism: with the S extension on and
       mie & ~mideleg = 0 (xv6 delegates everything it enables), the dispatch
       outcome in Supervisor mode is the FUNCTION [s_dispatch] of
       mip / sig_meip / sig_seip / mie / mideleg / mstatus.SIE --
       [exec_dispatchInterrupt_S_reduce] (the transient Iris bridge is
       [dispatch_S_transient], WpIntrInv.v).
   §3  the S-mode interrupt TRAP reduction: trap_handler Supervisor
       (Interrupt i) writes scause / mstatus(SPIE,SIE,SPP,SPELP) / stval /
       sepc / cur_privilege and lands on stvec's direct-mode base
       ([exec_trap_handler_S_intr], [exec_handle_interrupt_S]).
   §4  the step-level engine: [exec_riscv_step_interrupt] threads the
       try_step wrapper around the Step_Pending_Interrupt arm (NO fetch, NO
       retire, minstret NOT bumped), and [wp_exec_step_interrupt_inv] is its
       minstret_inv WP rule.  The continuation is handed back UNDER A LATER
       (the step consumed one), which is exactly what the Löb capstone needs
       to strip the ▷ off its induction hypothesis.
   §7  small capstone helpers ([elp_no_lp], [s_dispatch_Some_S]).

   The SIE=1 instruction step engine itself lives in WpSmodeIntr.v
   ([wp_instr_s_intr], over WpIntrInv.v's interrupt-absorbing
   [wp_exec_step_intr]); the old pinned-cell §5b/§6 engines are gone.   *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv.
Require Import WpDecode ExecCommon.
(* the swp layer, for the footprinted twins of the dispatch chain below *)
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb
        HartMFrame WpDecodeBridge WpMmodeCsrSwp.
Require Import WpGprMret.
Require Import SmodeCore.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §2 dispatchInterrupt determinism in Supervisor mode.                   *)
(* ===================================================================== *)

(* The platform-derived external-interrupt bits (read_mip's contribution
   beyond the [mip] register): MEI from sig_meip, SEI from sig_seip (S on). *)
Definition s_ext_ip (meip seip : mword 1) : mword 64 :=
  _update_Minterrupts_SEI (_update_Minterrupts_MEI (Mk_Minterrupts (zeros' 64)) meip) seip.

Definition s_mip_bits (mip_v : mword 64) (meip seip : mword 1) : mword 64 :=
  Mk_Minterrupts (or_vec mip_v (s_ext_ip meip seip)).

(* The S-destined pending-and-enabled set. *)
Definition s_pending (mip_v : mword 64) (meip seip : mword 1) (mie_v mdv : mword 64) : mword 64 :=
  and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v mdv).

(* The dispatch outcome as a FUNCTION of the pinned cells (Supervisor mode,
   mie & ~mideleg = 0 so nothing is ever M-destined). *)
Definition s_dispatch (mip_v : mword 64) (meip seip : mword 1) (mie_v mdv ms : mword 64)
    : option (InterruptType * Privilege) :=
  if andb (eq_vec (_get_Mstatus_SIE ms) ('b"1"))
          (neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64))
  then match findPendingInterrupt (s_pending mip_v meip seip mie_v mdv) with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Lemma exec_external_interrupts_pending_reduce (s : mstate) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  exec (external_interrupts_pending tt) s = Some (s_ext_ip meip seip, s).
Proof.
  intros HES Hmeip Hseip.
  unfold external_interrupts_pending.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)).
  rewrite Hmeip Hseip. apply exec_returnm.
Qed.

Lemma exec_read_mip_reduce (s : mstate) (mip_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  exec (read_mip IncludePlatformInterrupts) s = Some (s_mip_bits mip_v meip seip, s).
Proof.
  intros HES Hmip Hmeip Hseip.
  unfold read_mip. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_external_interrupts_pending_reduce s meip seip HES Hmeip Hseip)).
  rewrite Hmip. apply exec_returnm.
Qed.


(* ===================================================================== *)
(* THE SAME CHAIN AT THE SWP LAYER.                                       *)
(*                                                                       *)
(* THE PLIC WIRES ARE ∀-BOUND, and that is the point rather than a        *)
(* concession.  [sig_meip] / [sig_seip] are ordinary registers whose      *)
(* points-to's live in [WireInv.wire_inv], owned exclusively per CPU.  An *)
(* invariant opens around ONE atomic step and this dispatch is many nodes, *)
(* so no caller can hold them across it -- and none should want to: under  *)
(* per-node stepping another hart may move a wire BETWEEN these nodes,     *)
(* which is exactly why the cycle rule offers both arms.  So the wire      *)
(* reads are OFF-FRAME reads ([swp_read_reg_any], which needs no ownership *)
(* at all), they peel to a ∀-binder, and the answer is EXISTENTIAL in      *)
(* their values.                                                          *)
(*                                                                       *)
(* This is also the one stretch of the S-mode path the [goodb] bridge      *)
(* cannot carry: [getPendingSet] is event-free, but [hval_of_goodb]        *)
(* requires every certified read to be IN THE FOOTPRINT, and the wires are *)
(* precisely the registers that cannot be.  Hence a hand walk, mirroring   *)
(* the exec proofs above node for node.                                    *)
(* ===================================================================== *)
Section SwpDispatch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [goodb] on a [returnm] is [true], but only once the [returnm] is
     unfolded -- name it rather than fighting [cbn] at each use. *)
  Lemma goodb_returnm (Db : register -> bool) {E X : Type} (x : X) (s : mstate) :
    goodb Db (Defs.returnm (E := E) x) s = true.
  Proof. reflexivity. Qed.

  Lemma swp_external_interrupts_pending_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) :
    Drw ## Dro ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (external_interrupts_pending tt)
      (fun v => ∃ meip seip : mword 1, ⌜v = s_ext_ip meip seip⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDb Hag HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold external_interrupts_pending.
    (* the FIRST wire: nobody owns it, so it peels to a binder *)
    iApply (swp_bind_use (Defs.read_reg sig_meip) _ _ _ with "[] [-]").
    { iApply (swp_read_reg_any sig_meip (fun _ => True%I) with "Hcert").
      by iIntros (v). }
    iIntros (meip) "_".
    iApply (swp_bind_use (currentlyEnabled Ext_S) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag HESg HES)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    (* ...and the second *)
    iApply (swp_bind_use (Defs.read_reg sig_seip) _ _ _ with "[] [-]").
    { iApply (swp_read_reg_any sig_seip (fun _ => True%I) with "Hcert").
      by iIntros (v). }
    iIntros (seip) "_".
    iApply swp_ret. iExists meip, seip. unfold s_ext_ip. by iFrame.
  Qed.


  Lemma swp_read_mip_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (mip_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    register_lookup mip rs = mip_v ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (read_mip IncludePlatformInterrupts)
      (fun v => ∃ meip seip : mword 1, ⌜v = s_mip_bits mip_v meip seip⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmip Hmip HDb Hag HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold read_mip. cbn match.
    iApply (swp_bind_use (Defs.read_reg mip) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmip
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hmip.
    iApply (swp_bind_use (external_interrupts_pending tt) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_external_interrupts_pending_S Drw Dro Df rs dst Db Hdisj
                HDb Hag HES HESg with "Hcert Hrw Hro"). }
    iIntros (v). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
    iApply swp_ret. iExists meip, seip. unfold s_mip_bits. by iFrame.
  Qed.

  (* [getPendingSet Supervisor], SIE left symbolic and the M-destined set
     dead ([mie & ~mideleg = 0]) -- the statement
     [exec_getPendingSet_S_reduce] proves, with the wires existential.

     THE TWO BOOLEAN BLOCKS ARE BRIDGED, NOT PEELED: their operands are
     [returnM] applications, so [mbind_ret]'s [Interface.Ret] LHS does not
     match them, and widening the [cbn] to fix that would unfold [Defs.bind]
     across the goal.  Each reads only mstatus, which is framed, so each goes
     across as its exec fact (copied from the exec proof) plus a certificate.
     Both are NESTED two deep, so the inner bind's facts come first. *)
  Lemma swp_getPendingSet_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (mip_v mie_v mdv_v ms_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    Db mstatus = true ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    register_lookup mstatus dst.(sregs) = ms_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (getPendingSet Supervisor)
      (fun v => ∃ meip seip : mword 1,
                ⌜v = (if andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                              (neq_vec (s_pending mip_v meip seip mie_v mdv_v)
                                 (zeros' 64))
                      then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
                      else None)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmip HDmie HDmdl HDbmst Hmip Hmie Hmdl Hms Hmm HDb Hag
      HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold getPendingSet.
    iApply (swp_bind_use (currentlyEnabled Ext_S) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag HESg HES)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_bind_use (Defs.read_reg mideleg) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmdl
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (read_mip IncludePlatformInterrupts) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_mip_S Drw Dro Df rs dst Db mip_v Hdisj HDmip Hmip
                HDb Hag HES HESg with "Hcert Hrw Hro"). }
    iIntros (v). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg mie) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmie
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (Defs.read_reg mie) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmie
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* ---- the mIE block.  At Supervisor the and_boolM short-circuits on
       [generic_eq Supervisor Machine = false], so mstatus is never read. ---- *)
    match goal with |- context[Defs.or_boolM ?A ?B] =>
      set (Amie := Defs.or_boolM A B) end.
    assert (HmieAE : forall K : bool -> M bool,
              exec (Defs.bind (Defs.returnm (generic_eq Supervisor Machine)) K)
                dst = exec (K false) dst).
    { intro K.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_returnM (generic_eq Supervisor Machine) dst)).
      reflexivity. }
    assert (HmieE : exec Amie dst = Some (true, dst)).
    { subst Amie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- exec (Defs.bind ?A ?B) _ = _ =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HmieAE _); reflexivity
        | rewrite (exec_bind_Some _ _ _ _ _ HinE) ] end.
      cbn match.
      change (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User))
        with true.
      apply exec_returnm. }
    assert (HmieG : goodb Db Amie dst = true).
    { subst Amie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- goodb _ (Defs.bind ?A ?B) _ = true =>
        assert (HinE : exec A dst = Some (false, dst));
        [ rewrite (HmieAE _); reflexivity | ];
        assert (HinG : goodb Db A dst = true);
        [ rewrite (goodb_bind Db _ _ dst (generic_eq Supervisor Machine)
                     (goodb_returnm Db _ dst) ltac:(apply exec_returnm));
          apply (goodb_returnm Db _ dst)
        | rewrite (goodb_bind Db A B dst false HinG HinE) ] end.
      apply (goodb_returnm Db _ dst). }
    iApply (swp_bind_use Amie _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs Amie true Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw Amie dst rs true
                   HDb Hag HmieG HmieE)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* ---- the sIE block.  This one DOES read mstatus. ---- *)
    match goal with |- context[Defs.or_boolM ?A ?B] =>
      set (Asie := Defs.or_boolM A B) end.
    assert (HsieInE : forall K : bool -> M bool,
              exec (Defs.bind (Defs.returnm (generic_eq Supervisor Supervisor)) K)
                dst = exec (K true) dst).
    { intro K.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_returnM (generic_eq Supervisor Supervisor) dst)).
      reflexivity. }
    assert (HsieE : exec Asie dst
                    = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), dst)).
    { subst Asie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- exec (Defs.bind ?A ?B) _ = _ =>
        assert (HinE : exec A dst
                       = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), dst));
        [ rewrite (HsieInE _);
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus dst));
          rewrite Hms; apply exec_returnm
        | rewrite (exec_bind_Some _ _ _ _ _ HinE) ] end.
      destruct (eq_vec (_get_Mstatus_SIE ms_v) ('b"1")).
      - reflexivity.
      - change (generic_eq Supervisor User) with false. apply exec_returnm. }
    assert (HsieG : goodb Db Asie dst = true).
    { subst Asie. unfold Defs.or_boolM, Defs.and_boolM.
      match goal with |- goodb _ (Defs.bind ?A ?B) _ = true =>
        assert (HinE : exec A dst
                       = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), dst));
        [ rewrite (HsieInE _);
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus dst));
          rewrite Hms; apply exec_returnm | ];
        assert (HinG : goodb Db A dst = true);
        [ rewrite (goodb_bind Db _ _ dst (generic_eq Supervisor Supervisor)
                     (goodb_returnm Db _ dst) ltac:(apply exec_returnm));
          change (generic_eq Supervisor Supervisor) with true; cbn match;
          rewrite (goodb_bind Db (Defs.read_reg mstatus) _ dst
                     (register_lookup mstatus dst.(sregs))
                     ltac:(cbn [goodb Defs.read_reg read_reg];
                           by rewrite HDbmst)
                     ltac:(apply exec_read_reg));
          apply (goodb_returnm Db _ dst)
        | rewrite (goodb_bind Db A B dst
                     (eq_vec (_get_Mstatus_SIE ms_v) ('b"1")) HinG HinE) ] end.
      destruct (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"));
        apply (goodb_returnm Db _ dst). }
    iApply (swp_bind_use Asie _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs Asie _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw Asie dst rs _
                   HDb Hag HsieG HsieE)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite Hmie Hmdl Hmm.
    rewrite and_vec_zeros64_r.
    replace (neq_vec (zeros' 64 : mword 64) (zeros' 64)) with false
      by (vm_compute; reflexivity).
    rewrite andb_false_r.
    iApply swp_ret. iExists meip, seip.
    unfold s_pending, s_mip_bits. by iFrame.
  Qed.


  (* ==================================================================== *)
  (* THE S-MODE DISPATCH.  This is [HartRunGen]'s other obligation, and the *)
  (* wires make its answer genuinely the machine's choice: existential in    *)
  (* [meip] / [seip], which is exactly the shape                            *)
  (* [swp_run_hart_active_gen]'s match-shaped premise consumes.             *)
  (* ==================================================================== *)
  Lemma swp_dispatchInterrupt_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (dst : mstate)
      (Db : register -> bool) (mip_v mie_v mdv_v ms_v : mword 64) :
    Drw ## Dro ->
    (mip : register) ∈ Drw ∪ Dro ->
    (mie : register) ∈ Drw ∪ Dro ->
    (mideleg : register) ∈ Drw ∪ Dro ->
    Db mstatus = true ->
    register_lookup mip rs = mip_v ->
    register_lookup mie rs = mie_v ->
    register_lookup mideleg rs = mdv_v ->
    register_lookup mstatus dst.(sregs) = ms_v ->
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    exec (currentlyEnabled Ext_S) dst = Some (true, dst) ->
    goodb Db (currentlyEnabled Ext_S) dst = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (dispatchInterrupt Supervisor)
      (fun r => ∃ meip seip : mword 1,
                ⌜r = s_dispatch mip_v meip seip mie_v mdv_v ms_v⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmip HDmie HDmdl HDbmst Hmip Hmie Hmdl Hms Hmm HDb Hag
      HES HESg.
    iIntros "#Hcert Hrw Hro".
    unfold dispatchInterrupt.
    iApply (swp_bind_use (getPendingSet Supervisor) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_getPendingSet_S Drw Dro Df rs dst Db mip_v mie_v mdv_v ms_v
                Hdisj HDmip HDmie HDmdl HDbmst Hmip Hmie Hmdl Hms Hmm HDb Hag
                HES HESg with "Hcert Hrw Hro"). }
    iIntros (v). iDestruct 1 as (meip seip) "(-> & Hrw & Hro)".
    iApply swp_ret. iExists meip, seip. unfold s_dispatch.
    destruct (andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                   (neq_vec (s_pending mip_v meip seip mie_v mdv_v)
                      (zeros' 64))).
    - cbn match.
      destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
        by iFrame.
    - cbn match. by iFrame.
  Qed.

End SwpDispatch.

(* getPendingSet Supervisor, SIE left SYMBOLIC: the M-destined set is dead
   (mie & ~mideleg = 0), and the outcome is the [s_dispatch]-shaped test. *)
Lemma exec_getPendingSet_S_reduce (s : mstate)
    (mip_v mie_v mdv_v ms_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  register_lookup mstatus s.(sregs) = ms_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (getPendingSet Supervisor) s
    = Some ((if andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                     (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64))
             then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
             else None), s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm.
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq Supervisor Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Machine) s)).
      change (generic_eq Supervisor Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)) with true.
    apply exec_returnm. }
  assert (HsIE : exec (or_boolM
            (and_boolM (returnM (generic_eq Supervisor Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Supervisor User))) s
                = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Supervisor) s)).
      change (generic_eq Supervisor Supervisor) with true. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
      rewrite Hms. apply exec_returnm. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    destruct (eq_vec (_get_Mstatus_SIE ms_v) ('b"1")).
    - reflexivity.
    - change (generic_eq Supervisor User) with false. apply exec_returnm. }
  (* [getPendingSet] reads mideleg only under [currentlyEnabled Ext_S] now, and
     reads mie twice; the guard and its assert are gone. *)
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIE).
  rewrite Hmie Hmdl Hmm.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq.
  rewrite andb_false_r.
  unfold s_pending, s_mip_bits.
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_S_reduce (s : mstate)
    (mip_v mie_v mdv_v ms_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  register_lookup mstatus s.(sregs) = ms_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt Supervisor) s
    = Some (s_dispatch mip_v meip seip mie_v mdv_v ms_v, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm.
  unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_getPendingSet_S_reduce s mip_v mie_v mdv_v ms_v meip seip
               HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm)).
  unfold s_dispatch.
  destruct (andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                 (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64))).
  - cbn match. destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
      apply exec_returnm.
  - cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §2b WHICH CAUSE CAN BE DELIVERED: the dispatch is CONFINED by [mie].    *)
(*                                                                        *)
(* [IntrDefs.sconf] pins [mie] at [MIE_S] = 0x220 (bits 5 and 9), because  *)
(* xv6's [start] writes [sie] exactly once and never writes [mie] at all,  *)
(* and [mie] is 0 at reset.  [s_pending] is MASKED by [mie], so at that    *)
(* value no bit outside {5, 9} can ever be pending -- whatever [mip] holds *)
(* (it lives in [clock_inv] and may be rewritten by a tick at every step,  *)
(* so nothing can be pinned about it) and whatever [mideleg] holds.        *)
(* [findPendingInterrupt] therefore can only answer S-timer or S-external, *)
(* which is exactly the pair [devintr] recognises -- and THAT is what      *)
(* keeps kerneltrap's [printk] arm dead, hence printk-general out of the   *)
(* handler's cone.  See claude-notes/completed/kerneltrap.md.               *)
(*                                                                        *)
(* The confinement is proved bit by bit, and THE BIT LEMMA CANNOT BE       *)
(* GENERIC IN THE BIT INDEX: [subrange_vec_dec v k k : mword (k - k + 1)]  *)
(* is convertible to [mword 1] only when [k] is a LITERAL, so a [forall k] *)
(* statement does not even typecheck.  Hence one [Ltac] and five concrete  *)
(* instances -- one per non-S bit [findPendingInterrupt] tests before it    *)
(* reaches the two S ones.                                                 *)
(* ===================================================================== *)

Lemma mie_s_unsigned : bv_unsigned MIE_S = 0x220.
Proof. vm_compute. reflexivity. Qed.

(* a 1-bit word whose value is 0 is not '1' -- the shape every
   [findPendingInterrupt] test is in. *)
Lemma eqvec1_false (x : mword 1) : bv_unsigned x = 0 -> eq_vec x ('b"1") = false.
Proof.
  intros H. apply not_true_is_false. rewrite eq_vec_true_iff. intros ->.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  rewrite H1 in H. discriminate.
Qed.

(* a bit the MIE_S mask does not enable reads as 0, whatever the other two
   operands are.  [Z.land] is commutative-associative here only up to the
   [s_pending] spelling, so the mask sits in the middle exactly as
   [s_pending_unsigned] leaves it. *)
Lemma bit_zero_of_mask (a b k : Z) :
  0 <= k -> Z.testbit 0x220 k = false ->
  Z.land a (Z.land 0x220 b) / 2 ^ k mod 2 = 0.
Proof.
  intros Hk Hm.
  rewrite (z_bit_div (Z.land a (Z.land 0x220 b)) k ltac:(lia)).
  rewrite !Z.land_spec. rewrite Hm. rewrite andb_false_l. rewrite andb_false_r.
  reflexivity.
Qed.

(* the pending set's unsigned value, with the pinned mask made a literal *)
Lemma s_pending_unsigned (mip_v mdv : mword 64) (meip seip : mword 1) :
  bv_unsigned (s_pending mip_v meip seip MIE_S mdv)
  = Z.land (bv_unsigned (s_mip_bits mip_v meip seip)) (Z.land 0x220 (bv_unsigned mdv)).
Proof.
  unfold s_pending.
  rewrite !and_vec64_unsigned. rewrite mie_s_unsigned. reflexivity.
Qed.

Ltac pend_bit k :=
  apply eqvec1_false;
  unfold Mk_Minterrupts, _get_Minterrupts_MEI, _get_Minterrupts_MSI,
         _get_Minterrupts_MTI, _get_Minterrupts_SSI, _get_Minterrupts_LCOFI;
  match goal with
  | |- bv_unsigned (subrange_vec_dec ?v _ _) = 0 =>
      let H := fresh "Hb" in
      assert (H : bv_unsigned (subrange_vec_dec v k k : mword 1)
                  = bv_unsigned v / 2 ^ k mod 2)
        by (apply (subrange_dec_unsigned v k k (2 ^ k) 2);
            [lia | lia | reflexivity | reflexivity]);
      rewrite H
  end;
  rewrite s_pending_unsigned;
  apply bit_zero_of_mask; [lia | vm_compute; reflexivity].

Section PendBits.
  Context (mip_v mdv : mword 64) (meip seip : mword 1).
  Let p := s_pending mip_v meip seip MIE_S mdv.

  Lemma pend_MEI : eq_vec (_get_Minterrupts_MEI (Mk_Minterrupts p)) ('b"1") = false.
  Proof. unfold p. pend_bit 11. Qed.
  Lemma pend_MSI : eq_vec (_get_Minterrupts_MSI (Mk_Minterrupts p)) ('b"1") = false.
  Proof. unfold p. pend_bit 3. Qed.
  Lemma pend_MTI : eq_vec (_get_Minterrupts_MTI (Mk_Minterrupts p)) ('b"1") = false.
  Proof. unfold p. pend_bit 7. Qed.
  Lemma pend_SSI : eq_vec (_get_Minterrupts_SSI (Mk_Minterrupts p)) ('b"1") = false.
  Proof. unfold p. pend_bit 1. Qed.
  Lemma pend_LCOFI : eq_vec (_get_Minterrupts_LCOFI (Mk_Minterrupts p)) ('b"1") = false.
  Proof. unfold p. pend_bit 13. Qed.
End PendBits.

(* THE CONFINEMENT.  Note the constructor names carry the [I_] prefix. *)
Lemma s_dispatch_MIE_S (mip_v mdv ms : mword 64) (meip seip : mword 1)
    (i : InterruptType) (pr : Privilege) :
  s_dispatch mip_v meip seip MIE_S mdv ms = Some (i, pr) ->
  i = I_S_Timer \/ i = I_S_External.
Proof.
  unfold s_dispatch.
  destruct (andb _ _); [| discriminate].
  unfold findPendingInterrupt. cbv zeta.
  rewrite pend_MEI. rewrite pend_MSI. rewrite pend_MTI.
  destruct (eq_vec (_get_Minterrupts_SEI _) ('b"1")).
  - cbn match. intros H. right. congruence.
  - rewrite pend_SSI.
    destruct (eq_vec (_get_Minterrupts_STI _) ('b"1")).
    + cbn match. intros H. left. congruence.
    + rewrite pend_LCOFI. cbn match. discriminate.
Qed.

(* ===================================================================== *)
(* §3 The S-mode interrupt trap reduction.                                *)
(* ===================================================================== *)


(* stvec's direct-mode target. *)
Definition stvec_base (v : mword 64) : mword 64 :=
  concat_vec (_get_Mtvec_Base v) ('b"00").




(* track_trap Supervisor: reads + callbacks only, any state. *)
Lemma exec_track_trap_S (is_i : bool) (cause : mword 6) s :
  exec (track_trap Supervisor is_i cause) s = Some (tt, s).
Proof.
  unfold track_trap.
  erewrite exec_bind_Some. 2: apply (exec_read_reg mstatus s).
  cbn beta.
  (* the whole callback chain (long_csr / scause / stval / sepc reads +
     callbacks) is read-only and computes away by conversion *)
  erewrite exec_bind0_Some.
  2: eapply (exec_long_csr_write_mstatus (register_lookup mstatus s.(sregs)) s).
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

(* lookup through a set_reg tower *)
Ltac lk :=
  rewrite ?sregs_set_reg;
  repeat (first [ rewrite register_lookup_set
                | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ]).

Section TrapReduce.
  Context (s : mstate) (i : InterruptType) (pc0 : mword 64).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hms : register_lookup mstatus s.(sregs) = ms_v.
  Hypothesis Hsc : register_lookup scause s.(sregs) = sc_old.
  Hypothesis Hstvec : register_lookup stvec s.(sregs) = stvec_v.
  Hypothesis Help : register_lookup elp s.(sregs) = elp_v.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  Hypothesis Hpc : register_lookup PC s.(sregs) = pc0.

  (* the model's exact write order *)
  Let ms_e := update_subrange_vec_dec ms_v 23 23 elp_v.
  Let s1 := set_reg s mstatus ms_e.
  (* the zicfilp epilogue resets elp (value-identical: elp is pinned to
     NO_LP_EXPECTED by hw_config; the Iris side absorbs this write) *)
  Let s1e := set_reg s1 elp (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let c1 := update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
              (bool_to_bit (trapCause_is_interrupt (Interrupt i))).
  Let s2 := set_reg s1e scause c1.
  Let c2 := update_subrange_vec_dec c1 (64 - 2) 0
              (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i))).
  Let s3 := set_reg s2 scause c2.
  Let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e).
  Let s4 := set_reg s3 mstatus ms_a.
  Let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0").
  Let s5 := set_reg s4 mstatus ms_b.
  Let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"1").
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (zeros' 64).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_S_intr :
    exec (trap_handler Supervisor (Interrupt i) pc0 None None) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold trap_handler.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt)) with false.
    cbn match.
    assert (HZ : exec (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s = Some (true, s))
      by apply (exec_hartSupports_Zicfilp s).
    rewrite (exec_bind_Some _ _ _ _ _ HZ). cbn beta. cbn match.
    assert (HZP : exec (zicfilp_preserve_elp_on_trap Supervisor) s = Some (tt, s1e)).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- exec (Defs.bind0 ?A _) _ = _ =>
        assert (HARM : exec A s = Some (tt, s1)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help.
        apply exec_write_reg. }
      rewrite (exec_bind0_Some _ _ _ _ _ HARM).
      unfold reset_elp. apply exec_write_reg. }
    rewrite (exec_bind0_Some _ _ _ _ _ HZP).
    assert (HES1 : exec (currentlyEnabled Ext_S) s1e = Some (true, s1e)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal.
      unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _ HES1). cbn beta.
    assert (HAE : exec (Defs.assert_exp' true "no supervisor mode present for delegation") s1e
                  = Some (eq_refl, s1e)).
    { unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HAE). cbn beta.
    (* scause chain *)
    assert (Hrd1 : exec (Defs.read_reg scause : M _) s1e = Some (sc_old, s1e)).
    { rewrite (exec_read_reg scause s1e). unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hsc. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s1e)).
    assert (Hrd2 : exec (Defs.read_reg scause : M _) s2 = Some (c1, s2)).
    { rewrite (exec_read_reg scause s2). unfold s2; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s2)).
    (* mstatus chain *)
    assert (Hrm1 : exec (Defs.read_reg mstatus : M _) s3 = Some (ms_e, s3)).
    { rewrite (exec_read_reg mstatus s3). unfold s3, s2, s1e; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s1; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s3)).
    assert (Hrm2 : exec (Defs.read_reg mstatus : M _) s4 = Some (ms_a, s4)).
    { rewrite (exec_read_reg mstatus s4). unfold s4; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s4)).
    assert (Hrm3 : exec (Defs.read_reg mstatus : M _) s5 = Some (ms_b, s5)).
    { rewrite (exec_read_reg mstatus s5). unfold s5; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm3). cbn beta.
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (Supervisor, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"1" : mword 1) s5)). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s5)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stval _ s6)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc _ s7)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege _ s8)).
    cbn [handle_trap_extension].
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_track_trap_S (trapCause_is_interrupt (Interrupt i)) (trapCause_bits_forwards (Interrupt i)) s9)).
    assert (Hrc : exec (Defs.read_reg scause : M _) s9 = Some (c2, s9)).
    { rewrite (exec_read_reg scause s9).
      unfold s9, s8, s7, s6, s5, s4; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s3; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrc). cbn beta.
    unfold prepare_trap_vector.
    assert (Hrt : exec (Defs.read_reg stvec : M _) s9 = Some (stvec_v, s9)).
    { rewrite (exec_read_reg stvec s9).
      unfold s9, s8, s7, s6, s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hstvec. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrt). cbn beta.
    unfold tvec_addr. rewrite Htvd. cbn match.
    unfold stvec_base. apply exec_returnm.
  Qed.

  Lemma exec_handle_interrupt_S :
    exec (handle_interrupt i Supervisor) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_interrupt.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite Hpc.
    rewrite (exec_bind_Some _ _ _ _ _ exec_trap_handler_S_intr).
    apply exec_set_next_pc.
  Qed.


End TrapReduce.


(* ===================================================================== *)
(* §4 The interrupt step: run_hart_active early return + the try_step     *)
(* wrapper + the minstret_inv WP engine.                                  *)
(* ===================================================================== *)

Lemma execR_early_return {R X} (r : R) s :
  execR (Defs.early_return r : Defs.monadR R exception X) s = Some (inl r, s).
Proof. reflexivity. Qed.

(* run_hart_active on a pending interrupt: NO fetch, NO decode, NO execute;
   the state is UNTOUCHED (dispatchInterrupt only reads). *)
Lemma exec_run_hart_active_pending (s : mstate) (i : InterruptType) (p : Privilege) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (dispatchInterrupt Supervisor) s = Some (Some (i, p), s) ->
  exec (run_hart_active 0) s = Some (Step_Pending_Interrupt (i, p), s).
Proof.
  intros Hpriv Hdisp.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* the try_step wrapper on the Step_Pending_Interrupt arm: handle_interrupt,
   tick PC := nextPC, and NO minstret bump (the step did not retire). *)
(* ********************************************************************* *)
(* COMMENTED OUT -- pending the clock-tick rework of the interrupt stack.  *)
(* [mip] now lives in [clock_inv] (every step may nondeterministically     *)
(* rewrite MTIP/STIP via tick_clock), so the engines below -- which own    *)
(* [mip ↦ᵣ{dq}] across steps and state [exec riscv_step] witnesses --      *)
(* need a substantial redesign, not a mechanical port.                     *)
Section StepInterrupt.
  Context (s s_trap : mstate) (i : InterruptType) (p : Privilege) (b : bool).

  Hypothesis Hsi   :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Pending_Interrupt (i, p), s_a).
  Hypothesis Hhi : exec (handle_interrupt i p) s_a = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_interrupt : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    change (get_config_print_instr tt) with false. cbn match. cbv zeta.
    (* BODY = bind (bind0 (handle_interrupt i p) (read hart_state)) MATCH10 *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhi. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    (* retired = false: and_boolM (returnM false) _ short-circuits *)
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    (* the rest (no-bump arm / rvfi=false skip / pure hooks) computes away *)
    apply exec_returnm.
  Qed.
End StepInterrupt.

(* ===================================================================== *)
(* The Iris engine: one machine step that TAKES the pending interrupt.    *)
(* The continuation comes back UNDER A LATER -- the Löb capstone strips   *)
(* the ▷ off its induction hypothesis exactly here.                       *)
(* ===================================================================== *)
Section WpIntrEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* mstate_interp absorbs a same-value register write (the trap's
     [reset_elp], whose cell is pinned ↦ᵣ□ by hw_config). *)
  (* [reg_interp_set_same] lives in RiscvPtsto, where [reg_interp] does. *)


  Lemma wp_exec_step_interrupt_inv {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
         ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
         ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
         mstate_interp s_trap ∗
         ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
            WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as (i p s_trap) "(%Hha & %Hhi & Hpc & [Hreg Hmem] & Hcont)".
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
    assert (Hhart_a :
      register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
        = HART_ACTIVE tt).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    iModIntro. iExists _. iSplitR.
    { iPureIntro.
      exact (exec_riscv_step_interrupt σ s_trap i p b
               Hsi Hhart_a Hha Hhi Hhart_trap). }
    iNext.
    iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    iModIntro. rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem".
    iSplitL "Hmst Hmi".
    { iExists mst, b. iFrame. }
    iApply ("Hcont" with "Hhs Hpc").
  Qed.

End WpIntrEngine.


(* ===================================================================== *)
(* §7 Small capstone helpers.                                            *)
(* ===================================================================== *)

(* a 1-bit elp that is not LP_EXPECTED is NO_LP_EXPECTED. *)
Lemma elp_no_lp (x : mword 1) :
  eq_vec x (landing_pad_bits_backwards LP_EXPECTED) = false ->
  x = landing_pad_bits_backwards NO_LP_EXPECTED.
Proof.
  intros Hne.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr.
  match type of Hr with context [(2 ^ ?e)%Z] =>
    replace ((2 ^ e)%Z) with 2%Z in Hr by (vm_compute; reflexivity) end.
  destruct (decide (bv_unsigned x = 1)) as [He | Hne'].
  - exfalso.
    assert (Hx1 : x = landing_pad_bits_backwards LP_EXPECTED).
    { apply bv_eq. rewrite He. vm_compute. reflexivity. }
    rewrite Hx1 in Hne.
    assert (Ht : eq_vec (landing_pad_bits_backwards LP_EXPECTED)
                        (landing_pad_bits_backwards LP_EXPECTED) = true)
      by (vm_compute; reflexivity).
    congruence.
  - apply bv_eq.
    replace (bv_unsigned (landing_pad_bits_backwards NO_LP_EXPECTED)) with 0
      by (vm_compute; reflexivity).
    lia.
Qed.

(* [s_dispatch] only ever dispatches to Supervisor. *)
Lemma s_dispatch_Some_S (mip_v mie_v mdv ms : mword 64) (meip seip : mword 1)
    (i : InterruptType) (p : Privilege) :
  s_dispatch mip_v meip seip mie_v mdv ms = Some (i, p) -> p = Supervisor.
Proof.
  unfold s_dispatch.
  destruct (andb _ _); [| discriminate].
  destruct (findPendingInterrupt _); [| discriminate].
  intros H. injection H as -> ->. reflexivity.
Qed.
