(* WpUmodeStep.v -- THE STEP ENGINE of the VERIFIED user-execution tier
   (claude-notes/projects/user-verified.md).

   The safety tier's wrapper (UserStepFull.v) proves that an ARBITRARY user
   machine steps safely; this file is its VALUE-PRECISE twin.  Everything
   here threads the concrete bundle [uv_cap_gpr] (UmodeCap.v): a known
   image [M], a known register file [m], a known pc -- and hands the
   kernel the CONCRETE trapped frame [uv_trap_frame] rather than the
   existential [user_trap_frame].

   Four layers, bottom up:

   §1 [uv_interrupt_branch] -- the concrete-frame twin of
      [UserStepFull.interrupt_branch]: same minstret prelude, same
      [exec_riscv_step_interrupt] reduction, same [utrap_ghost] tower, but
      the pt/image/config payload it threads is the verified tier's
      ([utlb_inv_pt] + [umem] + [user_cfg]) and the continuation receives
      the frame at the EXACT cause / stval / registers / image.

   §2 [uv_step_obl] + [wp_uv_step] -- the interrupt-ABSORBING engine, the
      verified analog of [WpIntrInv.wp_exec_step_intr].  A Löb loop over
      [wp_exec_step_minstret]; each round borrows the wires ([wire_inv]),
      decides [u_dispatch] and branches: a pending delegated interrupt goes
      through §1 into the capability's [uv_intr_wp] and comes back -- same
      (M, m, pc), ARBITRARY hart -- at the Löb hypothesis, so arbitrarily
      many back-to-back interrupts (and migrations) are absorbed; no pending
      interrupt hands the caller's σ-callback [uv_step_obl] the real step.

   §3 [wp_uv_retire] -- the RETIRE funnel: from one [uinstr] fact and one
      value-precise [execute] obligation, drive the fetch (UmodeFetch.v's
      four geometry composers), transport the decode fact, assemble the
      [run_hart_active] witness (SmodeCore's progress composers at User),
      do the PC / gpr / nextPC ghost bookkeeping and re-establish
      [uv_cap_gpr] at the new register file.  Memory is UNCHANGED (the one
      store leaf comes later; the seam for it is the opaque frame [P] that
      [uv_retire_post_fetch] threads -- an [umem pt M'] instead of
      [umem pt M] is all that changes there).

      The post-execute machine state is described by TWO optional layers,
      applied in the order the model writes them: [jt] (a nextPC redirect,
      for a jump) then [wr] (one gpr write).  Both [None] is a plain
      arithmetic instruction; [Some]/[Some] is [jal]; [Some]/[None] is a
      [ret].  A leaf therefore never mentions fetch geometry, and the
      geometry dispatch (compressed x 4-aligned) is folded inside.

   §4 [wp_uv_ecall] -- the ECALL driver: execute raises E_U_EnvCall,
      delegated to S by [uc_del], delivered through the [utrap_state] /
      [utrap_ghost] tower, and the concrete frame is handed to the
      capability's [uv_sys_wp] with the caller's protocol payload. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv WireInv WpGpr RegFile InstrBytes.
Require Import SmodeCore WpIntrCore ExecCommon.
Require Import WpDecodeBridge DecodeTotalU.
Require Import UptTree UserPtTree UserExec UserStep UserTrap UserExecFacts.
Require Import UserStepFull.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpDecode.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 The interrupt branch, with the CONCRETE frame.                      *)
(* ===================================================================== *)
Section UvInterruptBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* The verified twin of [UserStepFull.interrupt_branch]: identical
     premises and identical internal reduction, but (i) the pt/image/config
     payload is the verified tier's, and (ii) the continuation receives the
     CONCRETE [uv_trap_frame] -- the delivered scause is
     [utrap_scause (Interrupt i) sc_v], the delivered stval is [tval None]
     (an interrupt carries no tval), sepc is the interrupted pc, and the
     register file and image come back verbatim.

     The two lemmas should eventually be UNIFIED by the wrapper recipe (a
     payload-generic core over an opaque [P : iProp Σ] plus two
     restatements); they are kept apart here so that landing this file
     touches no already-built file. *)
  Lemma uv_interrupt_branch (Ei : coPset)
      (σ : mstate) (i : InterruptType)
      (ms_v sc_v stval_v sepc_v va : mword 64) (g : regfile)
      (M : gmap Z (bv 8))
      (mst : mword 64) (mi : bool) (misa0 : type_of_register misa) (elpv : mword 1)
      (meip seip : mword 1) :
    user_mstatus_ok ms_v ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec elpv (landing_pad_bits_backwards LP_EXPECTED) = false ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup scause σ.(sregs) = sc_v ->
    register_lookup stvec σ.(sregs) = uc_stvec C ->
    register_lookup elp σ.(sregs) = elpv ->
    register_lookup misa σ.(sregs) = misa0 ->
    register_lookup PC σ.(sregs) = va ->
    register_lookup mip σ.(sregs) = uc_mip C ->
    register_lookup sig_meip σ.(sregs) = meip ->
    register_lookup sig_seip σ.(sregs) = seip ->
    register_lookup mie σ.(sregs) = uc_mie C ->
    register_lookup mideleg σ.(sregs) = uc_mideleg C ->
    u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C) = Some (i, Supervisor) ->
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
    umem pt M -∗ user_cfg C -∗
    ▷ (uv_trap_frame C pt (utrap_scause (Interrupt i) sc_v) (tval None) va g M -∗
       WP (Loop : expr riscv_lang)) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    iIntros (Hmsok HmisaS Help_ne Lpriv Lms Lsc Lstvec Lelp Lmisa Lpc
             Lmip Lmeip Lseip Lmie Lmdl Hd)
      "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr
       Hutlb Humem Hcfg Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg σ (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    assert (Hdisp_a : exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
                      = Some (Some (i, Supervisor), set_reg σ (R_bool minstret_increment) b)).
    { rewrite (exec_dispatchInterrupt_U_reduce (set_reg σ (R_bool minstret_increment) b)
                 (uc_mip C) (uc_mie C) (uc_mideleg C) meip seip
                 ltac:(rewrite exec_currentlyEnabled_S; rewrite (T misa _ Lmisa eq_refl);
                       rewrite HmisaS; reflexivity)
                 (T mip _ Lmip eq_refl) (T sig_meip _ Lmeip eq_refl)
                 (T sig_seip _ Lseip eq_refl) (T mie _ Lmie eq_refl)
                 (T mideleg _ Lmdl eq_refl) (uc_mm C)).
      rewrite Hd. reflexivity. }
    pose proof (exec_run_hart_active_pending_U (set_reg σ (R_bool minstret_increment) b)
                  i Supervisor (T cur_privilege _ Lpriv eq_refl) Hdisp_a) as Hha.
    pose proof (exec_handle_interrupt_U (set_reg σ (R_bool minstret_increment) b)
                  (Interrupt i) None va ms_v sc_v (uc_stvec C) elpv
                  (T cur_privilege _ Lpriv eq_refl) (T mstatus _ Lms eq_refl)
                  (T scause _ Lsc eq_refl) (T stvec _ Lstvec eq_refl)
                  (T elp _ Lelp eq_refl)
                  ltac:(rewrite (T misa _ Lmisa eq_refl); exact HmisaS)
                  (uc_tvd C) (T PC _ Lpc eq_refl) i eq_refl eq_refl) as Hhi.
    set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhi.
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Lhs0. }
    assert (Hstep : exec (riscv_step false) σ
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_interrupt;
        [ exact Hsi | exact Lhs | exact Hha | exact Hhi | exact Lhs_trap ]. }
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
    { unfold s_trap; rewrite ?sregs_set_reg. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    assert (Hs' : set_reg s_trap PC (stvec_base (uc_stvec C))
                = utrap_state (set_reg σ (R_bool minstret_increment) b)
                    (Interrupt i) None va ms_v sc_v elpv (uc_stvec C))
      by (unfold s_trap; reflexivity).
    rewrite Hs' in Hstep.
    iMod (utrap_ghost (set_reg σ (R_bool minstret_increment) b) (Interrupt i) None
            va ms_v sc_v stval_v sepc_v va va elpv (uc_stvec C)
            (T elp _ Lelp eq_refl) Help_ne
            with "[Hreg Hmd] Hms Hsc Hstval Hsepc Hpriv Hnpc Hpc")
      as "(Hint & Hms & Hsc & Hstval & Hsepc & Hpriv & Hnpc & Hpc)".
    { iFrame "Hreg Hmd". }
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    iFrame "Hint".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    iExists (utrap_ms elpv ms_v).
    iSplitR. { iPureIntro. exact (utrap_ms_ok elpv ms_v Hmsok). }
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hutlb Humem Hcfg".
  Qed.

End UvInterruptBranch.

(* ===================================================================== *)
(* §2 The interrupt-absorbing engine.                                     *)
(* ===================================================================== *)
Section UvStepEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* The per-leaf REAL-STEP obligation.  LINEAR (it captures the leaf's
     continuation) and consumed EXACTLY ONCE, by the round that takes the
     real step -- possibly after any number of absorbed interrupts and
     migrations, which is why the hart is quantified INSIDE. *)
  Definition uv_step_obl (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (CID : CpuId) (σ : mstate) (ms_v sc_v stval_v sepc_v : mword 64),
       ⌜user_mstatus_ok ms_v⌝ -∗
       ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
       ⌜register_lookup mstatus σ.(sregs) = ms_v⌝ -∗
       ⌜register_lookup PC σ.(sregs) = pc⌝ -∗
       ⌜forall b : bool,
          exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
            = Some (None, set_reg σ (R_bool minstret_increment) b)⌝ -∗
       (* the ambient per-hart persistent bundle, re-delivered AT THIS hart
          (hw_config / minstret_inv / wire_inv own THIS hart's cells, so the
          caller's ambient copy is useless after a migration) *)
       uv_amb -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
       stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ pc -∗ nextPC ↦ᵣ pc -∗
       gpr_file m -∗
       utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
       umem pt M -∗ user_cfg C -∗
       mstate_interp σ -∗ minstret_inv_body -∗
       |={⊤ ∖ ↑minstretN ∖ ↑wireN}=> ∃ s' : mstate,
          ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
          ▷ (mstate_interp s' ∗ minstret_inv_body ∗
             WP (Loop : expr riscv_lang)))%I.

  (* THE ENGINE, in the hart-quantified form the Löb induction needs: only
     [CID] is bound inside the entailment, everything else is a lemma
     binder, so the induction hypothesis can be re-applied at the RESUMING
     hart after a migration. *)
  Lemma wp_uv_step_gen (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) :
    ⊢ ∀ CID : CpuId,
        uv_cap_gpr (CID := CID) C pt Ψ M m -∗
        pc_is pc -∗
        uv_step_obl Ψ M m pc -∗
        WP (Loop : expr riscv_lang).
  Proof.
    iLöb as "IH".
    iIntros (CID) "(#Hcap & Hlin & Hgpr) [Hpc Hnpc] Hobl".
    iDestruct "Hcap" as "[#Hintr #Hsys]".
    iDestruct "Hlin" as "(#Hamb & Hregs & Hutlb & Humem & Hcfg)".
    iAssert uv_amb with "[]" as "#Hamb2". { iExact "Hamb". }
    iDestruct "Hamb" as "(#Hhw & #Hmin & #Hwinv)".
    iDestruct "Hregs" as (ms_v sc_v stval_v sepc_v)
      "(%Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc)".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN ∖ ↑wireN) with "Hmin").
    iIntros (σ) "Hint Hbody".
    (* borrow the wires for this step *)
    iInv "Hwinv" as ">Hwbody" "Hclosew".
    iDestruct "Hwbody" as (seipf meipf) "Hwires".
    iDestruct (big_sepS_delete _ _ cpu_id with "Hwires") as "[[Hseip Hmeip] Hwrest]";
      [ apply elem_of_fin_to_set |].
    set (meip := meipf cpu_id). set (seip := seipf cpu_id).
    iDestruct "Hint" as "[Hreg [Hmem Hdev]]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc.
    iAssert (mstate_interp σ) with "[Hreg Hmem Hdev]" as "Hint".
    { iFrame "Hreg Hmem Hdev". }
    iAssert (user_cfg C) with "[Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest". }
    destruct (u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C)) as [[i p]|] eqn:Hd.
    - (* ---- a pending delegated interrupt: absorb it ---- *)
      pose proof (u_dispatch_Supervisor _ _ _ _ _ _ _ Hd) as ->.
      iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
      iMod (uv_interrupt_branch C pt (⊤ ∖ ↑minstretN ∖ ↑wireN) σ i
              ms_v sc_v stval_v sepc_v pc m M mst mi misa0 elp0 meip seip
              Hmsok HmisaS Help_ne Lpriv Lms Lsc Lstvec Lelp Lmisa Lpc
              Lmip Lmeip Lseip Lmie Lmdl Hd
              with "Hint Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr
                    Hutlb Humem Hcfg [Hobl]")
        as (s') "[%Hexec Hrest]".
      { iNext. iIntros "Hframe".
        iApply ("Hintr" $! CID m M pc i sc_v (tval None) with "Hframe").
        iIntros (CID') "Hrun".
        iDestruct (uv_run_cap_gpr (CID := CID') C pt Ψ M m pc
                     with "[$Hintr $Hsys] Hrun") as "[Hcg Hpc']".
        iApply ("IH" $! CID' with "Hcg Hpc' Hobl"). }
      iModIntro. iExists s'. iSplitR. { iPureIntro. exact Hexec. }
      iNext. iDestruct "Hrest" as "(Hint & Hbody & HWP)".
      iMod ("Hclosew" with "[Hseip Hmeip Hwrest]") as "_".
      { iNext. iExists seipf, meipf.
        iApply (big_sepS_delete _ _ cpu_id); [ apply elem_of_fin_to_set |].
        iFrame "Hseip Hmeip Hwrest". }
      iModIntro. iFrame "Hint Hbody HWP".
    - (* ---- nothing pending: hand the caller its real step ---- *)
      assert (Hdisp_ab : forall b : bool,
                exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
                  = Some (None, set_reg σ (R_bool minstret_increment) b)).
      { intro b.
        assert (Tb : forall (r : register) (v : type_of_register r),
                  register_lookup r σ.(sregs) = v ->
                  register_beq r (R_bool minstret_increment) = false ->
                  register_lookup r (set_reg σ (R_bool minstret_increment) b).(sregs) = v).
        { intros r v Hv Hne. rewrite ?sregs_set_reg.
          rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
        rewrite (exec_dispatchInterrupt_U_reduce (set_reg σ (R_bool minstret_increment) b)
                   (uc_mip C) (uc_mie C) (uc_mideleg C) meip seip
                   ltac:(rewrite exec_currentlyEnabled_S; rewrite (Tb misa _ Lmisa eq_refl);
                         rewrite HmisaS; reflexivity)
                   (Tb mip _ Lmip eq_refl) (Tb sig_meip _ Lmeip eq_refl)
                   (Tb sig_seip _ Lseip eq_refl) (Tb mie _ Lmie eq_refl)
                   (Tb mideleg _ Lmdl eq_refl) (uc_mm C)).
        rewrite Hd. reflexivity. }
      iMod ("Hobl" $! CID σ ms_v sc_v stval_v sepc_v Hmsok Lpriv Lms Lpc Hdisp_ab
              with "Hamb2 Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr
                    Hutlb Humem Hcfg Hint Hbody")
        as (s') "[%Hexec Hrest]".
      iModIntro. iExists s'. iSplitR. { iPureIntro. exact Hexec. }
      iNext. iDestruct "Hrest" as "(Hint & Hbody & HWP)".
      iMod ("Hclosew" with "[Hseip Hmeip Hwrest]") as "_".
      { iNext. iExists seipf, meipf.
        iApply (big_sepS_delete _ _ cpu_id); [ apply elem_of_fin_to_set |].
        iFrame "Hseip Hmeip Hwrest". }
      iModIntro. iFrame "Hint Hbody HWP".
  Qed.

End UvStepEngine.

(* ===================================================================== *)
(* §3 The RETIRE funnel.                                                  *)
(*                                                                        *)
(* The state a retiring, non-CSR, memory-preserving instruction leaves is  *)
(* always the same two-layer tower over the post-fetch state: an OPTIONAL  *)
(* nextPC redirect (a jump) and an OPTIONAL single gpr write, in THAT      *)
(* order -- which is the order the model writes them (see                 *)
(* [exec_execute_JAL_gpr]: set_next_pc first, then wX).  Both layers are   *)
(* [None] for a plain arithmetic instruction, and the leaf states its      *)
(* execute fact against exactly this tower.                               *)
(* ===================================================================== *)

Definition uv_jmp (s : mstate) (jt : option (mword 64)) : mstate :=
  match jt with Some t => set_reg s nextPC t | None => s end.

Definition uv_wr (s : mstate) (wr : option (mword 5 * mword 64)) : mstate :=
  match wr with
  | Some (rd, v) => set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)
  | None => s
  end.

(* the post-execute machine state of a retiring instruction *)
Definition uv_post (s : mstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) : mstate := uv_wr (uv_jmp s jt) wr.

(* ... and the register file / next pc it leaves *)
Definition uv_upd (m : regfile) (wr : option (mword 5 * mword 64)) : regfile :=
  match wr with
  | Some (rd, v) => <[Regidx rd := regval_into_reg v]> m
  | None => m
  end.

Definition uv_next (jt : option (mword 64)) (d : mword 64) : mword 64 :=
  match jt with Some t => t | None => d end.

(* a gpr write must not target x0 (writing x0 is a no-op the tower does not
   describe; every leaf that "writes x0" states [wr := None] instead) *)
Definition uv_wrok (wr : option (mword 5 * mword 64)) : Prop :=
  match wr with Some (rd, _) => uint rd <> 0 | None => True end.

(* the instruction actually executed: the decoded one, or -- for the
   compressed / SINVAL_VMA style [ExecuteAs] redirects -- its expansion *)
Definition uv_exp (i : instruction) (o : option instruction) : instruction :=
  match o with Some j => j | None => i end.

(* the redirect premise, in the shape the leaves' [exec_execute_C_*] facts
   already have *)
Definition uv_redirect (i : instruction) (o : option instruction) : Prop :=
  forall s : mstate,
    match o with
    | Some j => exec (execute i) s = Some (ExecuteAs j, s)
    | None => True
    end.

Lemma uv_post_nextPC (s : mstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) (d : mword 64) :
  register_lookup nextPC s.(sregs) = d ->
  register_lookup nextPC (uv_post s jt wr).(sregs) = uv_next jt d.
Proof.
  intro Hd.
  assert (Hj : register_lookup nextPC (uv_jmp s jt).(sregs) = uv_next jt d).
  { destruct jt as [t | ]; [ | exact Hd ].
    unfold uv_jmp, uv_next; rewrite ?sregs_set_reg. apply register_lookup_set. }
  unfold uv_post. destruct wr as [[rd v] | ]; [ | exact Hj ].
  unfold uv_wr; rewrite ?sregs_set_reg.
  rewrite (irrelevant_register_set _ _ _ _ (regbeq_nextPC_gpr (uint rd))).
  exact Hj.
Qed.

(* ---- the two geometry-specific [run_hart_active] assemblers ---------- *)

Lemma uv_prog_rvc (sa sf : mstate) (h : mword 16) (i : instruction)
    (o : option instruction) (pc : mword 64) :
  register_lookup cur_privilege sa.(sregs) = User ->
  exec (dispatchInterrupt User) sa = Some (None, sa) ->
  exec (fetch tt) sa = Some (F_RVC h, sf) ->
  exec (ext_decode_compressed h) sf = Some (i, sf) ->
  eq_vec (register_lookup elp sf.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC sf.(sregs) = pc ->
  exec (currentlyEnabled Ext_Zca) sf = Some (true, sf) ->
  uv_redirect i o ->
  forall s_x : mstate,
    exec (execute (uv_exp i o)) (set_reg sf nextPC (add_vec_int pc 2))
      = Some (RETIRE_SUCCESS, s_x) ->
    exec (run_hart_active 0) sa
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Help Lpc Hzca Hred s_x Hex.
  destruct o as [other | ]; cbn [uv_exp] in Hex.
  - exact (exec_hart_active_progress_RVC_gen User sa sf s_x h i other pc
             RETIRE_SUCCESS Hpriv Hdisp Hfetch Hdec Help Lpc Hzca
             (Hred (set_reg sf nextPC (add_vec_int pc 2))) Hex).
  - exact (exec_hart_active_progress_RVC_direct_gen User sa sf s_x h i pc
             RETIRE_SUCCESS Hpriv Hdisp Hfetch Hdec Help Lpc Hzca Hex I).
Qed.

Lemma uv_prog_base (sa sf : mstate) (w : mword 32) (i : instruction)
    (o : option instruction) (pc : mword 64) :
  register_lookup cur_privilege sa.(sregs) = User ->
  exec (dispatchInterrupt User) sa = Some (None, sa) ->
  exec (fetch tt) sa = Some (F_Base w, sf) ->
  exec (ext_decode w) sf = Some (i, sf) ->
  eq_vec (register_lookup elp sf.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction i = false ->
  register_lookup PC sf.(sregs) = pc ->
  uv_redirect i o ->
  forall s_x : mstate,
    exec (execute (uv_exp i o)) (set_reg sf nextPC (add_vec_int pc 4))
      = Some (RETIRE_SUCCESS, s_x) ->
    exec (run_hart_active 0) sa
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Help Hlpad Lpc Hred s_x Hex.
  destruct o as [other | ]; cbn [uv_exp] in Hex.
  - exact (exec_hart_active_progress_base_redirect_gen User sa sf s_x w i other pc
             RETIRE_SUCCESS Hpriv Hdisp Hfetch Hdec Help Hlpad Lpc
             (Hred (set_reg sf nextPC (add_vec_int pc 4))) Hex).
  - exact (exec_hart_active_progress_base_gen User sa sf s_x w i pc
             RETIRE_SUCCESS Hpriv Hdisp Hfetch Hdec Help Hlpad Lpc Hex I).
Qed.

(* ---- the U-mode CONFIG agreement, transported to the leaf's state -----
   A retiring instruction that JUMPS needs more of the machine than its pc
   and its registers: [jump_to] consults Zca (the C extension gates the
   2-aligned-target relaxation) and [update_elp_state] consults Zicfilp.
   Both are functions of the very read-set the funnel already establishes
   at the fetched state -- [agree_on D_u sf dstateU] -- so the funnel hands
   the leaf THAT one fact (it survives the [nextPC := pc + k] write), and
   the leaf projects out whatever config value its execute obligation
   needs.  Nothing else about the machine leaks into a leaf. *)

Lemma D_u_ne_nextPC (r : register) : D_u r = true -> register_beq r nextPC = false.
Proof.
  unfold D_u. intro Hr.
  repeat (apply orb_true_elim in Hr as [Hr | Hr]);
    apply register_beq_eq in Hr; subst r; vm_compute; reflexivity.
Qed.

Lemma agree_u_set_nextPC (s : mstate) (v : mword 64) :
  agree_on D_u s dstateU -> agree_on D_u (set_reg s nextPC v) dstateU.
Proof.
  intros Hag r Hr. rewrite <- (Hag r Hr).
  rewrite ?sregs_set_reg.
  apply irrelevant_register_set. exact (D_u_ne_nextPC r Hr).
Qed.

Lemma agree_u_priv (s : mstate) :
  agree_on D_u s dstateU -> register_lookup cur_privilege s.(sregs) = User.
Proof.
  intro H.
  rewrite (H (R_Privilege cur_privilege) ltac:(vm_compute; reflexivity)).
  vm_compute; reflexivity.
Qed.

Lemma agree_u_misa (s : mstate) :
  agree_on D_u s dstateU -> register_lookup misa s.(sregs) = MISA_C.
Proof.
  intro H.
  rewrite (H (R_bitvector_64 misa) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

Lemma agree_u_menvcfg (s : mstate) :
  agree_on D_u s dstateU -> register_lookup menvcfg s.(sregs) = MENVCFG_S.
Proof.
  intro H.
  rewrite (H (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

Lemma agree_u_senvcfg (s : mstate) :
  agree_on D_u s dstateU ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64).
Proof.
  intro H.
  rewrite (H (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* the two extension gates a jumping leaf needs, straight off the
   agreement (Zca from misa.C; Zicfilp off because get_xLPE at User reads
   senvcfg.LPE and [user_cfg] pins senvcfg = 0) *)
Lemma agree_u_zca (s : mstate) :
  agree_on D_u s dstateU -> exec (currentlyEnabled Ext_Zca) s = Some (true, s).
Proof.
  intro H. apply exec_currentlyEnabled_Zca.
  rewrite (agree_u_misa s H). vm_compute; reflexivity.
Qed.

(* verbatim [UserTotalU.s0_zicfilp], restated off the agreement so the
   verified tier does not have to Require the classification/totality
   tower.  RELOCATION DEBT: the two should become one lemma once
   UserTotalU's copy can be re-derived from this one. *)
Lemma agree_u_zicfilp (s : mstate) :
  agree_on D_u s dstateU -> exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
Proof.
  intro Hag.
  pose proof (agree_u_priv s Hag) as Hpriv.
  pose proof (agree_u_misa s Hag) as Hmisa.
  pose proof (agree_u_menvcfg s Hag) as Hmenv.
  pose proof (agree_u_senvcfg s Hag) as Hsenv.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  match goal with |- context[_rec_get_xLPE User _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true
    by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_rec_cE_S_1 (currentlyEnabled_measure Ext_Zicfilp - 1 - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn beta.
  replace (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) with true
    by (rewrite Hmisa; vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned s Hmenv Hsenv)).
  cbn match beta.
  match goal with |- exec (returnM ?v) s = _ =>
    replace v with false by (vm_compute; reflexivity) end.
  apply exec_returnm.
Qed.

Section UvStepAt.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* the engine at the ambient hart *)
  Lemma wp_uv_step (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) :
    uv_cap_gpr C pt Ψ M m -∗ pc_is pc -∗ uv_step_obl C pt Ψ M m pc -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hobl".
    iPoseProof (wp_uv_step_gen C pt Ψ M m pc) as "H".
    iApply ("H" $! CID with "Hcg Hpc Hobl").
  Qed.

  (* every gpr value, read off the file at one state (pure conclusion, so
     the file is retained) *)
  Lemma gpr_file_values (f : regfile) (s : mstate) :
    reg_interp s.(sregs) -∗ gpr_file f -∗
    ⌜forall r : mword 5,
       (if Z.eqb (uint r) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs))
       = f !!! Regidx r⌝.
  Proof.
    iIntros "Hreg Hf". rewrite bi.pure_forall. iIntros (r).
    iDestruct (gpr_file_lookup_acc f (Regidx r) with "Hf") as "[Hpt _]".
    iApply (gpr_pt_value r (f (Regidx r)) s with "Hreg Hpt").
  Qed.

  Lemma uv_jmp_ghost (s : mstate) (jt : option (mword 64)) (v0 : mword 64) :
    mstate_interp s -∗ nextPC ↦ᵣ v0 ==∗
    mstate_interp (uv_jmp s jt) ∗ nextPC ↦ᵣ uv_next jt v0.
  Proof.
    iIntros "Hint Hnpc". destruct jt as [t | ]; cbn [uv_jmp uv_next];
      [ | iModIntro; iFrame ].
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iMod (reg_update _ nextPC _ t with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro. rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame.
  Qed.

  Lemma uv_wr_ghost (s : mstate) (wr : option (mword 5 * mword 64)) (m : regfile) :
    uv_wrok wr ->
    mstate_interp s -∗ gpr_file m ==∗
    mstate_interp (uv_wr s wr) ∗ gpr_file (uv_upd m wr).
  Proof.
    iIntros (Hok) "Hint Hgpr". destruct wr as [[rd v] | ]; cbn [uv_wr uv_upd];
      [ | iModIntro; iFrame ].
    cbn [uv_wrok] in Hok.
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg v) with "Hgpr")
      as "[Hpt Hins]".
    rewrite (gpr_pt_nz rd _ Hok).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hpt") as "[Hreg Hpt]".
    iDestruct ("Hins" with "[Hpt]") as "Hgpr".
    { rewrite (gpr_pt_nz rd _ Hok). iExact "Hpt". }
    iModIntro. rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame.
  Qed.

End UvStepAt.

Section UvRetirePost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------- *)
  (* Everything from the FETCHED state on: the nextPC := pc+k write, the   *)
  (* leaf's value-precise execute, the PC tick and the minstret bump.      *)
  (* Geometry-agnostic: the [run_hart_active] witness enters as the pure   *)
  (* implication [Hprog] that [uv_prog_rvc] / [uv_prog_base] produce.      *)
  (* ------------------------------------------------------------------- *)
  Lemma uv_retire_post_fetch (CIDp : CpuId) (P : iProp Σ)
      (sg sf : mstate) (b : bool) (mst pc : mword 64) (k : Z) (ib : mword 32)
      (m : regfile) (i : instruction) (o : option instruction)
      (jt : option (mword 64)) (wr : option (mword 5 * mword 64)) :
    exec (should_inc_minstret (register_lookup cur_privilege sg.(sregs))) sg
      = Some (b, sg) ->
    register_lookup hart_state
      (set_reg sg (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt ->
    register_lookup PC sf.(sregs) = pc ->
    register_lookup cur_privilege sf.(sregs) = User ->
    agree_on D_u sf dstateU ->
    uv_wrok wr ->
    (forall s_x : mstate,
       exec (execute (uv_exp i o)) (set_reg sf nextPC (add_vec_int pc k))
         = Some (RETIRE_SUCCESS, s_x) ->
       exec (run_hart_active 0) (set_reg sg (R_bool minstret_increment) b)
         = Some (Step_Execute (RETIRE_SUCCESS, ib), s_x)) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    mstate_interp sf -∗
    P -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    PC ↦ᵣ pc -∗ nextPC ↦ᵣ pc -∗ gpr_file m -∗
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ b -∗
    ▷ (P -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       PC ↦ᵣ uv_next jt (add_vec_int pc k) -∗
       nextPC ↦ᵣ uv_next jt (add_vec_int pc k) -∗
       gpr_file (uv_upd m wr) -∗
       WP (Loop : expr riscv_lang)) -∗
    |={⊤ ∖ ↑minstretN ∖ ↑wireN}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) sg = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hsi Hhart_a Lpcf Lprivf Hagreef Hwrok Hprog Hexec.
    iIntros "Hint HP Hhs Hpc Hnpc Hgpr Hmst Hmi Hcont".
    (* the model's nextPC := pc + k write *)
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iMod (reg_update _ nextPC _ (add_vec_int pc k) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_values m (set_reg sf nextPC (add_vec_int pc k))
                 with "[Hreg] Hgpr") as %Hvals.
    { rewrite ?sregs_set_reg. iExact "Hreg". }
    assert (Lnpc0 : register_lookup nextPC
              (set_reg sf nextPC (add_vec_int pc k)).(sregs) = add_vec_int pc k)
      by (rewrite ?sregs_set_reg; apply register_lookup_set).
    assert (Lpc0 : register_lookup PC
              (set_reg sf nextPC (add_vec_int pc k)).(sregs) = pc).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Lpcf | vm_compute; reflexivity ]. }
    assert (Lpriv0 : register_lookup cur_privilege
              (set_reg sf nextPC (add_vec_int pc k)).(sregs) = User).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Lprivf | vm_compute; reflexivity ]. }
    pose proof (Hexec _ Lpc0 Lnpc0 Lpriv0
                  (agree_u_set_nextPC sf (add_vec_int pc k) Hagreef) Hvals) as Hex.
    pose proof (Hprog _ Hex) as Hha.
    (* the execute's own writes, in the model's order *)
    iAssert (mstate_interp (set_reg sf nextPC (add_vec_int pc k)))
      with "[Hreg Hmem Hdev]" as "Hint".
    { rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iMod (uv_jmp_ghost (set_reg sf nextPC (add_vec_int pc k)) jt (add_vec_int pc k)
            with "Hint Hnpc") as "[Hint Hnpc]".
    iMod (uv_wr_ghost (uv_jmp (set_reg sf nextPC (add_vec_int pc k)) jt) wr m Hwrok
            with "Hint Hgpr") as "[Hint Hgpr]".
    assert (Lnpcx : register_lookup nextPC
              (uv_post (set_reg sf nextPC (add_vec_int pc k)) jt wr).(sregs)
              = uv_next jt (add_vec_int pc k))
      by (apply uv_post_nextPC; exact Lnpc0).
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_x.
    iDestruct (reg_valid_dq with "Hreg Hmi") as %Hmi_x.
    iDestruct (reg_valid_dq with "Hreg Hmst") as %Lmst_x.
    pose proof (exec_riscv_step_hart_active sg
                  (uv_post (set_reg sf nextPC (add_vec_int pc k)) jt wr) ib b
                  Hsi Hhart_a Hha Hhart_x Hmi_x) as Hstep.
    rewrite Lnpcx in Hstep.
    set (s_tick := set_reg (uv_post (set_reg sf nextPC (add_vec_int pc k)) jt wr)
                     PC (uv_next jt (add_vec_int pc k))) in *.
    assert (Lmst_t : register_lookup minstret s_tick.(sregs) = mst).
    { unfold s_tick; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Lmst_x | reflexivity ]. }
    rewrite Lmst_t in Hstep.
    iMod (reg_update _ PC _ (uv_next jt (add_vec_int pc k)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
        as "[Hreg Hmst]".
      iModIntro. iExists (set_reg s_tick minstret (add_vec_int mst 1)).
      iSplitR. { iPureIntro. exact Hstep. }
      iNext. unfold s_tick; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev".
      iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
      iApply ("Hcont" with "HP Hhs Hpc Hnpc Hgpr").
    - iModIntro. iExists s_tick.
      iSplitR. { iPureIntro. exact Hstep. }
      iNext. unfold s_tick; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "HP Hhs Hpc Hnpc Hgpr").
  Qed.

End UvRetirePost.

Section UvRetireFunnel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* THE RETIRE FUNNEL.                                                    *)
  (*                                                                       *)
  (* One [uinstr] fact + one value-precise execute obligation = one         *)
  (* verified instruction.  The funnel picks the fetch geometry off the     *)
  (* [uinstr] (compressed x 4-aligned), transports the decode fact to the   *)
  (* fetched state, assembles the [run_hart_active] witness at User, and    *)
  (* re-establishes [uv_cap_gpr] at the updated register file.  The image   *)
  (* [M] is UNCHANGED -- this is the memory-preserving funnel; a store leaf *)
  (* will need the [umem] update threaded through [uv_retire_post_fetch].   *)
  (*                                                                       *)
  (* The continuation quantifies the hart: the step may be preceded by an   *)
  (* arbitrary number of absorbed interrupts, each of which may migrate the *)
  (* process, so nothing after the step runs at the entry hart.             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_retire (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (jt : option (mword 64)) (wr : option (mword 5 * mword 64)) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_wrok wr ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0) (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hexec.
    destruct Hui as [Hal2 Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgprc)".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hlin Hgprc]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgprc". }
    iApply (wp_uv_step C pt Ψ M m pc with "Hcg Hpc [Hcont]").
    rewrite /uv_step_obl.
    iIntros (CID0 sg ms_v sc_v stval_v sepc_v)
      "%Hmsok %Lpriv %Lms %Lpc %Hdisp #Hamb Hhs Hpriv Hms Hsc Hstval Hsepc
       Hpc Hnpc Hgpr Hutlb Humem Hcfg Hint Hbody".
    iAssert uv_amb with "[]" as "#Hamb2". { iExact "Hamb". }
    iDestruct "Hamb" as "(#Hhw & #Hmin & #Hwinv)".
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hmenv & Hsenv & Hmse & Hsse)".
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmse") as %Lmse.
    iDestruct (reg_valid_dq with "Hreg Hsse") as %Lsse.
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & #Hpma & #Hhtif & #Help & _ & _ & _ & _ & %Hpma_all
        & _ & _ & %Help_ne & _ & %Hmisaval & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    subst misa0.
    iAssert (user_cfg C)
      with "[Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse". }
    (* ---- the minstret prelude: minstret_increment := should_inc ---- *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege sg.(sregs)) sg) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r sg.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    pose proof (T hart_state _ Lhs eq_refl) as Hhart_a.
    pose proof (T PC _ Lpc eq_refl) as LpcA.
    pose proof (T cur_privilege _ Lpriv eq_refl) as LprivA.
    pose proof (T misa _ Lmisa eq_refl) as LmisaA.
    pose proof (T menvcfg _ Lmenv eq_refl) as LmenvA.
    pose proof (T senvcfg _ Lsenv eq_refl) as LsenvA.
    pose proof (T mstateen0 _ Lmse eq_refl) as LmseA.
    pose proof (T sstateen0 _ Lsse eq_refl) as LsseA.
    pose proof (T elp _ Lelp eq_refl) as LelpA.
    assert (HSXL : _get_Mstatus_SXL
              (register_lookup mstatus (set_reg sg (R_bool minstret_increment) b).(sregs))
              = 'b"10")
      by (rewrite (T mstatus _ Lms eq_refl); exact (proj1 Hmsok)).
    assert (HpmaA : pma_allows_all
              (register_lookup pma_regions
                 (set_reg sg (R_bool minstret_increment) b).(sregs)))
      by (rewrite (T pma_regions _ Lpma eq_refl); exact Hpma_all).
    pose proof (Hdisp b) as HdispA.
    (* every post-fetch pin, in one place: the fetch only ever writes tlb *)
    assert (Hsf : forall sf : mstate,
              (forall r : register, register_beq r tlb = false ->
                 register_lookup r sf.(sregs)
                   = register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs)) ->
              register_lookup PC sf.(sregs) = pc /\
              register_lookup cur_privilege sf.(sregs) = User /\
              register_lookup misa sf.(sregs) = MISA_C /\
              eq_vec (register_lookup elp sf.(sregs))
                     (landing_pad_bits_backwards LP_EXPECTED) = false /\
              agree_on D_u sf dstateU).
    { intros sf Tr. split_and!.
      - rewrite (Tr PC ltac:(vm_compute; reflexivity)). exact LpcA.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
      - rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr elp ltac:(vm_compute; reflexivity)). rewrite LelpA. exact Help_ne.
      - apply agree_u.
        + rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
        + rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)). exact LmenvA.
        + rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)). exact LsenvA.
        + rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)). exact LmseA.
        + rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)). exact LsseA.
        + rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA. }
    (* the closure every geometry hands to [uv_retire_post_fetch] *)
    iAssert (▷ ((utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
                 umem pt M ∗ user_cfg C) -∗
                hart_state ↦ᵣ HART_ACTIVE tt -∗
                PC ↦ᵣ uv_next jt (add_vec_int pc (if is_rvc then 2 else 4)) -∗
                nextPC ↦ᵣ uv_next jt (add_vec_int pc (if is_rvc then 2 else 4)) -∗
                gpr_file (uv_upd m wr) -∗
                WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hpriv Hms Hsc Hstval Hsepc]" as "Hk".
    { iNext. iIntros "(Hutlb & Humem & Hcfg) Hhs Hpc Hnpc Hgpr".
      iApply ("Hcont" $! CID0 with "[-Hpc Hnpc] [$Hpc $Hnpc]").
      rewrite /uv_cap_gpr /uv_lin.
      iFrame "Hcap Hamb2 Hutlb Humem Hcfg Hgpr".
      rewrite /uv_regs.
      iExists ms_v, sc_v, stval_v, sepc_v.
      iSplitR; [ iPureIntro; exact Hmsok | ].
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc". }
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* 4-aligned: one 4-byte read *)
        destruct (Hnext2 ltac:(first [exact Hal4 | reflexivity]))
          as (b2 & b3 & Hb2 & Hb3).
        iMod (umode_fetch_rvc_4 pt M w_leaf pc h b2 b3
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanon Hinpage Hal4 Hbytes Hb2 Hb3 HisRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr) as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree).
        iApply (uv_retire_post_fetch CID0
                  (utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
                   umem pt M ∗ user_cfg C)%I sg sf b mst pc 2 (zero_extend' 32 h) m i o jt wr
                  Hsi Hhart_a Lpcf Lprivf Hagree Hwrok
                  (uv_prog_rvc _ _ h i o pc LprivA HdispA Hfetch
                     (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                     Helpf Lpcf
                     (exec_currentlyEnabled_Zca sf
                        ltac:(rewrite Lmisaf; vm_compute; reflexivity)) Hred)
                  Hexec
                  with "[Hreg Hmem Hdev] [$Hutlb $Humem $Hcfg] Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
      + (* 2 mod 4: one 2-byte read *)
        iMod (umode_fetch_rvc_2 pt M w_leaf pc h
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HisRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr) as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree).
        iApply (uv_retire_post_fetch CID0
                  (utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
                   umem pt M ∗ user_cfg C)%I sg sf b mst pc 2 (zero_extend' 32 h) m i o jt wr
                  Hsi Hhart_a Lpcf Lprivf Hagree Hwrok
                  (uv_prog_rvc _ _ h i o pc LprivA HdispA Hfetch
                     (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                     Helpf Lpcf
                     (exec_currentlyEnabled_Zca sf
                        ltac:(rewrite Lmisaf; vm_compute; reflexivity)) Hred)
                  Hexec
                  with "[Hreg Hmem Hdev] [$Hutlb $Humem $Hcfg] Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + iMod (umode_fetch_base_4 pt M w_leaf pc w
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanon Hinpage Hal4 Hbytes HnRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr) as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree).
        iApply (uv_retire_post_fetch CID0
                  (utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
                   umem pt M ∗ user_cfg C)%I sg sf b mst pc 4 (zero_extend' 32 w) m i o jt wr
                  Hsi Hhart_a Lpcf Lprivf Hagree Hwrok
                  (uv_prog_base _ _ w i o pc LprivA HdispA Hfetch
                     (Hdecbase sf Hagree) Helpf Hlpad Lpcf Hred)
                  Hexec
                  with "[Hreg Hmem Hdev] [$Hutlb $Humem $Hcfg] Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
      + iMod (umode_fetch_base_2 pt M w_leaf pc w
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HnRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr) as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree).
        iApply (uv_retire_post_fetch CID0
                  (utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
                   umem pt M ∗ user_cfg C)%I sg sf b mst pc 4 (zero_extend' 32 w) m i o jt wr
                  Hsi Hhart_a Lpcf Lprivf Hagree Hwrok
                  (uv_prog_base _ _ w i o pc LprivA HdispA Hfetch
                     (Hdecbase sf Hagree) Helpf Hlpad Lpcf Hred)
                  Hexec
                  with "[Hreg Hmem Hdev] [$Hutlb $Humem $Hcfg] Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
  Qed.

End UvRetireFunnel.

(* ===================================================================== *)
(* §4 The ECALL driver.                                                   *)
(*                                                                        *)
(* [ecall] at User raises E_U_EnvCall with the state UNCHANGED             *)
(* ([exec_execute_ECALL_U]); [uc_del] delegates it to Supervisor, the      *)
(* shared trap tower delivers it, and the CONCRETE frame goes to the       *)
(* capability's [uv_sys_wp] together with the caller's protocol payload    *)
(* at the number in a7.  Nothing comes back: what the syscall does is      *)
(* entirely the protocol's business.                                      *)
(* ===================================================================== *)

Lemma uv_prog_ecall (sa sf : mstate) (w : mword 32) (pc : mword 64) :
  register_lookup cur_privilege sa.(sregs) = User ->
  exec (dispatchInterrupt User) sa = Some (None, sa) ->
  exec (fetch tt) sa = Some (F_Base w, sf) ->
  exec (ext_decode w) sf = Some (ECALL tt, sf) ->
  eq_vec (register_lookup elp sf.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC sf.(sregs) = pc ->
  register_lookup cur_privilege sf.(sregs) = User ->
  exec (run_hart_active 0) sa
    = Some (Step_Execute
              (rv64d_types.Trap
                 (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc),
               zero_extend' 32 w),
            set_reg sf nextPC (add_vec_int pc 4)).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Help Lpc Lpriv.
  apply (exec_hart_active_progress_base_gen User sa sf _ w (ECALL tt) pc _
           Hpriv Hdisp Hfetch Hdec Help eq_refl Lpc); [ | exact I ].
  apply exec_execute_ECALL_U.
  - rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ].
  - rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ].
Qed.

Section UvEcallPost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* everything from the FETCHED state on, for the ecall trap *)
  Lemma uv_ecall_post_fetch (CIDp : CpuId) (C : ucfg) (pt : uptd)
      (Ψ : usys_protocol Σ) (Φ : mval -> iProp Σ)
      (sg sf : mstate) (b : bool) (mst pc : mword 64) (ib : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (m : regfile) (M : gmap Z (bv 8))
      (elp0 : mword 1) (misa0 : type_of_register misa) :
    user_mstatus_ok ms_v ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec (should_inc_minstret (register_lookup cur_privilege sg.(sregs))) sg
      = Some (b, sg) ->
    register_lookup hart_state
      (set_reg sg (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt ->
    register_lookup cur_privilege sf.(sregs) = User ->
    register_lookup mstatus sf.(sregs) = ms_v ->
    register_lookup scause sf.(sregs) = sc_v ->
    register_lookup stvec sf.(sregs) = uc_stvec C ->
    register_lookup elp sf.(sregs) = elp0 ->
    register_lookup misa sf.(sregs) = misa0 ->
    register_lookup medeleg sf.(sregs) = uc_medeleg C ->
    exec (run_hart_active 0) (set_reg sg (R_bool minstret_increment) b)
      = Some (Step_Execute
                (rv64d_types.Trap
                   (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc), ib),
              set_reg sf nextPC (add_vec_int pc 4)) ->
    mstate_interp sf -∗
    uv_sys_wp C pt Ψ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ pc -∗ nextPC ↦ᵣ pc -∗
    gpr_file m -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
    umem pt M -∗ user_cfg C -∗
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ b -∗
    Ψ (uint (m !!! Regidx a7_idx)) m pc M Φ -∗
    |={⊤ ∖ ↑minstretN ∖ ↑wireN}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) sg = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hmsok HmisaS Help_ne Hsi Hhart_a Lprivf Lmsf Lscf Lstvecf Lelpf
           Lmisaf Lmedlf Hha.
    iIntros "Hint #Hsys Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr
             Hutlb Humem Hcfg Hmst Hmi HPsi".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs_f.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    assert (Tn : forall (r : register) (v : type_of_register r),
              register_lookup r sf.(sregs) = v ->
              register_beq r nextPC = false ->
              register_lookup r (set_reg sf nextPC (add_vec_int pc 4)).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    iAssert (mstate_interp (set_reg sf nextPC (add_vec_int pc 4)))
      with "[Hreg Hmem Hdev]" as "Hint".
    { rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    assert (Hdel_x : bit_to_bool (access_vec_dec
              (register_lookup medeleg (set_reg sf nextPC (add_vec_int pc 4)).(sregs))
              (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true).
    { rewrite (Tn medeleg _ Lmedlf ltac:(vm_compute; reflexivity)).
      exact (uc_del C (E_U_EnvCall tt) eq_refl). }
    pose proof (exec_exception_handler_U
                  (set_reg sf nextPC (add_vec_int pc 4))
                  (rv64d_types.Exception (E_U_EnvCall tt))
                  (xtval_exception_value (E_U_EnvCall tt) (zeros' 64))
                  pc ms_v sc_v (uc_stvec C) elp0
                  (Tn cur_privilege _ Lprivf ltac:(vm_compute; reflexivity))
                  (Tn mstatus _ Lmsf ltac:(vm_compute; reflexivity))
                  (Tn scause _ Lscf ltac:(vm_compute; reflexivity))
                  (Tn stvec _ Lstvecf ltac:(vm_compute; reflexivity))
                  (Tn elp _ Lelpf ltac:(vm_compute; reflexivity))
                  ltac:(rewrite (Tn misa _ Lmisaf ltac:(vm_compute; reflexivity));
                        exact HmisaS)
                  (uc_tvd C)
                  (E_U_EnvCall tt) (zeros' 64) eq_refl eq_refl Hdel_x) as Heh.
    set (s9x := set_reg _ cur_privilege Supervisor) in Heh.
    set (s_trap := set_reg s9x nextPC (stvec_base (uc_stvec C))).
    assert (Hxh : exec (Defs.bind
                    (exception_handler User
                       (make_sync_exception (E_U_EnvCall tt) (zeros' 64)) pc)
                    set_next_pc) (set_reg sf nextPC (add_vec_int pc 4))
                  = Some (tt, s_trap)).
    { rewrite (exec_bind_Some _ _ _ _ _ Heh). unfold s_trap. apply exec_set_next_pc. }
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, s9x; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Lhs_f. }
    assert (Hstep : exec (riscv_step false) sg
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_execute_trap;
        [ exact Hsi | exact Hhart_a | exact Hha | exact Hxh | exact Lhs_trap ]. }
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs)
                        = stvec_base (uc_stvec C)).
    { unfold s_trap; rewrite ?sregs_set_reg. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    assert (Hs' : set_reg s_trap PC (stvec_base (uc_stvec C))
                = utrap_state (set_reg sf nextPC (add_vec_int pc 4))
                    (rv64d_types.Exception (E_U_EnvCall tt))
                    (xtval_exception_value (E_U_EnvCall tt) (zeros' 64))
                    pc ms_v sc_v elp0 (uc_stvec C))
      by (unfold s_trap, s9x; reflexivity).
    rewrite Hs' in Hstep.
    iMod (utrap_ghost (set_reg sf nextPC (add_vec_int pc 4))
            (rv64d_types.Exception (E_U_EnvCall tt))
            (xtval_exception_value (E_U_EnvCall tt) (zeros' 64))
            pc ms_v sc_v stval_v sepc_v pc (add_vec_int pc 4) elp0 (uc_stvec C)
            (Tn elp _ Lelpf ltac:(vm_compute; reflexivity)) Help_ne
            with "[Hreg Hmem Hdev] Hms Hsc Hstval Hsepc Hpriv Hnpc Hpc")
      as "(Hint & Hms & Hsc & Hstval & Hsepc & Hpriv & Hnpc & Hpc)".
    { iFrame "Hreg Hmem Hdev". }
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext. iFrame "Hint".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hsys" $! CIDp Φ m M pc sc_v
              (tval (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)))
              with "[-HPsi] HPsi").
    iExists (utrap_ms elp0 ms_v).
    iSplitR. { iPureIntro. exact (utrap_ms_ok elp0 ms_v Hmsok). }
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hutlb Humem Hcfg".
  Qed.

End UvEcallPost.

Section UvEcall.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* THE ECALL DRIVER.  The process supplies (and relies on) its protocol's
     arm at the number in a7; the kernel's syscall service takes it from
     there, so this WP has no continuation of its own. *)
  Lemma wp_uv_ecall (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (Φ : mval -> iProp Σ) :
    uinstr pt M pc false (ECALL tt) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    Ψ (uint (m !!! Regidx a7_idx)) m pc M Φ -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui.
    destruct Hui as [Hal2 Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
    iIntros "Hcg Hpc HPsi".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgprc)".
    iDestruct "Hcap" as "[#Hintr #Hsys]".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hlin Hgprc]" as "Hcg".
    { rewrite /uv_cap_gpr /uv_cap. iFrame "Hintr Hsys Hlin Hgprc". }
    iApply (wp_uv_step C pt Ψ M m pc with "Hcg Hpc [HPsi]").
    rewrite /uv_step_obl.
    iIntros (CID0 sg ms_v sc_v stval_v sepc_v)
      "%Hmsok %Lpriv %Lms %Lpc %Hdisp #Hamb Hhs Hpriv Hms Hsc Hstval Hsepc
       Hpc Hnpc Hgpr Hutlb Humem Hcfg Hint Hbody".
    iDestruct "Hamb" as "(#Hhw & #Hmin & #Hwinv)".
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hmenv & Hsenv & Hmse & Hsse)".
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmse") as %Lmse.
    iDestruct (reg_valid_dq with "Hreg Hsse") as %Lsse.
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & #Hpma & #Hhtif & #Help & %HmisaS & _ & _ & _ & %Hpma_all
        & _ & _ & %Help_ne & _ & %Hmisaval & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    subst misa0.
    iAssert (user_cfg C)
      with "[Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hmenv Hsenv Hmse Hsse". }
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege sg.(sregs)) sg) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r sg.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    pose proof (T hart_state _ Lhs eq_refl) as Hhart_a.
    pose proof (T PC _ Lpc eq_refl) as LpcA.
    pose proof (T cur_privilege _ Lpriv eq_refl) as LprivA.
    pose proof (T misa _ Lmisa eq_refl) as LmisaA.
    pose proof (T menvcfg _ Lmenv eq_refl) as LmenvA.
    pose proof (T senvcfg _ Lsenv eq_refl) as LsenvA.
    pose proof (T mstateen0 _ Lmse eq_refl) as LmseA.
    pose proof (T sstateen0 _ Lsse eq_refl) as LsseA.
    pose proof (T elp _ Lelp eq_refl) as LelpA.
    pose proof (T mstatus _ Lms eq_refl) as LmsA.
    pose proof (T scause _ Lsc eq_refl) as LscA.
    pose proof (T stvec _ Lstvec eq_refl) as LstvecA.
    pose proof (T medeleg _ Lmedl eq_refl) as LmedlA.
    assert (HSXL : _get_Mstatus_SXL
              (register_lookup mstatus (set_reg sg (R_bool minstret_increment) b).(sregs))
              = 'b"10")
      by (rewrite LmsA; exact (proj1 Hmsok)).
    assert (HpmaA : pma_allows_all
              (register_lookup pma_regions
                 (set_reg sg (R_bool minstret_increment) b).(sregs)))
      by (rewrite (T pma_regions _ Lpma eq_refl); exact Hpma_all).
    pose proof (Hdisp b) as HdispA.
    assert (Hsf : forall sf : mstate,
              (forall r : register, register_beq r tlb = false ->
                 register_lookup r sf.(sregs)
                   = register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs)) ->
              register_lookup PC sf.(sregs) = pc /\
              register_lookup cur_privilege sf.(sregs) = User /\
              register_lookup misa sf.(sregs) = MISA_C /\
              eq_vec (register_lookup elp sf.(sregs))
                     (landing_pad_bits_backwards LP_EXPECTED) = false /\
              agree_on D_u sf dstateU /\
              register_lookup mstatus sf.(sregs) = ms_v /\
              register_lookup scause sf.(sregs) = sc_v /\
              register_lookup stvec sf.(sregs) = uc_stvec C /\
              register_lookup elp sf.(sregs) = elp0 /\
              register_lookup medeleg sf.(sregs) = uc_medeleg C).
    { intros sf Tr. split_and!.
      - rewrite (Tr PC ltac:(vm_compute; reflexivity)). exact LpcA.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
      - rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr elp ltac:(vm_compute; reflexivity)). rewrite LelpA. exact Help_ne.
      - apply agree_u.
        + rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
        + rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)). exact LmenvA.
        + rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)). exact LsenvA.
        + rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)). exact LmseA.
        + rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)). exact LsseA.
        + rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr mstatus ltac:(vm_compute; reflexivity)). exact LmsA.
      - rewrite (Tr scause ltac:(vm_compute; reflexivity)). exact LscA.
      - rewrite (Tr stvec ltac:(vm_compute; reflexivity)). exact LstvecA.
      - rewrite (Tr elp ltac:(vm_compute; reflexivity)). exact LelpA.
      - rewrite (Tr medeleg ltac:(vm_compute; reflexivity)). exact LmedlA. }
    destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
    - iMod (umode_fetch_base_4 pt M w_leaf pc w
              (set_reg sg (R_bool minstret_increment) b)
              Hum Hlok Hcanon Hinpage Hal4 Hbytes HnRVC
              LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
              HSXL HpmaA
              with "[Hreg] [Hmem] Hutlb Humem")
        as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
      { rewrite ?sregs_set_reg. iExact "Hreg". }
      { rewrite ?mem_set_reg. iExact "Hmem". }
      destruct (Hsf sf Tr)
        as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lmsf & Lscf & Lstvecf & Lelpf & Lmedlf).
      iApply (uv_ecall_post_fetch CID0 C pt Ψ Φ sg sf b mst pc (zero_extend' 32 w)
                ms_v sc_v stval_v sepc_v m M elp0 MISA_C
                Hmsok HmisaS Help_ne Hsi Hhart_a Lprivf Lmsf Lscf Lstvecf Lelpf
                Lmisaf Lmedlf
                (uv_prog_ecall _ _ w pc LprivA HdispA Hfetch
                   (Hdecbase sf Hagree) Helpf Lpcf Lprivf)
                with "[Hreg Hmem Hdev] Hsys Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc
                      Hgpr Hutlb Humem Hcfg Hmst Hmi HPsi").
      unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev".
    - iMod (umode_fetch_base_2 pt M w_leaf pc w
              (set_reg sg (R_bool minstret_increment) b)
              Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HnRVC
              LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
              HSXL HpmaA
              with "[Hreg] [Hmem] Hutlb Humem")
        as (sf) "(%Hfetch & %Hmdev & %Tr & Hreg & Hmem & Hutlb & Humem)".
      { rewrite ?sregs_set_reg. iExact "Hreg". }
      { rewrite ?mem_set_reg. iExact "Hmem". }
      destruct (Hsf sf Tr)
        as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lmsf & Lscf & Lstvecf & Lelpf & Lmedlf).
      iApply (uv_ecall_post_fetch CID0 C pt Ψ Φ sg sf b mst pc (zero_extend' 32 w)
                ms_v sc_v stval_v sepc_v m M elp0 MISA_C
                Hmsok HmisaS Help_ne Hsi Hhart_a Lprivf Lmsf Lscf Lstvecf Lelpf
                Lmisaf Lmedlf
                (uv_prog_ecall _ _ w pc LprivA HdispA Hfetch
                   (Hdecbase sf Hagree) Helpf Lpcf Lprivf)
                with "[Hreg Hmem Hdev] Hsys Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc
                      Hgpr Hutlb Humem Hcfg Hmst Hmi HPsi").
      unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev".
  Qed.

End UvEcall.
