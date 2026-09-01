(* ===================================================================== *)
(* UkStepGen.v -- THE X-GENERIC U-MODE-ON-KERNEL STEP ENGINE: UkStep.v's   *)
(* SS3 (the obligation and the Loeb hypothesis), SS5 (the engine) and SS8  *)
(* (the ecall driver) with the SLOT FAMILY as a PARAMETER instead of       *)
(* UexecRet's hardwired one.                                               *)
(*                                                                         *)
(* THIS FILE IS A COMPILED RECEIPT, NOT A DESTINATION.  It is the twin     *)
(* upstream ask (4) asks for IN PLACE: landing the ask deletes this file   *)
(* and re-opens UkStep.v's own SS3/SS5/SS8 inside the same [Context].  The *)
(* measured delta between this file's proof text and UkStep.v's is the     *)
(* receipt -- see claude-notes/design/fd-row-pilot.md SS8 ask (4).         *)
(*                                                                         *)
(* WHAT IS PARAMETERISED, AND WHAT THE ENGINE ACTUALLY USES.  The section  *)
(* takes the return contract [RetF] (over the fixpoint variable) and the   *)
(* fixpoint [X], and re-states [ukb_F'] / [ukont_F'] / [uvb_F'] / [ukc']   *)
(* at them -- literally UexecRet.v's [ukb_F] / [ukont_F] / [uvb_F] / [ukc] *)
(* with [uexec_ret_F] replaced by [RetF] and [uslot] by [X].  The engine   *)
(* proofs then use exactly TWO facts about the pair, both hypotheses of    *)
(* the section:                                                            *)
(*                                                                         *)
(*   [X_unfold]        the fixpoint unfolding, i.e. [X W] read as the      *)
(*                     continuation at the key's own state.  It is used    *)
(*                     ONCE, at the interrupt arm, through [ukc'_run];     *)
(*   [Ret_transparent] the transparent arm: off the ecall cause the return *)
(*                     IS the slot.  Also used once, at the same arm.      *)
(*                                                                         *)
(* NO OTHER ENGINE STEP INSPECTS THE FAMILY.  Everything else in SS3/SS5/  *)
(* SS8 threads [ukb_F'] / [uvb_F'] as opaque payload.                      *)
(*                                                                         *)
(* THE THIRD CONTEXT PARAMETER, AND WHY IT IS NOT A THIRD FACT.  A slot    *)
(* family also decides WHICH ambient TSO contexts it covers.  UexecRet's   *)
(* [uslot] quantifies [CurCtx] INSIDE the fixpoint -- safe at EVERY        *)
(* context; the pilot's [UexecRetFs.uslot_fs] is pinned to one, because    *)
(* its section takes [CurCtx] as an ambient.  Neither is a special case of *)
(* the other, so the generic continuation carries a PREDICATE [Q] on       *)
(* contexts and quantifies [xi] under [Q xi]: [Q := fun _ => True] is the  *)
(* plain family, [Q := fun xi => xi = XI] the enriched one.  This is a     *)
(* parameter of the [Context], not an extra obligation on the engine --    *)
(* the engine never inspects [Q] either; it only carries [Q xi] along the  *)
(* binder it already carries [xi] on.                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import WpGpr RegFile InstrBytes.
Require Import WpIntrCore.
Require Import RiscvExtras.
Require Import WpDecodeBridge DecodeTotalU.
Require Import PtreeType PtTree.
Require Import UptTree.
Require Import UserPtTree.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import UserBytes UserFrame UserClassifyAsm.
Require Import UserExec UserStep UserTrap UserExecFacts.
Require UserTotalU.
Require Import UserActiveClass.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep.
Require Import ProcPtOwn.    (* [proc_pt_wf] *)
Require Import UserPerm.
Require Import UsysMemOk.
Require Import UexecWp UexecSlot UexecRet.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Require Import TsoCtxShim.  (* [own_context_sc]: SC-minted token (cutover seam) *)
Local Open Scope Z_scope.
Import Defs.

(* the trap-file peeler, verbatim from WpUmodeStep.v (a [Local] there) *)
Local Ltac uv_trap_peel :=
  unfold u_trap_rs; cbv zeta;
  repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).

Require Import UkStep.

(* ===================================================================== *)
(* SS0 THE SLOT FAMILY, and the bundle re-stated at it.                    *)
(* ===================================================================== *)
Section UkGen.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* the family: the return contract over the fixpoint variable, and the
     fixpoint itself.  [(uexec_ret_F, uslot)] is the plain instance;
     [(uexec_ret_fs_F γm, uslot_fs γm)] the pilot's enriched one. *)
  Context (RetF : (uvis -d> iPropO Σ) -> mword 64 -> uvis -> iProp Σ).
  Context (X : uvis -d> iPropO Σ).
  (* ...and which ambient TSO contexts the family's slot covers (header) *)
  Context (Q : TsoCtx.CurCtx -> Prop).

  (* UexecRet.[ukb_F] at [RetF] *)
  Definition ukb_F' `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) : iProp Σ :=
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗
       ⌜uvis_sz W' = sz⌝ -∗
       ⌜uvis_fd W' = fdv⌝ -∗
       trapped_machine C pt Rut sz sc stv W' ∗ Rfd (uvis_fd W') ∗
       RetF X sc W' -∗
       WP (Loop : expr riscv_lang))%I.

  (* UexecRet.[ukont_F] at [RetF] *)
  Definition ukont_F' `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) : iProp Σ :=
    (▷ ukb_F' C pt Rfd Rut sz π fdv)%I.

  (* UexecRet.[uvb_F] at [RetF] *)
  Definition uvb_F' `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (uv_amb ∗ uv_regs ∗ ⌜usz_ok sz⌝ ∗ user_ptm_inv pt sz M ∗
     Rfd fdv ∗ user_cfg C ∗
     gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ukont_F' C pt Rfd Rut sz π fdv)%I.

  (* UexecRet.[ukc] at [RetF] / [X], with the context binder guarded by [Q] *)
  Definition ukc' (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
      (szv : Z) (fdv : list fdstate) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd)
       (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ),
       ⌜Q xi⌝ -∗
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) szv = π⌝ -∗
       uvb_F' (CID := h) (XI := xi) C pt Rfd Rut szv π fdv M m pc -∗
       WP (Loop : expr riscv_lang))%I.

  (* ---- THE TWO FACTS ---- *)
  Hypothesis X_unfold : forall W : uvis,
    X W ⊣⊢
    ukc' (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).

  Hypothesis Ret_transparent : forall (sc : mword 64) (W : uvis),
    sc <> uecall_scause -> RetF X sc W ⊣⊢ X W.

  (* the slot at a TRAP-OUT key is the continuation at the running state --
     UexecRet.[uslot_run]'s proof, at the hypothesis *)
  Lemma ukc'_run (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    X (uvis_of_run m pc M π szv fdv) ⊣⊢ ukc' π M szv fdv m pc.
  Proof.
    intros Hx0 Hal. rewrite X_unfold.
    cbn [uvis_tf uvis_M uvis_perm uvis_sz uvis_fd uvis_of_run].
    rewrite (tf_of_resume_gpr m pc Hx0) (tf_of_resume_pc m pc Hal).
    reflexivity.
  Qed.

(* ===================================================================== *)
(* SS2 The bundle, opened and closed -- UkStep SS2's two movers, at
   [uvb_F'].                                                             *)
(* ===================================================================== *)
Section UkGenBundle.
  Context `{CID : CpuId} `{XI : CurCtx}.

  Lemma uvb_elim' (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (sz : Z)
      (π : gmap (mword 27) uperm) (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    uvb_F' C pt Rfd Rut sz π fdv M m pc -∗
    ∃ Mp : gmap Z (bv 8),
    ⌜uk_pt_pure pt sz M Mp⌝ ∗
    uv_amb ∗ uv_regs ∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt Mp ∗
    (* the descriptor fragments come out beside the image, and go back in
       beside it ([uvb_intro']): the engine threads them unchanged, exactly
       as it threads [umem] *)
    Rfd fdv ∗
    user_cfg C ∗ gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ▷ ukb_F' C pt Rfd Rut sz π fdv.
  Proof.
    rewrite /uvb_F' /user_ptm_inv /umem_lazy.
    iIntros "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct "Hpt" as "(Htlb & Hlz & %Hinj & %Hacc)".
    iDestruct "Hlz" as (Mp) "(%Hsub & %Himg & %Hz & [%Hdom Hmem])".
    iExists Mp.
    iSplitR; [ iPureIntro; exact (ukp_intro pt sz M Mp Hsub Himg Hz Hdom Hinj Hacc Hsz) | ].
    rewrite /umem.
    iFrame "Hamb Hur Htlb Hmem Hfrag Hcfg Hg Hpc Hrut". iExact "Hk".
  Qed.

  Lemma uvb_intro' (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (sz : Z)
      (π : gmap (mword 27) uperm) (M Mp : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) :
    uk_pt_pure pt sz M Mp ->
    uv_amb -∗ uv_regs -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt Mp -∗
    Rfd fdv -∗
    user_cfg C -∗ gpr_file m -∗ pc_is pc -∗ Rut pt -∗ ukb_F' C pt Rfd Rut sz π fdv -∗
    uvb_F' C pt Rfd Rut sz π fdv M m pc.
  Proof.
    intros (Hsub & Himg & Hz & Hdom & Hinj & Hacc & Hsz).
    iIntros "Hamb Hur Htlb Hmem Hfrag Hcfg Hg Hpc Hrut Hk".
    rewrite /uvb_F' /user_ptm_inv.
    iFrame "Hamb Hur Hfrag Hcfg Hg Hpc Hrut".
    iSplitR; [ iPureIntro; exact Hsz | ].
    iSplitL "Htlb Hmem".
    { iFrame "Htlb".
      iSplitL; [ | iPureIntro; exact (conj Hinj Hacc) ].
      rewrite /umem_lazy /umem_own. iExists Mp.
      iSplitR; [ iPureIntro; exact Hsub | ].
      iSplitR; [ iPureIntro; exact Himg | ].
      iSplitR; [ iPureIntro; exact Hz | ].
      iSplitR; [ iPureIntro; exact Hdom | ].
      iExact "Hmem". }
    rewrite /ukont_F'. iNext. iExact "Hk".
  Qed.
End UkGenBundle.

(* ===================================================================== *)
(* §3 THE OBLIGATION AND THE LÖB HYPOTHESIS (CpuId-free: the hart is a    *)
(* leading binder, so the induction hypothesis can be re-applied at the   *)
(* RESUMING hart after a migration).                                       *)
(* ===================================================================== *)
Section UkGenObl.
  Context `{XI : CurCtx}.

  (* [sz] is a PARAMETER, not quantified: an instruction step does not call
     sbrk, so the process's break is the same on re-entry.  It used to be
     ∀-bound along with the rest of the ambient, which was harmless while
     [ukc'] quantified [sz] too -- now that the key carries the break, the
     obligation has to be at THE size, and saying so is what makes the
     caller's continuation usable here. *)
  Definition uk_step_obl' (π : gmap (mword 27) uperm) (Kc : iProp Σ) (sz : Z)
      (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (R : iProp Σ) (CIDo : CpuId) (XIo : TsoCtx.CurCtx)
       (C : ucfg) (pt : uptd)
       (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
       (Mp : gmap Z (bv 8)) (t : ptree) (rs1 rsA : regstate)
       (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n),
       (* the ONE line the generic form adds: the fetch obligation re-binds
          the ambient context, so it must say the family covers the one it
          re-binds to.  At [Q := fun _ => True] this is [⌜True⌝]. *)
       ⌜Q XIo⌝ -∗
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) sz = π⌝ -∗
       ⌜uk_pt_pure pt sz M Mp⌝ -∗
       ⌜uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr⌝ -∗
       uv_amb (CID := CIDo) -∗
       (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' (CID := CIDo) C pt Rfd Rut sz π fdv ∗ (Kc ∧ ukc' π M sz fdv m pc)) -∗
       resv_any cpu_id -∗
       hreg_frame rsA u_Drw -∗
       hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
       bytes_own (XI := XIo) (uv_mm t (upa_map pt Mp)) -∗
       uv_res (CID := CIDo) (XI := XIo) pt Mp t usatp pcfg paddr -∗
       swp (fetch tt)
         (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
            (fun (r : ExecutionResult) (ib : mword 32) =>
               uv_step_post (CID := CIDo) C R rs1 (Step_Execute (r, ib)))
            (fun (xv : mword 64) (e : ExceptionType) =>
               uv_step_post (CID := CIDo) C R rs1
                 (Step_Fetch_Failure (Virtaddr xv, e)))
            (fun _ : ext_fetch_addr_error => False)))%I.

  Definition uk_ih' (π : gmap (mword 27) uperm) (Kc : iProp Σ)
      (fdv : list fdstate)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ) (sz : Z),
       ⌜Q xi⌝ -∗
       ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = π⌝ -∗
       uvb_F' (CID := h) (XI := xi) C pt Rfd Rut sz π fdv M m pc -∗
       □ uk_step_obl' π Kc sz fdv M m pc -∗ ▷ Kc -∗ WP (Loop : expr riscv_lang))%I.

  (* the payload the wrapper hands the closer at the cycle's tail *)
  Definition uk_payload' `{CID : CpuId} (sz : Z) (π : gmap (mword 27) uperm)
      (fdv : list fdstate) (Kc : iProp Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64)
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) : iProp Σ :=
    ((Kc ∧ ukc' π M sz fdv m pc) ∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv)%I.

End UkGenObl.

(* ===================================================================== *)
(* §4 THE TWO ARMS.                                                       *)
(* ===================================================================== *)
Section UkGenArms.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* the RETIRING payload: the process runs on, at the new file and pc,
     under the bundle rebuilt from the landing *)
  Lemma uk_psi_active' (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (M Mp : gmap Z (bv 8))
      (m' : regfile) (npc : mword 64) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs2 : regstate) (fdv : list fdstate) :
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    register_lookup (R_bitvector_64 nextPC) rs2 = npc ->
    u_gpr_agree m' rs2 ->
    m' (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    uv_tree_ok pt (upa_map pt Mp) t ->
    tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rs2) ->
    uk_pt_pure pt sz M Mp ->
    uv_amb -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv ∗
          (uvb_F' C pt Rfd Rut sz π fdv M m' npc -∗ WP (Loop : expr riscv_lang))) -∗
    uv_psi C R rs2.
  Proof.
    intros Lhs Lpriv Hmsok Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv Lmste
      Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok Hpure.
    iIntros "#Hamb Hresv Hmm Hres Hk".
    rewrite /uv_psi. iFrame "Hresv".
    iIntros (rs3) "%Htail Hrw Hro Hresv HR".
    iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hcont)".
    iDestruct (uv_land_close C pt Mp m' npc t usatp pcfg paddr User rs2 rs3
                 Htail Lhs Lpriv Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv
                 Lmste Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok
                 with "Hrw Hro Hresv Hmm Hres")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hgpr & Hcfg &
           Hutlb & Humem)".
    iApply "Hcont".
    iApply (uvb_intro' C pt Rfd Rut sz π M Mp m' npc fdv Hpure
              with "Hamb [Hhs Hpriv Hms Hsc Hstval Hsepc] Hutlb Humem Hfdr
                    Hcfg Hgpr Hpc Hrut Hkb").
    rewrite /uv_regs.
    iExists _, _, _, _. iSplitR; [ iPureIntro; exact Hmsok |].
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc".
  Qed.

  (* ---- ARM 1: a pending delegated interrupt.  The frame goes to the
     kernel's obligation as a trapped machine at the trap-out key, with the
     TRANSPARENT arm of the return -- the slot at that same key, which is
     the Löb hypothesis re-packed. *)
  Lemma uk_arm_intr' (Rut : uptd -> iProp Σ) (sz : Z) (π : gmap (mword 27) uperm)
      (Kc : iProp Σ) (M Mp : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA : regstate) (i : InterruptType) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    uv_step_post C (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) rs1
      (Step_Pending_Interrupt (i, Supervisor)).
  Proof.
    intros Hpre Hpure Hal2.
    pose proof Hpre as (Hinj & Htok & Hpins & Lhs & Lpriv & Hmsok & Lpc & Hgag & Lstvec &
            Lmie & Lmdl & Lmedl & Lmenv & Lsatp & Lpcfg & Lpaddr & Lmi & Hx0).
    pose proof Hpins as ((Hmisa & Hsec & Hsenv & Hhtif & Hall & Helpne) &
                         (Hmste & Hsste) & _ & Htlbok).
    pose proof (elp_no_lp _ Helpne) as Lelp.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsA))
                       ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "#Hcert Hany Hrw Hro Hmm Hres".
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    rewrite Lelp.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hmm Hres".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs | uv_trap_peel; exact Lmi | exact I ]. }
    iApply (swp_mono with "[Hmm Hres] [Hany Hrw Hro]").
    2:{ iApply (swp_handle_interrupt_u
                  (u_state rsA (uv_mm t (upa_map pt Mp)))
                  (Interrupt i) None pc
                  (register_lookup (R_bitvector_64 mstatus) rsA)
                  (register_lookup (R_bitvector_64 scause) rsA)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lpriv eq_refl eq_refl Lstvec Lelp HmisaS (uc_tvd C) Lpc
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rsA i eq_refl eq_refl
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros r _; reflexivity) eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs'
                 (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)) u_Drw
                 ltac:(intros r Hr; apply Hag, elem_of_union_l, Hr)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)) u_Dro
                 ltac:(intros r Hr; apply Hag, elem_of_union_r, Hr)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap C pt (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) Mp m t usatp pcfg paddr
              (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C))
              (utrap_scause (Interrupt i) (register_lookup (R_bitvector_64 scause) rsA))
              (tval None) pc
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; exact Lhs)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsok))
              ltac:(uv_trap_peel; apply register_lookup_set)
              (uv_gpr_agree_trap m rsA _ _ _ _ Hgag) Hx0
              ltac:(uv_trap_peel; exact Lstvec)
              ltac:(uv_trap_peel; exact Lmie)
              ltac:(uv_trap_peel; exact Lmdl)
              ltac:(uv_trap_peel; exact Lmedl)
              ltac:(uv_trap_peel; exact Lmenv)
              ltac:(uv_trap_peel; exact Hmste)
              ltac:(uv_trap_peel; exact Hsste)
              ltac:(uv_trap_peel; exact Hsenv)
              ltac:(uv_trap_peel; exact Lsatp)
              ltac:(uv_trap_peel; exact Lpcfg)
              ltac:(uv_trap_peel; exact Lpaddr)
              Htok ltac:(uv_trap_peel; exact Htlbok)
              with "Hany Hmm Hres []").
    iIntros "Hframe (Hkc & Hrut & Hfdr & Hkb)".
    iApply ("Hkb" $! (uvis_of_run m pc M π sz fdv)
              (utrap_scause (Interrupt i) (register_lookup (R_bitvector_64 scause) rsA))
              (tval None) with "[%] [%] [%] [Hframe Hrut Hfdr Hkc]");
      [ reflexivity | reflexivity | reflexivity | ].
    iSplitL "Hframe Hrut".
    { iApply (trapped_of_uv_trap_frame C pt Rut _ _ m pc M Mp sz π fdv Hpure Hx0
                with "Hframe Hrut"). }
    (* the bundle takes the descriptor view back at the trap ([ukb_F]'s
       second conjunct); the key is built AT [fdv], so this is [Rfd fdv] *)
    iSplitL "Hfdr"; [ iExact "Hfdr" | ].
    (* THE ONLY TWO PLACES THE ENGINE INSPECTS THE FAMILY: the goal here is
       [ukb_F']'s body, i.e. [RetF X _ _], and it is discharged by the
       transparent arm plus the fixpoint's reading at the running key. *)
    iApply (bi.equiv_entails_1_2 _ _
              (Ret_transparent _ (uvis_of_run m pc M π sz fdv)
                 (utrap_scause_intr_ne i (register_lookup (R_bitvector_64 scause) rsA)))).
    rewrite (ukc'_run m pc M π sz fdv Hx0 Hal2).
    iDestruct "Hkc" as "[_ Hkc]". iExact "Hkc".
  Qed.

End UkGenArms.

(* ===================================================================== *)
(* §5 THE ENGINE.                                                         *)
(* ===================================================================== *)
Section UkGenStepEngine.
  Context `{XI : CurCtx}.

  Lemma wp_uk_step_gen' (π : gmap (mword 27) uperm) (Kc : iProp Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    ⊢ uk_ih' π Kc fdv M m pc.
  Proof.
    intros Hal2.
    rewrite /uk_ih'.
    iLöb as "IH".
    iIntros (CID XIv C pt Rfd Rut sz) "%HQ %Hlo %Hpm Hb #Hobl Hkc".
    iDestruct (uvb_elim' with "Hb")
      as (Mp) "(%Hpure & #Hamb & Hregs & Hutlb & Humem & Hfdv & Hcfg & Hgpr & Hpc & Hrut & Hk)".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iDestruct "Hregs" as (ms_v sc_v stval_v sepc_v)
      "(%Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc)".
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (mst mi mc micfg) "(Hminstret & Hmincr & #Hmcnt & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hmcycle & Hmtime & Hmip)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & #Hmedl & Hmenv & #Hsenv &
                          #Hmste & #Hsste & Hctr & Hhpmb)".
    iDestruct "Hctr" as (mcenv scenv) "[#Hmcen #Hscen]".
    iDestruct "Hhpmb" as (hpm) "#Hhpm".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenvhw &
        _ & _ & _ & _ & %Hpmaall & _ & _ & %Helpne & _ &
        %Hmisaeq & %Hseceq & _ & #Hcert & _)".
    iDestruct (gpr_file_x0 m (mword_of_int 0)
                 ltac:(apply (u_uint_mword5 0); lia) with "Hgpr")
      as "[%Hx0 Hgpr]".
    iDestruct (uv_pt_open pt Mp with "Hutlb Humem")
      as (t usatp tlbvec pcfg paddr)
         "(%Hinj & %Htok & %Hsatpok & %Hpmpok & %Htlbok &
           Hsatp & Htlb & Hpcfg & Hpaddr & #Hclaims & Hmm & Hcl)".
    pose proof Hpmpok as (HpA & Hpord & HpX & HpW & HpR & Hpcov).
    (* ---- the entry file ---- *)
    set (RS := u_rs m (HART_ACTIVE tt) mi mc (mword_of_int 0 : mword 32)
                 mcenv scenv hpm elp0 pmar0 None pcfg paddr tlbvec
                 pc pc ms_v sc_v stval_v sepc_v mst cy ti ip micfg
                 misa0 mseccfg0 (mword_of_int 0 : mword 64)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C) (uc_medeleg C)
                 MENVCFG_S (mword_of_int 0 : mword 64) usatp).
    iDestruct (u_frames_intro RS (uc_dqc C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (u_rs_pins_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_tick _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_cfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr
                       Hminstret Hmincr Hmcnt Hmicfg Hmcycle Hmtime Hmip
                       Hstvec Hmie Hmdl Hmedl Hmenv Hmste Hsste
                       Hmcen Hscen Hhpm
                       Hmisa Hmseccfg Hpma Hhtif Help Hsenv
                       Hsatp Htlb Hpcfg Hpaddr")
      as "[Hrw Hro]".
    (* ---- the ambient pins, at the entry file and after the prelude ---- *)
    assert (HpinsR : u_exec_pins pt t RS).
    { rewrite /u_exec_pins /u_hw_pins /u_cfg_pins /u_pt_pins.
      split_and!;
        [ exact Hmisaeq | exact Hseceq | reflexivity | reflexivity
        | exact Hpmaall | exact Helpne
        | reflexivity | reflexivity
        | exists usatp; split; [ exact Hsatpok | reflexivity ]
        | exact HpA | exact Hpord | exact HpX | exact HpW | exact HpR
        | exact Hpcov
        | exact Htlbok ]. }
    assert (Hpre : uv_pre C pt Mp m pc t RS (wrap_pre RS) usatp pcfg paddr).
    { rewrite /uv_pre. split_and!.
      - exact Hinj.
      - exact Htok.
      - exact (uv_pins_wpre pt t RS HpinsR).
      - rewrite (wrap_pre_other hart_state RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other cur_privilege RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mstatus) RS
                   ltac:(vm_compute; reflexivity)). exact Hmsok.
      - rewrite (wrap_pre_other (R_bitvector_64 PC) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - apply uv_gpr_agree_wpre.
        exact (u_rs_gpr_agree m (HART_ACTIVE tt) mi mc _ mcenv scenv hpm elp0
                 pmar0 None pcfg paddr tlbvec pc pc ms_v sc_v stval_v sepc_v
                 mst cy ti ip micfg misa0 mseccfg0 _ (uc_stvec C) (uc_mie C)
                 (uc_mideleg C) (uc_medeleg C) MENVCFG_S _ usatp).
      - rewrite (wrap_pre_other (R_bitvector_64 stvec) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mie) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mideleg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 medeleg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 menvcfg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 satp) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other pmpcfg_n RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other pmpaddr_n RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - exact (wrap_pre_mi RS).
      - exact Hx0. }
    pose proof Hpre as (_ & _ & HpinsA & LhsA & LcpA & HmsokA & LpcA & _ &
                        LstvecA & LmieA & LmdlA & LmedlA & LmenvA & LsatpA &
                        LpcfgA & LpaddrA & LmiA & _).
    pose proof HpinsA as (HhwA & HcfgpA & _ & _).
    assert (HagdA : agree_on D_u
              (u_state (wrap_pre RS) (uv_mm t (upa_map pt Mp))) dstateU)
      by exact (UserTotalU.u_agree_decode (wrap_pre RS) (uv_mm t (upa_map pt Mp))
                  LcpA LmenvA HhwA HcfgpA).
    (* the kernel obligation's later-free body ([uvb_elim'] already gave it
       under one later) goes into the payload; the wrapper strips the later *)
    (* ---- the one cycle ---- *)
    iApply (swp_exec_step_full u_Drw u_Dro (u_Df (uc_dqc C)) RS (wrap_pre RS)
              (uv_land RS) (uv_psi C (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut))
              u_disj u_w_cy u_w_ti u_w_ip u_in_priv u_w_hart u_in_hart
              u_in_mc u_in_micfg u_w_mi u_in_mi u_w_ms u_in_ms
              u_w_PC u_in_PC u_in_nPC
              (eq_refl : register_lookup hart_state RS = HART_ACTIVE tt)
              ltac:(intros st rs2 H; exact (proj1 H))
              ltac:(intros st rs2 H; exact (proj1 (proj2 H)))
              ltac:(intros r _; reflexivity)
              with "Hcert Hresv Hrw Hro [Hmm Hcl] [Hkc Hrut Hfdv Hk]").
    - (* ================= THE BODY SLOT ================= *)
      iIntros "Hfrag Hrw Hro".
      iApply (swp_mono with "[] [-]").
      2: iApply (swp_run_hart_active_res u_Drw u_Dro (u_Df (uc_dqc C))
                   (wrap_pre RS) User
                   (resv_frag cpu_id None ∗
                    bytes_own (uv_mm t (upa_map pt Mp)) ∗
                    uv_res pt Mp t usatp pcfg paddr)%I
                   (fun (ii : InterruptType) (pr : Privilege) =>
                      uv_step_post C (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) RS
                        (Step_Pending_Interrupt (ii, pr)))
                   (fun (r : ExecutionResult) (ib : mword 32) =>
                      uv_step_post C (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) RS
                        (Step_Execute (r, ib)))
                   (fun (xv : mword 64) (e : ExceptionType) =>
                      uv_step_post C (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) RS
                        (Step_Fetch_Failure (Virtaddr xv, e)))
                   (fun _ : ext_fetch_addr_error => False%I)
                   u_disj u_in_priv u_in_PC u_w_nPC LcpA
                   with "Hcert Hrw Hro [Hfrag Hmm Hcl] [] []").
      + (* the outcome map: the three shapes this tier rules out are
           [False] on our side and anything at all on the rule's *)
        iIntros (st) "H". rewrite /uv_step_post.
        destruct st as [ [ii pr] | x | [[xv] e] | [r ib] | wq ].
        * iDestruct "H" as (rs2) "[%Hq H]".
          iExists rs2. iSplitR; [ by iPureIntro |]. iApply "H".
        * iExFalso. iExact "H".
        * iDestruct "H" as (rs2) "[%Hq H]". iExFalso. iExact "H".
        * destruct r as [u | i0 | wr0 | u1 | u2 | trp | u3 | ec | ed | u4];
            [ destruct u | | | | | destruct trp as [[p exc] pcx] | | | | ];
            iDestruct "H" as (rs2) "[%Hq H]";
            try (iExFalso; iExact "H");
            iExists rs2; (iSplitR; [ by iPureIntro |]); iApply "H".
        * iExFalso. iExact "H".
      + (* the threaded residue *)
        rewrite /uv_res. iFrame "Hfrag Hmm Hclaims Hcl".
      + (* ---- THE DISPATCH ---- *)
        iIntros "HWd Hrw Hro".
        iApply (swp_mono with "[HWd] [Hrw Hro]").
        2:{ iApply (swp_dispatchInterrupt_U u_Drw u_Dro (u_Df (uc_dqc C))
                      (wrap_pre RS) dstateU D_u
                      (register_lookup mip (wrap_pre RS)) (uc_mie C)
                      (uc_mideleg C) u_disj u_in_ip u_in_mie u_in_mdl
                      eq_refl LmieA LmdlA (uc_mm C) UserTotalU.u_D_u_sub HagdA
                      (UserTotalU.s0_ext_S dstateU ltac:(vm_compute; reflexivity))
                      ltac:(reflexivity)
                      with "Hcert Hrw Hro"). }
        iIntros (o). iDestruct 1 as (meip seip) "(%Hd & Hrw & Hro)".
        destruct o as [[ii pr] |].
        * assert (Hsup : pr = Supervisor).
          { rewrite <- u_dispatch_of_pending in Hd. unfold u_dispatch in Hd.
            destruct (neq_vec (s_pending (register_lookup mip (wrap_pre RS))
                                 meip seip (uc_mie C) (uc_mideleg C))
                        (zeros' 64)); [| discriminate Hd].
            destruct (findPendingInterrupt
                        (s_pending (register_lookup mip (wrap_pre RS)) meip seip
                           (uc_mie C) (uc_mideleg C))); [| discriminate Hd].
            congruence. }
          subst pr.
          iDestruct "HWd" as "(Hfrag & Hmm & Hres)".
          iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
          iApply (uk_arm_intr' C pt Rfd Rut sz π Kc M Mp m pc t usatp pcfg paddr RS
                    (wrap_pre RS) ii fdv Hpre Hpure Hal2
                    with "Hcert Hany Hrw Hro Hmm Hres").
        * iFrame.
      + (* ---- THE FETCH: the caller's obligation ---- *)
        iIntros "HWd Hrw Hro".
        iDestruct "HWd" as "(Hfrag & Hmm & Hres)".
        iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
        iApply ("Hobl" $! (uk_payload' sz π fdv Kc M m pc C pt Rfd Rut) CID XIv C pt Rfd Rut Mp t RS
                  (wrap_pre RS) usatp pcfg paddr
                  with "[%] [%] [%] [%] [%] Hamb [] Hany Hrw Hro Hmm Hres");
          [ exact HQ | exact Hlo | exact Hpm | exact Hpure | exact Hpre | ].
        rewrite /uk_payload'. iIntros "(Hkc & Hrut & Hfdr & Hkb)". iFrame "Hrut Hfdr Hkb Hkc".
    - (* ================= THE CYCLE'S TAIL ================= *)
      iNext. iIntros (rs3 rs2) "%Hag Hrw Hro [Hresv Hcl]".
      iApply ("Hcl" $! rs3 with "[%] Hrw Hro Hresv [Hkc Hrut Hfdv Hk]");
        [ exact (uv_tail_of RS rs2 rs3 Hag) | ].
      rewrite /uk_payload'.
      (* [Hfdv] is the [Rfd fdv] [uvb_elim'] handed out at the cycle's head;
         the payload carries it back to the next bundle.  NOT [Hfrag] --
         that name is taken twice below, by the fetch's [HWd] split. *)
      iSplitL "Hkc"; [ | iFrame "Hrut Hfdv Hk" ].
      iSplit; [ iExact "Hkc" | ].
      rewrite /ukc'. iIntros (h' xi' C' pt' Rfd' Rut') "%HQ' %Hlo' %Hpm' Hb".
      rewrite /uk_ih'.
      iApply ("IH" $! h' xi' C' pt' Rfd' Rut' sz with "[%] [%] [%] Hb Hobl [Hkc]");
        [ exact HQ' | exact Hlo' | exact Hpm' | iNext; iExact "Hkc" ].
  Qed.

End UkGenStepEngine.

(* ===================================================================== *)
(* §6 THE RETIRE FUNNEL: WpUmodeStep's §6-§7 with the payload re-typed.  *)
(* ===================================================================== *)
Section UkGenFunnel.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  (* the ambient context is one the family covers -- [I] at [Q := True] *)
  Hypothesis (HQ0 : Q XI).

  (* the engine at the ambient hart and table *)
  Lemma wp_uk_step' (Kc : iProp Σ) (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    uvb_F' C pt Rfd Rut sz π fdv M m pc -∗ □ uk_step_obl' π Kc sz fdv M m pc -∗
    ▷ Kc -∗ WP (Loop : expr riscv_lang).
  Proof.
    intros Hal2.
    iIntros "Hb #Hobl Hkc".
    iPoseProof (wp_uk_step_gen' π Kc M m pc fdv Hal2) as "H". rewrite /uk_ih'.
    iApply ("H" $! CID XI C pt Rfd Rut sz with "[%] [%] [%] Hb Hobl Hkc");
      [ exact HQ0 | exact Hlo | exact Hpm ].
  Qed.

End UkGenFunnel.

(* ===================================================================== *)
(* §8 THE ECALL DRIVER: the trapped machine and the caller's [RetF X]  *)
(* at the ecall cause go to the kernel obligation.                        *)
(* ===================================================================== *)
Section UkGenEcallPost.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  Lemma uk_ecall_post_fetch' (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rs2 : regstate) (fdv : list fdstate) :
    (forall s : mstate,
       register_lookup cur_privilege s.(sregs) = User ->
       register_lookup (R_bitvector_64 PC) s.(sregs) = pc ->
       goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bitvector_64 misa) rs2 = MISA_C ->
    eq_vec (register_lookup (R_bitvector_1 elp) rs2)
      (landing_pad_bits_backwards LP_EXPECTED) = false ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs2) ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    uk_pt_pure pt sz M Mp ->
    gen_cert -∗
    (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv ∗ RetF X uecall_scause (uvis_of_run m pc M π sz fdv)) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt Mp)) -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc 4) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc 4) rs2) u_Dro -∗
    swp (execute (ECALL tt))
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rs1 (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hg Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmisa2 Helpne2 Lmi2
      Htlbok2 Htok' Hpure.
    set (rsx := register_set nextPC (add_vec_int pc 4) rs2).
    (* every named pin survives the [nextPC := pc+4] write *)
    assert (Tx : forall (r : register) (val : type_of_register r),
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rs2 = val -> register_lookup r rsx = val).
    { intros r val Hne Hv. unfold rsx.
      rewrite (irrelevant_register_set r (R_bitvector_64 nextPC) rs2 _ Hne).
      exact Hv. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by exact (Tx (R_bitvector_64 PC) _ ltac:(vm_compute; reflexivity) Lpc2).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by exact (Tx cur_privilege _ ltac:(vm_compute; reflexivity) Lcp2).
    assert (Lhsx : register_lookup hart_state rsx = HART_ACTIVE tt)
      by exact (Tx hart_state _ ltac:(vm_compute; reflexivity) Lhs2).
    assert (Hmsx : user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsx))
      by (rewrite (Tx (R_bitvector_64 mstatus) _
                     ltac:(vm_compute; reflexivity) eq_refl); exact Hms2).
    assert (Lstvecx : register_lookup (R_bitvector_64 stvec) rsx = uc_stvec C)
      by exact (Tx (R_bitvector_64 stvec) _ ltac:(vm_compute; reflexivity) Lstvec2).
    assert (Lmiex : register_lookup (R_bitvector_64 mie) rsx = uc_mie C)
      by exact (Tx (R_bitvector_64 mie) _ ltac:(vm_compute; reflexivity) Lmie2).
    assert (Lmdlx : register_lookup (R_bitvector_64 mideleg) rsx = uc_mideleg C)
      by exact (Tx (R_bitvector_64 mideleg) _ ltac:(vm_compute; reflexivity) Lmdl2).
    assert (Lmedlx : register_lookup (R_bitvector_64 medeleg) rsx = uc_medeleg C)
      by exact (Tx (R_bitvector_64 medeleg) _ ltac:(vm_compute; reflexivity) Lmedl2).
    assert (Lmenvx : register_lookup (R_bitvector_64 menvcfg) rsx = MENVCFG_S)
      by exact (Tx (R_bitvector_64 menvcfg) _ ltac:(vm_compute; reflexivity) Lmenv2).
    assert (Lmstex : register_lookup (R_bitvector_64 mstateen0) rsx
                     = (mword_of_int 0 : mword 64))
      by exact (Tx (R_bitvector_64 mstateen0) _ ltac:(vm_compute; reflexivity) Lmste2).
    assert (Lsstex : register_lookup (R_bitvector_32 sstateen0) rsx
                     = (mword_of_int 0 : mword 32))
      by exact (Tx (R_bitvector_32 sstateen0) _ ltac:(vm_compute; reflexivity) Lsste2).
    assert (Lsenvx : register_lookup (R_bitvector_64 senvcfg) rsx
                     = (mword_of_int 0 : mword 64))
      by exact (Tx (R_bitvector_64 senvcfg) _ ltac:(vm_compute; reflexivity) Lsenv2).
    assert (Lsatpx : register_lookup (R_bitvector_64 satp) rsx = usatp)
      by exact (Tx (R_bitvector_64 satp) _ ltac:(vm_compute; reflexivity) Lsatp2).
    assert (Lpcfgx : register_lookup pmpcfg_n rsx = pcfg)
      by exact (Tx pmpcfg_n _ ltac:(vm_compute; reflexivity) Lpcfg2).
    assert (Lpaddrx : register_lookup pmpaddr_n rsx = paddr)
      by exact (Tx pmpaddr_n _ ltac:(vm_compute; reflexivity) Lpaddr2).
    assert (Lmisax : register_lookup (R_bitvector_64 misa) rsx = MISA_C)
      by exact (Tx (R_bitvector_64 misa) _ ltac:(vm_compute; reflexivity) Lmisa2).
    assert (Helpnex : eq_vec (register_lookup (R_bitvector_1 elp) rsx)
                        (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite (Tx (R_bitvector_1 elp) _
                     ltac:(vm_compute; reflexivity) eq_refl); exact Helpne2).
    assert (Lmix : register_lookup (R_bool minstret_increment) rsx
              = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
                  (register_lookup (R_bitvector_64 minstretcfg) rs1)
                  (register_lookup cur_privilege rs1))
      by exact (Tx (R_bool minstret_increment) _ ltac:(vm_compute; reflexivity) Lmi2).
    assert (Ltlbx : register_lookup tlb rsx = register_lookup tlb rs2)
      by exact (Tx tlb _ ltac:(vm_compute; reflexivity) eq_refl).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. rewrite (Hgag2 q Hnz). symmetry.
      exact (Tx (R_bitvector_64 (gpr_of_Z (uint q))) _ (regbeq_gpr_nextPC (uint q)) eq_refl). }
    pose proof (elp_no_lp _ Helpnex) as Lelpx.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsx))
                       ('b"1") = true)
      by (rewrite Lmisax; vm_compute; reflexivity).
    assert (Hdel : bit_to_bool (access_vec_dec
              (register_lookup (R_bitvector_64 medeleg) rsx)
              (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true)
      by (rewrite Lmedlx; exact (uc_del C (E_U_EnvCall tt) eq_refl)).
    pose proof (exec_execute_ECALL_U (u_state rsx ∅) pc Lcpx Lpcx) as Hex.
    iIntros "#Hcert Hk Hany Hmm Hres Hrw Hro".
    iAssert (bytes_own (∅ : gmap Arch.pa (bv 8))) as "#Hemp";
      [ by rewrite /bytes_own big_sepM_empty |].
    iPoseProof (TsoCtxShim.own_context_sc XI) as "Hrun".
    (* ---- the execute: one node, no memory ---- *)
    iApply (swp_mono with "[Hk Hmm Hres] [Hany Hrw Hro Hrun]").
    2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C))
                  (execute (ECALL tt)) (u_state rsx ∅) (u_state rsx ∅)
                  (rv64d_types.Trap
                     (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc))
                  rsx ∅ u_disj Du_r_sub Du_w_sub
                  ltac:(intros q _; reflexivity) (map_empty_subseteq _)
                  (Hg (u_state rsx ∅) Lcpx Lpcx) Hex
                  with "Hcert Hany Hrw Hro Hrun Hemp"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost" as (rs3 mm3)
      "(%Hag3 & _ & _ & Hrw & Hro & _ & _ & Hany)".
    iApply (run_exec_post_direct
              (fun (r : ExecutionResult) (ib' : mword 32) =>
                 uv_step_post C R rs1 (Step_Execute (r, ib'))) ib
              (rv64d_types.Trap
                 (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc)) I).
    (* ---- the trap tower ---- *)
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    assert (Lelp3 : register_lookup (R_bitvector_1 elp) rs3
                    = landing_pad_bits_backwards NO_LP_EXPECTED)
      by (rewrite (Hag3 _ u_in_elp); exact Lelpx).
    rewrite Lelp3.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
               (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
               (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hmm Hres Hk".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs2 | uv_trap_peel; exact Lmi2 | exact I ]. }
    iApply (swp_mono with "[Hk Hmm Hres] [Hany Hrw Hro]").
    2:{ iApply (swp_exec_trap_u (u_state rsx ∅)
                  (rv64d_types.Exception (E_U_EnvCall tt))
                  (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                  (register_lookup (R_bitvector_64 mstatus) rsx)
                  (register_lookup (R_bitvector_64 scause) rsx)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lcpx eq_refl eq_refl Lstvecx Lelpx HmisaS (uc_tvd C)
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rs3
                  (E_U_EnvCall tt) (zeros' 64) eq_refl eq_refl Hdel
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Hag3 eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                    (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                    (uc_stvec C)) u_Drw
                 ltac:(intros q Hq; apply Hag, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                    (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                    (uc_stvec C)) u_Dro
                 ltac:(intros q Hq; apply Hag, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap C pt R Mp m t' usatp pcfg paddr
              (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                 (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                 (uc_stvec C))
              (utrap_scause (rv64d_types.Exception (E_U_EnvCall tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_U_EnvCall tt) (zeros' 64))) pc
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; exact Lhs2)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsx))
              ltac:(uv_trap_peel; apply register_lookup_set)
              (uv_gpr_agree_trap m rsx _ _ _ _ Hgagx) Hx0
              ltac:(uv_trap_peel; exact Lstvec2)
              ltac:(uv_trap_peel; exact Lmie2)
              ltac:(uv_trap_peel; exact Lmdl2)
              ltac:(uv_trap_peel; exact Lmedl2)
              ltac:(uv_trap_peel; exact Lmenv2)
              ltac:(uv_trap_peel; exact Lmste2)
              ltac:(uv_trap_peel; exact Lsste2)
              ltac:(uv_trap_peel; exact Lsenv2)
              ltac:(uv_trap_peel; exact Lsatp2)
              ltac:(uv_trap_peel; exact Lpcfg2)
              ltac:(uv_trap_peel; exact Lpaddr2)
              Htok'
              ltac:(uv_trap_peel; exact Htlbok2)
              with "Hany Hmm Hres [Hk]").
    iIntros "Hframe HR".
    iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hret)".
    iApply ("Hkb" $! (uvis_of_run m pc M π sz fdv)
              (utrap_scause (rv64d_types.Exception (E_U_EnvCall tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)))
              with "[%] [%] [%] [Hframe Hrut Hfdr Hret]");
      [ reflexivity | reflexivity | reflexivity | ].
    iSplitL "Hframe Hrut".
    { iApply (trapped_of_uv_trap_frame C pt Rut _ _ m pc M Mp sz π fdv Hpure Hx0
                with "Hframe Hrut"). }
    (* the bundle takes the descriptor view back at the trap ([ukb_F]'s
       second conjunct); the key is built AT [fdv], so this is [Rfd fdv] *)
    iSplitL "Hfdr"; [ iExact "Hfdr" | ].
    rewrite utrap_scause_ecall. iExact "Hret".
  Qed.

End UkGenEcallPost.

Section UkGenEcall.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  Hypothesis (HQ0 : Q XI).

  Lemma wp_uk_ecall' (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (fdv : list fdstate) :
    uk_instr π M pc false (ECALL tt) ->
    (forall s : mstate,
       register_lookup cur_privilege s.(sregs) = User ->
       register_lookup (R_bitvector_64 PC) s.(sregs) = pc ->
       goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
    uvb_F' C pt Rfd Rut sz π fdv M m pc -∗
    RetF X uecall_scause (uvis_of_run m pc M π sz fdv) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hg.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hret".
    iApply (wp_uk_step' C pt Rfd Rut π sz Hlo Hpm HQ0 _ M m pc fdv Hal2
              with "Hb [] [Hret]").
    2:{ iNext. iExact "Hret". }
    iModIntro.
    rewrite /uk_step_obl'.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' Mp' t rs1 rsA usatp pcfg paddr)
      "%HQo %Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hmm Hres".
    iAssert (R -∗ Rut' pt' ∗ Rfd' fdv ∗ ukb_F' (CID := CIDo) C' pt' Rfd' Rut' sz π fdv ∗
             RetF X uecall_scause (uvis_of_run m pc M π sz fdv))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[Hkc _]". iFrame "Hrut Hfdr Hkb". iExact "Hkc". }
    destruct (uk_instr_mapped π M Mp' pc false (ECALL tt) pt' sz
                (loop_ok_wf C' pt' Hlo') Hpm' Hpure Hui)
      as [Hal2' Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    assert (Hfetch : exists (rsf : regstate) (t' : ptree),
              exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt' Mp')))
                = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt' Mp'))) /\
              goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt' Mp')))
                (uv_mm t (upa_map pt' Mp')) = true /\
              u_tlb_only rsA rsf /\
              tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) /\
              uv_tree_ok pt' (upa_map pt' Mp') t' /\
              pt_same_shape 2 t t').
    { destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      - destruct (uv_fetch_4 pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        exists rsf, t'. split_and!;
          [ exact Hfe | exact Hfg | exact Tr | exact Htlbok' | exact Htok'
          | exact Hshape ].
      - destruct (uv_fetch_base_2_pg pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal2' Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        exists rsf, t'. split_and!;
          [ exact Hfe | exact Hfg | exact Tr | exact Htlbok' | exact Htok'
          | exact Hshape ]. }
    destruct Hfetch as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
    iApply (uv_swp_fetch pt' Mp' t t' (uc_dqc C') rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt' Mp' t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt' t' rs2).
    { apply (u_pins_move pt' t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, (ECALL tt), pc, 8%nat.
    iSplitR.
    { iPureIntro. exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w (ECALL tt) Hagd2
               (Hdecbase dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_ecall_post_fetch' C' pt' Rfd' R Rut' sz π M Mp' m pc (zero_extend' 32 w) t' usatp
              pcfg paddr rs1 rs2 fdv Hg
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              Hmisa2 Helpne2
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Htok' Hpure
              with "Hcert Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UkGenEcall.

Section UkGenPostFetch.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* everything from the FETCHED file on: the leaf's value-precise execute,
     and the payload that rebuilds [uvb_F'] at the new file *)
  Lemma uk_retire_post_fetch' (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (k : Z)
      (i : instruction) (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rs2 : regstate) (fdv : list fdstate) :
    uv_wrok wr ->
    uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs2) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    uk_pt_pure pt sz M Mp ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv ∗
          (uvb_F' C pt Rfd Rut sz π fdv M (uv_upd m wr) (uv_next jt (add_vec_int pc k)) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt Mp)) -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc k) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc k) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rs1 (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hwrok Hred Hg1 Hg2 Hexec Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2
      Lmie2 Lmdl2 Lmedl2 Lmenv2 Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2
      Lmi2 Htlbok2 Hagd2 Htok' Hpure.
    set (rsx := register_set nextPC (add_vec_int pc k) rs2).
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc).
    { unfold rsx.
      rewrite (irrelevant_register_set (R_bitvector_64 PC)
                 (R_bitvector_64 nextPC) rs2 _ ltac:(vm_compute; reflexivity)).
      exact Lpc2. }
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc k)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User).
    { unfold rsx.
      rewrite (irrelevant_register_set cur_privilege
                 (R_bitvector_64 nextPC) rs2 _ ltac:(vm_compute; reflexivity)).
      exact Lcp2. }
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc k) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    pose proof (Hexec (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                  (uv_gpr_vals m rsx Hgagx Hx0)) as Hex.
    iIntros "#Hcert #Hamb Hk Hany Hmm Hres Hrw Hro".
    iApply (uv_swp_exec (uc_dqc C) rsx i o
              (uv_post (u_state rsx ∅) jt wr) ib _
              Hred
              (Hg1 (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                 (uv_gpr_vals m rsx Hgagx Hx0))
              (Hg2 (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                 (uv_gpr_vals m rsx Hgagx Hx0))
              Hex with "Hcert Hany Hrw Hro [Hk Hmm Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hany".
    rewrite uv_post_sregs in Hag3.
    rewrite /uv_step_post.
    iExists (uv_post_rs rsx jt wr).
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (uv_land_reg rs2 _ jt wr hart_state _
                   ltac:(vm_compute; reflexivity) uv_nogpr_hart Lhs2)
        | exact (uv_land_reg rs2 _ jt wr (R_bool minstret_increment) _
                   ltac:(vm_compute; reflexivity) uv_nogpr_minc Lmi2)
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 (uv_post_rs rsx jt wr) u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3
                 (uv_post_rs rsx jt wr) u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uk_psi_active' C pt Rfd R Rut sz π M Mp (uv_upd m wr)
              (uv_next jt (add_vec_int pc k)) t' usatp pcfg paddr
              (uv_post_rs rsx jt wr) fdv
              (uv_land_reg rs2 _ jt wr hart_state _
                 ltac:(vm_compute; reflexivity) uv_nogpr_hart Lhs2)
              (uv_land_reg rs2 _ jt wr cur_privilege _
                 ltac:(vm_compute; reflexivity) uv_nogpr_priv Lcp2)
              ltac:(rewrite (uv_land_reg rs2 _ jt wr (R_bitvector_64 mstatus) _
                               ltac:(vm_compute; reflexivity) uv_nogpr_mst eq_refl);
                    exact Hms2)
              (uv_land_nextPC rs2 (add_vec_int pc k) jt wr)
              (uv_gpr_agree_post m rsx jt wr Hwrok Hgagx)
              (uv_upd_x0 m wr Hwrok Hx0)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 stvec) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_stvec Lstvec2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mie) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mie Lmie2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mideleg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mdl Lmdl2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 medeleg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_medl Lmedl2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 menvcfg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_menv Lmenv2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mstateen0) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mste Lmste2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_32 sstateen0) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_sste Lsste2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 senvcfg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_senv Lsenv2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 satp) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_satp Lsatp2)
              (uv_land_reg rs2 _ jt wr pmpcfg_n _
                 ltac:(vm_compute; reflexivity) uv_nogpr_pcfg Lpcfg2)
              (uv_land_reg rs2 _ jt wr pmpaddr_n _
                 ltac:(vm_compute; reflexivity) uv_nogpr_paddr Lpaddr2)
              Htok'
              ltac:(rewrite (uv_land_reg rs2 _ jt wr tlb _
                               ltac:(vm_compute; reflexivity) uv_nogpr_tlb eq_refl);
                    exact Htlbok2)
              Hpure
              with "Hamb Hany Hmm Hres Hk").
  Qed.

End UkGenPostFetch.

(* ===================================================================== *)
(* §6c THE OBLIGATION, once per FETCH SHAPE.                              *)
(* ===================================================================== *)
Section UkGenObligation.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  Lemma uk_obl_base' (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (M Mp : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (w : mword 32) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (t t' : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA rsf : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt Mp))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      (uv_mm t (upa_map pt Mp)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    uv_wrok wr -> uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv ∗
          (uvb_F' C pt Rfd Rut sz π fdv M (uv_upd m wr) (uv_next jt (add_vec_int pc 4)) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hwrok Hred Hg1 Hg2 Hexec.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt Mp t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt Mp t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, i, pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_retire_post_fetch' C pt Rfd R Rut sz π M Mp m pc 4 i o jt wr
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2 fdv
              Hwrok Hred Hg1 Hg2 Hexec
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Hagd2 Htok' Hpure
              with "Hcert Hamb Hk Hany Hmm Hres Hrw Hro").
  Qed.

  Lemma uk_obl_rvc' (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (M Mp : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (h : mword 16) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (t t' : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA rsf : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt Mp))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      (uv_mm t (upa_map pt Mp)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    uv_wrok wr -> uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ Rfd fdv ∗ ukb_F' C pt Rfd Rut sz π fdv ∗
          (uvb_F' C pt Rfd Rut sz π fdv M (uv_upd m wr) (uv_next jt (add_vec_int pc 2)) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hwrok Hred Hg1 Hg2 Hexec.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt Mp t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt Mp t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_retire_post_fetch' C pt Rfd R Rut sz π M Mp m pc 2 i o jt wr
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2 fdv
              Hwrok Hred Hg1 Hg2 Hexec
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Hagd2 Htok' Hpure
              with "Hcert Hamb Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UkGenObligation.

(* ===================================================================== *)
(* §7 THE RETIRE FUNNEL.  One [uk_instr] fact + one value-precise execute  *)
(* obligation = one verified instruction, stated against [uvb_F'] with the    *)
(* continuation [ukc'] (re-binding the table).  [wp_uk_retire_later'] hands  *)
(* the step's own later out; [wp_uk_retire'] is the later-free form.        *)
(* ===================================================================== *)
Section UkGenRetire.
  Context `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  Hypothesis (HQ0 : Q XI).

  Lemma wp_uk_retire_later' (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (fdv : list fdstate)
      (is_rvc : bool) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) :
    uk_instr π M pc is_rvc i ->
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
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
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
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
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
    uvb_F' C pt Rfd Rut sz π fdv M m pc -∗
    ▷ ukc' π M sz fdv (uv_upd m wr) (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hcont".
    iApply (wp_uk_step' C pt Rfd Rut π sz Hlo Hpm HQ0 _ M m pc fdv Hal2
              with "Hb [] Hcont").
    iModIntro.
    rewrite /uk_step_obl'.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' Mp' t rs1 rsA usatp pcfg paddr)
      "%HQo %Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hmm Hres".
    destruct (uk_instr_mapped π M Mp' pc _ i pt' sz
                (loop_ok_wf C' pt' Hlo') Hpm' Hpure Hui)
      as [Hal2' Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    (* the continuation at THIS table, out of the table-generic one *)
    iAssert (R -∗ Rut' pt' ∗ Rfd' fdv ∗ ukb_F' C' pt' Rfd' Rut' sz π fdv ∗
             (uvb_F' (CID := CIDo) C' pt' Rfd' Rut' sz π fdv M (uv_upd m wr)
                (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
              WP (Loop : expr riscv_lang)))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[Hkc _]".
      iFrame "Hrut Hfdr Hkb". iIntros "Hb".
      rewrite /ukc'.
      iApply ("Hkc" $! CIDo XIo C' pt' Rfd' Rut' with "[%] [%] [%] Hb");
        [ exact HQo | exact Hlo' | exact Hpm' ]. }
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* 4-aligned: one 4-byte read, low half is the instruction *)
        destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes Mp' (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt' Mp' t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanon Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uk_obl_rvc' C' pt' Rfd' R Rut' sz π M Mp' m pc h i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdecrvc
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
      + (* 2 mod 4: one 2-byte read *)
        destruct (uv_fetch_rvc_2 pt' Mp' t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanon Hal2' Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_obl_rvc' C' pt' Rfd' R Rut' sz π M Mp' m pc h i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdecrvc
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uk_obl_base' C' pt' Rfd' R Rut' sz π M Mp' m pc w i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdecbase
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_base_2_pg pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal2' Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_obl_base' C' pt' Rfd' R Rut' sz π M Mp' m pc w i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdecbase
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every leaf takes *)
  Lemma wp_uk_retire' (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (is_rvc : bool) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) :
    uk_instr π M pc is_rvc i ->
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
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
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
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
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
    uvb_F' C pt Rfd Rut sz π fdv M m pc -∗
    ukc' π M sz fdv (uv_upd m wr) (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec.
    iIntros "Hb Hcont".
    iApply (wp_uk_retire_later' M m pc fdv is_rvc i o jt wr
              Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec with "Hb [Hcont]").
    iNext. iExact "Hcont".
  Qed.

End UkGenRetire.

End UkGen.

(* ===================================================================== *)
(* SS9 THE PLAIN INSTANCE: [(uexec_ret_F, uslot)], and the RECOVERY       *)
(* CHECK.                                                                 *)
(*                                                                        *)
(* The two facts are UexecRet.v's own [uslot_unfold] and                   *)
(* [uexec_ret_transparent] -- the first with the vacuous [Q] premise       *)
(* inserted, the second [exact].  The recovery check below is the point of *)
(* the file: ONE type, [uk_ecall_ty], inhabited twice -- by UkStep.v's     *)
(* exported [wp_uk_ecall] and by the generic engine at the plain family.   *)
(* Both inhabitations are [exact], so the generic form is not merely       *)
(* equivalent to the hardwired one, it is CONVERTIBLE with it.             *)
(* ===================================================================== *)
Section UkGenPlain.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* fact (i) at [uslot]: the fixpoint unfolding.  [Q] is [True] here, so
     the only difference from [uslot_unfold] is one vacuous premise. *)
  Lemma uslot_unfold_gen (W : uvis) :
    uslot W ⊣⊢
    ukc' uexec_ret_F uslot (fun _ : TsoCtx.CurCtx => Logic.True) (uvis_perm W) (uvis_M W)
      (uvis_sz W) (uvis_fd W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof.
    rewrite (uslot_unfold W) /ukc'.
    iSplit.
    - iIntros "H" (h xi C pt Rfd Rut) "_ %Hlo %Hpm Hb".
      iApply ("H" $! h xi C pt Rfd Rut with "[%] [%] Hb");
        [ exact Hlo | exact Hpm ].
    - iIntros "H" (h xi C pt Rfd Rut) "%Hlo %Hpm Hb".
      iApply ("H" $! h xi C pt Rfd Rut with "[%] [%] [%] Hb");
        [ exact I | exact Hlo | exact Hpm ].
  Qed.

  (* fact (ii) at [uexec_ret_F] IS UexecRet's transparent arm *)
  Lemma uexec_ret_transparent_gen (sc : mword 64) (W : uvis) :
    sc <> uecall_scause -> uexec_ret_F uslot sc W ⊣⊢ uslot W.
  Proof. exact (uexec_ret_transparent sc W). Qed.

  (* UkStep.v's exported ecall-driver type, spelled out once *)
  Definition uk_ecall_ty `{CID : CpuId} `{XI : CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm) (sz : Z)
      (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π) : Prop :=
    forall (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64)
      (fdv : list fdstate),
      uk_instr π M pc false (ECALL tt) ->
      (forall s : mstate,
         register_lookup cur_privilege s.(sregs) = User ->
         register_lookup (R_bitvector_64 PC) s.(sregs) = pc ->
         goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
      uvb C pt Rfd Rut sz π fdv M m pc -∗
      uexec_ret uecall_scause (uvis_of_run m pc M π sz fdv) -∗
      WP (Loop : expr riscv_lang).

  (* inhabitant 1: upstream's own constant *)
  Lemma uk_ecall_ty_upstream `{CID : CpuId} `{XI : CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (π : gmap (mword 27) uperm) (sz : Z)
      (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π) :
    uk_ecall_ty C pt Rfd Rut π sz Hlo Hpm.
  Proof. exact (UkStep.wp_uk_ecall C pt Rfd Rut π sz Hlo Hpm). Qed.

  (* inhabitant 2: the X-generic engine at [(uexec_ret_F, uslot, True)] *)
  Lemma uk_ecall_ty_gen `{CID : CpuId} `{XI : CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ) (π : gmap (mword 27) uperm) (sz : Z)
      (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π) :
    uk_ecall_ty C pt Rfd Rut π sz Hlo Hpm.
  Proof.
    exact (wp_uk_ecall' uexec_ret_F uslot (fun _ : TsoCtx.CurCtx => Logic.True)
             uslot_unfold_gen uexec_ret_transparent_gen
             C pt Rfd Rut π sz Hlo Hpm I).
  Qed.

End UkGenPlain.

(* ===================================================================== *)
(*  SS10.  THE DIFF-SHAPED ASK, MEASURED AGAINST THE CURRENT TEXT         *)
(*                                                                        *)
(*  (2026-09-01, fd-row lane 2, against UkStep.v at e66817bce.)  COMPILED, *)
(*  not proposed: every line below is in this file and the file is green   *)
(*  on the mirror in 18s, with the plain instance's recovery an [exact].   *)
(* ===================================================================== *)
(*                                                                        *)
(*  WHAT UPSTREAM WOULD DO, IN PLACE.  Open one [Section] around           *)
(*  UkStep.v's SS3 / SS4 / SS5 / SS6 / SS6b / SS6c / SS7 / SS8 with        *)
(*                                                                        *)
(*    Context (RetF : (uvis -d> iPropO Sigma) -> mword 64 -> uvis          *)
(*                    -> iProp Sigma).                                     *)
(*    Context (X : uvis -d> iPropO Sigma).                                 *)
(*    Hypothesis X_unfold        : ... (the fixpoint unfolding)            *)
(*    Hypothesis Ret_transparent : ... (the transparent arm)               *)
(*                                                                        *)
(*  move UexecRet.v's [ukb_F] / [ukont_F] / [uvb_F] / [ukc] bodies inside  *)
(*  it as [ukb_F'] / [ukont_F'] / [uvb_F'] / [ukc'], and substitute        *)
(*  [uvb -> uvb_F'], [ukb -> ukb_F'], [ukc -> ukc'],                       *)
(*  [uexec_ret -> RetF X], [uslot_run -> ukc'_run],                        *)
(*  [uexec_ret_transparent -> Ret_transparent] throughout.  Then close the *)
(*  section and re-export the plain instance at [(uexec_ret_F, uslot)].    *)
(*                                                                        *)
(*  THE MEASURED DELTA (this file's copied region vs UkStep.v, mechanical) *)
(*                                                                        *)
(*    1585  lines of UkStep.v carried over (SS2's two movers, SS3, SS4,    *)
(*          SS5, SS6, SS6b, SS6c, SS7, SS8).  SS1's pure facts and         *)
(*          [trapped_of_uv_trap_frame] mention no slot family at all and   *)
(*          are REUSED by [Require Import UkStep], not copied.             *)
(*     130  of those lines touched by the substitution, and NOTHING else:  *)
(*          52 statement / section / definition lines, 70 proof-body       *)
(*          lines, 8 comment lines.  (Nine of the 130 are the              *)
(*          [Context riscvGS] lines the enclosing section now owns.)       *)
(*      +0  new proof STEPS.  Not one tactic was added, deleted or         *)
(*          reordered for the generalisation itself: the substitution IS   *)
(*          the diff.                                                      *)
(*     249  hand-written lines here (this header, SS0, SS9) -- of which    *)
(*          SS0's four definitions and two hypotheses are ~60 and the      *)
(*          plain-instance recovery is ~80.                                *)
(*                                                                        *)
(*  THE TWO-FACTS CLAIM HELD, EXACTLY AS FILED.  No third fact was         *)
(*  needed: [X_unfold] and [Ret_transparent] are each used ONCE, both in   *)
(*  [uk_arm_intr'], and every other proof threads the family as opaque     *)
(*  payload.                                                               *)
(*                                                                        *)
(*  WHAT THE ASK DID NOT ANTICIPATE, AND IT IS A CONTEXT PARAMETER AND     *)
(*  NOT A FACT.  A parallel family also fixes WHICH ambient [CurCtx] its   *)
(*  slot covers.  [UexecRet.uslot] quantifies [xi] INSIDE the fixpoint;    *)
(*  [UexecRetFs.uslot_fs] is pinned to its section's ambient, so           *)
(*  [X_unfold] is not even STATEABLE at the enriched family against a      *)
(*  [ukc'] that quantifies [xi] freely.  The fix is the third [Context]    *)
(*  line, [Q : CurCtx -> Prop], with [ukc'] binding [xi] under [Q xi]:     *)
(*  [Q := fun _ => True] is upstream's family, [Q := fun xi => xi = XI]    *)
(*  the pilot's.  MEASURED COST OF [Q] ON TOP OF THE SUBSTITUTION:         *)
(*  +24 / -14 lines over the whole 1585 -- two statement lines             *)
(*  ([⌜Q XIo⌝] in [uk_step_obl'], [⌜Q xi⌝] in [uk_ih']), three             *)
(*  [Hypothesis (HQ0 : Q XI)] lines (one per driver section), and nine     *)
(*  call sites that pass one more [ [%] ] / [exact].  The engine never     *)
(*  INSPECTS [Q].                                                          *)
(*                                                                        *)
(*  If upstream would rather not carry [Q], the alternative is to make     *)
(*  [UexecRetFs.uslot_fs] quantify [CurCtx] the way [uslot] does -- OUR    *)
(*  file, not theirs, but it moves the ambient out of five files           *)
(*  (UexecRetFs, UkRunSysFs, UkRunFsLeaf, FdRowPilot, UkInitFs) and buys   *)
(*  nothing else.  24 lines here is the cheaper of the two, and it is the  *)
(*  one that keeps the generic engine usable by the NEXT parallel family   *)
(*  without asking it to be context-generic first.                         *)
(*                                                                        *)
(*  WHAT LANDING IT IN PLACE BUYS, COMPILED (UkStepGenFs.v):               *)
(*    - [UkRunSysFs.FDROW_UKFS_STEP.wp_uk_ecall_fs_step] is [wp_uk_ecall'] *)
(*      at [(uexec_ret_fs_F gm, uslot_fs gm)] -- one instantiation;        *)
(*    - [UkRunFsLeaf.FDROW_UKFS_RETIRE.wp_uk_retire_fs_later] is           *)
(*      [wp_uk_retire_later'] at the same pair -- one instantiation;       *)
(*    - both seals of the pilot are therefore THEOREMS, and                *)
(*      UkStepGenSeals.v applies the two walk functors at them, so         *)
(*      [FdRowPilot.wp_pilot_open2] and                                    *)
(*      [UkInitFs.wp_kinit_console_arm_then_loop] audit to the two         *)
(*      platform axioms + funext with no [Parameter] under them --         *)
(*      the SAME assumption set as UkStep.v's own [wp_uk_ecall].           *)
(*    - and UkRunFsLeaf.v's SS2 (~360 lines of re-derived per-kind         *)
(*      wrappers) becomes redundant with UkLeaf.v / UkBranch.v outright.   *)
(*                                                                        *)
(*  THIS FILE IS THE RECEIPT, NOT THE DESTINATION.  Landing ask (4) in     *)
(*  place DELETES UkStepGen.v: SS0 moves into UkStep.v's own section       *)
(*  header, the copied region becomes UkStep.v itself, and SS9's recovery  *)
(*  check becomes UkStep.v's re-export.  UkStepGenFs.v and                 *)
(*  UkStepGenSeals.v survive, shrunk to the two instantiations and the two *)
(*  functor applications.                                                  *)
(* ===================================================================== *)
