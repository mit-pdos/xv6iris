(* ProofUserretClosed.v -- THE TRAP LOOP, closed.

   [SpecUserretClosed]'s theorem is userret's spec with no premise about
   what happens at user mode and no [stvec_handler_wp]: the machine is
   entered where the kernel first enters this loop (forkret's tail, at
   [uva 0x9c]) and runs forever.  What closes it is a Löb induction whose
   cut point is [UserExec.stvec_handler_wp] itself, taken at ANY hart, ANY
   config record and ANY address space:

     userret -> user mode -> uservec -> usertrap -> userret -> ...

   [wp_uservec_pt] already chains usertrap and userret, so one round of the
   loop is ONE application of it: from the trap frame it runs the whole
   kernel excursion and lands back in USER mode, at the resuming hart, with
   the address space in the user view.  All this file does is hand that
   CONCRETE state, and the next round's contract, to the PER-PROCESS
   CONTINUATION user execution itself handed back at the trap.

   THE KEYED CONTRACT (MILESTONE J).  The loop no longer circulates a
   forall-state WP.  Its Löb hypothesis is now [UexecRet.ukb]'s body: the
   trapped machine at the user-visible record [W] that trapped, with the
   cause and tval NAMED, paired with [UexecRet.uexec_ret sc W] -- what a
   verified program can actually produce.  At the round's end the loop
   re-keys that return onto the record the round left ([UexecApply], steps
   A/B: [uexec_ret_run] moves the key onto the run projection the round's
   relation is stated at, then [UexecRound.uround_ok]'s own arm picks which
   of [uexec_ret]'s arms pays), meets [uslot]'s guard by computation, and
   builds the U-mode bundle ([UexecApply.ukc_apply], step D).  Everything
   between the round's post and the next [WP Loop] is in those two named
   lemmas: this is a whole-function continuation, so an inline discharge
   would be paid at every step of the walk (optimization.md, RULE ONE).

   THIS FILE MINTS, AND ONLY ON TWO ARMS (refutation R-c).  [UserretClosed]
   takes a [UEXEC_GEN] again, for exec-success -- where [uround_ok]'s left
   disjunct says NOTHING, by design, because the new program's slot is
   exec's to build -- and for fork, where nothing yet states [r <> 0] (K2).
   The mint goes through [UexecCond.cond_entry_slot], so a process whose key
   qualifies picks up sync's own constructor.  Every other arm spends what
   user execution returned.  See claude-notes/design/user-wp-slot.md.

   TWO THINGS THAT ARE NOT PLUMBING.

   [Rut] IS THE RESIDUE, AND uservec MUST NOT BE GIVEN IT TWICE.  The
   kernel-side bundle parks across user execution as the bundle's [Rut]
   conjunct -- that is what [Rut] is for -- so at the trap it arrives INSIDE
   [trapped_machine].  But [wp_uservec_pt] takes the frame AND the residue
   as separate premises, so handing it both would claim the same bundle
   twice and the precondition would be unsatisfiable.  The loop therefore
   OPENS the frame, takes the residue out, and rebuilds it at
   [Rut := fun _ => emp] for uservec.  Nothing is lost: uservec's own post
   does not mention [Rut] at all.  The residue is WHOLE again (R-a): the
   slot never rides it, so there is no hole to fill -- what crosses
   [wp_uservec_pt]'s park is the loop's own framed [uexec_ret] (K8: nothing
   on that crossing is persistent, so a linear resource travels).

   THE CONFIG RECORD IS REBUILT EVERY ROUND.  [mideleg]'s value is a genuine
   existential of usertrap's exit ([sconf] never pinned it), so the [ucfg]
   the next round runs at is not the one this round ran at -- only its shape
   is.  [loop_ucfg] is that shape, and its three proof fields are what the
   round has to re-establish: [uc_tvd] from stvec's pinned value, [uc_mm]
   from the post's own mask fact, and [uc_del] from [medeleg = MEDELEG_S],
   which is [SpecUserretClosed.medeleg_S_delegates] -- a closed computation, because
   [start()] fixes the delegation word once and nothing writes it again. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile WpNext WpGpr.   (* [gpr_file_x0]: the dead base's x0 *)
Require Import MinstretInv WireInv.
Require Import KernelText MstatusBits.
Require Import RiscvExtras.
Require Import KptExecMap.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import ProcGeom ProcInv.
Require Import FdSlots FileInvDefs.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import SpecUserret SpecUservec SpecUserretClosed.
Require Import UexecWp.      (* [uexec_wp] / [loop_ok] -- the [UEXEC_GEN] the
                                loop MINTS from, and the loop's own guard *)
Require Import ProcPtOwn.    (* [ud_norm] / [ud_norm_id] -- the index re-key *)
Require Import UserPerm.     (* [perm_of] / [usz_ok] -- the key's permissions *)
Require Import UexecSlot.    (* [uvis] / [uvis_of] / [tf_w] *)
Require Import UexecRet.     (* [uslot] / [uexec_ret] / [ukb] / [ukc] /
                                [trapped_machine] -- REQUIRED DIRECTLY: this
                                file puts a [uslot]/[uvb] in the proofmode
                                context and the [Typeclasses Opaque] seal
                                does not travel through a re-export
                                (durable-notes). *)
Require Import UexecApply.   (* the round's tail, as named lemmas *)
Require Import UexecCond.    (* [cond_entry_slot] -- the loop's MINT (R-c) *)
Require Import UserretUser.
Require Import TfPage36.
From Kernel Require KernelSyms.
Require Import UserFrame.  (* [u_regs_pc_is]: the pc_is bundle in u_regs *)
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ParkCap.   (* [park_token] *)
Require Import UsertrapRes.  (* [ut_park_intro_body] -- the park's producer entry *)
Require Import TsoCtx.   (* [CurCtx]: the residue owns a thread token *)
Import Defs.

(* ===================================================================== *)
(* §3 THE LOOP.                                                            *)
(* ===================================================================== *)
(* THE [UEXEC_GEN] ARGUMENT IS BACK (milestone J, R-c): two of the round's
   arms -- exec-success and fork -- are kernel mints by design, so the loop
   needs a generic inhabitant to fall back on.  Everything else it runs is
   the continuation the process itself handed back. *)
Module UserretClosed (R : USERRET) (UV : USERVEC) (UG : UEXEC_GEN).

Section UserretClosed.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  (* userret runs AS the thread, so its residue is at the AMBIENT context
     (tso-port.md: this-thread sites take the ambient ξ). *)
  Context `{XI : CurCtx}.

  (* [Rut], instantiated: the kernel-side bundle, parked inside the trapped
     machine across user execution -- WHOLE, not holed.  R-a deleted the
     hole: the slot no longer rides the residue at all, the LOOP frames
     [UexecRet.uexec_ret] across [wp_uservec_pt]'s park crossing instead
     (K8: nothing on that crossing is persistent, so a linear resource
     travels).  Hart-indexed because the residue is.

     THE SIZE IS PART OF THE PREDICATE, and it is not decoration.
     [UV.wp_uservec_pt] takes the entry frame at the RESIDUE INDEX's own
     [p->sz], while the loop holds it at the [sz] the key was resumed under;
     nothing else ties the two, so the park records the tie it establishes
     by construction.  The DESCRIPTOR needs no such row: [loop_ok]'s
     [ud_data = ud_pas] makes [ProcPtOwn.ud_norm] the identity on [pt], so
     the loop re-keys the index onto [pt] itself when it reads the residue
     back ([UV.usertrap_res_bare_norm]). *)
  (* [sts] is ∃-packed here beside [ksp] and [U]: [Rut] is [uptd -> iProp],
     so the loop carries the residue without naming its index.  Stage B --
     the fd resource in [uvb] -- is what gives the key a name for it. *)
  Definition Rut_at (h : CpuId) (sz : Z) : uptd -> iProp Σ :=
    fun p => (∃ (ksp : mword 64) (U : ustate) (sts : list fdstate),
                ⌜uint (pv_sz (us_V U)) = sz⌝ ∗
                UV.usertrap_res_bare (CID := h) p ksp U sts)%I.

  Lemma Rut_at_intro (h : CpuId) (sz : Z) (p : uptd) (ksp : mword 64)
      (U : ustate) (sts : list fdstate) :
    uint (pv_sz (us_V U)) = sz ->
    UV.usertrap_res_bare (CID := h) p ksp U sts -∗ Rut_at h sz p.
  Proof.
    intros Hsz. iIntros "H". rewrite /Rut_at. iExists ksp, U, sts.
    iSplitR; [ iPureIntro; exact Hsz | iExact "H" ].
  Qed.

  Lemma stvec_handler_loop (j : nat) :
    (j < NPROC)%nat ->
    kernel_text -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    wire_inv -∗
    (* THE ROUND'S ENTRY, NAMED (milestone J).  It used to be the ∃-hidden
       [user_trap_frame] paired with a [uexec_wp]; it is now the trapped
       machine at the user-visible record [W] that trapped, with the cause
       and tval named, PAIRED with what user execution handed back there
       ([UexecRet.uexec_ret sc W]).  That pair is exactly [UexecRet.ukb]'s
       body, which is what makes this Löb hypothesis the kernel obligation
       the process's own continuation consumes. *)
    □ (∀ (h : CpuId) (C : ucfg) (pt : uptd) (sz : Z)
         (W : uvis) (sc stv : mword 64),
         ⌜loop_ok C pt⌝ -∗
         ⌜uvis_perm W = perm_of (ud_um pt) sz⌝ -∗
         (* the key carries the break now, and the round below reads it *)
         ⌜uvis_sz W = sz⌝ -∗
         hw_config (CID := h) -∗
         (* [minstret_inv] is [emp] post-port: no hart index left *)
         minstret_inv -∗
         (trapped_machine (CID := h) C pt (Rut_at h sz) sz sc stv W
          ∗ uexec_ret sc W) -∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hj.
    iIntros "#Hkt #Hclaim #Hwire".
    (* THE LOOP MINTS (refutation R-c).  Two of the round's arms are kernel
       mints by design -- exec-success, where [uround_ok]'s left disjunct
       says nothing at all, and fork, where nothing yet says [r <> 0] (K2)
       -- so [UserretClosed] takes a [UEXEC_GEN] again.  Through
       [UexecCond.cond_entry_slot], not the bare generic inhabitant, so a
       process whose key qualifies picks up sync's own constructor. *)
    iAssert (□ (∀ W : uvis, uslot W))%I as "#Hmk".
    { iPoseProof UG.uexec_wp_gen as "#Hgen".
      iModIntro. iIntros (W).
      iApply (UexecCond.cond_entry_slot W with "Hgen"). }
    iLöb as "IH".
    iIntros "!>" (h C pt sz W sc stv) "%Hok %Hperm %Hszw #Hhw #Hmin [Hframe Hret]".
    destruct Hok as (Hstv & Hdqc & Hmie & Hmedl & Hnorm & Hptwf).
    (* ---- open the trapped machine.  [user_cfg] stays BUNDLED: the frame
           uservec takes is the same predicate at [Rut := emp], so nothing
           has to be taken apart and rebuilt here. ---- *)
    iEval (rewrite /trapped_machine /user_trap_frame_atm) in "Hframe".
    iDestruct "Hframe" as (ms_v)
      "(%Hlen & %Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc &
        Hpc & Hgpr & Hupt & Hcfg & Hrut)".
    (* [Rut_at] packs three: the stack, the record, and the descriptor
       states the residue is indexed by. *)
    iDestruct "Hrut" as (ksp U0 sts0) "[%Hsz Hures]".
    (* put [Hszw] in terms of the residue's size FIRST: otherwise [subst sz]
       has two equations to choose from and takes the wrong one. *)
    rewrite <- Hsz in Hszw.
    subst sz.
    (* THE INDEX, RE-KEYED ONTO [pt].  The round's relation reads its entry
       permission map off the residue index's own descriptor, and the loop
       needs that to be the table it resumed under; [loop_ok]'s
       [ud_data = ud_pas] makes the renormalisation the identity. *)
    iDestruct (UV.usertrap_res_bare_norm pt ksp U0 with "Hures") as "Hures".
    rewrite (ud_norm_id pt Hnorm).
    (* ---- rebuild the frame for uservec at the EMPTY residue ---- *)
    iDestruct (user_trap_frame_atm_intro C pt (fun _ : uptd => emp%I)
                 (uint (pv_sz (us_V (us_upt U0 pt)))) (uvis_M W)
                 ms_v sc stv (tf_w (uvis_tf W) tf_epc_idx)
                 (tf_resume_gpr0 (uvis_tf W)) Hmsok
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr Hupt Hcfg []")
      as "Hframe".
    { done. }
    (* ---- one round.  [Hret] -- the linear [uexec_ret] user execution
           handed back -- is FRAMED across the crossing (R-a / K8). ---- *)
    iApply (UV.wp_uservec_pt C pt (fun _ : uptd => emp%I) j ksp
              (us_upt U0 pt) sts0 (uvis_M W) (tf_resume_gpr0 (uvis_tf W))
              ms_v sc stv (tf_w (uvis_tf W) tf_epc_idx)
              Hstv Hdqc Hmie Hj Hnorm Hptwf
              with "Hkt Hhw Hmin Hclaim Hframe Hures [-]").
    iApply wp_next_intro. iIntros (CID').
    rewrite /uservec_post.
    iIntros (pt' mf ms' usatp uepc sc' stval' mdv0 U2 sts2)
      "%Huptpt' %Hround' %Hpcret' %Hgprtie'
       %Hpttf %Hmapwf %Hsatpr %Hnorm' %Hptwf' %Hmm %Hretms %Hacc'
       Hhs' Hpriv' Hms' Hmie' Hmdl' Hmenv' Hstvec' #Hsenv' Hsc' Hstval' Hsepc'
       Hupt' Hpc' Hgpr' Hures' #Hhw' #Hmin'".
    (* the three frozen CSRs, duplicated out of the residue for [user_cfg] *)
    iDestruct (UV.usertrap_res_csrs_open (CID := CID') pt' ksp U2 with "Hures'")
      as "[Hcsrs Hcback]".
    iDestruct "Hcsrs" as "(Hssc' & #Hmedl' & #Hmse' & #Hsse')".
    iDestruct ("Hcback" with "[Hssc']") as "Hures'".
    { iFrame "Hssc' Hmedl' Hmse' Hsse'". }
    (* the counter cells, at the hart the round LANDED on *)
    iDestruct (hw_config_counters with "Hhw'") as (scen' hpm') "[#Hscen' #Hhpm']".
    iDestruct (UV.usertrap_res_sstc pt' ksp U2 with "Hures'") as "[Hsstc' Hures']".
    iDestruct "Hsstc'" as (mcen') "[#Hmcen' _]".
    (* xv6's own bound on [p->sz], read off the residue -- [UexecRet.uvb]'s
       size guard.  Pure conclusion, so the bundle stays whole. *)
    iDestruct (UV.usertrap_res_bare_sz pt' ksp U2 with "Hures'") as "%Hszb".
    assert (Hszok : usz_ok (uint (pv_sz (us_V U2))))
      by exact (usz_ok_of_maxsz _ Hszb).
    destruct Hretms as (_ & _ & HSXL & HTVM & HMXR & HTSR & HFS & HVS & _
                        & HXS & HSD & HMPP & HSPIE).
    (* [pc_is] is ONE resource post-port -- it carries [minstret_res],
       [clock_res] and [resv_any] beside the two cells, so splitting it off
       into PC/nextPC drops the riders on the floor (worklist 13.2). *)
    iAssert (u_regs (CID := CID') (HART_ACTIVE tt) (sret_ms5 ms') sc' stval'
               uepc (ret_pc uepc) (ret_pc uepc) mf)
      with "[Hhs' Hpriv' Hms' Hsc' Hstval' Hsepc' Hpc' Hgpr']" as "Hregs'".
    { rewrite u_regs_pc_is.
      iFrame "Hhs' Hpriv' Hms' Hsc' Hstval' Hsepc' Hpc' Hgpr'". }
    iAssert (user_cfg (CID := CID') (loop_ucfg mdv0 Hmm))
      with "[Hstvec' Hmie' Hmdl' Hmenv']" as "Hcfg'".
    { rewrite /user_cfg /=.
      iFrame "Hstvec' Hmie' Hmdl' Hmenv' Hmedl' Hsenv' Hmse' Hsse'".
      iSplitR; [iExists mcen', scen'; iFrame "Hmcen' Hscen'"
               | iExists hpm'; iFrame "Hhpm'"]. }
    (* the residue, parked at the size the next round will resume under *)
    (* the residue comes back at whatever states the round left ([sts2'],
       named where [uservec_post] handed it over); [Rut_at] packs them. *)
    iDestruct (Rut_at_intro CID' (uint (pv_sz (us_V U2))) pt' ksp U2 _ eq_refl
                 with "Hures'") as "Hrut'".
    (* ---- STEPS A/B: the returned [uexec_ret], re-keyed onto the record
           the round left ([UexecApply]).  The round is stated at the RUN
           projection of the trapped key, and its entry permission map is
           the key's own once the index has been re-keyed onto [pt]. ---- *)
    assert (Hpi0 : perm_of (ud_um (pv_upt (us_V (us_upt U0 pt))))
                     (uint (pv_sz (us_V (us_upt U0 pt)))) = uvis_perm W)
      by (rewrite Hperm; reflexivity).
    unfold uv_round in Hround'.
    rewrite Hpi0 in Hround'.
    (* ...and the same for the break, which the key carries now *)
    assert (Hsz0 : uint (pv_sz (us_V (us_upt U0 pt))) = uvis_sz W)
      by exact (eq_sym Hszw).
    rewrite Hsz0 in Hround'.
    iDestruct (uexec_ret_round_slot_of sc W (tf_resume_gpr0 (uvis_tf W))
                 (tf_w (uvis_tf W) tf_epc_idx) U2 Hlen eq_refl eq_refl Hround'
                 with "Hmk Hret") as "Hslot".
    (* ---- STEPS C/D: the guard, and the bundle, both inside the named
           lemma -- the loop only says which key it is at. ---- *)
    (* THE RESUMED KEY'S DESCRIPTOR VIEW is the one that trapped: user
       execution runs no kernel code, and the loop's choice for the syscall
       arms (which ∀-bind it) is the same value -- see
       [UexecApply.uexec_ret_round_slot]'s header. *)
    assert (Hpi2 : uvis_perm (uvis_of U2 (uvis_fd W))
                   = perm_of (ud_um pt') (uint (pv_sz (us_V U2))))
      by (cbn [uvis_of uvis_perm]; rewrite Huptpt'; reflexivity).
    (* [Rfd] AT [emp], FOR NOW.  The bundle has the slot for the process's
       descriptor view but the loop does not yet put the fragments in it:
       they stay in the residue ([UsertrapRes.ut_own]'s named [sts]), and
       moving them across is the next increment.  What this buys already is
       that every layer between here and the program proofs carries the
       view's RESOURCE POSITION, so that move is a change to this file and
       the residue accessors rather than to the engine. *)
    iApply (uslot_apply_loop (CID := CID') (loop_ucfg mdv0 Hmm) pt'
              (fun _ : list fdstate => emp)%I
              (Rut_at CID' (uint (pv_sz (us_V U2)))) (uint (pv_sz (us_V U2)))
              (uvis_fd W)
              (uvis_of U2 (uvis_fd W)) (us_M U2) mf
              (sret_ms5 ms') sc' stval' uepc (ret_pc uepc)
              (loop_ok_loop_ucfg mdv0 Hmm pt' Hnorm' Hptwf')
              Hszok
              (user_mstatus_ok_sret_ms5 ms' HSXL HMXR HFS HVS HTVM HTSR
                 HXS HSD HMPP HSPIE)
              Hpi2 eq_refl eq_refl eq_refl (eq_sym Hgprtie') (eq_sym Hpcret')
              with "Hslot Hhw' Hmin' Hwire Hregs' Hupt' [] Hcfg' Hrut' [-]").
    (* the bundle's [Rfd fdv] premise, which is [emp] while [Rfd] is
       instantiated at [λ _, emp] -- this is the goal the fragments will
       discharge once they move out of the residue *)
    { iEmpIntro. }
    (* the next round's contract, under the later the bundle takes it at --
       which is exactly the shape of the Löb hypothesis.  A GENUINE Löb back
       edge, so [iNext] and not [bi.later_intro]. *)
    iNext. rewrite /ukb /ukb_F.
    (* the fd pin is DROPPED here: the Löb hypothesis is ∀-general in the
       key, so the next round is proved at whatever descriptor view the
       trap-out key names. *)
    (* the middle conjunct is [Rfd (uvis_fd W2)] = [emp] at this
       instantiation, so it is dropped; when the fragments move in, this is
       where the loop takes them back and closes the residue with them. *)
    iIntros (W2 sc2 stv2) "%Hp2 %Hs2 %Hf2 (Hframe2 & _ & Hret2)".
    iApply ("IH" $! CID' (loop_ucfg mdv0 Hmm) pt' (uint (pv_sz (us_V U2)))
              W2 sc2 stv2 with "[%] [%] [%] Hhw' Hmin' [$Hframe2 $Hret2]").
    - exact (loop_ok_loop_ucfg mdv0 Hmm pt' Hnorm' Hptwf').
    - exact Hp2.
    - exact Hs2.
  Qed.

End UserretClosed.
End UserretClosed.

(* ===================================================================== *)
(* §4 THE ENTRY POINT: userret, run once, with the loop underneath.        *)
(* ===================================================================== *)
Module UserretClosedProof (R : USERRET) (UV : USERVEC) (UG : UEXEC_GEN)
  : USERRET_CLOSED.

  (* the dovetail no longer names [USER]: it runs WHATEVER slot it is handed,
     and neither does this functor -- the entry mints nothing either. *)
  Module RU := UserretUser R.
  Module LP := UserretClosed R UV UG.

Section Res.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the residue is uservec's, re-exported unchanged *)
  Definition usertrap_res := UV.usertrap_res.
  Definition usertrap_res_parked := UV.usertrap_res_parked.
  Definition usertrap_res_tlb_close := UV.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := UV.usertrap_res_tlb_open.
  Definition usertrap_res_bare := UV.usertrap_res_bare.
  Definition usertrap_res_pt_close := UV.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := UV.usertrap_res_pt_open.
  Definition usertrap_res_ptm_close := UV.usertrap_res_ptm_close.
  Definition usertrap_res_ptm_open := UV.usertrap_res_ptm_open.
  Definition usertrap_res_bare_norm := UV.usertrap_res_bare_norm.
  Definition usertrap_res_csrs_open := UV.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UV.usertrap_res_sstc.
  Definition usertrap_res_bare_sz := UV.usertrap_res_bare_sz.
  Definition usertrap_res_tf_csrs_open := UV.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := UV.usertrap_res_tf_open.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun h : CpuId => UV.usertrap_res_bare (CID := h))
        (park_token (un_s N)) N av
    := UV.usertrap_res_bare_park N av.

End Res.

  Theorem wp_userret_closed
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (C : ucfg) (pt : uptd)
      (kroot : mword 44) (j : nat) (ksp : mword 64)
      (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64) (U : ustate)
      (fdv : list fdstate) :
      wp_userret_closed_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt kroot j ksp m usatp mstatus0 sepc0 sc_v stval_v U fdv fdv.
  Proof.
    cbv beta delta [wp_userret_closed_body].
    intros Hok Hj Hretms Hwf Ha0 Hsatpr Hinj Hacc.
    destruct Hretms as (HSIE & HMPRV & HSXL & HTVM & HMXR & HTSR & HFS & HVS & Hsup
                        & HXS & HSD & HMPP & HSPIE).
    pose proof Hok as Hlok.   (* the dovetail wants it whole; the loop's own
                                bullet and the premise list want the pieces *)
    destruct Hok as (Hstv & Hdqc & Hmie & Hmedl & Hnorm & Hptwf).
    destruct Hsatpr as (HuMode & Huasid & Huppn).
    iIntros "#Hkt #Hhw #Hmin #Hwire #Hclaim #Hkpt Hhs Hpriv Hms Hmiec Hmdlc
             Hmenvc #Hsenvc Hsepc Hsc Hstval Hstvec #Hmedlc #Hmsec #Hssec
             Hktlb Hufr Hdata Hpc Hfile Hkc Hures".
    (* the loop, once: it is [□], so one instance serves every round *)
    iDestruct (LP.stvec_handler_loop j Hj with "Hkt Hclaim Hwire") as "#Hloop".
    (* THE SAVE SLOTS COME OUT OF THE RESIDUE, not from the caller: the
       residue owns the trapframe page, so a boundary that asked for both
       would be unsatisfiable (SpecUserretClosed.v's header).  userret READS
       the 31 words and hands them straight back, and the closer below is
       what makes the bundle whole again before user mode -- the same
       open/close every LOOP round already performs inside
       [wp_uservec_pt]. *)
    (* THE THREE COUNTER-PERMISSION CELLS the user invariant now carries.
       scounteren and mhpmcounter are frozen into [hw_config] at boot (nothing
       ever writes them); mcounteren cannot be -- timerinit writes it after
       that bundle exists -- so it comes out of the residue's own timer
       capability.  All three are [↦ᵣ□], so nothing is spent and nothing has
       to come back. *)
    iDestruct (hw_config_counters with "Hhw") as (scen hpm) "[#Hscen #Hhpm]".
    iDestruct (usertrap_res_sstc pt ksp U with "Hures") as "[Hsstc Hures]".
    iDestruct "Hsstc" as (mcen) "[#Hmcen _]".
    (* xv6's own bound on [p->sz], off the residue -- [UexecRet.uvb]'s size
       guard, which the dovetail now takes as a premise.  Pure conclusion,
       so the bundle stays whole. *)
    iDestruct (usertrap_res_bare_sz pt ksp U with "Hures") as "%Hszb".
    assert (Hszok : usz_ok (uint (pv_sz (us_V U))))
      by exact (usz_ok_of_maxsz _ Hszb).
    (* THE TRAPFRAME WORDS userret is about to read.  NO SLOT COMES OUT WITH
       THEM any more (refutation R-a): the continuation this entry runs is
       the one the PARK deposited and the caller hands over ([Hkc]), so the
       plain [_tf_open] replaces the combined [_run_open], whose only reader
       this was. *)
    iDestruct (usertrap_res_tf_open pt ksp U with "Hures") as "Hopen".
    iDestruct "Hopen" as (kroot') "(#Hkpt' & %Hokws & Htfp & Hclose)".
    (* the borrowed words ARE the residue index's -- named so the open below
       substitutes a variable, exactly as it did before the re-key *)
    remember (pv_tf (us_V U)) as ws eqn:Hws.
    iDestruct (tf_page_length with "Htfp") as %Hlenws.
    (* THE DEAD BASE.  [Hkc] is keyed at [tf_resume_gpr0 ws] -- the file
       restored on the canonical zero base -- and userret restores it on the
       base it was handed; the two agree because [userret_gpr] reads its base
       at x0 only, and every [gpr_file] has x0 = 0. *)
    iDestruct (gpr_file_x0 m (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0 Hfile]".
    iEval (rewrite <- (tf_resume_gpr_x0 m ws Hx0)) in "Hkc".
    iDestruct (tf_page_open36 (ud_tfp pt) ws Hlenws with "Htfp") as
      (u0 u1 u2 u3 u4 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280) "(-> & Hu0 & Hu8 & Hu16 & Hu24 & Hu32 & Htf40 & Htf48 & Htf56 & Htf64 & Htf72 & Htf80 & Htf88 & Htf96 & Htf104 & Htf112 & Htf120 & Htf128 & Htf136 & Htf144 & Htf152 & Htf160 & Htf168 & Htf176 & Htf184 & Htf192 & Htf200 & Htf208 & Htf216 & Htf224 & Htf232 & Htf240 & Htf248 & Htf256 & Htf264 & Htf272 & Htf280 & Htail)".
    iApply (RU.wp_userret_user C pt (uint (pv_sz (us_V U))) fdv (us_M U)
              (* [Rfd] at [emp] here too -- see the loop's note *)
              (fun _ : list fdstate => emp)%I
              (LP.Rut_at CID (uint (pv_sz (us_V U)))) kroot m usatp
              mstatus0 sepc0 sc_v stval_v
              u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280 u112 (DfracOwn 1)
              mcen scen hpm
              HSIE HMPRV HSXL HTVM HMXR (uc_mm C) Hwf HTSR Hsup Ha0
              HuMode Huasid Huppn HFS HVS HXS HSD HMPP HSPIE Hdqc Hinj Hacc Hlok
              Hszok
              with "Hkt Hhw Hmin Hwire Hhs Hpriv Hms Hmiec Hmdlc Hmenvc Hsenvc
                    Hsepc Hclaim Hktlb Hufr Hpc Hfile
                    Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264 Htf272 Htf280 Htf112
                    Hsc Hstval Hstvec Hmedlc Hmsec Hssec Hmcen Hscen Hhpm Hdata
                    [] [Hclose Hu0 Hu8 Hu16 Hu24 Hu32 Htail] Hkc [-]").
    - (* the bundle's [Rfd fdv], [emp] at this stage's instantiation *)
      iEmpIntro.
    - (* [Rut] at this hart, as a CLOSER: the residue minus the save slots,
         completed by the words userret gives back -- and WHOLE, since the
         slot never came out of it (R-a).  The size row is [reflexivity]:
         restoring the trapframe words does not move [p->sz]. *)
      iIntros "K40 K48 K56 K64 K72 K80 K88 K96 K104 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 K112".
      iDestruct (tf_page_close36 (ud_tfp pt) u0 u1 u2 u3 u4 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280
                with "Hu0 Hu8 Hu16 Hu24 Hu32 K40 K48 K56 K64 K72 K80 K88 K96 K104 K112 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 Htail") as "Htfp'".
      (* the kernel words are untouched: userret only READ the page *)
      iDestruct ("Hclose" with "[%] Htfp'") as "Hres'";
        [ refine (tf_kernel_words_ok_tail _ _ _ _ _ _ _ _ _ Hokws) | ].
      (* [Rut_at] packs three now: the stack, the record, and the states *)
      rewrite /LP.Rut_at. iExists ksp, _, _.
      iSplitR; [| iExact "Hres'"].
      iPureIntro. reflexivity.
    - (* the trap seam, at the kernel obligation's own shape: the loop is
         handed the record that trapped and what user execution returned
         there, which is exactly this Löb hypothesis. *)
      iApply bi.later_intro. rewrite /ukb /ukb_F.
      (* the fd pin is dropped: the loop's Löb hypothesis is ∀-general in
         the key, so it is proved at whatever descriptor view the trap-out
         key names. *)
      iIntros (W sc stv) "%Hp %Hs %Hf (Hframe & _ & Hret)".
      iApply ("Hloop" $! CID C pt (uint (pv_sz (us_V U))) W sc stv
                with "[%] [%] [%] Hhw Hmin [$Hframe $Hret]").
      + rewrite /loop_ok.
        split; [exact Hstv | split; [exact Hdqc | split; [exact Hmie |
          split; [exact Hmedl | split; [exact Hnorm | exact Hptwf]]]]].
      + exact Hp.
      + exact Hs.
  Qed.

End UserretClosedProof.
