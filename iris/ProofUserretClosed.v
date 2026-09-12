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
Require Import UsysMemOk.    (* [usys_num]: the syscall number the deposit is keyed on *)
Require Import UexecRet.     (* [uslot] / [uexec_ret] / [ukb] / [ukc] /
                                [trapped_machine] -- REQUIRED DIRECTLY: this
                                file puts a [uslot]/[uvb] in the proofmode
                                context and the [Typeclasses Opaque] seal
                                does not travel through a re-export
                                (durable-notes). *)
Require Import UexecApply.   (* the round's tail, as named lemmas *)
Require Import UexecSG.       (* [uexecSG]: [sbundle_at] / [spost_at] / [skey_eq] -- the loop runs on the
                                 enriched slot (lane E3b) *)
Require Import UexecExecMint. (* [udep_gen]/[uslot_mint]: the generic slot's
                                 construction, which [UexecCond]'s gate chain
                                 below is stated against *)
Require Import UexecExecInst. (* the class INSTANCE: what the loop hands the
                                 process back at each contracted number *)
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
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)

Module UserretClosed (R : USERRET) (UV : USERVEC) (UG : UEXEC_GEN).

Section UserretClosed.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  (* userret runs AS the thread, so its residue is at the AMBIENT context
     (tso-port.md: this-thread sites take the ambient ξ). *)
  Context `{XI : CurCtx}.
  (* NO [Context {SG : uexecSG Σ}]: this file sits ABOVE
     [UexecExecInst], so the deposit class it speaks is that file's
     INSTANCE, and so is the one the specs it inhabits were stated at.  A
     section variable here would be a SECOND class of the same type, and the
     two [UexecRet.uslot]s print identically -- the unifier does not stop. *)

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
  (* THE RESIDUE THE LOOP PARKS ACROSS USER EXECUTION, WITHOUT THE
     DESCRIPTOR FRAGMENTS -- they are in the process's bundle for the
     duration ([UexecRet.uvb]'s [Rfd fdv]), which is the whole of Stage B.

     There is no "residue minus the fragments" DEFINITION to hold: the
     ∀-general closer [UsertrapRes.ut_res_bare_fd_open] hands back IS that
     residue, and this is where it lives.  Applying it to the fragments the
     bundle returns at the trap rebuilds the real thing.

     [γfd] IS PINNED, and that is what makes the arrangement work.  [Rut] is
     [uptd -> iProp], so it cannot mention the states -- but the loop's Löb
     hypothesis has to carry [fd_frags γfd (uvis_fd W)] beside the machine,
     and nothing would otherwise say that those fragments belong to THIS
     process.  The pin says it, so the closer accepts them. *)
  (* [tlb_res_pt]'s creds conjunct, read off without consuming the residue
     (A6.91's ninth, persistent, member). *)
  Lemma urc_tlb_res_creds `{CID : CpuId} (r : mword 44) :
    KptShare.tlb_res_pt r -∗ KptShare.kpt_creds ∗ KptShare.tlb_res_pt r.
  Proof.
    iIntros "H".
    iDestruct "H" as (s0 tv) "(Hsatp & %A & %B & %C & Htlb & Hsnap & Hpmp & #Hk & #Hcr)".
    iSplitR; [ iExact "Hcr" | ].
    iExists s0, tv.
    iSplitL "Hsatp"; [ iExact "Hsatp" | ].
    iSplitR; [iPureIntro; exact A |].
    iSplitR; [iPureIntro; exact B |].
    iSplitR; [iPureIntro; exact C |].
    iSplitL "Htlb"; [ iExact "Htlb" | ].
    iSplitL "Hsnap"; [ iExact "Hsnap" | ].
    iSplitL "Hpmp"; [ iExact "Hpmp" | ].
    iSplitR; [ iExact "Hk" | iExact "Hcr" ].
  Qed.

  (* [cs] IS AN INDEX, beside [sz]/[γfd]/[cw] and for their reason: the
     residue is indexed by the children set ([UsertrapRes.ut_own]'s
     [WaitInv.ch_frag]) and the key's [UexecSlot.uvis_ch] is a READING of
     it, so the loop has to name it on both sides of user execution.  The
     ROW ITSELF STAYS INSIDE the residue -- unlike the descriptor
     fragments, which come out to the process: nothing between the
     trap-out and the trap-in can move the set (moving it takes
     <wait_lock>), and the program mirrors the reading with
     [UserChildren.uch]. *)
  (* ...AND THE PID, the residue's own index now ([UsertrapRes.ut_res_bare]):
     the loop hands usertrap the number its block is at, and the resume key
     is built at the same one, so getpid's answer and the kernel's cell are
     one value by construction. *)
  (* ...AND THE LAZY BIT, the residue's own index on the [cw] precedent
     (lane LAZY-FLAG, K1): the round's key carries it
     ([UexecSlot.uvis_lazy]) and the BLOCK is where it lives
     ([ProcDefs.pv_lazy]), so the loop -- which holds the block across user
     execution -- is what ties the two.  fork's deposit is the consumer:
     the child's key is built at the parent's bit, and without this pin
     nothing here could say which bit that is. *)
  Definition Rut_at (h : CpuId) (sz : Z) (γfd : gname) (cw : Z)
      (gn : gname) (cs : gset gname) (pid : mword 32) (lz : bool)
      : uptd -> iProp Σ :=
    fun p => (∃ (ksp : mword 64) (U : ustate),
                (* the closer LEADS: at the entry the record it produces is
                   only known once the trapframe words are back, so a
                   [⌜⌝] stated ahead of it would pin the existential before
                   there is anything to pin it to *)
                (* THE RUNNING TOKEN, BESIDE THE CLOSER (A6.140 / r12's
                   accessor shape): user execution borrows it out of [Rut]
                   per step ([Rut_at_acc] below is the [HRut] every loop
                   lemma takes) and the trap folds it back into the residue
                   through the closer, which is why the closer takes it. *)
                TsoCtx.own_context TsoCtx.cur_ctx ∗
                (∀ sts' : list fdstate,
                   FdSlots.fd_frags γfd sts' -∗ TsoCtx.own_context TsoCtx.cur_ctx -∗
                   UV.usertrap_res_bare (CID := h) p ksp U sts' cs pid) ∗
                ⌜uint (pv_sz (us_V U)) = sz⌝ ∗
                ⌜pv_fdg (us_V U) = γfd⌝ ∗
                (* ...and the block's cwd inum, which the trap-out key's
                   fourth pin ([UexecRet.ukb_F]) is matched against *)
                ⌜pv_cwi (us_V U) = cw⌝ ∗
                (* ...AND THE BLOCK'S GENERATION, on the same footing as the
                   two names above.  The round's key is at [gn]
                   ([UexecSlot.uvis_gen]) and the block names
                   [ProcDefs.pv_gen]; the EXIT DEPOSIT is stated at the
                   key's name and spent at the block's
                   ([SpecKexit]'s escrow), so the loop has to be told they
                   are one.  usertrap keeps it across the round
                   ([SpecUsertrap.ut_gen_kept]) and the park established it
                   ([SpecForkret.forkret_closer]'s pin). *)
                ⌜pv_gen (us_V U) = gn⌝ ∗
                (* ...and the block's lazy bit, the pin the round's key is
                   matched against ([UexecRet.ukb_F]'s eighth) *)
                ⌜pv_lazy (us_V U) = lz⌝)%I.

  Lemma Rut_at_intro (h : CpuId) (sz : Z) (γfd : gname) (cw : Z)
      (gn : gname) (cs : gset gname) (pid : mword 32) (lz : bool) (p : uptd)
      (ksp : mword 64) (U : ustate) :
    uint (pv_sz (us_V U)) = sz ->
    pv_fdg (us_V U) = γfd ->
    pv_cwi (us_V U) = cw ->
    pv_gen (us_V U) = gn ->
    pv_lazy (us_V U) = lz ->
    TsoCtx.own_context TsoCtx.cur_ctx -∗
    (∀ sts' : list fdstate,
       FdSlots.fd_frags γfd sts' -∗ TsoCtx.own_context TsoCtx.cur_ctx -∗
       UV.usertrap_res_bare (CID := h) p ksp U sts' cs pid) -∗
    Rut_at h sz γfd cw gn cs pid lz p.
  Proof.
    intros Hsz Hg Hc Hgn Hlz. iIntros "Hctx H". rewrite /Rut_at. iExists ksp, U.
    iSplitL "Hctx"; [ iExact "Hctx" |].
    iSplitL; [ iExact "H" |].
    iSplitR; [ iPureIntro; exact Hsz |].
    iSplitR; [ iPureIntro; exact Hg |].
    iSplitR; [ iPureIntro; exact Hc |].
    iSplitR; [ iPureIntro; exact Hgn | iPureIntro; exact Hlz ].
  Qed.

  (* the accessor every U-mode loop lemma takes as [HRut]: the token is a
     conjunct, so borrowing it is a split and a re-pack *)
  Lemma Rut_at_acc (h : CpuId) (sz : Z) (γfd : gname) (cw : Z)
      (gn : gname) (cs : gset gname) (pid : mword 32) (lz : bool) (p : uptd) :
    ⊢ Rut_at h sz γfd cw gn cs pid lz p -∗
      TsoCtx.own_context TsoCtx.cur_ctx ∗
      (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut_at h sz γfd cw gn cs pid lz p).
  Proof.
    iIntros "H".
    iDestruct "H" as (ksp U) "(Hctx & Hclose & %Hsz & %Hg & %Hc & %Hgn & %Hlz)".
    iFrame "Hctx". iIntros "Hctx". iExists ksp, U. iFrame "Hctx Hclose".
    iSplitR; [ iPureIntro; exact Hsz |].
    iSplitR; [ iPureIntro; exact Hg |].
    iSplitR; [ iPureIntro; exact Hc |].
    iSplitR; [ iPureIntro; exact Hgn | iPureIntro; exact Hlz ].
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
    □ (∀ (h : CpuId) (C : ucfg) (pt : uptd) (sz : Z) (γfd : gname) (cw : Z)
         (lz : bool) (W : uvis) (sc stv : mword 64),
         ⌜loop_ok C pt⌝ -∗
         ⌜uvis_perm W = perm_of (ud_um pt) sz⌝ -∗
         (* the key carries the break now, and the round below reads it *)
         ⌜uvis_sz W = sz⌝ -∗
         (* ...and the cwd's inum, which the round reads off the block:
            the pin is what ties the two ([UexecRet.ukb_F]) *)
         ⌜uvis_cwd W = cw⌝ -∗
         (* ...AND THE LAZY BIT, on the cwd's terms exactly (lane
            LAZY-FLAG): the block holds it ([ProcDefs.pv_lazy]) and the key
            carries what the boundary read off the block, so the loop is
            told they are one -- which is what lets fork's deposit be
            stated at the parent's bit. *)
         ⌜uvis_lazy W = lz⌝ -∗
         hw_config (CID := h) -∗
         (* [minstret_inv] is [emp] post-port: no hart index left *)
         minstret_inv -∗
         KptShare.kpt_creds (CID := h) -∗
         (* THE DESCRIPTOR VIEW COMES BACK WITH THE MACHINE.  [ukb_F]'s body
            hands the kernel [Rfd (uvis_fd W')] at the trap, and at this
            loop's instantiation [Rfd] IS [fd_frags γfd] -- so the round's
            entry now carries the process's fd view as a RESOURCE, at the
            value its own key names. *)
         (trapped_machine (CID := h) C pt
            (Rut_at h sz γfd cw (uvis_gen W) (uvis_ch W) (uvis_pid W) lz) sz sc stv W
          ∗ FdSlots.fd_frags γfd (uvis_fd W)
          ∗ uexec_ret sc W) -∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hj.
    iIntros "#Hkt #Hclaim #Hwire".
    (* THE LOOP MINTS NOTHING.  Every arm of the round is the process's
       own: exec's two success arms are paid out of the process's exec
       deposit ([SpecKexec.exec_slot_pre]'s two wands), and fork's parent
       arm is instantiated at the pid, which [UsysMemOk.usys_mem_ok]'s fork
       row says is never 0.  So the round takes no slot family and this
       loop passes none. *)
    iLöb as "IH".
    iIntros "!>" (h C pt sz γfd cw lz W sc stv)
      "%Hok %Hperm %Hszw %Hcww %Hlzw #Hhw #Hmin #Hcreds (Hframe & Hfrag & Hret)".
    destruct Hok as (Hstv & Hdqc & Hmie & Hmedl & Hnorm & Hptwf).
    (* ---- open the trapped machine.  [user_cfg] stays BUNDLED: the frame
           uservec takes is the same predicate at [Rut := emp], so nothing
           has to be taken apart and rebuilt here. ---- *)
    iEval (rewrite /trapped_machine /user_trap_frame_atm) in "Hframe".
    iDestruct "Hframe" as (ms_v)
      "(%Hlen & %Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc &
        Hpc & Hgpr & Hupt & Hcfg & Hrut)".
    (* [Rut_at] packs the stack, the record and the residue-minus-fragments;
       feeding it the view the bundle just handed back rebuilds the residue
       AT THAT VIEW.  This is the step that makes [uvis_fd W] the process's
       real descriptor state rather than a value the key merely names. *)
    iDestruct "Hrut" as (ksp U0)
      "(Hctx & Hclose & %Hsz & %Hgam & %Hcwi & %Hgen0 & %Hlz0)".
    iDestruct ("Hclose" $! (uvis_fd W) with "Hfrag Hctx") as "Hures".
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
    (* ---- THE SPLIT: the process's deposit -- owed at every returning
           ecall, and at [UexecExecInst]'s instance that syscall's own AU
           input at each of the nine contracted numbers -- goes DOWN to the
           kernel as uservec's pre row; the arm without it stays for the
           round ([UexecRet.uexec_ret_split]). ---- *)
    iDestruct (uexec_ret_split sc W with "Hret") as (fdep) "[[Hpay Hxin] Hret]".
    (* THE PAYMENT IS THE ONE ROW WITH NO GUARD, so it is split off here
       rather than in the case analysis below: the process owes it at every
       cause and every number ([UexecRet.upay_at]), and what carries it
       across the save walk is its own congruence -- the number and
       argument 0, which [TfUser.tf_ueq] carries, and the generation, which
       the residue's pin ties to the block's ([Rut_at]'s last conjunct). *)
    iDestruct (upay_at_ueq (uvis_gen W) (pv_gen (us_V U0)) sc
                 (uvis_tf W)
                 (tf_of (tf_resume_gpr0 (uvis_tf W))
                    (ret_pc (tf_w (uvis_tf W) tf_epc_idx))) fdep
                 (eq_sym (uvis_run_num W))
                 (eq_sym (uvis_run_arg0 W))
                 (eq_sym Hgen0)
              with "Hpay") as "Hpay".
    (* the residue's index, read at the key: the three equations the round
       and fork's deposit both cross by.  [Hpi0] is stated at the RE-KEYED
       index ([us_upt U0 pt]), which is what the loop resumed under. *)
    assert (Hpi0 : perm_of (ud_um (pv_upt (us_V (us_upt U0 pt))))
                     (uint (pv_sz (us_V (us_upt U0 pt)))) = uvis_perm W)
      by (rewrite Hperm; reflexivity).
    assert (Hsz0 : uint (pv_sz (us_V (us_upt U0 pt))) = uvis_sz W)
      by exact (eq_sym Hszw).
    assert (Hcw0 : pv_cwi (us_V (us_upt U0 pt)) = uvis_cwd W)
      by (rewrite Hcww; exact Hcwi).
    (* ...and the lazy bit, the fourth of the same family: the residue's pin
       and the loop's premise are the two halves (lane LAZY-FLAG) *)
    assert (Hlz0k : pv_lazy (us_V (us_upt U0 pt)) = uvis_lazy W)
      by exact (eq_trans Hlz0 (eq_sym Hlzw)).
    (* ---- FORK'S DEPOSIT IS A SECOND ROW, and the two are exclusive.  At
           every returning number the deposit is the syscall's bundle and
           travels as [SpecUsertrap.ut_sys_in]; at FORK it is the child's
           own continuation and travels as [SpecUsertrap.ut_fork_in].  Both
           rows are guarded on the number, so the one this trap is not at
           is proved without touching the resource. ---- *)
    assert (Hla1 : (tf_arg_idx 0 < length (uvis_tf W))%nat)
      by (rewrite Hlen; unfold tf_arg_idx, TFWORDS; lia).
    assert (Hle1 : (tf_epc_idx < length (uvis_tf W))%nat)
      by (rewrite Hlen; unfold tf_epc_idx, TFWORDS; lia).
    assert (Hla2 : (tf_arg_idx 0
                    < length (tf_of (tf_resume_gpr0 (uvis_tf W))
                                (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))%nat)
      by (rewrite tf_of_length; unfold tf_arg_idx, TFWORDS; lia).
    assert (Hle2 : (tf_epc_idx
                    < length (tf_of (tf_resume_gpr0 (uvis_tf W))
                                (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))%nat)
      by (rewrite tf_of_length; unfold tf_epc_idx, TFWORDS; lia).
    assert (Hgpr0 : tf_resume_gpr0 (bump_tf (uvis_tf W) (mword_of_int 0))
                    = tf_resume_gpr0
                        (bump_tf (tf_of (tf_resume_gpr0 (uvis_tf W))
                                    (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                           (mword_of_int 0))).
    { rewrite (tf_resume_gpr0_bump (uvis_tf W) (mword_of_int 0) Hla1).
      rewrite (tf_resume_gpr0_bump
                 (tf_of (tf_resume_gpr0 (uvis_tf W))
                    (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                 (mword_of_int 0) Hla2).
      rewrite (tf_of_resume_gpr (tf_resume_gpr0 (uvis_tf W))
                 (ret_pc (tf_w (uvis_tf W) tf_epc_idx))
                 (tf_resume_gpr0_x0 (uvis_tf W))).
      reflexivity. }
    (* the resume pc crosses the run projection by [UexecApply.ret_pc_add4]:
       clearing bit 0 before the +4 and after it give the same target *)
    assert (Hpc0 : tf_resume_pc (bump_tf (uvis_tf W) (mword_of_int 0))
                   = tf_resume_pc
                       (bump_tf (tf_of (tf_resume_gpr0 (uvis_tf W))
                                   (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                          (mword_of_int 0))).
    { rewrite (tf_resume_pc_bump (uvis_tf W) (mword_of_int 0) Hle1).
      rewrite (tf_resume_pc_bump
                 (tf_of (tf_resume_gpr0 (uvis_tf W))
                    (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                 (mword_of_int 0) Hle2).
      rewrite (tf_of_epc (tf_resume_gpr0 (uvis_tf W))
                 (ret_pc (tf_w (uvis_tf W) tf_epc_idx))).
      exact (eq_sym (ret_pc_add4 (tf_w (uvis_tf W) tf_epc_idx))). }
    iAssert ((∀ n : Z,
                SpecUsertrap.ut_sys_in n fdep sc
                  (tf_of (tf_resume_gpr0 (uvis_tf W))
                     (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                  (ProcDefs.upd_usM
                     (ProcInv.us_tf (us_upt U0 pt)
                        (tf_of (tf_resume_gpr0 (uvis_tf W))
                           (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))
                     (uvis_M W))
                  (uvis_fd W) (uvis_gen W) (uvis_ch W) (uvis_pid W))
             ∗ SpecUsertrap.ut_fork_in fdep sc
                  (tf_of (tf_resume_gpr0 (uvis_tf W))
                     (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                  (ProcDefs.upd_usM
                     (ProcInv.us_tf (us_upt U0 pt)
                        (tf_of (tf_resume_gpr0 (uvis_tf W))
                           (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))
                     (uvis_M W))
                  (uvis_fd W))%I
      with "[Hxin]" as "[Hin Hfin]".
    { destruct (decide (usys_num (uvis_tf W) = USYS_fork)) as [Hfk | Hnfk].
      - iSplitR.
        + (* the bundle row excludes fork by its own guard *)
          iIntros (n) "%Hg". exfalso.
          destruct Hg as (_ & Hgn & _ & Hgf). apply Hgf. rewrite <- Hgn.
          exact (eq_trans (uvis_run_num W) Hfk).
        + (* THE CHILD'S CONTINUATION.  The deposit's key is the TRAPPED
             frame bumped and the row's is the RUN projection's bumped, and
             the two agree at everything a slot reads
             ([UexecApply.uslot_key_cong]). *)
          rewrite /SpecUsertrap.ut_fork_in. iIntros "%Hg".
          rewrite /uexec_dep /uexec_dep_F. cbv zeta.
          destruct (decide (sc = uecall_scause)) as [_ | Hc];
            [ | exfalso; exact (Hc (proj1 Hg)) ].
          destruct (decide (usys_num (uvis_tf W) = USYS_exit)) as [He | _];
            [ exfalso; rewrite Hfk in He; discriminate He | ].
          destruct (decide (usys_num (uvis_tf W) = USYS_fork)) as [_ | Hc];
            [ | exfalso; exact (Hc Hfk) ].
          (* THE CHILD'S PID IS ∀-BOUND, beside its generation: the process
             deposited a family over every number <allocpid> might choose
             and the kernel instantiates it ([UexecRet.uexec_fork_child_F]). *)
          iIntros (g' pidc) "Hmp".
          rewrite /uexec_fork_child_F SpecUsertrap.uvis_of_us_tf.
          iSpecialize ("Hxin" $! g' pidc). iSpecialize ("Hxin" with "Hmp").
          iEval (rewrite (uslot_key_cong
                            (bump_at W (mword_of_int 0) (uvis_M W) (uvis_perm W)
                               (uvis_sz W) (uvis_fd W) (uvis_cwd W) g' ∅ pidc
                               (uvis_lazy W))
                            (MkUvis
                               (bump_tf (tf_of (tf_resume_gpr0 (uvis_tf W))
                                           (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                                  (mword_of_int 0))
                               (uvis_M W)
                               (perm_of (ud_um (pv_upt (us_V (us_upt U0 pt))))
                                  (uint (pv_sz (us_V (us_upt U0 pt)))))
                               (uint (pv_sz (us_V (us_upt U0 pt))))
                               (uvis_fd W)
                               (pv_cwi (us_V (us_upt U0 pt)))
                               g' ∅ pidc
                               (pv_lazy (us_V (us_upt U0 pt))))
                            Hgpr0 Hpc0 eq_refl (eq_sym Hpi0) (eq_sym Hsz0)
                            eq_refl (eq_sym Hcw0) eq_refl eq_refl eq_refl
                            (* the eleventh reading: the child is born at
                               the parent's bit, and the loop's pin is what
                               says which bit the block holds *)
                            (eq_trans Hlzw (eq_sym Hlz0)))) in "Hxin".
          iExact "Hxin".
      - iSplitL "Hxin".
        + (* the pre row is the deposit at the RUN projection of the trapped
             key, which reads the same image, argument words and descriptor
             view ([UexecApply.uvis_run_arg0] / [_arg1] / [_arg2]) *)
          iIntros (n) "%Hg".
          destruct Hg as (Hgc & Hgn & Hgx & Hgf).
          assert (Hn : usys_num (uvis_tf W) = n)
            by (rewrite <- (uvis_run_num W); exact Hgn).
          rewrite /uexec_dep /uexec_dep_F. cbv zeta.
          destruct (decide (sc = uecall_scause)) as [_ | Hc];
            [ | exfalso; exact (Hc Hgc) ].
          rewrite Hn.
          destruct (decide (n = USYS_exit)) as [He | _];
            [ exfalso; exact (Hgx He) | ].
          destruct (decide (n = USYS_fork)) as [He | _];
            [ exfalso; exact (Hgf He) | ].
          match goal with
          | |- environments.envs_entails _ (sbundle_at _ _ _ ?W') =>
              rewrite <- (sbundle_at_cong uslot n fdep W W'
                            ltac:(rewrite /skey_eq; split_and!;
                                  [ reflexivity
                                  | exact (eq_sym (uvis_run_arg0 W))
                                  | exact (eq_sym (uvis_run_arg1 W))
                                  | exact (eq_sym (uvis_run_arg2 W))
                                  | reflexivity
                                  | exact (eq_trans Hcww (eq_sym Hcwi))
                                  | reflexivity | reflexivity
                                  | reflexivity
                                  (* the permission map and the size: both
                                     keys are the ENTRY projection, which is
                                     what [Hpi0] / [Hsz0] say *)
                                  | exact (eq_sym Hpi0)
                                  | exact (eq_sym Hsz0)
                                  (* ...and the lazy bit: the deposit's key
                                     is the RUN projection of the trapped
                                     one, which reads the same block *)
                                  | exact (eq_trans Hlzw (eq_sym Hlz0)) ]))
          end.
          iExact "Hxin".
        + (* not fork, so the fork row is vacuous *)
          rewrite /SpecUsertrap.ut_fork_in. iIntros "%Hg". exfalso.
          apply Hnfk. rewrite <- (uvis_run_num W). exact (proj2 Hg). }
    (* ---- one round.  [Hret] -- the linear return user execution handed
           back -- is FRAMED across the crossing (R-a / K8). ---- *)
    iApply (UV.wp_uservec_pt C pt (fun _ : uptd => emp%I) j ksp
              (us_upt U0 pt) (uvis_fd W) (uvis_gen W) (uvis_ch W) (uvis_pid W) fdep
              (uvis_M W)
              (tf_resume_gpr0 (uvis_tf W))
              ms_v sc stv (tf_w (uvis_tf W) tf_epc_idx)
              Hstv Hdqc Hmie Hj Hnorm Hptwf
              with "Hkt Hhw Hmin Hclaim Hcreds Hframe Hures Hin Hfin [Hpay] [-]").
    { rewrite /SpecUsertrap.ut_pay_in. iExact "Hpay". }
    iApply wp_next_intro. iIntros (CID').
    rewrite /uservec_post.
    iIntros (pt' mf ms' usatp uepc sc' stval' mdv0 U2 sts2 cs2)
      "%Huptpt' %Hround' %Hfdkept %Hchkept %Hgenk2 %Hfdecall %Hpipecall %Hpidrow %Hpcret' %Hgprtie'
       %Hpttf %Hmapwf %Hsatpr %Hnorm' %Hptwf' %Hmm %Hretms %Hacc'
       Hhs' Hpriv' Hms' Hmie' Hmdl' Hmenv' Hstvec' #Hsenv' Hsc' Hstval' Hsepc'
       Hupt' Hpc' Hgpr' Hures' #Hhw' #Hmin' #Hcreds' Hxo Hfo Hwo Hso Hpay".
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
    (* THE SPLIT: the fragments come OUT of the residue the round returned
       and go into the process's bundle; what is left -- the ∀-general
       closer -- is what the loop parks.  [sts2] is where the round actually
       left the descriptor states, so this is the view the process resumes
       at, not the one it trapped at. *)
    iDestruct (UV.usertrap_res_bare_fd_open pt' ksp U2 sts2 with "Hures'")
      as "(Hfrag2 & Hctx2 & Hclose2)".
    iDestruct (Rut_at_intro CID' (uint (pv_sz (us_V U2))) (pv_fdg (us_V U2))
                 (pv_cwi (us_V U2)) (uvis_gen W) cs2 (uvis_pid W)
                 (pv_lazy (us_V U2)) pt' ksp U2
                 eq_refl eq_refl eq_refl
                 (* the round keeps the generation ([SpecUsertrap.ut_gen_kept]),
                    and the entry residue's was the key's *)
                 ltac:(rewrite Hgenk2; exact Hgen0)
                 eq_refl
                 with "Hctx2 Hclose2") as "Hrut'".
    (* ---- STEPS A/B: the returned [uexec_ret], re-keyed onto the record
           the round left ([UexecApply]).  The round is stated at the RUN
           projection of the trapped key, and its entry permission map is
           the key's own once the index has been re-keyed onto [pt]. ---- *)
    unfold uv_round in Hround'.
    rewrite Hpi0 in Hround'.
    (* ...and the same for the break and the cwd's inum, which the key
       carries now ([Hsz0] / [Hcw0], hoisted above the round) *)
    rewrite Hsz0 in Hround'.
    rewrite Hcw0 in Hround'.
    rewrite Hlz0k in Hround'.
    (* THE RESUMED KEY IS AT [sts2], THE POST-SYSCALL VIEW.  That is the
       whole point of the conditional pin: on an ecall the kernel may have
       retyped a descriptor and the key must say so, and on any other cause
       [Hfdkept] -- [SpecUsertrap.ut_fd_kept], certified by usertrap and
       forwarded by uservec -- says the states did not move, which is
       exactly the transparent arm's premise. *)
    (* ...and the kernel's exec result, at the same key: [ut_exec_out]
       unfolded IS the round lemma's row once the entry permission map and
       break are the key's own *)
    iEval (rewrite /SpecUsertrap.ut_exec_out Hpi0 Hsz0 Hlz0k) in "Hxo".
    (* ---- THE SET THE ROUND RESUMES AT IS THE RESIDUE'S OWN INDEX.  The
       children row rides the residue ([UsertrapRes.ut_own]'s
       [WaitInv.ch_frag]), so [cs2] is a READING of the <wait_lock> map and
       not a choice: every entry but fork keeps it
       ([SpecUsertrap.ut_ch_kept], forwarded by uservec), and at fork the
       kernel's own answer says what it became -- the row moved under the
       lock kfork holds. ---- *)
    iEval (rewrite /SpecUsertrap.ut_fork_out) in "Hfo".
    (* ...and wait's, on the same terms: the reap moved the row under the
       lock kwait holds, and this is what says where it left it. *)
    iEval (rewrite /SpecUsertrap.ut_wait_out) in "Hwo".
    (* ...AND THE EXEC ANSWER AT THE SET THE ROUND RESUMES AT: exec is not
       fork, so on that arm the set did not move and the row's slot is at
       the same key. *)
    iAssert (⌜sc = uecall_scause
             /\ usys_num (tf_of (tf_resume_gpr0 (uvis_tf W))
                            (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                = USYS_exec⌝ -∗
             (⌜exists r : mword 64,
                 UexecRound.uround_bump_ok
                   (tf_of (tf_resume_gpr0 (uvis_tf W))
                      (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                   (pv_tf (us_V U2)) r
                 /\ usys_mem_ok USYS_exec
                      (tf_of (tf_resume_gpr0 (uvis_tf W))
                         (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                      r (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_lazy W)
                      (us_M U2)
                      (perm_of (ud_um (pv_upt (us_V U2))) (uint (pv_sz (us_V U2))))
                      (uint (pv_sz (us_V U2))) (pv_lazy (us_V U2))
                 /\ sts2 = uvis_fd W⌝
              ∨ (uexec_pay_arm fdep -∗
                   uslot (uvis_of U2 sts2 (uvis_gen W) cs2 (uvis_pid W)))))%I
      with "[Hxo]" as "Hxo".
    { iIntros "%Hg".
      assert (Hnf : ~ (sc = uecall_scause
                       /\ (usys_num (tf_of (tf_resume_gpr0 (uvis_tf W))
                                       (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                           = USYS_fork
                           \/ usys_num (tf_of (tf_resume_gpr0 (uvis_tf W))
                                          (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))
                              = USYS_wait))).
      { intros [_ [Hx | Hx]]; rewrite (proj2 Hg) in Hx; discriminate Hx. }
      rewrite (Hchkept Hnf). iApply "Hxo". iPureIntro. exact Hg. }
    iDestruct (uexec_ret_round_slot_of sc W fdep (tf_resume_gpr0 (uvis_tf W))
                 (tf_w (uvis_tf W) tf_epc_idx) U2 sts2 cs2
                 Hlen eq_refl eq_refl Hfdkept Hchkept
                 (* ...and the ECALL arm's row, which is what stops the
                    process resuming at an ARBITRARY descriptor view.  It
                    arrives from uservec's post ([Hfdecall]), which got it
                    from usertrap, which got it from the dispatcher -- and
                    it is stated at the same trapframe on both sides, so it
                    goes in verbatim. *)
                 Hfdecall
                 (* ...and pipe's join beside it, from the same three hops
                    and stated at the same trapframe pair *)
                 Hpipecall
                 (* ...and getpid's answer, from the same three hops and at
                    the same trapframe pair -- [SpecUsertrap.ut_ret_pid] *)
                 Hpidrow Hround'
                 (* ...AND THE SYSCALL'S ARMED POST, back under the arm's own
                    [∀ r], AT THE FAMILIES THE DEPOSIT WAS MADE AT ([fdep],
                    the witness the split handed out).  It comes off
                    [SpecUsertrap.ut_sys_out], uservec's own post row, at the
                    key the deposit went down at -- which differs from the
                    round's run projection in none of [UexecSG.skey_eq]'s six
                    rows, exactly as it did on the way in. *)
                 with "Hxo Hfo Hwo [Hso] Hpay Hret") as "Hslot";
      [ iIntros "%Hg"; destruct Hg as (Hgec & Hgex & Hgfk);
        (* THE ROW IS AT THE SET THE ROUND RESUMES AT, whatever it is: at
           wait that set is what the reap left and the trapped one is gone,
           so the transport must NOT go through [Hchkept].  The armed post
           reads the set only as its own last argument, and both sides name
           the same [cs2]. *)
        iDestruct ("Hso" $! (usys_num (tf_of (tf_resume_gpr0 (uvis_tf W))
                               (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))
                     with "[%]") as "Hso";
        [ split_and!;
          [ exact Hgec | reflexivity | exact Hgex | exact Hgfk ] |];
        iEval (rewrite (spost_at_cong uslot
                 (usys_num (tf_of (tf_resume_gpr0 (uvis_tf W))
                    (ret_pc (tf_w (uvis_tf W) tf_epc_idx)))) fdep
                 (uvis_of (upd_usM (us_tf (us_upt U0 pt)
                             (tf_of (tf_resume_gpr0 (uvis_tf W))
                                (ret_pc (tf_w (uvis_tf W) tf_epc_idx))))
                             (uvis_M W)) (uvis_fd W) (uvis_gen W) (uvis_ch W)
                             (uvis_pid W))
                 (uvis_run W) (pv_tf (us_V U2) !!! tf_arg_idx 0)
                 (us_M U2) sts2 (pv_cwi (us_V U2)) cs2
                 ltac:(rewrite /skey_eq; split_and!;
                       [ reflexivity | reflexivity | reflexivity
                       | reflexivity | reflexivity
                       | exact (eq_trans Hcwi (eq_sym Hcww))
                       | reflexivity | reflexivity | reflexivity
                       (* ...and the two the read row reads, and the lazy
                          bit beside them *)
                       | exact Hpi0 | exact Hsz0
                       | exact (eq_trans Hlz0 (eq_sym Hlzw)) ]))) in "Hso";
        iExact "Hso" | ].
    (* ---- STEPS C/D: the guard, and the bundle, both inside the named
           lemma -- the loop only says which key it is at. ---- *)
    assert (Hpi2 : uvis_perm (uvis_of U2 sts2 (uvis_gen W) cs2 (uvis_pid W))
                   = perm_of (ud_um pt') (uint (pv_sz (us_V U2))))
      by (cbn [uvis_of uvis_perm]; rewrite Huptpt'; reflexivity).
    (* [Rfd] IS THE PROCESS'S OWN FRAGMENTS, at its own ghost name.  The
       bundle carries the descriptor view for the duration of user execution
       and gives it back at the trap; the residue keeps the AUTHORITY, so
       neither side can move a descriptor's state alone
       ([FdSlots.fd_st_both_update]). *)
    iApply (uslot_apply_loop (CID := CID') (loop_ucfg mdv0 Hmm) pt'
              (FdSlots.fd_frags (pv_fdg (us_V U2)))
              (Rut_at CID' (uint (pv_sz (us_V U2))) (pv_fdg (us_V U2))
                 (pv_cwi (us_V U2)) (uvis_gen W) cs2 (uvis_pid W)
                 (pv_lazy (us_V U2)))
              (Rut_at_acc CID' (uint (pv_sz (us_V U2))) (pv_fdg (us_V U2))
                 (pv_cwi (us_V U2)) (uvis_gen W) cs2 (uvis_pid W)
                 (pv_lazy (us_V U2)))
              (uint (pv_sz (us_V U2)))
              sts2 (pv_cwi (us_V U2)) (uvis_gen W) cs2 (uvis_pid W)
              (pv_lazy (us_V U2))
              (uvis_of U2 sts2 (uvis_gen W) cs2 (uvis_pid W)) (us_M U2) mf
              (sret_ms5 ms') sc' stval' uepc (ret_pc uepc)
              (loop_ok_loop_ucfg mdv0 Hmm pt' Hnorm' Hptwf')
              Hszok
              (user_mstatus_ok_sret_ms5 ms' HSXL HMXR HFS HVS HTVM HTSR
                 HXS HSD HMPP HSPIE)
              Hpi2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              eq_refl
              (eq_sym Hgprtie') (eq_sym Hpcret')
              with "Hslot Hhw' Hmin' Hwire Hregs' Hupt' Hfrag2 Hcfg' Hrut' [-]").
    (* the next round's contract, under the later the bundle takes it at --
       which is exactly the shape of the Löb hypothesis.  A GENUINE Löb back
       edge, so [iNext] and not [bi.later_intro]. *)
    iNext. rewrite ukb_unfold.
    (* the fd pin is DROPPED here: the Löb hypothesis is ∀-general in the
       key, so the next round is proved at whatever descriptor view the
       trap-out key names. *)
    (* the middle conjunct IS the descriptor view coming back -- [Rfd] here
       is [fd_frags (pv_fdg (us_V U2))], so this is the process's own
       fragments at the trap-out key's own [uvis_fd]. *)
    iIntros (W2 sc2 stv2) "%Hp2 %Hs2 %Hf2 %Hc2 %Hgn2 %Hch2 %Hpid2 %Hlz2 (Hframe2 & Hfrag2' & Hret2)".
    (* the [Rut] the next round is re-entered at is the one this round
       parked: [cs2] is the residue's index and the trap-out key reads the
       same set ([UexecRet.ukb_F]'s own pin), so the frame is re-spelled at
       the key's reading rather than the residue's index. *)
    iEval (rewrite -Hch2) in "Hframe2".
    (* ...and the same for the GENERATION the residue is indexed by: this
       round parked it at the entry key's [uvis_gen], the trap-out key
       carries the same one ([UexecRet.ukb_F]'s fifth pin -- user execution
       cannot re-incarnate the process), and the Löb hypothesis is at the
       trap-out key's own reading. *)
    iEval (rewrite -Hgn2) in "Hframe2".
    (* ...and for the PID, on the same terms: the round parked the residue
       at the entry key's [uvis_pid] and the trap-out key carries the same
       number ([UexecRet.ukb_F]'s seventh pin). *)
    iEval (rewrite -Hpid2) in "Hframe2".
    iApply ("IH" $! CID' (loop_ucfg mdv0 Hmm) pt' (uint (pv_sz (us_V U2)))
              (pv_fdg (us_V U2)) (pv_cwi (us_V U2)) (pv_lazy (us_V U2))
              W2 sc2 stv2
              with "[%] [%] [%] [%] [%] Hhw' Hmin' Hcreds' [$Hframe2 $Hfrag2' $Hret2]").
    - exact (loop_ok_loop_ucfg mdv0 Hmm pt' Hnorm' Hptwf').
    - exact Hp2.
    - exact Hs2.
    - exact Hc2.
    - exact Hlz2.
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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!ufdG Σ}.
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
  Definition usertrap_res_bare_fd_open := UV.usertrap_res_bare_fd_open.
  Definition usertrap_res_bare_fd_tf_open := UV.usertrap_res_bare_fd_tf_open.
  Definition usertrap_res_csrs_open := UV.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UV.usertrap_res_sstc.
  Definition usertrap_res_bare_sz := UV.usertrap_res_bare_sz.
  Definition usertrap_res_tf_csrs_open := UV.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := UV.usertrap_res_tf_open.
  Definition usertrap_res_bare_fsabs := UV.usertrap_res_bare_fsabs.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun (h : CpuId) (Xc : CurCtx) => UV.usertrap_res_bare (CID := h) (XI := Xc))
        (park_token (un_s N)) N av
    := UV.usertrap_res_bare_park N av.

End Res.

  Theorem wp_userret_closed
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (C : ucfg) (pt : uptd)
      (kroot : mword 44) (j : nat) (ksp : mword 64)
      (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64) (U : ustate)
      (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32) :
      wp_userret_closed_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt kroot j ksp m usatp mstatus0 sepc0 sc_v stval_v U fdv fdv gn cs
        pidv.
  Proof.
    cbv beta delta [wp_userret_closed_body].
    intros Hok Hj Hgnw Hretms Hwf Ha0 Hsatpr Hinj Hacc.
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
    (* ...AND THE DESCRIPTOR VIEW WITH THEM.  One accessor, because the
       fragments go into the bundle this entry builds while the page words
       are what the restore walk reads, and taking either alone strands the
       other -- see [UsertrapRes.ut_res_bare_fd_tf_open]. *)
    iDestruct (usertrap_res_bare_fd_tf_open pt ksp U fdv with "Hures")
      as "[Hfrag Hopen]".
    iDestruct "Hopen" as (kroot') "(#Hkpt' & %Hokws & Htfp & Hctx & Hclose)".
    (* the walk credential, read off the kernel residue's tlb bundle (A6.91) *)
    iDestruct (LP.urc_tlb_res_creds kroot with "Hktlb") as "[#Hcreds Hktlb]".
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
    iApply (RU.wp_userret_user C pt (uint (pv_sz (us_V U))) fdv (pv_cwi (us_V U))
              gn cs pidv (pv_lazy (us_V U)) (us_M U)
              (FdSlots.fd_frags (pv_fdg (us_V U)))
              (LP.Rut_at CID (uint (pv_sz (us_V U))) (pv_fdg (us_V U))
                 (pv_cwi (us_V U)) gn cs pidv (pv_lazy (us_V U)))
              (LP.Rut_at_acc CID (uint (pv_sz (us_V U))) (pv_fdg (us_V U))
                 (pv_cwi (us_V U)) gn cs pidv (pv_lazy (us_V U)))
              kroot m usatp
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
                    Hfrag Hcreds Hctx [Hclose Hu0 Hu8 Hu16 Hu24 Hu32 Htail] Hkc [-]").
    - (* [Rut] at this hart, as a CLOSER: the residue minus the save slots,
         completed by the words userret gives back -- and WHOLE, since the
         slot never came out of it (R-a).  The size row is [reflexivity]:
         restoring the trapframe words does not move [p->sz]. *)
      iIntros "K40 K48 K56 K64 K72 K80 K88 K96 K104 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 K112 Ktok".
      iDestruct (tf_page_close36 (ud_tfp pt) u0 u1 u2 u3 u4 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280
                with "Hu0 Hu8 Hu16 Hu24 Hu32 K40 K48 K56 K64 K72 K80 K88 K96 K104 K112 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 Htail") as "Htfp'".
      (* [Rut_at] holds the residue MINUS the descriptor fragments -- which
         is exactly the combined closer, partially applied to the trapframe
         words and still waiting on the view.  The bundle gives that view
         back at the trap and the loop feeds it in. *)
      rewrite /LP.Rut_at. iExists ksp, _.
      (* the token userret hands back goes BESIDE the closer: the resumed
         loop's accessor ([Rut_at_acc]) is what borrows it next (A6.140) *)
      iSplitL "Ktok"; [ iExact "Ktok" |].
      iSplitL.
      + iIntros (sts') "Hfr Hctx".
        iApply ("Hclose" with "[%] Htfp' Hfr Hctx").
        refine (tf_kernel_words_ok_tail _ _ _ _ _ _ _ _ _ Hokws).
      + iSplitR; [ iPureIntro; reflexivity |].
        iSplitR; [ iPureIntro; reflexivity |].
        iSplitR; [ iPureIntro; reflexivity |].
        iSplitR; iPureIntro; [ exact Hgnw | reflexivity ].
    - (* the trap seam, at the kernel obligation's own shape: the loop is
         handed the record that trapped and what user execution returned
         there, which is exactly this Löb hypothesis. *)
      iApply bi.later_intro. rewrite /ukb /ukb_F.
      (* the fd pin is dropped: the loop's Löb hypothesis is ∀-general in
         the key, so it is proved at whatever descriptor view the trap-out
         key names. *)
      iIntros (W sc stv) "%Hp %Hs %Hf %Hc %Hgn %Hch %Hpidk %Hlzk (Hframe & Hfrag' & Hret)".
      (* the residue this round parked is indexed by [cs], and the trap-out
         key reads the same set ([UexecRet.ukb_F]'s own pin) -- so the
         [Rut] the loop is re-entered at is the one it was handed. *)
      iEval (rewrite -Hch) in "Hframe".
      (* ...and the GENERATION on the same footing: this entry parked the
         residue at the record's own [gn] and the loop is stated at the
         trap-out key's [uvis_gen], which [UexecRet.ukb_F]'s fifth pin says
         is that one. *)
      iEval (rewrite -Hgn) in "Hframe".
      (* ...and the PID, the seventh pin, on exactly those terms *)
      iEval (rewrite -Hpidk) in "Hframe".
      iApply ("Hloop" $! CID C pt (uint (pv_sz (us_V U))) (pv_fdg (us_V U))
                (pv_cwi (us_V U)) (pv_lazy (us_V U)) W sc stv
                with "[%] [%] [%] [%] [%] Hhw Hmin Hcreds [$Hframe $Hfrag' Hret]").
      + rewrite /loop_ok.
        split; [exact Hstv | split; [exact Hdqc | split; [exact Hmie |
          split; [exact Hmedl | split; [exact Hnorm | exact Hptwf]]]]].
      + exact Hp.
      + exact Hs.
      + exact Hc.
      + exact Hlzk.
      + (* the return the dovetail hands over, at the one tier *)
        iExact "Hret".
  Qed.

End UserretClosedProof.
