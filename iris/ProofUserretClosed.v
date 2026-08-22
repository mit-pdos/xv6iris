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
   the address space in the user view.  All this file does is rebuild
   [user_inv] there and hand the next round's handler contract to
   [SpecUser]'s WP -- which takes it under a [▷], which is exactly what the
   Löb hypothesis is.

   TWO THINGS THAT ARE NOT PLUMBING.

   [Rut] IS THE RESIDUE, AND uservec MUST NOT BE GIVEN IT TWICE.  The
   kernel-side bundle parks across user execution inside [user_inv] as its
   [Rut] conjunct -- that is what [Rut] is for -- so at the trap it arrives
   INSIDE the frame.  But [wp_uservec_pt] takes the frame AND the residue as
   separate premises, so handing it the frame at [Rut := fun _ => ∃ ksp,
   usertrap_res_bare _ ksp] and the residue beside it would claim the same
   bundle twice and the precondition would be unsatisfiable.  The loop
   therefore OPENS the frame, takes the residue out, and rebuilds the frame
   at [Rut := fun _ => emp] for uservec.  Nothing is lost: uservec's own
   post does not mention [Rut] at all.

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
Require Import RegFile WpNext.
Require Import MinstretInv WireInv.
Require Import KernelText MstatusBits.
Require Import RiscvExtras.
Require Import KptExecMap.
Require Import UserPtTree UserExec UserKernelBridge.
Require Import ProcGeom ProcInv.
Require Import FdSlots FileInvDefs.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import SpecUserret SpecUser SpecUservec SpecUserretClosed.
Require Import UserretUser.
Require Import TfPage36.
From Kernel Require KernelSyms.
Require Import UserFrame.  (* [u_regs_pc_is]: the pc_is bundle in u_regs *)
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ParkCap.   (* [park_token] *)
Require Import UsertrapRes.  (* [ut_park_intro_body] -- the park's producer entry *)
Import Defs.

(* ===================================================================== *)
(* §3 THE LOOP.                                                            *)
(* ===================================================================== *)
Module UserretClosed (R : USERRET) (US : USER) (UV : USERVEC).
Section UserretClosed.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* [Rut], instantiated: the kernel-side bundle, keyed on the address space
     and hiding the stack top, parked inside [user_inv] across user
     execution.  Hart-indexed because the residue is. *)
  Definition Rut_at (h : CpuId) : uptd -> iProp Σ :=
    fun p => (∃ ksp : mword 64, UV.usertrap_res_bare (CID := h) p ksp)%I.

  Lemma stvec_handler_loop (j : nat) :
    (j < NPROC)%nat ->
    kernel_text -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    wire_inv -∗
    □ (∀ (h : CpuId) (C : ucfg) (pt : uptd),
         ⌜loop_ok C pt⌝ -∗
         hw_config (CID := h) -∗
         (* [minstret_inv] is [emp] post-port: no hart index left *)
         minstret_inv -∗
         user_trap_frame (CID := h) C pt (Rut_at h) -∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hj.
    iIntros "#Hkt #Hclaim #Hwire".
    iLöb as "IH".
    iIntros "!>" (h C pt) "%Hok #Hhw #Hmin Hframe".
    destruct Hok as (Hstv & Hdqc & Hmie & Hmedl & Hnorm & Hptwf).
    (* ---- open the frame: the residue comes OUT, so uservec is not handed
           it twice (see the header) ---- *)
    iDestruct (user_trap_frame_open C pt (Rut_at h) with "Hframe") as
      (ms_v sc_v stval_v sepc_v g)
      "(%Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hgpr &
        Hutlb & Hdata & %Hupinj & %Hacc & Hstvec & Hmiec & Hmdlc & #Hmedlc & Hmenvc &
        #Hsenvc & #Hmsec & #Hssec & Hrut)".
    iDestruct "Hrut" as (ksp) "Hures".
    (* the three counter-permission cells [user_cfg] carries.  The opener
       does not hand them back (they are [box] and the builder keeps its own
       copies), so each rebuild re-takes them: scounteren / mhpmcounter from
       [hw_config], mcounteren from the residue's own timer capability -- see
       [UsertrapRes.ut_res_bare_sstc] for why the third cannot ride
       [hw_config] too. *)
    iDestruct (hw_config_counters with "Hhw") as (scen hpm) "[#Hscen #Hhpm]".
    iDestruct (UV.usertrap_res_sstc pt ksp with "Hures") as "[Hsstc Hures]".
    iDestruct "Hsstc" as (mcen) "[#Hmcen _]".
    (* ---- and rebuild it for uservec at the EMPTY residue ---- *)
    iDestruct (user_trap_frame_intro C pt (fun _ : uptd => emp%I)
                 ms_v sc_v stval_v sepc_v g Hmsok
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr
                       [Hutlb Hdata] [Hstvec Hmiec Hmdlc Hmenvc] []") as "Hframe".
    { rewrite user_pt_any_unfold. iFrame "Hutlb Hdata".
      iPureIntro. split; [exact Hupinj | exact Hacc]. }
    { rewrite /user_cfg.
      iFrame "Hstvec Hmiec Hmdlc Hmenvc Hmedlc Hsenvc Hmsec Hssec".
      iSplitR; [iExists mcen, scen; iFrame "Hmcen Hscen" | iExists hpm; iFrame "Hhpm"]. }
    { done. }
    (* ---- one round ---- *)
    iApply (UV.wp_uservec_pt C pt (fun _ : uptd => emp%I) j ksp
              Hstv Hdqc Hmie Hj Hnorm Hptwf
              with "Hkt Hhw Hmin Hclaim Hframe Hures [-]").
    iApply wp_next_intro. iIntros (CID').
    rewrite /uservec_post.
    iIntros (pt' mf ms' usatp uepc sc' stval' mdv0)
      "%Hpttf %Hmapwf %Hsatpr %Hnorm' %Hptwf' %Hmm %Hretms %Hacc'
       Hhs' Hpriv' Hms' Hmie' Hmdl' Hmenv' Hstvec' #Hsenv' Hsc' Hstval' Hsepc'
       Hupt' Hpc' Hgpr' Hures' #Hhw' #Hmin'".
    (* the three frozen CSRs, duplicated out of the residue for [user_cfg] *)
    iDestruct (UV.usertrap_res_csrs_open (CID := CID') pt' ksp with "Hures'")
      as "[Hcsrs Hcback]".
    iDestruct "Hcsrs" as "(Hssc' & #Hmedl' & #Hmse' & #Hsse')".
    iDestruct ("Hcback" with "[Hssc']") as "Hures'".
    { iFrame "Hssc' Hmedl' Hmse' Hsse'". }
    (* the same three, at the hart the round LANDED on *)
    iDestruct (hw_config_counters with "Hhw'") as (scen' hpm') "[#Hscen' #Hhpm']".
    iDestruct (UV.usertrap_res_sstc pt' ksp with "Hures'") as "[Hsstc' Hures']".
    iDestruct "Hsstc'" as (mcen') "[#Hmcen' _]".
    (* [pc_is] is ONE resource post-port -- it carries [minstret_res],
       [clock_res] and [resv_any] beside the two cells, so splitting it off
       into PC/nextPC drops the riders on the floor (worklist 13.2). *)
    iApply (US.wp_user_exec_closed (loop_ucfg mdv0 Hmm) pt' (Rut_at CID')
              with "Hhw' Hmin' Hwire
                    [Hhs' Hpriv' Hms' Hsc' Hstval' Hsepc' Hpc' Hgpr'
                     Hupt' Hstvec' Hmie' Hmdl' Hmenv' Hures'] []").
    - (* [user_inv] at the rebuilt config record *)
      iExists (HART_ACTIVE tt), (sret_ms5 ms'), sc', stval', uepc,
              (ret_pc uepc), (ret_pc uepc), mf.
      destruct Hretms as (_ & _ & HSXL & HTVM & HMXR & HTSR & HFS & HVS & _
                          & HXS & HSD & HMPP & HSPIE).
      iSplitR; [iPureIntro; exact I |].
      iSplitR; [iPureIntro;
                exact (user_mstatus_ok_sret_ms5 ms' HSXL HMXR HFS HVS HTVM HTSR
                         HXS HSD HMPP HSPIE) |].
      iSplitR; [iPureIntro; intros u _; reflexivity |].
      iSplitL "Hhs' Hpriv' Hms' Hsc' Hstval' Hsepc' Hpc' Hgpr'".
      { (* [u_regs] spells PC / nextPC / the three riders out; the round's
           [pc_is] is exactly their bundle at va' = va ([u_regs_pc_is]). *)
        rewrite /user_regs u_regs_pc_is.
        iFrame "Hhs' Hpriv' Hms' Hsc' Hstval' Hsepc' Hpc' Hgpr'". }
      iFrame "Hupt'".
      iSplitL "Hstvec' Hmie' Hmdl' Hmenv'".
      { rewrite /user_cfg /=.
        iFrame "Hstvec' Hmie' Hmdl' Hmenv' Hmedl' Hsenv' Hmse' Hsse'".
        iSplitR; [iExists mcen', scen'; iFrame "Hmcen' Hscen'"
                 | iExists hpm'; iFrame "Hhpm'"]. }
      iExists ksp. iExact "Hures'".
    - (* the next round's handler contract, under the later the user WP takes
         it at -- which is exactly the shape of the Löb hypothesis *)
      iNext. iIntros "Hframe2".
      iApply ("IH" $! CID' (loop_ucfg mdv0 Hmm) pt' with "[%] Hhw' Hmin' Hframe2").
      exact (loop_ok_loop_ucfg mdv0 Hmm pt' Hnorm' Hptwf').
  Qed.

End UserretClosed.
End UserretClosed.

(* ===================================================================== *)
(* §4 THE ENTRY POINT: userret, run once, with the loop underneath.        *)
(* ===================================================================== *)
Module UserretClosedProof (R : USERRET) (US : USER) (UV : USERVEC)
  : USERRET_CLOSED.

  Module RU := UserretUser R US.
  Module LP := UserretClosed R US UV.

Section Res.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the residue is uservec's, re-exported unchanged *)
  Definition usertrap_res := UV.usertrap_res.
  Definition usertrap_res_parked := UV.usertrap_res_parked.
  Definition usertrap_res_tlb_close := UV.usertrap_res_tlb_close.
  Definition usertrap_res_tlb_open := UV.usertrap_res_tlb_open.
  Definition usertrap_res_bare := UV.usertrap_res_bare.
  Definition usertrap_res_pt_close := UV.usertrap_res_pt_close.
  Definition usertrap_res_pt_open := UV.usertrap_res_pt_open.
  Definition usertrap_res_bare_norm := UV.usertrap_res_bare_norm.
  Definition usertrap_res_csrs_open := UV.usertrap_res_csrs_open.
  Definition usertrap_res_sstc := UV.usertrap_res_sstc.
  Definition usertrap_res_tf_csrs_open := UV.usertrap_res_tf_csrs_open.
  Definition usertrap_res_tf_open := UV.usertrap_res_tf_open.
  (* ...and the park's one producer-side entry, threaded like the rest.
     A file that merely passes the residue through has nothing to say about
     it; the entry exists so that whoever PARKS a never-run process can
     build one (UsertrapRes.v, "THE PARK'S CHANNEL THROUGH THE MODULE
     TYPES"). *)
  Definition usertrap_res_bare_park
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (N : ut_names) (av : nat)
    : ut_park_intro_body
        (fun h : CpuId => UV.usertrap_res_bare (CID := h))
        (park_token (un_s N)) N av
    := UV.usertrap_res_bare_park N av.

End Res.

  Theorem wp_userret_closed
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd)
      (kroot : mword 44) (j : nat) (ksp : mword 64)
      (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64) :
      wp_userret_closed_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt kroot j ksp m usatp mstatus0 sepc0 sc_v stval_v.
  Proof.
    cbv beta delta [wp_userret_closed_body].
    intros Hok Hj Hretms Hwf Ha0 Hsatpr Hinj Hacc.
    destruct Hretms as (HSIE & HMPRV & HSXL & HTVM & HMXR & HTSR & HFS & HVS & Hsup
                        & HXS & HSD & HMPP & HSPIE).
    destruct Hok as (Hstv & Hdqc & Hmie & Hmedl & Hnorm & Hptwf).
    destruct Hsatpr as (HuMode & Huasid & Huppn).
    iIntros "#Hkt #Hhw #Hmin #Hwire #Hclaim #Hkpt Hhs Hpriv Hms Hmiec Hmdlc
             Hmenvc #Hsenvc Hsepc Hsc Hstval Hstvec #Hmedlc #Hmsec #Hssec
             Hktlb Hufr Hdata Hpc Hfile Hures".
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
    iDestruct (usertrap_res_sstc pt ksp with "Hures") as "[Hsstc Hures]".
    iDestruct "Hsstc" as (mcen) "[#Hmcen _]".
    iDestruct (usertrap_res_tf_open pt ksp with "Hures")
      as (kroot' ws) "(#Hkpt' & %Hokws & Htfp & Hclose)".
    iDestruct (tf_page_length with "Htfp") as %Hlenws.
    iDestruct (tf_page_open36 (ud_tfp pt) ws Hlenws with "Htfp") as
      (u0 u1 u2 u3 u4 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280) "(-> & Hu0 & Hu8 & Hu16 & Hu24 & Hu32 & Htf40 & Htf48 & Htf56 & Htf64 & Htf72 & Htf80 & Htf88 & Htf96 & Htf104 & Htf112 & Htf120 & Htf128 & Htf136 & Htf144 & Htf152 & Htf160 & Htf168 & Htf176 & Htf184 & Htf192 & Htf200 & Htf208 & Htf216 & Htf224 & Htf232 & Htf240 & Htf248 & Htf256 & Htf264 & Htf272 & Htf280 & Htail)".
    iApply (RU.wp_userret_user C pt (LP.Rut_at CID) kroot m usatp
              mstatus0 sepc0 sc_v stval_v
              u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280 u112 (DfracOwn 1)
              mcen scen hpm
              HSIE HMPRV HSXL HTVM HMXR (uc_mm C) Hwf HTSR Hsup Ha0
              HuMode Huasid Huppn HFS HVS HXS HSD HMPP HSPIE Hdqc Hinj Hacc
              with "Hkt Hhw Hmin Hwire Hhs Hpriv Hms Hmiec Hmdlc Hmenvc Hsenvc
                    Hsepc Hclaim Hktlb Hufr Hpc Hfile
                    Htf40 Htf48 Htf56 Htf64 Htf72 Htf80 Htf88 Htf96 Htf104 Htf120 Htf128 Htf136 Htf144 Htf152 Htf160 Htf168 Htf176 Htf184 Htf192 Htf200 Htf208 Htf216 Htf224 Htf232 Htf240 Htf248 Htf256 Htf264 Htf272 Htf280 Htf112
                    Hsc Hstval Hstvec Hmedlc Hmsec Hssec Hmcen Hscen Hhpm Hdata
                    [Hclose Hu0 Hu8 Hu16 Hu24 Hu32 Htail] [-]").
    - (* [Rut] at this hart, as a CLOSER: the residue minus the save slots,
         completed by the words userret gives back *)
      iIntros "K40 K48 K56 K64 K72 K80 K88 K96 K104 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 K112".
      iExists ksp.
      iDestruct (tf_page_close36 (ud_tfp pt) u0 u1 u2 u3 u4 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264 u272 u280
                with "Hu0 Hu8 Hu16 Hu24 Hu32 K40 K48 K56 K64 K72 K80 K88 K96 K104 K112 K120 K128 K136 K144 K152 K160 K168 K176 K184 K192 K200 K208 K216 K224 K232 K240 K248 K256 K264 K272 K280 Htail") as "Htfp'".
      (* the kernel words are untouched: userret only READ the page *)
      iApply ("Hclose" with "[%] Htfp'").
      refine (tf_kernel_words_ok_tail _ _ _ _ _ _ _ _ _ Hokws).
    - (* the handler contract, under the later the user WP takes it at *)
      iNext. iIntros "Hframe".
      iApply ("Hloop" $! CID C pt with "[%] Hhw Hmin Hframe").
      rewrite /loop_ok.
      split; [exact Hstv | split; [exact Hdqc | split; [exact Hmie |
        split; [exact Hmedl | split; [exact Hnorm | exact Hptwf]]]]].
  Qed.

End UserretClosedProof.
