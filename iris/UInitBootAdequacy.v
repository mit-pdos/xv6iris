(* ===================================================================== *)
(* UInitBootAdequacy.v -- E2's B3: the whole-system theorem at echo's     *)
(* era, with every obligation of the application record discharged        *)
(* EXCEPT [Hphi] (E5's) and what the rest of the arc still owes on the    *)
(* shell's side.                                                         *)
(*                                                                       *)
(* WHY IT IS ITS OWN FILE AND NOT THE BOTTOM OF [UInitBoot.v].  This      *)
(* statement needs the ADEQUACY CONE -- [RiscvAdequacy.boot_fixedGS],     *)
(* [SystemAdequacy.xv6_slot], [FsCfgBoot.fs_boot_image_wf],              *)
(* [FsImgDisk.fsimg_P], [iris.program_logic.adequacy] -- and a [Require   *)
(* Import App] brings none of it along ([App.v] is not a [Require         *)
(* Export]).  Pulling that cone into [UInitBoot.v], which is a            *)
(* proofmode-heavy u-tier assembly full of [UexecSG.sbundle] wand towers, *)
(* makes the elaboration blow up: measured at 54 GB RSS in 64 seconds     *)
(* (and 489 GB in nine minutes, before the build cap was tightened).      *)
(* Split, each file carries one cone and both elaborate promptly.  The    *)
(* SAME shape of rule is already in durable-notes for the other           *)
(* direction ("do not import application-level files into the            *)
(* proofmode-heavy walks").                                              *)
(*                                                                       *)
(* WHAT IT TAKES FROM THE LANE: exactly [UInitBoot.echo_Hinit_boot].      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang ObsTrace RiscvPtsto.
Require Import FsState.
Require Import FsAbsDefs.
Require Import InitBoot.
Require Import InodeInv.
Require Import AppCfg.
Require Import AppInv.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import WpUart.
Require Import FsCfgBoot.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import VirtioModel.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FsImg.
Require Import ProcAvail.
Require Import Xv6G.
Require Import UserFd.
Require Import SystemAdequacy.
Require Import FsImgCheck.
Require Import FsImgDisk.
Require Import TsoCtx.             (* [CurCtx] *)
Require Import UexecSG.            (* [uprogSG] *)
Require Import UexecExecInst.      (* [uprogSG_free] -- /init's own instance *)
Require Import UkRun.              (* [udepw_law] *)
Require Import UkSh.               (* [sh_deps] *)
Require Import UInitSh.            (* [sh_pay_state] / [sh_pay_rest] *)
Require Import App.                (* [xv6_app_adequacy] and the record *)
Require Import AppEcho.            (* [app_echo] and its obligations *)
Require Import UInitBoot.          (* [echo_Hinit_boot] -- E2's discharge *)
(* ===================================================================== *)
(*  6.  THE ADEQUACY STATEMENT E2 CLOSES (B3)                             *)
(*                                                                       *)
(*  [App.xv6_app_adequacy] at [AppEcho.app_echo], with every obligation   *)
(*  of the record discharged EXCEPT [Hphi] (E5's) and what the rest of    *)
(*  the arc still owes on the shell's side.  Those are the hypotheses     *)
(*  below and there are no others: the console dance, the boot bundle and *)
(*  /init's own entry are closed here.                                    *)
(* ===================================================================== *)
Section EchoAdequacy.
  Context {Σ : gFunctors}.
  Context `{!xv6G Σ, !riscvGpreS Σ, !fileGpreS Σ, !pavGpreS Σ,
            !fdslotGpreS Σ, !irefslotGpreS Σ, !bioslotGpreS Σ, !wchGpreS Σ}.
  Context `{!ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.

  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (* ---- WHAT THE ARC STILL OWES ON THE SHELL'S SIDE, by lane: the
             three deposits sh calls ([UkSh.sh_deps]: read(5) -- SH-LINE
             2b, open(15) -- SH-OPEN, write(16) -- E5), write(16) at
             /init's own instance (E5), sh's static state out of the data
             below the frame (E4), and sh's tail (SH-LINE 2b).  Quantified
             over the era's classes for [Hinit_boot]'s own reason: they
             are born by the boot mint. ---- *)
      (* NO [(XI : CurCtx)] BINDER: [echo_Hinit_boot] does not take one
         either -- the working-context class is resolved from the ambient
         instance, and quantifying it here would leave a [_] at the call
         that nothing determines ("Could not find an instance for
         CurCtx"). *)
      (* [GEN] IS BACK, and it has to be: [UkRun.udepw_law] and
         [UkSh.sh_deps] are [urun]-shaped, so they need a full [riscvGS]
         and a [GenId], and the only [riscvGS] in sight is this field's
         [HR] -- the section has the PRE-structure classes only.  Without
         the binder the whole hypothesis loses its instances
         ("Could not find an instance for ?riscvGS0 / ?GEN / ?ctokG0 /
         ?SG"). *)
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (* FOUR SEPARATE COQ-LEVEL ENTAILMENTS under a COQ existential,
            not one [iProp] conjunction under an Iris one.  Each is owed
            whole by a different lane, and [echo_Hinit_boot] takes them as
            Coq premises -- an Iris [∃] would have to be opened inside the
            proofmode and its components could not be handed to a Coq
            argument position at all.  Every one of them is at
            [UexecExecInst.uprogSG_free]: that is the acceptance test, and
            it is readable here. *)
         exists Rsh : gname -> gname -> gname -> iProp Σ,
           (⊢ UkRun.udepw_law (PS := uprogSG_free) 16)
           /\ (⊢ UkSh.sh_deps (PS := uprogSG_free))
           /\ (⊢ UInitSh.sh_pay_state Rsh 0%nat)
           /\ (⊢ UInitSh.sh_pay_rest Rsh))
      (* ---- ...AND THE TRACE INVARIANT, which is E5's ---- *)
      (Hphi : forall (Hinv : invGS Σ)
                     (γgen γstart γreg γd γsw γobs γhist : gname)
                     (c : app_fixed app_echo)
                     (T : list mobs) (g' : gstate) (h : list mobs),
         ⊢ @power_interp Σ
              (boot_fixedGS Hinv γgen γstart γreg γd XV6_DISK_BYTES γsw
                 (xv6_slot (app_names app_echo) (app_pred app_echo) cov
                    (FsImg.sb_logstart sb) γd γsw γreg γstart c)
                 γobs T (obs_ledger_at (app_R app_echo c) γobs) γhist
                 (app_tag app_echo c) (echo_Htagp c) (echo_Htagt c)
                 (app_fixed app_echo) c) g' -∗
           ghost_var γobs (1/2) h -∗ ⌜obs_wf h g'⌝ -∗
           ▷ xv6_slot (app_names app_echo) (app_pred app_echo) cov
               (FsImg.sb_logstart sb) γd γsw γreg γstart c -∗
           ▷ obs_ledger_at (app_R app_echo c) γobs -∗
           ◇ ⌜app_phi app_echo g' h⌝)
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_echo g2 κs.
  Proof.
    intros n κs t2 g2 Hn.
    (* EVERY OBLIGATION GOES IN AS A HOLE, and that is not a style choice.
       Handing [xv6_app_adequacy] its fifteen arguments at once makes the
       elaborator unify each one against a record field whose type it is
       still solving, and it does not come back (measured: 47 GB RSS in 59
       seconds, killed by the build cap; the theorem's STATEMENT and these
       intros elaborate promptly, so the blow-up is this application and
       nothing before it).  With holes, each obligation is checked against
       a type that is already known. *)
    (* FIFTEEN HOLES, AND THE BULLETS IN THE ORDER [refine] LEAVES THEM.
       Handing [xv6_app_adequacy] its arguments instead of holes makes the
       elaborator unify each one against a record field whose type it is
       still solving, and it does not come back (measured: 47 GB RSS in 59
       seconds).  Offering the same [exact]s to every goal with a [try
       first [...]] sweep is worse: each is then tried against
       [Hinit_boot]'s goal as well, which is that unification twice over
       (493 GB in nine minutes, killed).  With holes the elaboration is
       prompt -- and THREE of the fifteen never become goals at all:
       [HRt], [Htagp] and [Htagt] are fixed by unification, because
       [Hphi]'s own statement above names [echo_Htagp c] and [echo_Htagt
       c] inside [boot_fixedGS].  The twelve that remain are these, in
       this order (read off the elaborator, not guessed). *)
    refine (xv6_app_adequacy Σ g sb nib cov app_echo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n κs t2 g2 Hn).
    - exact echo_Hbirth.
    - exact echo_HR0.
    - exact echo_Hpow.
    - (* POINTWISE, not as one term.  [echo_Htx]/[echo_Hrx] state the era
         identification with [fileG] and [uartGhostG] as INSTANCE binders,
         ahead of [HR]; the record field puts [HR] first and [fileG] after
         it.  [exact echo_Htx] therefore asks for one unification of two
         [box]-quantified UART bodies at once, and it does not come back
         (measured: 34 GB RSS in 45 seconds).  Introducing the field's own
         binders first turns it into an application at known arguments. *)
      
      intros HR HF c r γ Heq Huart.
      exact (echo_Htx (HF := HF) HR c r γ Heq Huart).
    - 
      intros HR HF c r γ Heq Huart.
      exact (echo_Hrx (HF := HF) HR c r γ Heq Huart).
    - exact echo_Happ_boot.
    - exact (echo_Happ_init g sb nib cov Himg Hdk Hsb Hcov).
    - (* ---- [Hinit_boot]: E2's own, and the only obligation of the
             record this lane owes.  Everything it needs is at
             [UexecExecInst.uprogSG_free]: the shell's deposits come in as
             [Hsh_owed] at that instance, and [echo_Hinit_boot] builds
             /init's slot from them without ever touching the supply. ---- *)
      
      intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Htag Hgen.
      (* THE TWO LAYERS MEET HERE, and this is the only place they have to.
         [Heq] arrives carrying [app_echo] at the record's PRE-structure
         counter; [echo_Hinit_boot] -- and every [AppInv] law its proof
         uses -- is at the FIXED layer's.  [Hgen] says they are the same
         term at this instance, so one [rewrite] puts the equation where
         the laws are. *)
      rewrite <- Hgen in Heq, Htag |- *.
      destruct (Hsh_owed HR GEN HBs HFd HIr HPav HWc HF)
        as (Rsh & Hw16 & Hdeps & Hst & Hre).
      iIntros "#Hinv Hb".
      (* [GEN] is IMPLICIT and fixed by unification -- from [Hw16] first
         and [Heq] after, both of which carry the record's own [GenId].
         Naming it here would pin the wrong one: the [GEN] this field
         binds is not the one [app_echo] was elaborated at. *)
      iApply (echo_Hinit_boot HR GEN Rsh c r Hw16 Hdeps Hst Hre
                Heq Htag with "Hinv Hb").
    - exact Hphi.
    - exact Hgen0.
    - exact Hpow0.
    - exact Himg.
  Qed.


End EchoAdequacy.