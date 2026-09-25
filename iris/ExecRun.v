(* ===================================================================== *)
(* ExecRun.v -- THE U-TIER exec RULE, over the general bundle.            *)
(*                                                                       *)
(* design/user-exec.md section 2, lane EX-4.  [ExecBundle.exec_bundle_of] *)
(* says what an exec bundle is made of -- (W) the resolution, (L) the     *)
(* loadability, (E) the entry -- and says nothing about how a PROCESS     *)
(* gets from there to a WP.  That last step was written twice, inline,    *)
(* inside the two program supplies ([UInitSh.init_exec_sup_of_sh_slot]    *)
(* and [UShEchoPay.sh_exec_sup_echo_wq_holds]), and it is the same step   *)
(* both times.  It is here once.                                         *)
(*                                                                       *)
(* WHAT THE STEP IS.  The exec leaf takes a DEPOSIT at the trapping key   *)
(* ([UkRunExecRef.udepw_at_refR]); the bundle is stated at a key too.     *)
(* Fusing them is [sbundle_pay_refR_of_exec] below: one key, the bundle's *)
(* premises in, the deposit out.  Everything above it is plumbing: the    *)
(* supply [uexec_sup_run] is that at EVERY key the run may be at (which   *)
(* is forced -- [UkRun.urun] binds the image, the break, the descriptor   *)
(* view and the generation under its own existential, so no lemma up the  *)
(* chain can name them), and [wp_uk_ecall_exec_run] is the leaf composed  *)
(* with it.                                                              *)
(*                                                                       *)
(* WHY THE ENTRY SITS UNDER THAT ∀ AND NOT BESIDE IT.  The design page    *)
(* writes the rule with [image_entry f Q Pay X] as a premise of the rule  *)
(* itself.  It cannot be: [ExecEntry.image_entry] names the CALLER'S      *)
(* IMAGE [M] and its argv pointer, because the entry has to consume the   *)
(* caller's own argument reading (ExecEntry.v's second EX-1 ruling), and  *)
(* [M] is bound by [urun].  So the entry is owed at every image the run   *)
(* may be at, which is exactly what both landed suppliers do -- they read *)
(* their own node off the LENT heap and build the entry there.  EX-3's    *)
(* second prize (an agreement lemma for [exec_args_of] plus a congruence  *)
(* for [kexec_image_ok]) is what would lift it back out; nothing else     *)
(* will.                                                                 *)
(*                                                                       *)
(* THERE IS NO SUCCESS CONTINUATION.  A successful exec never returns to  *)
(* this WP -- the process continues as [X] at the loaded key, which is    *)
(* what [image_entry] promised -- so the rule's ONLY continuation is the  *)
(* failure arm: the refund [R] the supplier named, the caller's own half  *)
(* of its working directory back, and the run at [a0 := -1].  That        *)
(* asymmetry is the honest shape of exec and is why the entry is a        *)
(* separate theorem rather than a postcondition.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import ProcGeom.        (* [tf_arg_idx] *)
(* THE GHOST BINDER LIST'S DEFINING MODULES, each one IMPORTED and not
   merely required ([PinnedExec.v]'s note): a field instance is inert
   wherever its module is not imported. *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG] *)
Require Import UserFd.          (* [ufdG], [ufd_auth] *)
Require Import UserHeap.        (* [uheap] *)
Require Import UserPerm.        (* [uperm] *)
Require Import UserCwd.         (* [ucwd] *)
Require Import ChildTok.        (* [my_pay] *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun.
Require Import UkRunSys.        (* [usysno], [wp_uk_ecall_exec_at_cwd] *)
Require Import UkRunExecRef.    (* [udepw_at_refR] / [sbundle_pay_refR] and
                                   the two leaves at a supplier-named refund *)
Require Import UexecExecInst.   (* THE INSTANCE: [xfam_exec] / [sbundle_at] *)
Require Import ElfFile.         (* [elf_bytes] *)
Require Import PathElems.       (* [path_elems] *)
Require Import SpecKexec.       (* [kexec_loadable] *)
Require Import SpecSysExec.     (* [exec_path_of] / [sys_exec_au_pre] *)
Require Import PieceFam.        (* [pfam] / [pf_at] *)
Require Import SysOpenDefs.     (* [aopen_commit_at] *)
Require Import AppCfg AppInv.   (* [appE], [app_inv], [app_pred] *)
Require Import FsCfg.           (* [fsc_fs]: THE file-system configuration the
                                   deposit's own instance is stated at *)
Require Import FsBlocks.        (* [fs_names] *)
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import ExecEntry.       (* [image_entry] / [image_entry_taint] *)
Require Import ExecArgs.        (* [image_entry_of_at_reading]: EX-3's lift,
                                   which is what lets the entry below be
                                   stated OUTSIDE the key's forall *)
Require Import ExecBundle.      (* [ex_node_id] / [exec_bundle_of] *)
Require Import PinnedObs.       (* [pobs_walk] / [pobs_aopen]: THE PIN SUPPLIER *)
Require Import PinnedExec.      (* [pin_resolves] / [pobs_node_id] *)
Require Import FsAbsEra.        (* [ex_start] / [ax_hops_triv] *)
Require Import FsAbsDefs.       (* [anode] / [aview] (FsAbs's own rule: LAST) *)
Import Defs.

Local Open Scope Z_scope.

Section ExecRun.
  (* [UInitSh]'s context minus the console and echo cameras: the kernel's
     deposit instance is AMBIENT ([UexecExecInst] declares [uexecSG_xv6] and
     [uprogSG_gen] globally) and a local [Context {SG}] beside it would be
     two [sbundle]s that print identically. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* ------------------------------------------------------------------ *)
  (*  1.  (W) AS ONE RESOURCE                                             *)
  (* ------------------------------------------------------------------ *)

  (* [ExecBundle.exec_bundle_of]'s three walk premises, with the SUPPLIER'S
     own families where they belong -- inside.  The bundle leaves them as
     parameters because the deposit site is what closes them
     ([PinnedExec.pinned_exec_bundle] does the [iExists]); a RULE has to
     close them, because the process that execs does not get to choose the
     cursor family of the walk it is about to run. *)
  Definition exec_walk_of (cw : Z) (T : iProp Σ) (pl : list (bv 8))
      (a : anode) : iProp Σ :=
    (∃ (P Pmiss : nat -> Z -> iProp Σ)
       (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
       ex_start fsc_fs cw P Pmiss pl ∗
       pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Fo ∗
       ex_node_id T (P (length (path_elems pl))) Fo.(pf_recv) a)%I.

  (* SUPPLIER ONE: THE PIN.  The application asserts the file-system shape
     as an invariant and reads the walk out of it -- [PinnedObs]'s three
     lemmas, at [PinnedExec.pin_resolves_at]'s one hypothesis. *)
  Lemma exec_walk_of_pin (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (a : anode) :
    pin_resolves_at Pin cw pl hops ino a ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv fsc_fs -∗
    exec_walk_of cw T pl a.
  Proof using .
    intros Hres. iIntros "#Hcl #Hinv". rewrite /exec_walk_of.
    iExists (pobs_P T hops), (pobs_Pmiss T), (pobs_Fo Pin T).
    iSplitL.
    { iApply (pobs_walk fsc_fs Pin T (pobs_Pmiss T) cw pl hops ino a Hres
                with "[] Hcl Hinv").
      iApply pobs_miss_taint_Pmiss. }
    iSplitR.
    { iApply (pobs_aopen fsc_fs Pin T with "Hcl Hinv"). }
    rewrite /pobs_Fo /pfam_triv. cbn [pf_recv].
    iApply (pobs_node_id Pin T cw pl hops ino a Hres).
  Qed.

  (* [FsAbsEra.ep_start_triv] at the exec side.  It is not there because
     nothing below needed it; the two are the same three lines. *)
  Lemma ex_start_triv (γfs : fs_names) (cw : Z) (pl : list (bv 8)) :
    ⊢ ex_start γfs cw (fun _ _ => True%I) (fun _ _ => True%I) pl.
  Proof using .
    rewrite /ex_start. iIntros (r) "_". iModIntro.
    iSplit; [done |]. rewrite /ex_hops_from. iApply ax_hops_triv.
  Qed.

  (* SUPPLIER TWO: THE TAINT.  A process that answers for nothing learns
     nothing from the walk: every cursor is [True], the observation opens
     nothing ([FsAbsInvFire.fsabs_aopen] is the same two lines, here so
     that this file does not depend on the generic supply), and the node
     the walk reports is identified only by the taint itself. *)
  Lemma exec_walk_of_taint (T : iProp Σ) (cw : Z) (pl : list (bv 8))
      (a : anode) :
    □ T -∗ exec_walk_of cw T pl a.
  Proof using .
    iIntros "#HT". rewrite /exec_walk_of.
    iExists (fun _ _ => True%I), (fun _ _ => True%I),
            (pfam_triv (fun _ _ _ => True%I)).
    iSplitL; [ iApply ex_start_triv | ].
    iSplitR.
    { iApply pf_at_triv. rewrite /aopen_commit_at.
      iIntros (I i b) "%Hi Ha". iModIntro. by iFrame "Ha". }
    rewrite /ex_node_id /pfam_triv. cbn [pf_recv].
    iIntros "!>" (v i b) "_ _". iRight. iExact "HT".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  ONE KEY: THE BUNDLE IS THE DEPOSIT                              *)
  (* ------------------------------------------------------------------ *)

  (* [UexecExecInst.sbundle_pay_exec_intro_ref] with the refund's
     consequence a parameter (lane M6b): the same deposit, its refund wand
     stated at whatever the supplier wants back instead of the record's
     exit payload.  Same proof.  It stood in [UInitSh] -- a PROGRAM file --
     because /init's child was the first caller that needed it; it is the
     general deposit introduction and belongs beside the rule. *)
  Lemma sbundle_pay_exec_intro_refR (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) (R : iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    □ (Rs -∗ R) -∗
    my_pay (uvis_gen W) Q -∗
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W) (uvis_secc W)
      Q P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) (uvis_ch W) (uvis_pid W) -∗
    sbundle_pay_refR X Q R W.
  Proof using .
    iIntros "#Hrf Hmp H". rewrite /sbundle_pay_refR.
    iExists (xfam_at Q (xfam_exec P Pmiss Fo Rs)).
    iSplitR; [ done | ].
    iSplitR; [ iExact "Hrf" | ].
    rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle /=. iFrame "Hmp". iExact "H".
  Qed.

  (* THE SEAM.  [ExecBundle.exec_bundle_of] at the key
     [UkRun.uvis_of_run m pc M pm sz fdv c gn cs pidv false] -- whose cwd is
     [c], whose image is [M], whose a0 and a1 are the register file's and
     whose descriptor view is [fdv] -- is exactly the deposit the exec leaf
     consumes.  Both program supplies end in these four lines; this is them.

     THE REFUND IS A PARAMETER, and has to be: what a FAILED exec hands back
     is whatever went in, and for /init's child that is the lend with its
     credential, which does not fit the record's own exit family
     ([UkRunExecRef.v]'s header).  [R := Pay] with the identity wand is the
     general reading -- the linear payload comes back -- and a record whose
     exit owes nothing reads [UkRun.ukn_pay N (-1)] off it for free. *)
  Lemma sbundle_pay_refR_of_exec (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (c : Z) (gn : gname) (cs : gset gname)
      (pidv : mword 32) (pv av : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (nl : nat) (Pay R : iProp Σ) :
    kexec_loadable f ->
    (* the two argument registers, as the caller's own instruction
       sequence left them *)
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    exec_path_of M pv pl ->
    (* NO ALL-PARKED ROW (lane OFF-HAND-6, H3): the taint arm asks for
       none, because the half a held row's fire needs is in the descriptor
       bundle and the kernel holds it (design/app-file.md SS3 fact 4). *)
    □ (Pay -∗ R) -∗
    my_pay gn (ukn_pay N) -∗
    exec_walk_of c T pl (MkAnode (AFile f) nl) -∗
    image_entry f M av fdv c secc_all cs pidv (ukn_pay N) Pay X -∗
    image_entry_taint T (ukn_pay N) X -∗
    Pay -∗
    sbundle_pay_refR X (ukn_pay N) R
      (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all).
  Proof using .
    intros Hload Ha0 Ha1 Hpath.
    iIntros "#Hrf Hmp Hw #Hcon #Hgen HPay".
    iDestruct "Hw" as (P Pmiss Fo) "(Hst & Hobs & #Hid)".
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))
                    (tf_arg_idx 0) = pv)
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))
                    (tf_arg_idx 1) = av)
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    iApply (sbundle_pay_exec_intro_refR X
              (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
              (ukn_pay N) R P Pmiss Fo Pay with "Hrf [Hmp]").
    { cbn [uvis_gen uvis_of_run]. iExact "Hmp". }
    rewrite Ea0 Ea1. cbn [uvis_M uvis_cwd uvis_secc uvis_fd uvis_ch uvis_pid uvis_of_run].
    iApply (exec_bundle_of fsc_fs X T P Pmiss Fo c secc_all pl f nl Pay (ukn_pay N)
              M pv av fdv cs pidv
              Hload Hpath with "Hst Hobs Hid Hcon Hgen HPay").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE SUPPLY: THE BUNDLE AT EVERY KEY THE RUN MAY BE AT           *)
  (* ------------------------------------------------------------------ *)

  (* WHAT THE PROGRAM ACTUALLY CARRIES.  [UkRun.urun] binds the image, the
     permission map, the break, the descriptor view, the generation, the
     children set and the pid under its own existential, so a lemma stated
     where the program is cannot name any of them: what it can carry is the
     bundle AT EVERY such key, with the two authorities LENT so that the
     facts about the key -- the path string in the caller's own rodata, its
     argv node, the length of its descriptor list -- can be read off them
     (UkRun.v's note at [udepw_at]).  That loan is the whole reason this
     shape exists and is not a bare conjunction.

     [cs] and [pidv] are bound and NOT lent here: a supplier that reads
     neither states its entry at the bound pair, which is what "the identity
     rows are the caller's knowledge" means for a program that has none.
     One that DOES read them takes [uexec_sup_run_ids] below.

     [pv] and [av] -- the path pointer and the argument vector -- are
     PARAMETERS rather than [m !!! a0] / [m !!! a1]: a supplier knows the
     two addresses it put there (they are its own rodata's and its own
     node's), and the rule takes the two equations against the register
     file.  That is design/user-exec.md section 2's own [m[a0] = pv] line,
     and it is what keeps [Regidx] out of a program's supply lemma. *)
  Definition uexec_sup_run (N : uk_names Σ) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cs : gset gname) (pidv : mword 32),
       (* ...and whether that table holds a pipe row (design/pipe.md, "The
          exit path"): the new image's entry (E) asks for it, because the
          run it builds carries it and the exit leaf mints the tear-down's
          bundle row off it.  It is a fact about the EXEC'ING process's
          table ([SpecKexec.kexec_image_ok_fd]), i.e. about this very
          [fdv], and it is persistent, so nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (* (W)'s pure input: the path the caller's a0 names, off its image *)
       ⌜exec_path_of M pv pl⌝ ∗
       (* (W) *)
       exec_walk_of c T pl (MkAnode (AFile f) nl) ∗
       (* (E) *)
       image_entry f M av fdv c secc_all cs pidv
         (ukn_pay N) Pay uslot ∗
       (* ...AND THE LINEAR PAYLOAD ITSELF, HANDED OVER HERE and not beside
          the rule.  It has to be here: what a supplier may need the loan
          FOR includes reading its own payload against the key's authorities
          -- sh's child reads fd 1's row off the table the ledger fragment
          it is about to spend agrees with -- and a [Pay] taken outside the
          ∀ is not in scope when the authorities are. *)
       Pay)%I.

  (* ...AND WITH THE IDENTITY AUTHORITIES LENT TOO (lane EXEC-SEAM).  A
     supplier that wants to SAY what the resumed key's children set and pid
     are -- /init's, for the shell it starts: "no children yet, and not
     <init>" -- reads them off the record's authority against its own
     fragments, exactly as it reads the image off the heap. *)
  Definition uexec_sup_run_ids (N : uk_names Σ) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cs : gset gname) (pidv : mword 32),
       (* ...and whether that table holds a pipe row (design/pipe.md, "The
          exit path"): the new image's entry (E) asks for it, because the
          run it builds carries it and the exit leaf mints the tear-down's
          bundle row off it.  It is a fact about the EXEC'ING process's
          table ([SpecKexec.kexec_image_ok_fd]), i.e. about this very
          [fdv], and it is persistent, so nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       urun_ids N cs pidv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       urun_ids N cs pidv ∗
       ⌜exec_path_of M pv pl⌝ ∗
       exec_walk_of c T pl (MkAnode (AFile f) nl) ∗
       image_entry f M av fdv c secc_all cs pidv
         (ukn_pay N) Pay uslot ∗
       Pay)%I.

  (* the forgetful direction: a supplier that reads no identity row hands
     the loan straight back *)
  Lemma uexec_sup_run_ids_of_sup (N : uk_names Σ) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8))
      (f : elf_bytes) (nl : nat) (Pay : iProp Σ) :
    uexec_sup_run N pv av c T pl f nl Pay -∗
    uexec_sup_run_ids N pv av c T pl f nl Pay.
  Proof using .
    rewrite /uexec_sup_run /uexec_sup_run_ids.
    iIntros "H" (M pm sz fdv cs pidv) "#Hnpw Hh Hf Hids".
    iDestruct ("H" $! M pm sz fdv cs pidv with "Hnpw Hh Hf") as "(Hh & Hf & Hr)".
    iFrame "Hh Hf Hids Hr".
  Qed.

  (* THE DEPOSIT, out of the supply. *)
  Lemma udepw_at_refR_of_sup (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay R : iProp Σ) :
    kexec_loadable f ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    □ (Pay -∗ R) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_sup_run N pv av c T pl f nl Pay -∗
    udepw_at_refR N m pc c R.
  Proof using .
    intros Hload Ha0 Ha1. iIntros "#Hrf #Hgen Hsup".
    rewrite /udepw_at_refR. iIntros (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf".
    rewrite /uexec_sup_run.
    iDestruct ("Hsup" $! M pm sz fdv cs pidv with "Hnpw Hh Hf")
      as "(Hh & Hf & %Hpath & Hw & #Hcon & HPay)".
    iFrame "Hh Hf".
    iApply (sbundle_pay_refR_of_exec uslot T N m pc M pm sz fdv c gn cs pidv
              pv av pl f nl Pay R Hload Ha0 Ha1 Hpath
              with "Hrf Hmp Hw Hcon Hgen HPay").
  Qed.

  Lemma udepw_at_refR_ids_of_sup_ids (N : uk_names Σ) (m : regfile)
      (pc : mword 64) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8))
      (f : elf_bytes) (nl : nat) (Pay R : iProp Σ) :
    kexec_loadable f ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    □ (Pay -∗ R) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_sup_run_ids N pv av c T pl f nl Pay -∗
    udepw_at_refR_ids N m pc c R.
  Proof using .
    intros Hload Ha0 Ha1. iIntros "#Hrf #Hgen Hsup".
    rewrite /udepw_at_refR_ids. iIntros (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf Hids".
    rewrite /uexec_sup_run_ids.
    iDestruct ("Hsup" $! M pm sz fdv cs pidv with "Hnpw Hh Hf Hids")
      as "(Hh & Hf & Hids & %Hpath & Hw & #Hcon & HPay)".
    iFrame "Hh Hf Hids".
    iApply (sbundle_pay_refR_of_exec uslot T N m pc M pm sz fdv c gn cs pidv
              pv av pl f nl Pay R Hload Ha0 Ha1 Hpath
              with "Hrf Hmp Hw Hcon Hgen HPay").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE RULE                                                        *)
  (* ------------------------------------------------------------------ *)

  (* design/user-exec.md section 2's [wp_uk_ecall_exec_run], at the shapes
     the landed seam forces: (W) and (E) inside the supply (the key is
     [urun]'s, not the caller's), (L) as the one decidable pure premise, the
     taint arm beside the entry, and NO SUCCESS CONTINUATION -- on success
     the process continues as [uslot] at the loaded key, which is what
     [image_entry] promised.  What comes back on the failure arm is the
     caller's own half of its working directory (a program that execs in a
     loop still knows where it is), the refund the supplier named, and the
     run at [a0 := -1]. *)
  Lemma wp_uk_ecall_exec_run (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (T : iProp Σ)
      (pv av : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (nl : nat) (Pay R : iProp Σ) :
    usysno m = USYS_exec ->
    (* the path pointer and the argument vector, as the caller's own
       instruction sequence left them *)
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* (L), by computation ([ElfLoadable.kexec_loadable_of_b]) *)
    kexec_loadable f ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    (* what a failed exec is worth to the caller *)
    □ (Pay -∗ R) -∗
    (* the taint arm: an application that is already tainted runs on the
       generic family, whatever the kernel loaded *)
    image_entry_taint T (ukn_pay N) uslot -∗
    (* (W) + (E) + the linear resource the new image owns from birth, at
       every key this run may be at *)
    uexec_sup_run N pv av c T pl f nl Pay -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Ha1 Hal4 Hload.
    iIntros "#Hi Hrun Hcwd #Hrf #Hgen Hsup Hcont".
    iApply (wp_uk_ecall_exec_at_cwd_refR N h m pc avail c R Hn Hal4
              with "Hi Hrun Hcwd [Hsup] Hcont").
    iApply (udepw_at_refR_of_sup N m pc pv av c T pl f nl Pay R
              Hload Ha0 Ha1 with "Hrf Hgen Hsup").
  Qed.

  (* ...and the same at a supply that reads the record's identity rows *)
  Lemma wp_uk_ecall_exec_run_ids (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (T : iProp Σ)
      (pv av : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (nl : nat) (Pay R : iProp Σ) :
    usysno m = USYS_exec ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    kexec_loadable f ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    □ (Pay -∗ R) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_sup_run_ids N pv av c T pl f nl Pay -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Ha1 Hal4 Hload.
    iIntros "#Hi Hrun Hcwd #Hrf #Hgen Hsup Hcont".
    iApply (wp_uk_ecall_exec_at_cwd_refR_ids N h m pc avail c R Hn Hal4
              with "Hi Hrun Hcwd [Hsup] Hcont").
    iApply (udepw_at_refR_ids_of_sup_ids N m pc pv av c T pl f nl Pay R
              Hload Ha0 Ha1 with "Hrf Hgen Hsup").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  THE CONSUMER TESTS -- what a NEW program writes                 *)
  (* ------------------------------------------------------------------ *)

  (* A TAINTED CALLER'S ENTRY IS THE GENERIC ONE.  [image_entry] promises
     the new image's WP given the kernel's image fact; a process whose
     application is already tainted promises it given nothing, so the
     specific entry is the generic one with the taint spent inside.  This is
     the whole content of "exec'ing an unverified binary is the same rule". *)
  Lemma image_entry_of_taint (f : elf_bytes) (M : gmap Z (bv 8))
      (av : mword 64) (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ) (Pay : iProp Σ)
      (T : iProp Σ) (X : uvis -d> iPropO Σ) :
    (* ...AND IT TAKES NOTHING ABOUT THE CALLER'S OFFSETS (lane
       OFF-HAND-6, H3).  Lane OFF-HAND-4 took the row off the VERIFIED
       entries and lane OFF-HAND-5 put the TAINT arm's on the builder;
       fact 4 deletes it, so a tainted caller with a HELD descriptor
       execs exactly as one without. *)
    □ T -∗ image_entry_taint T Q X -∗
    image_entry f M av sts cw secc cs pidv Q Pay X.
  Proof using .
    iIntros "#HT #Hgen". rewrite /image_entry /image_entry_taint.
    iIntros "!>" (na alen afun W') "%Hok _ _ _ _ _ Hmp _".
    iApply ("Hgen" $! W' with "HT Hmp").
  Qed.

  (* THE PATH READING, as a program actually holds it: the string exec
     resolves lives in the caller's OWN image, and the caller can read it
     back off whatever heap the run turns out to be at.  Both landed
     programs have exactly this shape ([UInitSh]'s [init_rodata] against
     [UserHeap.uheap_text], [UShEcho]'s [ush_cmd] against
     [uheap_ubytesq_img]); stating it as a premise is what lets a rule stop
     short of naming any one program's catalog. *)
  Definition uexec_path_reading (N : uk_names Σ) (pv : mword 64)
      (pl : list (bv 8)) : iProp Σ :=
    (□ (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
          uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
          ⌜exec_path_of M pv pl⌝))%I.

  (* ...AND THE ARGUMENT READING BESIDE IT (lane EX-3).  The vector a
     program laid out, read back off whatever heap the run turns out to be
     at: [ExecArgs.exec_args_of_uargv] is what a program with an owned
     vector discharges it with, [ExecArgs.exec_args_of_uargv_img] what one
     with a constant image does. *)
  Definition uexec_args_reading (N : uk_names Σ) (av : mword 64)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) : iProp Σ :=
    (□ (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
          uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
          ⌜exec_args_of M av na alen afun⌝))%I.

  (* EX-3'S PAYOFF ON THE SUPPLY.  [uexec_sup_run] carries (E) INSIDE the
     key's [∀] because [image_entry] names the caller's image [M] and its
     argv pointer -- design/user-exec.md section 2's first placement, whose
     own note says an [exec_args_of] agreement lemma is the only thing that
     would lift them out.  It exists now
     ([ExecArgs.exec_args_of_agree], with the [kexec_image_ok] congruence
     [ExecArgs.kexec_image_ok_ext]), so the entry may be stated OUTSIDE the
     [∀] at the ONE argument shape the caller's own reading names -- which
     is the form a program proof is naturally in.

     [fdv], [cs] and [pidv] STAY under the [∀]: they are the RECORD's data,
     not the image's, and no reading determines them.  A program that reads
     none of them quantifies over all three, which is exactly the shape
     echo's landed entry already has.  [uexec_sup_run]'s statement is
     untouched; this is a corollary. *)
  Lemma uexec_sup_run_of_entry_at (N : uk_names Σ) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes) (nl : nat)
      (Pay : iProp Σ) (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) :
    uexec_path_reading N pv pl -∗
    uexec_args_reading N av na alen afun -∗
    exec_walk_of c T pl (MkAnode (AFile f) nl) -∗
    □ (∀ (fdv : list fdstate) (cs : gset gname) (pidv : mword 32),
         image_entry_at f na alen afun fdv c secc_all cs pidv (ukn_pay N) Pay uslot) -∗
    Pay -∗
    uexec_sup_run N pv av c T pl f nl Pay.
  Proof using .
    iIntros "#Hrd #Hra Hw #Hcon HPay".
    rewrite /uexec_sup_run. iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct ("Hrd" $! M pm sz with "Hheap") as %Hpath.
    iDestruct ("Hra" $! M pm sz with "Hheap") as %Hargs.
    iFrame "Hheap Hufd". iSplitR; [ by iPureIntro | ]. iFrame "Hw".
    iSplitR "HPay"; [ | iExact "HPay" ].
    iDestruct ("Hcon" $! fdv cs pidv) as "#He".
    iApply (image_entry_of_at_reading f M av fdv c secc_all cs pidv (ukn_pay N) Pay
              uslot na alen afun Hargs with "He").
  Qed.

  (* ---- TEST ONE: A PROGRAM WITH A PIN EXECS THE FILE IT PINNED --------
     Everything a new program's author writes is here and nothing else: a
     claim law for a pin of their own choosing, the application invariant,
     the path they pass, the loadability of the image by computation, and
     the ENTRY -- the exec'd program's own theorem.  Its continuation is
     the entry's [X] (here [UexecRet.uslot], which the deposit fixes), and
     what comes back on the only arm that returns is the refund. *)
  Lemma wp_uk_ecall_exec_pin_test (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (pv av : mword 64)
      (Pin : aview -> Prop) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (f : elf_bytes) (nl : nat) (Pay R : iProp Σ) :
    usysno m = USYS_exec ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* (L), decided *)
    kexec_loadable f ->
    (* (W)'s content: at every view the claim admits, this path walks to a
       node that is THIS file *)
    pin_resolves Pin c pl hops ino f nl ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv fsc_fs -∗
    uexec_path_reading N pv pl -∗
    (* (E): the exec'd program's own theorem, at the caller's readings *)
    □ (∀ (M : gmap Z (bv 8)) (fdv : list fdstate) (cs : gset gname)
         (pidv : mword 32),
         image_entry f M av fdv c secc_all cs pidv (ukn_pay N) Pay uslot) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    □ (Pay -∗ R) -∗
    Pay -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗ R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Ha1 Hal4 Hload Hres.
    iIntros "#Hi Hrun Hcwd #Hcl #Hinv #Hrd #Hcon #Hgen #Hrf HPay Hcont".
    iApply (wp_uk_ecall_exec_run N h m pc avail c T pv av pl f nl Pay R
              Hn Ha0 Ha1 Hal4 Hload
              with "Hi Hrun Hcwd Hrf Hgen [HPay] Hcont").
    rewrite /uexec_sup_run. iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct ("Hrd" $! M pm sz with "Hheap") as %Hpath.
    iFrame "Hheap Hufd". iSplitR; [ by iPureIntro | ].
    iSplitR "HPay"; [ | iSplitR; [ iApply "Hcon" | iExact "HPay" ] ].
    iApply (exec_walk_of_pin Pin T c pl hops ino
              (MkAnode (AFile f) nl) Hres with "Hcl Hinv").
  Qed.

  (* ---- TEST TWO: THE SAME RULE AT THE TAINT --------------------------
     The caller answers for NOTHING about the file its path names, and the
     system stays safe: every cursor of the walk is [True], the node is
     identified only by the taint, and the continuation is the generic slot
     at whatever the kernel loaded.  [f] and (L) are still parameters and
     are never read on this route -- they are what REFUTES the deposit's
     not-loadable arm, and at the taint BOTH arms go to the generic entry,
     so any witness serves.  Nothing here is new machinery: it is
     [wp_uk_ecall_exec_run] at [exec_walk_of_taint] and
     [image_entry_of_taint]. *)
  Lemma wp_uk_ecall_exec_taint_test (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (T : iProp Σ) (pv : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (nl : nat) :
    usysno m = USYS_exec ->
    m !!! Regidx a0_idx = pv ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    kexec_loadable f ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    □ T -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_path_reading N pv pl -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hal4 Hload.
    iIntros "#Hi Hrun Hcwd #HT #Hgen #Hrd Hcont".
    iApply (wp_uk_ecall_exec_run N h m pc avail c T pv
              (m !!! Regidx a1_idx) pl f nl emp emp
              Hn Ha0 eq_refl Hal4 Hload
              with "Hi Hrun Hcwd [] Hgen [] [Hcont]").
    - iIntros "!> _". done.
    - rewrite /uexec_sup_run. iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
      iDestruct ("Hrd" $! M pm sz with "Hheap") as %Hpath.
      iFrame "Hheap Hufd". iSplitR; [ by iPureIntro | ].
      iSplitR; [ iApply (exec_walk_of_taint with "HT") | ].
      iSplitR; [ | done ].
      iApply (image_entry_of_taint with "HT Hgen").
    - iIntros (h') "Hcwd _ Hrun". iApply ("Hcont" with "Hcwd Hrun").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  (W) AT A CLAIM THAT DOES NOT PIN THE LINK COUNT                 *)
  (*                                                                      *)
  (*  design/user-tree.md section 6, TL-2's FINDING 2, and this is the     *)
  (*  ExecRun half of its price (the other is                             *)
  (*  [PinnedObs.pin_resolves_abs], section 10 there).                     *)
  (*                                                                      *)
  (*  WHY IT IS NEEDED.  [exec_walk_of] names an [anode] -- a node WITH    *)
  (*  its link count -- because [ExecBundle.ex_node_id] concludes [b = a]. *)
  (*  An application whose claim is about the NAMESPACE (AppTree's owned   *)
  (*  subtree) pins a row's CONTENT and not its count, and the count is    *)
  (*  genuinely not determined: two views the claim admits may differ in   *)
  (*  the terminal row's [nlink] (a hard link outside the subtree), so     *)
  (*  there is no [a] the identification could be stated at.  Hence a      *)
  (*  CONTENT-level twin of the triple, and a rule at it.                  *)
  (*                                                                      *)
  (*  WHY IT COSTS NOTHING.  The count is never SPENT: exec's arm (a)      *)
  (*  reads the image out of [AFile f] and substitutes the count it was    *)
  (*  handed, and its arm (b) refutes [~ anode_loadable a], which is a     *)
  (*  fact about [an_node a] alone.  So the three lemmas below are         *)
  (*  [ExecBundle]'s three with [ex_node_id] replaced by [ex_node_abs] and *)
  (*  the same proofs; ExecBundle's own statements are untouched, and      *)
  (*  [exec_walk_of_abs_of_walk] makes every landed [exec_walk_of]         *)
  (*  supplier -- the pin's and the taint's -- feed the new rule as well.  *)
  (* ------------------------------------------------------------------ *)

  (* [ExecBundle.ex_node_id] at the observed row's CONTENT *)
  Definition ex_node_abs (T : iProp Σ) (Pfin : Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (nd : absnode) : iProp Σ :=
    (□ (∀ (v : aview) (i : Z) (b : anode),
          Pfin i -∗ Φo v i b -∗ ⌜an_node b = nd⌝ ∨ T))%I.

  Global Instance ex_node_abs_persistent T Pfin Φo nd :
    Persistent (ex_node_abs T Pfin Φo nd).
  Proof using . rewrite /ex_node_abs. apply _. Qed.

  Lemma ex_node_abs_of_id (T : iProp Σ) (Pfin : Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (a : anode) :
    ex_node_id T Pfin Φo a -∗ ex_node_abs T Pfin Φo (an_node a).
  Proof using .
    rewrite /ex_node_id /ex_node_abs. iIntros "#Hid !>" (v i b) "HP Hr".
    iDestruct ("Hid" $! v i b with "HP Hr") as "[%Hb | HT]";
      [ iLeft; iPureIntro; by rewrite Hb | iRight; iExact "HT" ].
  Qed.

  Definition exec_walk_of_abs (cw : Z) (T : iProp Σ) (pl : list (bv 8))
      (nd : absnode) : iProp Σ :=
    (∃ (P Pmiss : nat -> Z -> iProp Σ)
       (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)),
       ex_start fsc_fs cw P Pmiss pl ∗
       pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Fo ∗
       ex_node_abs T (P (length (path_elems pl))) Fo.(pf_recv) nd)%I.

  (* the forgetful direction: an [anode]-level walk is a content-level one *)
  Lemma exec_walk_of_abs_of_walk (cw : Z) (T : iProp Σ) (pl : list (bv 8))
      (a : anode) :
    exec_walk_of cw T pl a -∗ exec_walk_of_abs cw T pl (an_node a).
  Proof using .
    rewrite /exec_walk_of /exec_walk_of_abs.
    iIntros "H". iDestruct "H" as (P Pmiss Fo) "(Hst & Hobs & #Hid)".
    iExists P, Pmiss, Fo. iFrame "Hst Hobs".
    iApply (ex_node_abs_of_id with "Hid").
  Qed.

  (* SUPPLIER: A CONTENT PIN ([PinnedObs.pin_resolves_abs]).  The tree
     application's frozen deed is one ([TreeExec.exec_walk_of_own]); so is
     any pin that names a row up to its count. *)
  Lemma exec_walk_of_abs_pin (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (nd : absnode) :
    pin_resolves_abs Pin cw pl hops ino nd ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv fsc_fs -∗
    exec_walk_of_abs cw T pl nd.
  Proof using .
    intros Hres. iIntros "#Hcl #Hinv". rewrite /exec_walk_of_abs.
    iExists (pobs_P T hops), (pobs_Pmiss T), (pobs_Fo Pin T).
    iDestruct (pinned_obs_abs fsc_fs Pin T (pobs_Pmiss T) cw pl hops ino nd
                 Hres with "[] Hcl Hinv") as "(Hw & Ho & #Hid)";
      [ iApply pobs_miss_taint_Pmiss | ].
    iFrame "Hw Ho". rewrite /ex_node_abs /pobs_Fo /pfam_triv. cbn [pf_recv].
    iIntros "!>" (v i b) "HP Hr".
    iDestruct ("Hid" $! v i b with "HP Hr") as "[%Hid' | HT]";
      [ iLeft; iPureIntro; exact (proj2 Hid') | iRight; iExact "HT" ].
  Qed.

  Lemma exec_walk_of_abs_taint (T : iProp Σ) (cw : Z) (pl : list (bv 8))
      (nd : absnode) :
    □ T -∗ exec_walk_of_abs cw T pl nd.
  Proof using .
    iIntros "#HT".
    iPoseProof (exec_walk_of_taint T cw pl (MkAnode nd 0%nat) with "HT") as "Hw".
    iApply (exec_walk_of_abs_of_walk cw T pl (MkAnode nd 0%nat) with "Hw").
  Qed.

  (* ---- 6a.  THE BUNDLE, AT THE CONTENT ------------------------------- *)

  (* [ExecBundle.exec_slot_of_entry_at]'s proof, at [ex_node_abs]: arm (a)
     reads [f] out of the content and keeps the kernel's own count, arm (b)
     refutes [~ anode_loadable] from the content alone. *)
  Lemma exec_slot_of_entry_at_abs (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (Pfin : Z -> iProp Σ) (Φo : aview -> Z -> anode -> iProp Σ)
      (f : elf_bytes) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (cw : Z) (secc : mword 64) (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    (* NO ALL-PARKED ROW (lane OFF-HAND-6, H3): the taint arm asks for
       none, because the half a held row's fire needs is in the descriptor
       bundle and the kernel holds it (design/app-file.md SS3 fact 4). *)
    ex_node_abs T Pfin Φo (AFile f) -∗
    image_entry_at f na alen afun sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T Q X -∗
    Pay -∗
    exec_slot_pre X Q Pfin Φo cw secc na alen afun sts cs pidv.
  Proof using .
    intros Hload. iIntros "#Hid #Hcon #Hgen HPay".
    rewrite /exec_slot_pre /ex_node_abs /image_entry_at /image_entry_taint.
    iSplitL "HPay".
    - (* ---- ARM (a): the observed content IS the caller's file ---- *)
      iIntros (av' i f' nl' W') "HP Hrecv %Hload' %Hok %Hcwq %Hlzq %Hscw %Hchq %Hpiq #Hp".
      iPoseProof ("Hid" $! av' i (MkAnode (AFile f') nl')) as "Hid'".
      iDestruct ("Hid'" with "HP Hrecv") as "[%Hnode | HT]"; last first.
      { iApply ("Hgen" $! W' with "HT Hp"). }
      cbn [an_node] in Hnode. injection Hnode as Hf. subst f'.
      iApply ("Hcon" $! W' with "[%] [%] [%] [%] [%] [%] Hp HPay");
        [ exact Hok | exact Hcwq | exact Hlzq | exact Hscw | exact Hchq | exact Hpiq ].
    - (* ---- ARM (b): a loadable content IS loadable ---- *)
      iIntros (av' i a W') "HP Hrecv %Hnload %Hkey %Hcwq %Hlzq %Hscw %Hchq %Hpiq #Hp".
      iPoseProof ("Hid" $! av' i a) as "Hid'".
      iDestruct ("Hid'" with "HP Hrecv") as "[%Hnode | HT]"; last first.
      { iApply ("Hgen" $! W' with "HT Hp"). }
      exfalso. apply Hnload. exists f, (an_nlink a).
      split; [ | exact Hload ].
      destruct a as [nd k]. cbn [an_node an_nlink] in Hnode |- *.
      by rewrite Hnode.
  Qed.

  Lemma sys_exec_slot_of_entry_abs (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (P : nat -> Z -> iProp Σ) (Φo : aview -> Z -> anode -> iProp Σ)
      (f : elf_bytes) (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (M : gmap Z (bv 8)) (pv av : mword 64)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* NO ALL-PARKED ROW (lane OFF-HAND-6, H3): the taint arm asks for
       none, because the half a held row's fire needs is in the descriptor
       bundle and the kernel holds it (design/app-file.md SS3 fact 4). *)
    ex_node_abs T (P (length (path_elems pl))) Φo (AFile f) -∗
    image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T Q X -∗
    Pay -∗
    pf_at (fun S => sys_exec_slot_pre S Q P Φo cw secc M pv av sts cs pidv)
      (MkPfam X Pay).
  Proof using .
    intros Hload Hpath. iIntros "#Hid #Hcon #Hgen HPay".
    rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [ | iExact "HPay" ].
    rewrite /sys_exec_slot_pre. iIntros (pl' na alen afun) "%Hpath' %Hargs".
    rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath).
    iApply (exec_slot_of_entry_at_abs X T (P (length (path_elems pl))) Φo f
              Pay Q cw secc na alen afun sts cs pidv Hload
              with "Hid [] Hgen HPay").
    iApply (image_entry_at_of f M av sts cw secc cs pidv Q Pay X na alen afun Hargs
              with "Hcon").
  Qed.

  Lemma exec_bundle_of_abs (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (cw : Z) (secc : mword 64) (pl : list (bv 8)) (f : elf_bytes)
      (Pay : iProp Σ) (Q : Z -> iProp Σ)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) :
    kexec_loadable f ->
    exec_path_of M pv pl ->
    (* NO ALL-PARKED ROW (lane OFF-HAND-6, H3): the taint arm asks for
       none, because the half a held row's fire needs is in the descriptor
       bundle and the kernel holds it (design/app-file.md SS3 fact 4). *)
    ex_start fsc_fs cw P Pmiss pl -∗
    pf_at (aopen_commit_at (fs_gamma_L fsc_fs) appE) Fo -∗
    ex_node_abs T (P (length (path_elems pl))) Fo.(pf_recv) (AFile f) -∗
    image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry_taint T Q X -∗
    Pay -∗
    sys_exec_au_pre (MkPfam X Pay) (fs_gamma_L fsc_fs) fsc_fs cw secc Q P Pmiss Fo
      M pv av sts cs pidv.
  Proof using .
    intros Hload Hpath. iIntros "Hwalk Hobs #Hid #Hcon #Hgen HPay".
    rewrite /sys_exec_au_pre. iSplitL "Hwalk".
    { iIntros (pl') "%Hpath'".
      rewrite (exec_path_of_uniq M pv pl' pl Hpath' Hpath). iExact "Hwalk". }
    iSplitL "Hobs"; [ iExact "Hobs" | ].
    iApply (sys_exec_slot_of_entry_abs X T P Fo.(pf_recv) f Pay Q cw secc pl M pv av
              sts cs pidv Hload Hpath with "Hid Hcon Hgen HPay").
  Qed.

  (* ---- 6b.  THE DEPOSIT AND THE RULE, AT THE CONTENT ----------------- *)

  Lemma sbundle_pay_refR_of_exec_abs (X : uvis -d> iPropO Σ) (T : iProp Σ)
      (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (c : Z) (gn : gname) (cs : gset gname)
      (pidv : mword 32) (pv av : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (Pay R : iProp Σ) :
    kexec_loadable f ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    exec_path_of M pv pl ->
    (* NO ALL-PARKED ROW (lane OFF-HAND-6, H3): the taint arm asks for
       none, because the half a held row's fire needs is in the descriptor
       bundle and the kernel holds it (design/app-file.md SS3 fact 4). *)
    □ (Pay -∗ R) -∗
    my_pay gn (ukn_pay N) -∗
    exec_walk_of_abs c T pl (AFile f) -∗
    image_entry f M av fdv c secc_all cs pidv (ukn_pay N) Pay X -∗
    image_entry_taint T (ukn_pay N) X -∗
    Pay -∗
    sbundle_pay_refR X (ukn_pay N) R
      (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all).
  Proof using .
    intros Hload Ha0 Ha1 Hpath.
    iIntros "#Hrf Hmp Hw #Hcon #Hgen HPay".
    iDestruct "Hw" as (P Pmiss Fo) "(Hst & Hobs & #Hid)".
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))
                    (tf_arg_idx 0) = pv)
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))
                    (tf_arg_idx 1) = av)
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    iApply (sbundle_pay_exec_intro_refR X
              (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)
              (ukn_pay N) R P Pmiss Fo Pay with "Hrf [Hmp]").
    { cbn [uvis_gen uvis_of_run]. iExact "Hmp". }
    rewrite Ea0 Ea1. cbn [uvis_M uvis_cwd uvis_secc uvis_fd uvis_ch uvis_pid uvis_of_run].
    iApply (exec_bundle_of_abs X T P Pmiss Fo c secc_all pl f Pay (ukn_pay N)
              M pv av fdv cs pidv Hload Hpath
              with "Hst Hobs Hid Hcon Hgen HPay").
  Qed.

  (* [uexec_sup_run] at the content: the same loan, the same entry, the
     walk at a node the caller knows only up to its link count. *)
  Definition uexec_sup_run_abs (N : uk_names Σ) (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes)
      (Pay : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cs : gset gname) (pidv : mword 32),
       (* ...and whether that table holds a pipe row (design/pipe.md, "The
          exit path"): the new image's entry (E) asks for it, because the
          run it builds carries it and the exit leaf mints the tear-down's
          bundle row off it.  It is a fact about the EXEC'ING process's
          table ([SpecKexec.kexec_image_ok_fd]), i.e. about this very
          [fdv], and it is persistent, so nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       ⌜exec_path_of M pv pl⌝ ∗
       exec_walk_of_abs c T pl (AFile f) ∗
       image_entry f M av fdv c secc_all cs pidv (ukn_pay N) Pay uslot ∗
       Pay)%I.

  Lemma udepw_at_refR_of_sup_abs (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (pv av : mword 64)
      (c : Z) (T : iProp Σ) (pl : list (bv 8)) (f : elf_bytes)
      (Pay R : iProp Σ) :
    kexec_loadable f ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    □ (Pay -∗ R) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_sup_run_abs N pv av c T pl f Pay -∗
    udepw_at_refR N m pc c R.
  Proof using .
    intros Hload Ha0 Ha1. iIntros "#Hrf #Hgen Hsup".
    rewrite /udepw_at_refR. iIntros (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf".
    rewrite /uexec_sup_run_abs.
    iDestruct ("Hsup" $! M pm sz fdv cs pidv with "Hnpw Hh Hf")
      as "(Hh & Hf & %Hpath & Hw & #Hcon & HPay)".
    iFrame "Hh Hf".
    iApply (sbundle_pay_refR_of_exec_abs uslot T N m pc M pm sz fdv c gn cs pidv
              pv av pl f Pay R Hload Ha0 Ha1 Hpath
              with "Hrf Hmp Hw Hcon Hgen HPay").
  Qed.

  (* THE RULE at a content-level walk.  [wp_uk_ecall_exec_run]'s statement
     with the link count gone -- nothing else about it moves, and the two
     are interderivable at a supply that names a count
     ([exec_walk_of_abs_of_walk]). *)
  Lemma wp_uk_ecall_exec_run_abs (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (T : iProp Σ)
      (pv av : mword 64)
      (pl : list (bv 8)) (f : elf_bytes) (Pay R : iProp Σ) :
    usysno m = USYS_exec ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = av ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    kexec_loadable f ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    □ (Pay -∗ R) -∗
    image_entry_taint T (ukn_pay N) uslot -∗
    uexec_sup_run_abs N pv av c T pl f Pay -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Ha1 Hal4 Hload.
    iIntros "#Hi Hrun Hcwd #Hrf #Hgen Hsup Hcont".
    iApply (wp_uk_ecall_exec_at_cwd_refR N h m pc avail c R Hn Hal4
              with "Hi Hrun Hcwd [Hsup] Hcont").
    iApply (udepw_at_refR_of_sup_abs N m pc pv av c T pl f Pay R
              Hload Ha0 Ha1 with "Hrf Hgen Hsup").
  Qed.

End ExecRun.
